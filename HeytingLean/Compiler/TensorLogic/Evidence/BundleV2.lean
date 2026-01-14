import Std
import Lean.Data.Json

import HeytingLean.Compiler.TensorLogic.Bot
import HeytingLean.Compiler.TensorLogic.Evidence.Canonical

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Evidence

open Std
open Lean
open Lean.Json

open HeytingLean.Compiler.TensorLogic (Atom Mode TNorm Program RunConfig RunResult Facts)
open HeytingLean.Compiler.TensorLogic (BotKind Explanation)

/-!
Evidence bundle schema v2:

- supports multiple demos via a `demo` name
- includes a list of certification references (Lean declaration names)
- includes a stable hash (`bundle_hash`) computed as SHA-256 of canonical JSON bytes of the bundle
  with the hash field omitted

This is intentionally “audit-friendly”: small, deterministic, and replayable.
-/

structure DemoConfig where
  deterministic : Bool := true
  maxIter : Nat := 50
  /-- The *exact* epsilon string used for replay (decimal). -/
  epsRaw : String := "0.000001"
  /-- A stable hint for humans/auditors; not used for replay. -/
  epsQ16Hint : Nat := quantizeQ16Clamp01 1e-6
  maxAtoms : Nat := 20
  tnorm : TNorm := .product
  deriving Repr

def runConfigToDemoConfig (cfg : RunConfig) (deterministic : Bool) (epsRaw : String) : DemoConfig :=
  { deterministic := deterministic
  , maxIter := cfg.maxIter
  , epsRaw := epsRaw
  , epsQ16Hint := quantizeQ16Clamp01 cfg.eps
  , maxAtoms := cfg.maxAtoms
  , tnorm := cfg.tnorm
  }

private def demoConfigToJson (cfg : DemoConfig) : Json :=
  Json.mkObj
    [ ("deterministic", Json.bool cfg.deterministic)
    , ("max_iter", Json.num (JsonNumber.fromNat cfg.maxIter))
    , ("eps_raw", Json.str cfg.epsRaw)
    , ("eps_q16", weightToJsonQ16 cfg.epsQ16Hint)
    , ("max_atoms", Json.num (JsonNumber.fromNat cfg.maxAtoms))
    , ("tnorm", Json.str (tnormToString cfg.tnorm))
    ]

structure BotRunResult where
  bot : BotKind
  mode : Mode
  tnorm : TNorm
  outputFactsQ16 : List (Atom × Nat)
  explanation? : Option Explanation := none
  deriving Repr

private def explanationToJson (e : Explanation) : Json :=
  Json.mkObj
    [ ("bot", Json.str (BotKind.toString e.bot))
    , ("iters", Json.num (JsonNumber.fromNat e.iters))
    , ("delta", weightToJsonQ16 (quantizeQ16Clamp01 e.delta))
    , ("converged", Json.bool e.converged)
    , ("rules", Json.num (JsonNumber.fromNat e.rules))
    ]

private def botRunToJson (r : BotRunResult) : Json :=
  let base :=
    [ ("bot", Json.str (BotKind.toString r.bot))
    , ("mode", Json.str (modeToString r.mode))
    , ("tnorm", Json.str (tnormToString r.tnorm))
    , ("facts", factsQ16ToJson r.outputFactsQ16)
    ]
  let fields :=
    match r.explanation? with
    | none => base
    | some e => base ++ [("explain", explanationToJson e)]
  Json.mkObj fields

structure BundleV2 where
  format : String := "heytinglean.tensorlogic.bundle"
  version : Nat := 2
  toolVersion : String := "heytinglean.tensorlogic.harness/1"
  demo : String
  timestamp? : Option String := none
  gitCommit? : Option String := none
  program : Program
  inputFactsQ16 : List (Atom × Nat)
  config : DemoConfig
  results : List BotRunResult
  certRefs : Array String := #[]
  bundleHash : String := ""
  deriving Repr

private def bundleToJson (b : BundleV2) (includeHash : Bool) : Json :=
  let base : List (String × Json) :=
    [ ("format", Json.str b.format)
    , ("version", Json.num (JsonNumber.fromNat b.version))
    , ("tool_version", Json.str b.toolVersion)
    , ("demo", Json.str b.demo)
    , ("program", programToJson b.program)
    , ("input_facts", factsQ16ToJson b.inputFactsQ16)
    , ("config", demoConfigToJson b.config)
    , ("results", Json.arr (b.results.map botRunToJson |>.toArray))
    , ("cert_refs", Json.arr (b.certRefs.map Json.str))
    ]
  let withTs :=
    match b.timestamp? with
    | none => base
    | some s => base ++ [("timestamp", Json.str s)]
  let withGit :=
    match b.gitCommit? with
    | none => withTs
    | some s => withTs ++ [("git_commit", Json.str s)]
  let withHash :=
    if includeHash then withGit ++ [("bundle_hash", Json.str b.bundleHash)] else withGit
  Json.mkObj withHash

def toJson (b : BundleV2) : Json :=
  bundleToJson b (includeHash := true)

def toJsonForHash (b : BundleV2) : Json :=
  bundleToJson b (includeHash := false)

def canonicalJsonString (b : BundleV2) : String :=
  canonicalString (toJson b)

def canonicalJsonStringForHash (b : BundleV2) : String :=
  canonicalString (toJsonForHash b)

def computeBundleHash (b : BundleV2) : String :=
  sha256Hex (canonicalJsonStringForHash b)

def withComputedHash (b : BundleV2) : BundleV2 :=
  { b with bundleHash := computeBundleHash b }

/-!
V2 parsing (used by `tensorlogic_verify_evidence` / `tensorlogic_replay`).

We intentionally keep parsing minimal: it extracts only the “header-ish” fields needed for routing,
while hash verification operates on the raw JSON object by removing the `bundle_hash` field and
re-canonicalizing.
-/

private def expectObj (j : Json) : Except String Json := do
  match j.getObj? with
  | .ok _ => pure j
  | .error _ => throw "expected JSON object"

private def getStr (obj : Json) (k : String) : Except String String := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getStr? with
      | .ok s => pure s
      | .error _ => throw s!"field '{k}' not a string"
  | .error _ => throw s!"missing field '{k}'"

private def parseNat (j : Json) : Except String Nat := do
  match j.getNum? with
  | .ok n =>
      if n.mantissa < 0 then
        throw s!"expected Nat, got {n}"
      let m : Nat := n.mantissa.natAbs
      if n.exponent == 0 then
        pure m
      else
        let pow10 : Nat := 10 ^ n.exponent
        if m % pow10 != 0 then
          throw s!"expected Nat, got {n}"
        pure (m / pow10)
  | .error _ => throw "expected JSON number"

private def getNatField (obj : Json) (k : String) : Except String Nat := do
  match obj.getObjVal? k with
  | .ok v => parseNat v
  | .error _ => throw s!"missing field '{k}'"

private def getOptStr (obj : Json) (k : String) : Except String (Option String) := do
  match obj.getObjVal? k with
  | .error _ => pure none
  | .ok v =>
      match v.getStr? with
      | .ok s => pure (some s)
      | .error _ => throw s!"field '{k}' not a string"

def parseBundleV2 (j : Json) : Except String BundleV2 := do
  let j ← expectObj j
  let format ← getStr j "format"
  let version ← getNatField j "version"
  if version != 2 then
    throw s!"unsupported bundle version {version}"
  let toolVersion ← getStr j "tool_version"
  let demo ← getStr j "demo"
  let timestamp? ← getOptStr j "timestamp"
  let gitCommit? ← getOptStr j "git_commit"
  let bundleHash ← getStr j "bundle_hash"
  pure
    { format := format
    , version := version
    , toolVersion := toolVersion
    , demo := demo
    , timestamp? := timestamp?
    , gitCommit? := gitCommit?
    , program := { rules := [] }
    , inputFactsQ16 := []
    , config := {}
    , results := []
    , certRefs := #[]
    , bundleHash := bundleHash
    }

end Evidence
end TensorLogic
end Compiler
end HeytingLean
