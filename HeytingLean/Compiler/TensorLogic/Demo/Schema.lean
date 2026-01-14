import Std
import Lean.Data.Json

import HeytingLean.Util.JCS
import HeytingLean.Util.SHA

import HeytingLean.Compiler.TensorLogic.AST
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bot

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demo

open Std
open Lean
open Lean.Json

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)
open HeytingLean.Compiler.TensorLogic (Mode TNorm Facts RunConfig RunResult)
open HeytingLean.Compiler.TensorLogic (BotKind Explanation)

/-!
Evidence bundle schema for the “applied-first” TensorLogic demo.

Design goal: deterministic, byte-identical serialization in deterministic mode.

We avoid relying on platform-dependent float formatting by canonicalizing all weights via Q16.16
fixed-point integers (Nat). The canonical JSON string is produced by `HeytingLean.Util.JCS`.
-/

private def q16Scale : Nat := 65536

private def quantizeQ16Clamp01 (x : Float) : Nat :=
  let x :=
    if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x
  let q : Int64 := Float.toInt64 (Float.round (x * Float.ofNat q16Scale))
  q.toNatClampNeg

private def padLeftZeros (w : Nat) (s : String) : String :=
  if s.length ≥ w then s else String.mk (List.replicate (w - s.length) '0') ++ s

private def q16ApproxString (q : Nat) : String :=
  let intPart := q / q16Scale
  let rem := q % q16Scale
  -- 6 decimals is enough for a stable “human hint”; the canonical part is `q16`.
  let micro := (rem * 1000000) / q16Scale
  s!"{intPart}.{padLeftZeros 6 (toString micro)}"

private def modeToString : Mode → String
  | .boolean => "boolean"
  | .f2 => "f2"
  | .fuzzy => "fuzzy"
  | .heyting => "heyting"

private def tnormToString : TNorm → String
  | .product => "product"
  | .lukasiewicz => "lukasiewicz"

private def symToJson : Sym → Json
  | .var v => Json.mkObj [("var", Json.str v)]
  | .const c => Json.mkObj [("const", Json.str c)]

private def atomToJson (a : Atom) : Json :=
  Json.mkObj
    [ ("pred", Json.str a.pred)
    , ("args", Json.arr (a.args.map Json.str |>.toArray))
    ]

private def atomPatToJson (a : AtomPat) : Json :=
  Json.mkObj
    [ ("pred", Json.str a.pred)
    , ("args", Json.arr (a.args.map symToJson |>.toArray))
    ]

private def weightToJsonQ16 (q : Nat) : Json :=
  Json.mkObj
    [ ("q16", Json.num (JsonNumber.fromNat q))
    , ("scale", Json.num (JsonNumber.fromNat q16Scale))
    , ("approx", Json.str (q16ApproxString q))
    ]

private def ruleToJson (r : Rule) : Json :=
  let wq := quantizeQ16Clamp01 (r.weight.getD 1.0)
  Json.mkObj
    [ ("head", atomPatToJson r.head)
    , ("body", Json.arr (r.body.map atomPatToJson |>.toArray))
    , ("weight", weightToJsonQ16 wq)
    ]

private def programToJson (p : Program) : Json :=
  Json.mkObj [("rules", Json.arr (p.rules.map ruleToJson |>.toArray))]

private def lexLt (a b : List String) : Bool :=
  match a, b with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true
      else if x = y then lexLt xs ys
      else false

private def atomLt (a b : Atom) : Bool :=
  if a.pred < b.pred then true
  else if a.pred = b.pred then lexLt a.args b.args
  else false

private def factsToQ16Sorted (xs : List (Atom × Float)) : List (Atom × Nat) :=
  let ys := xs.map (fun (aw : Atom × Float) => (aw.1, quantizeQ16Clamp01 aw.2))
  let ys := ys.filter (fun aw => aw.2 != 0)
  ys.toArray.qsort (fun a b => atomLt a.1 b.1) |>.toList

private def factsQ16ToJson (xs : List (Atom × Nat)) : Json :=
  let arr :=
    xs.map (fun aw =>
      Json.mkObj
        [ ("atom", atomToJson aw.1)
        , ("weight", weightToJsonQ16 aw.2)
        ])
  Json.arr (arr.toArray)

structure DemoConfig where
  deterministic : Bool := true
  maxIter : Nat := 50
  epsQ16 : Nat := quantizeQ16Clamp01 1e-6
  maxAtoms : Nat := 20
  tnorm : TNorm := .product
  deriving Repr

private def demoConfigToJson (cfg : DemoConfig) : Json :=
  Json.mkObj
    [ ("deterministic", Json.bool cfg.deterministic)
    , ("max_iter", Json.num (JsonNumber.fromNat cfg.maxIter))
    , ("eps", weightToJsonQ16 cfg.epsQ16)
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

structure EvidenceBundle where
  format : String := "heytinglean.tensorlogic.demo.bundle"
  version : Nat := 1
  timestamp? : Option String := none
  program : Program
  inputFactsQ16 : List (Atom × Nat)
  config : DemoConfig
  results : List BotRunResult
  bundleHash : String := ""
  deriving Repr

private def bundleToJson (b : EvidenceBundle) (includeHash : Bool) : Json :=
  let base : List (String × Json) :=
    [ ("format", Json.str b.format)
    , ("version", Json.num (JsonNumber.fromNat b.version))
    , ("program", programToJson b.program)
    , ("input_facts", factsQ16ToJson b.inputFactsQ16)
    , ("config", demoConfigToJson b.config)
    , ("results", Json.arr (b.results.map botRunToJson |>.toArray))
    ]
  let withTs :=
    match b.timestamp? with
    | none => base
    | some s => base ++ [("timestamp", Json.str s)]
  let withHash :=
    if includeHash then withTs ++ [("bundle_hash", Json.str b.bundleHash)] else withTs
  Json.mkObj withHash

def canonicalJsonString (b : EvidenceBundle) : String :=
  HeytingLean.Util.JCS.canonicalString (bundleToJson b (includeHash := true))

def canonicalJsonStringForHash (b : EvidenceBundle) : String :=
  HeytingLean.Util.JCS.canonicalString (bundleToJson b (includeHash := false))

def computeBundleHash (b : EvidenceBundle) : String :=
  HeytingLean.Util.SHA256.sha256Hex (canonicalJsonStringForHash b |>.toUTF8)

def withComputedHash (b : EvidenceBundle) : EvidenceBundle :=
  { b with bundleHash := computeBundleHash b }

/-!
Utilities that Phase 3 will use when assembling the bundle from actual runs.
-/

def factsFromRunResultQ16Sorted (rr : RunResult) : List (Atom × Nat) :=
  factsToQ16Sorted (rr.facts.toListSorted)

def factsFromFactsQ16Sorted (F : Facts) : List (Atom × Nat) :=
  factsToQ16Sorted (F.toListSorted)

def runConfigToDemoConfig (cfg : RunConfig) (deterministic : Bool) : DemoConfig :=
  { deterministic := deterministic
  , maxIter := cfg.maxIter
  , epsQ16 := quantizeQ16Clamp01 cfg.eps
  , maxAtoms := cfg.maxAtoms
  , tnorm := cfg.tnorm
  }

end Demo
end TensorLogic
end Compiler
end HeytingLean

