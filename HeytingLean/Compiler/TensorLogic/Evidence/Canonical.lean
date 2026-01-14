import Std
import Lean.Data.Json

import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.String.Basic

import HeytingLean.Util.JCS
import HeytingLean.Util.SHA

import HeytingLean.Compiler.TensorLogic.AST
import HeytingLean.Compiler.TensorLogic.Eval

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Evidence

open Std
open Lean
open Lean.Json

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)
open HeytingLean.Compiler.TensorLogic (Mode TNorm Facts RunResult)

/-!
Shared canonicalization utilities for TensorLogic evidence bundles.

Design goal: deterministic, byte-identical serialization in deterministic mode.

We avoid platform-dependent float formatting by canonicalizing all weights via Q16.16 fixed-point
integers (`Nat`). Canonical JSON output uses JCS (see `HeytingLean.Util.JCS`).
-/

def q16Scale : Nat := 65536

def quantizeQ16Clamp01 (x : Float) : Nat :=
  let x :=
    if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x
  let q : Int64 := Float.toInt64 (Float.round (x * Float.ofNat q16Scale))
  q.toNatClampNeg

private def padLeftZeros (w : Nat) (s : String) : String :=
  if s.length ≥ w then s else String.mk (List.replicate (w - s.length) '0') ++ s

def q16ApproxString (q : Nat) : String :=
  let intPart := q / q16Scale
  let rem := q % q16Scale
  let micro := (rem * 1000000) / q16Scale
  s!"{intPart}.{padLeftZeros 6 (toString micro)}"

def modeToString : Mode → String
  | .boolean => "boolean"
  | .f2 => "f2"
  | .fuzzy => "fuzzy"
  | .heyting => "heyting"

def tnormToString : TNorm → String
  | .product => "product"
  | .lukasiewicz => "lukasiewicz"

def symToJson : Sym → Json
  | .var v => Json.mkObj [("var", Json.str v)]
  | .const c => Json.mkObj [("const", Json.str c)]

def atomToJson (a : Atom) : Json :=
  Json.mkObj
    [ ("pred", Json.str a.pred)
    , ("args", Json.arr (a.args.map Json.str |>.toArray))
    ]

def atomPatToJson (a : AtomPat) : Json :=
  Json.mkObj
    [ ("pred", Json.str a.pred)
    , ("args", Json.arr (a.args.map symToJson |>.toArray))
    ]

def weightToJsonQ16 (q : Nat) : Json :=
  Json.mkObj
    [ ("q16", Json.num (JsonNumber.fromNat q))
    , ("scale", Json.num (JsonNumber.fromNat q16Scale))
    , ("approx", Json.str (q16ApproxString q))
    ]

def ruleToJson (r : Rule) : Json :=
  let wq := quantizeQ16Clamp01 (r.weight.getD 1.0)
  Json.mkObj
    [ ("head", atomPatToJson r.head)
    , ("body", Json.arr (r.body.map atomPatToJson |>.toArray))
    , ("weight", weightToJsonQ16 wq)
    ]

def programToJson (p : Program) : Json :=
  Json.mkObj [("rules", Json.arr (p.rules.map ruleToJson |>.toArray))]

def atomKey (a : Atom) : String ×ₗ List String :=
  toLex (a.pred, a.args)

def factKey (aw : Atom × Nat) : (String ×ₗ List String) ×ₗ Nat :=
  toLex (atomKey aw.1, aw.2)

def factLEb (a b : Atom × Nat) : Bool :=
  decide (factKey a ≤ factKey b)

def factsToQ16Sorted (xs : List (Atom × Float)) : List (Atom × Nat) :=
  let ys := xs.map (fun (aw : Atom × Float) => (aw.1, quantizeQ16Clamp01 aw.2))
  let ys := ys.filter (fun aw => aw.2 != 0)
  ys.mergeSort (fun a b => factLEb a b)

def factsQ16ToJson (xs : List (Atom × Nat)) : Json :=
  let arr :=
    xs.map (fun aw =>
      Json.mkObj
        [ ("atom", atomToJson aw.1)
        , ("weight", weightToJsonQ16 aw.2)
        ])
  Json.arr (arr.toArray)

def factsFromRunResultQ16Sorted (rr : RunResult) : List (Atom × Nat) :=
  factsToQ16Sorted (rr.facts.toListSorted)

def factsFromFactsQ16Sorted (F : Facts) : List (Atom × Nat) :=
  factsToQ16Sorted (F.toListSorted)

def canonicalString (j : Json) : String :=
  HeytingLean.Util.JCS.canonicalString j

def sha256Hex (s : String) : String :=
  HeytingLean.Util.SHA256.sha256Hex (s.toUTF8)

end Evidence
end TensorLogic
end Compiler
end HeytingLean
