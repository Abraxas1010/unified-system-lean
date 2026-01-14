import Std
import HeytingLean.Compiler.TensorLogic.Eval

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Bots

open Std
open HeytingLean.Compiler.TensorLogic (Mode Ops RunConfig Program Rule Atom AtomPat Facts RunResult unify instantiate)

-- Only used to satisfy `Array.get!` defaults; indices are guarded by loop bounds.
instance : Inhabited Atom :=
  ⟨{ pred := "", args := [] }⟩

/-!
## F₂ linear solver (restricted)

This bot is intentionally restricted to the *linear* fragment where every rule body has length ≤ 1.

Rationale: with `Mode.f2`, conjunction is interpreted as multiplication in `F₂`, so rules with
multiple body literals yield *nonlinear* (polynomial) constraints, and “solve by linear algebra” is
not correct in general.

We therefore:
- reject non-linear programs (`∃ rule, body.length ≥ 2`);
- compute a finite atom universe via boolean closure (safe upper bound);
- build an affine linear system `A x = b` over `F₂` for the linear fragment;
- return a canonical solution (free vars = 0), or an error on inconsistency.
-/

private def bit (x : Float) : Bool :=
  x != 0.0

private def rowXor (a b : Array Bool) : Array Bool := Id.run do
  let mut out := a
  for i in [:a.size] do
    out := out.set! i (Bool.xor (a[i]!) (b[i]!))
  out

private def isLinearProgram (p : Program) : Bool :=
  p.rules.all (fun r => r.body.length ≤ 1)

private def universeByBooleanClosure (p : Program) (init : Facts) (maxIter : Nat) : Facts :=
  let cfg : RunConfig := { mode := .boolean, maxIter := maxIter, eps := 0.0 }
  let ops := Ops.forConfig cfg.mode cfg.tnorm
  let initBool : Facts :=
    Facts.fromList ops <|
      init.toListSorted.map (fun (aw : Atom × Float) => (aw.1, if bit aw.2 then 1.0 else 0.0))
  (HeytingLean.Compiler.TensorLogic.run cfg p initBool).facts

private def gaussSolve (mat : Array (Array Bool)) (n : Nat) : Except String (Array Bool) := Id.run do
  -- `mat` is `n` rows, each of length `n+1` (augmented).
  let mut a := mat
  let mut pivotAt : Array (Option Nat) := Array.replicate n none
  let mut row : Nat := 0

  for col in [:n] do
    -- find pivot
    let mut piv : Option Nat := none
    for r in [row:n] do
      if a[r]![col]! then
        piv := some r
        break
    match piv with
    | none => continue
    | some pivRow =>
        -- swap into position `row`
        if pivRow != row then
          let tmp := a[row]!
          a := a.set! row (a[pivRow]!)
          a := a.set! pivRow tmp
        pivotAt := pivotAt.set! col (some row)
        -- eliminate other rows
        for r in [:n] do
          if r != row && a[r]![col]! then
            a := a.set! r (rowXor (a[r]!) (a[row]!))
        row := row + 1
        if row == n then
          break

  -- inconsistency: 0 = 1 row
  for r in [:n] do
    let mut allZero := true
    for c in [:n] do
      if a[r]![c]! then
        allZero := false
        break
    if allZero && a[r]![n]! then
      return .error "inconsistent F₂ linear system (no solution)"

  -- canonical solution: free variables = 0
  let mut x : Array Bool := Array.replicate n false
  for col in [:n] do
    match pivotAt[col]! with
    | none => continue
    | some r => x := x.set! col (a[r]![n]!)
  return .ok x

def runF2Linear (cfg : RunConfig) (p : Program) (init : Facts) : Except String RunResult := do
  if cfg.mode != .f2 then
    throw "F2Linear bot requires mode=f2."
  if !isLinearProgram p then
    throw "F2Linear bot only supports linear programs (each rule body length ≤ 1)."

  let univFacts := universeByBooleanClosure p init (Nat.max cfg.maxIter 64)
  let atoms : Array Atom :=
    univFacts.toListSorted.toArray.map (fun (aw : Atom × Float) => aw.1)

  let n := atoms.size
  let mut atomIx : HashMap Atom Nat := {}
  for i in [:n] do
    atomIx := atomIx.insert atoms[i]! i

  let mut byPred : HashMap String (Array Atom) := {}
  for a in atoms do
    let bucket := byPred.getD a.pred (#[] : Array Atom)
    byPred := byPred.insert a.pred (bucket.push a)

  let mut rows : Array (Array Bool) := Array.replicate n (Array.replicate (n + 1) false)

  -- Base equations: x_i + (deps...) = b_i
  for i in [:n] do
    let a := atoms[i]!
    let mut row : Array Bool := Array.replicate (n + 1) false
    row := row.set! i true
    row := row.set! n (bit (init.get a))
    rows := rows.set! i row

  -- Add linear rule contributions
  for r in p.rules do
    let rw := bit (r.weight.getD 1.0)
    if !rw then
      continue
    match r.body with
    | [] =>
        match instantiate r.head {} with
        | none => throw "F2Linear: unsafe/ungroundable empty-body rule"
        | some h =>
            match atomIx.get? h with
            | none => throw "F2Linear: head atom not in computed universe"
            | some hi =>
                -- toggle constant term
                let row := rows[hi]!
                rows := rows.set! hi (row.set! n (Bool.xor row[n]! true))
    | [lit] =>
        let cand := byPred.getD lit.pred (#[] : Array Atom)
        for bAtom in cand do
          match unify lit bAtom {} with
          | none => continue
          | some s =>
              match instantiate r.head s with
              | none => continue
              | some hAtom =>
                  match atomIx.get? hAtom, atomIx.get? bAtom with
                  | some hi, some bi =>
                      let row := rows[hi]!
                      rows := rows.set! hi (row.set! bi (Bool.xor row[bi]! true))
                  | _, _ => throw "F2Linear: atom not in computed universe"
    | _ :: _ :: _ =>
        -- guarded by `isLinearProgram`
        continue

  let sol ← gaussSolve rows n
  let ops := Ops.forConfig .f2 cfg.tnorm
  let outFacts : List (Atom × Float) :=
    (List.range n).filterMap fun i =>
      if sol[i]! then some (atoms[i]!, 1.0) else none
  pure
    { facts := Facts.fromList ops outFacts
    , iters := 1
    , delta := 0.0
    , converged := true
    }

end Bots
end TensorLogic
end Compiler
end HeytingLean
