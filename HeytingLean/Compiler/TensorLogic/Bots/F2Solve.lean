import Std
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Validate

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Bots

open Std
open HeytingLean.Compiler.TensorLogic (Mode Ops RunConfig Program Rule Atom AtomPat Facts RunResult unify instantiate Subst)

-- Only used to satisfy `Array.get!` / `Array.back!` defaults; indices are guarded by loop bounds.
private instance : Inhabited Atom :=
  ⟨{ pred := "", args := [] }⟩

/-!
## F₂ solver (finite, exact)

`Mode.f2` uses XOR as “or”, so naive Kleene iteration is not a correct solver for recursive programs
(it can oscillate). This bot implements an *exact* solver on a finite Herbrand universe:

* Compute a finite ground atom universe from the program + base facts (constants only, no function symbols).
* Build the fixed-point equations induced by `stepFromBase`:
  `x = init ⊕ T(x)` over `F₂`, where conjunction is multiplication (`&&`) and disjunction is XOR.
* Enumerate assignments in a deterministic order (false-before-true), returning the first fixed point found
  (lexicographically minimal, hence subset-minimal).

The search is capped by `RunConfig.maxAtoms` to avoid exponential blow-ups.
-/

private def bit (x : Float) : Bool :=
  x != 0.0

private def atomStr (a : Atom) : String :=
  reprStr a

private def dedupSorted (xs : Array String) : Array String := Id.run do
  if xs.isEmpty then
    return xs
  let mut out : Array String := #[xs[0]!]
  for i in [1:xs.size] do
    let x := xs[i]!
    if x != out.back! then
      out := out.push x
  return out

private def sortDedupStrings (xs : List String) : Array String :=
  dedupSorted (xs.toArray.qsort (· < ·))

private def gatherPredArities (p : Program) (init : Facts) : Except String (HashMap String Nat) := do
  -- Validate first to guarantee internal arity consistency.
  let _ ← validateProgram p
  let mut m : HashMap String Nat := {}
  for r in p.rules do
    m := m.insert r.head.pred r.head.arity
    for a in r.body do
      m := m.insert a.pred a.arity
  -- Also include any predicates only present in init facts.
  for (a, _) in init.toListSorted do
    match m.get? a.pred with
    | none => m := m.insert a.pred a.arity
    | some n =>
        if n != a.arity then
          throw s!"arity mismatch for predicate '{a.pred}': saw {n} (rules) and {a.arity} (facts)"
  pure m

private def herbrandUniverse (cfg : RunConfig) (p : Program) (init : Facts) : Except String (Array Atom) := do
  let mut consts : List String := []
  for (a, _) in init.toListSorted do
    consts := consts ++ a.args
  for r in p.rules do
    consts := consts ++ r.head.consts
    for a in r.body do
      consts := consts ++ a.consts

  let constArr := sortDedupStrings consts
  let arities ← gatherPredArities p init
  let preds := (arities.toList.map (fun (kv : String × Nat) => kv.1)).toArray.qsort (· < ·)

  let base := constArr.size
  let mut out : Array Atom := #[]

  for pred in preds do
    let arity := arities.getD pred 0
    if arity > 0 && base == 0 then
      continue
    -- count = base^arity (or 1 when arity=0)
    let mut count : Nat := 1
    for _ in [:arity] do
      count := count * base
      if out.size + count > cfg.maxAtoms then
        throw s!"f2solve: atom universe exceeds maxAtoms={cfg.maxAtoms} (pred '{pred}', arity {arity}, consts {base})"
    for ix in [:count] do
      if out.size ≥ cfg.maxAtoms then
        throw s!"f2solve: atom universe exceeds maxAtoms={cfg.maxAtoms}"
      let mut k := ix
      let mut argsRev : List String := []
      for _ in [:arity] do
        let d := k % base
        k := k / base
        argsRev := constArr[d]! :: argsRev
      out := out.push { pred := pred, args := argsRev }

  -- Ensure base facts are represented even if the predicate never appears in rules.
  -- (Also dedup in case `herbrandUniverse` already generated them.)
  let mut seen : HashSet Atom := {}
  let mut out2 : Array Atom := #[]
  for a in out do
    if !seen.contains a then
      seen := seen.insert a
      out2 := out2.push a
  for (a, _) in init.toListSorted do
    if !seen.contains a then
      seen := seen.insert a
      if out2.size ≥ cfg.maxAtoms then
        throw s!"f2solve: atom universe exceeds maxAtoms={cfg.maxAtoms}"
      out2 := out2.push a
  pure out2

private def matchesForBody
    (byPred : HashMap String (Array Atom))
    (body : List AtomPat) : Array Subst :=
  let bodySorted : List AtomPat :=
    body.toArray.qsort (fun a b => (byPred.getD a.pred #[]).size < (byPred.getD b.pred #[]).size) |>.toList
  bodySorted.foldl
    (fun acc lit =>
      Id.run do
        let mut out : Array Subst := #[]
        let facts := byPred.getD lit.pred #[]
        for s in acc do
          for a in facts do
            match unify lit a s with
            | none => continue
            | some s' => out := out.push s'
        return out)
    #[({} : Subst)]

private def buildContribs
    (p : Program)
    (atoms : Array Atom)
    (atomIx : HashMap Atom Nat) :
    Except String (Array (Array (Array Nat))) := do
  let n := atoms.size
  let mut byPred : HashMap String (Array Atom) := {}
  for a in atoms do
    let bucket := byPred.getD a.pred (#[] : Array Atom)
    byPred := byPred.insert a.pred (bucket.push a)

  let mut contribs : Array (Array (Array Nat)) := Array.replicate n #[]

  for r in p.rules do
    let rw := bit (r.weight.getD 1.0)
    if !rw then
      continue
    let ms := matchesForBody byPred r.body
    for s in ms do
      match instantiate r.head s with
      | none => continue
      | some hAtom =>
          match atomIx.get? hAtom with
          | none => throw s!"f2solve: head atom not in universe: {atomStr hAtom}"
          | some hi =>
              let mut bodyIxs : Array Nat := #[]
              let mut ok := true
              for lit in r.body do
                match instantiate lit s with
                | none => ok := false; break
                | some bAtom =>
                    match atomIx.get? bAtom with
                    | none => throw s!"f2solve: body atom not in universe: {atomStr bAtom}"
                    | some bi => bodyIxs := bodyIxs.push bi
              if ok then
                contribs := contribs.set! hi (contribs[hi]!.push bodyIxs)

  pure contribs

private def satisfies
    (assign initBits : Array Bool)
    (contribs : Array (Array (Array Nat))) : Bool := Id.run do
  let n := assign.size
  for hi in [:n] do
    let mut rhs := initBits[hi]!
    for term in contribs[hi]! do
      let mut t := true
      for bi in term do
        t := t && assign[bi]!
        if !t then
          break
      rhs := Bool.xor rhs t
    if assign[hi]! != rhs then
      return false
  return true

private partial def searchFirst
    (i : Nat)
    (assign : Array Bool)
    (initBits : Array Bool)
    (contribs : Array (Array (Array Nat))) : Option (Array Bool) :=
  if i = assign.size then
    if satisfies assign initBits contribs then some assign else none
  else
    let a0 := assign.set! i false
    match searchFirst (i + 1) a0 initBits contribs with
    | some sol => some sol
    | none =>
        let a1 := assign.set! i true
        searchFirst (i + 1) a1 initBits contribs

def runF2Solve (cfg : RunConfig) (p : Program) (init : Facts) : Except String RunResult := do
  if cfg.mode != .f2 then
    throw "F2Solve bot requires mode=f2."

  let atoms ← herbrandUniverse cfg p init
  let n := atoms.size
  if n > cfg.maxAtoms then
    throw s!"f2solve: atom universe size {n} exceeds maxAtoms={cfg.maxAtoms}"

  let mut atomIx : HashMap Atom Nat := {}
  for i in [:n] do
    atomIx := atomIx.insert atoms[i]! i

  let mut initBits : Array Bool := Array.replicate n false
  for i in [:n] do
    initBits := initBits.set! i (bit (init.get (atoms[i]!)))

  let contribs ← buildContribs p atoms atomIx
  let seed : Array Bool := Array.replicate n false

  match searchFirst 0 seed initBits contribs with
  | none =>
      throw "f2solve: no fixed point found (unexpected for finite systems)"
  | some sol =>
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
