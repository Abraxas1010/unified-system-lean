import HeytingLean.Compiler.TensorLogic.Demo.Program

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demo

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)

/-!
## Demo theorem (declarative/monotone reading)

This file proves a small “certified fact” about the demo program: the expected reachability
atoms are derivable from the demo’s base facts by iterating the (ground, unary) rules.

Note: this theorem is *about the demo program as a logic program* (monotone boolean reading),
not about performance or about fuzzy/F₂ solver choices.
-/

private def baseAtoms : List Atom :=
  demoInputFacts.map (fun aw => aw.1)

namespace Ground

def toAtom? (p : AtomPat) : Option Atom := do
  let args ←
    p.args.mapM (fun s =>
      match s with
      | .const c => some c
      | .var _ => none)
  pure { pred := p.pred, args := args }

def unaryGround? (r : Rule) : Option (Atom × Atom) := do
  let head ← toAtom? r.head
  match r.body with
  | [b] =>
      let body ← toAtom? b
      pure (head, body)
  | _ => none

end Ground

open Ground

inductive Derives : Nat → Atom → Prop
  | base {a : Atom} (h : a ∈ baseAtoms) : Derives 0 a
  | step {n : Nat} {r : Rule} {head body : Atom}
      (hr : r ∈ demoProgram.rules)
      (hg : unaryGround? r = some (head, body))
      (hb : Derives n body) :
      Derives (n + 1) head

def Derivable (a : Atom) : Prop := ∃ n, Derives n a

private def edge (x y : String) : Atom := { pred := "edge", args := [x, y] }
private def start (x : String) : Atom := { pred := "start", args := [x] }
private def reach (x : String) : Atom := { pred := "reach", args := [x] }

private theorem base_edge_ab : Derives 0 (edge "a" "b") := by
  refine Derives.base ?_
  simp [baseAtoms, demoInputFacts, edge, atom0]

private theorem base_start_a : Derives 0 (start "a") := by
  refine Derives.base ?_
  simp [baseAtoms, demoInputFacts, start, atom0]

private def rReachB : Rule :=
  { head := pat1 "reach" "b"
  , body := [pat2 "edge" "a" "b"]
  , weight := some 0.95
  }

private def rReachC : Rule :=
  { head := pat1 "reach" "c"
  , body := [pat1 "reach" "b"]
  , weight := some 0.90
  }

private def rReachD : Rule :=
  { head := pat1 "reach" "d"
  , body := [pat1 "reach" "c"]
  , weight := some 0.85
  }

private theorem rReachB_mem : rReachB ∈ demoProgram.rules := by
  simp [demoProgram, rReachB]

private theorem rReachC_mem : rReachC ∈ demoProgram.rules := by
  simp [demoProgram, rReachC]

private theorem rReachD_mem : rReachD ∈ demoProgram.rules := by
  simp [demoProgram, rReachD]

private theorem rReachB_ground : unaryGround? rReachB = some (reach "b", edge "a" "b") := by
  rfl

private theorem rReachC_ground : unaryGround? rReachC = some (reach "c", reach "b") := by
  rfl

private theorem rReachD_ground : unaryGround? rReachD = some (reach "d", reach "c") := by
  rfl

private theorem derives_reach_b : Derives 1 (reach "b") := by
  refine Derives.step (n := 0) (r := rReachB) (head := reach "b") (body := edge "a" "b") ?_ ?_ ?_
  · exact rReachB_mem
  · exact rReachB_ground
  · exact base_edge_ab

private theorem derives_reach_c : Derives 2 (reach "c") := by
  refine Derives.step (n := 1) (r := rReachC) (head := reach "c") (body := reach "b") ?_ ?_ ?_
  · exact rReachC_mem
  · exact rReachC_ground
  · exact derives_reach_b

private theorem derives_reach_d : Derives 3 (reach "d") := by
  refine Derives.step (n := 2) (r := rReachD) (head := reach "d") (body := reach "c") ?_ ?_ ?_
  · exact rReachD_mem
  · exact rReachD_ground
  · exact derives_reach_c

theorem demo_monotone_derives_expected :
    ∀ a : Atom, a ∈ expectedMonotoneReach → Derivable a := by
  intro a ha
  have hb : a = reach "b" ∨ a = reach "c" ∨ a = reach "d" := by
    simpa [expectedMonotoneReach, reach, atom1] using ha
  rcases hb with rfl | hb
  · exact ⟨1, derives_reach_b⟩
  rcases hb with rfl | rfl
  · exact ⟨2, derives_reach_c⟩
  · exact ⟨3, derives_reach_d⟩

end Demo
end TensorLogic
end Compiler
end HeytingLean
