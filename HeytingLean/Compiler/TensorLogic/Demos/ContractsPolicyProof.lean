import HeytingLean.Compiler.TensorLogic.Demos.ContractsPolicy

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demos

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)

/-!
## Contracts/policy closure demo theorem (declarative/monotone reading)

This is a tiny “certified claim” about the contracts/policy toy demo:

If the base event `event(signed, contract)` holds, then an obligation
`obl(notify, counterparty)` is derivable by one step.
-/

private def baseAtoms : List Atom :=
  contractsPolicyInputFacts.map (fun aw => aw.1)

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
      (hr : r ∈ contractsPolicyProgram.rules)
      (hg : unaryGround? r = some (head, body))
      (hb : Derives n body) :
      Derives (n + 1) head

def Derivable (a : Atom) : Prop := ∃ n, Derives n a

private def signedEvt : Atom :=
  contractsPolicyAtom2 "event" "signed" "contract"

private def notifyObl : Atom :=
  contractsPolicyAtom2 "obl" "notify" "counterparty"

private def signedPat : AtomPat :=
  contractsPolicyPat2 "event" "signed" "contract"

private def notifyPat : AtomPat :=
  contractsPolicyPat2 "obl" "notify" "counterparty"

private def rNotify : Rule :=
  contractsPolicyRuleNotify

private theorem rNotify_mem : rNotify ∈ contractsPolicyProgram.rules := by
  simp [contractsPolicyProgram, rNotify]

private theorem rNotify_ground :
    unaryGround? rNotify = some (notifyObl, signedEvt) := by
  rfl

private theorem base_signed : Derives 0 signedEvt := by
  refine Derives.base ?_
  simp [baseAtoms, contractsPolicyInputFacts, signedEvt]

theorem contractsPolicy_derives_notify :
    Derivable notifyObl := by
  refine ⟨1, ?_⟩
  refine Derives.step (n := 0) (r := rNotify)
    (head := notifyObl)
    (body := signedEvt)
    rNotify_mem rNotify_ground base_signed

end Demos
end TensorLogic
end Compiler
end HeytingLean
