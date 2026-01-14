import Mathlib.Data.List.Perm.Lattice
import Mathlib.Data.List.Sort

import HeytingLean.Compiler.TensorLogic.Evidence.Canonical

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Evidence

open List
noncomputable section

/-!
## Canonicalization determinism (proof-carrying)

This file proves a small but important “determinism contract” lemma:

`factsToQ16Sorted` is invariant under permutation of its input list.

This is used to justify that evidence bundle emission is independent of upstream collection order
(e.g. hash map fold order), provided the semantic content (multiset of facts) is unchanged.
-/

private def Quant (aw : Atom × Float) : Atom × Nat :=
  (aw.1, quantizeQ16Clamp01 aw.2)

private def Nonzero (aw : Atom × Nat) : Bool :=
  aw.2 != 0

private def r (a b : Atom × Nat) : Prop :=
  factKey a ≤ factKey b

private instance : DecidableRel r := fun a b => by
  classical
  exact inferInstance

private lemma r_decide_eq_factLEb :
    (fun a b => decide (r a b)) = fun a b => factLEb a b := by
  classical
  funext a b
  simp [r, factLEb]

private lemma factKey_injective : Function.Injective factKey := by
  classical
  intro a b h
  cases a with
  | mk aAtom aW =>
    cases b with
    | mk bAtom bW =>
      cases aAtom with
      | mk ap aa =>
        cases bAtom with
        | mk bp ba =>
          have hk0 :
              ofLex (factKey ({ pred := ap, args := aa }, aW)) =
                ofLex (factKey ({ pred := bp, args := ba }, bW)) :=
            congrArg ofLex h
          have hk : atomKey { pred := ap, args := aa } = atomKey { pred := bp, args := ba } :=
            congrArg Prod.fst hk0
          have hw : aW = bW := congrArg Prod.snd hk0
          have hk1 : ofLex (atomKey { pred := ap, args := aa }) =
              ofLex (atomKey { pred := bp, args := ba }) :=
            congrArg ofLex hk
          have hp : ap = bp := by
            simpa [atomKey] using congrArg Prod.fst hk1
          have ha : aa = ba := by
            simpa [atomKey] using congrArg Prod.snd hk1
          cases hp
          cases ha
          cases hw
          rfl

private instance : IsTotal (Atom × Nat) r :=
  ⟨fun a b => by
    classical
    -- totality on the key order
    exact le_total (factKey a) (factKey b)⟩

private instance : IsTrans (Atom × Nat) r :=
  ⟨fun a b c hab hbc => by
    classical
    exact le_trans hab hbc⟩

private instance : IsAntisymm (Atom × Nat) r :=
  ⟨fun a b hab hba => by
    classical
    have : factKey a = factKey b := le_antisymm hab hba
    exact factKey_injective this⟩

theorem factsToQ16Sorted_perm {xs ys : List (Atom × Float)} (h : xs ~ ys) :
    factsToQ16Sorted xs = factsToQ16Sorted ys := by
  -- `map` and `filter` preserve permutations.
  have h1 : xs.map Quant ~ ys.map Quant := h.map _
  have h2 : (xs.map Quant).filter Nonzero ~ (ys.map Quant).filter Nonzero := h1.filter _

  -- Reduce to determinism of mergeSort under a linear order on `factKey`.
  have hp :
      ((xs.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b)) ~
        ((ys.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b)) := by
    exact (mergeSort_perm _ _).trans (h2.trans (mergeSort_perm _ _).symm)

  have hs₁ : Sorted r (((xs.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b))) := by
    simpa using sorted_mergeSort' (r := r) ((xs.map Quant).filter Nonzero)
  have hs₂ : Sorted r (((ys.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b))) := by
    simpa using sorted_mergeSort' (r := r) ((ys.map Quant).filter Nonzero)

  -- Unfold `factsToQ16Sorted` and apply uniqueness of sorted outputs.
  have :
      ((xs.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b)) =
        ((ys.map Quant).filter Nonzero).mergeSort (fun a b => decide (r a b)) :=
    eq_of_perm_of_sorted (hp := hp) (hs₁ := hs₁) (hs₂ := hs₂)
  -- Rewrite `(r · ·)` to the concrete comparator used in implementation.
  have this' :
      ((xs.map Quant).filter Nonzero).mergeSort (fun a b => factLEb a b) =
        ((ys.map Quant).filter Nonzero).mergeSort (fun a b => factLEb a b) := by
    simpa [r_decide_eq_factLEb] using this
  simpa [factsToQ16Sorted, Quant, Nonzero, factLEb] using this'

end
end Evidence
end TensorLogic
end Compiler
end HeytingLean
