import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.Combinators.Topos.SieveNucleus

/-!
# NucleusBridge — Unified nucleus interface

This “bridge module” makes explicit that the main closure operators used across the unified stack
are instances of `Order.Nucleus`:

* `Reentry.nucleus` (LoF / semantic layer)
* `GrothendieckTopology.close` packaged as `sieveNucleus` (Topos layer)

It intentionally contains only lightweight, name-stable lemmas used by later bridges/tests.
-/

namespace HeytingLean
namespace LoF
namespace Bridge

open Order
open CategoryTheory

universe v u

section Reentry

variable {α : Type u} [PrimaryAlgebra α]

@[simp] theorem reentry_nucleus_idempotent (R : Reentry α) (x : α) :
    R.nucleus (R.nucleus x) = R.nucleus x := by
  exact R.nucleus.idempotent x

@[simp] theorem reentry_nucleus_le_apply (R : Reentry α) (x : α) :
    x ≤ R.nucleus x := by
  exact Nucleus.le_apply (n := R.nucleus) (x := x)

@[simp] theorem reentry_nucleus_map_inf (R : Reentry α) (x y : α) :
    R.nucleus (x ⊓ y) = R.nucleus x ⊓ R.nucleus y := by
  exact Nucleus.map_inf (n := R.nucleus) (x := x) (y := y)

end Reentry

section Sieves

variable {C : Type u} [Category.{v} C]

@[simp] theorem sieveNucleus_idempotent (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    (Combinators.Topos.sieveNucleus (C := C) J X) ((Combinators.Topos.sieveNucleus (C := C) J X) S) =
      (Combinators.Topos.sieveNucleus (C := C) J X) S := by
  exact Nucleus.idempotent (n := Combinators.Topos.sieveNucleus (C := C) J X) S

@[simp] theorem sieveNucleus_le_apply (J : GrothendieckTopology C) {X : C} (S : Sieve X) :
    S ≤ (Combinators.Topos.sieveNucleus (C := C) J X) S := by
  exact Nucleus.le_apply (n := Combinators.Topos.sieveNucleus (C := C) J X) (x := S)

@[simp] theorem sieveNucleus_map_inf (J : GrothendieckTopology C) {X : C} (S T : Sieve X) :
    (Combinators.Topos.sieveNucleus (C := C) J X) (S ⊓ T) =
      (Combinators.Topos.sieveNucleus (C := C) J X) S ⊓ (Combinators.Topos.sieveNucleus (C := C) J X) T := by
  exact Nucleus.map_inf (n := Combinators.Topos.sieveNucleus (C := C) J X) (x := S) (y := T)

end Sieves

end Bridge
end LoF
end HeytingLean
