import HeytingLean.LoF.BoundaryHeyting
import HeytingLean.Compiler.TensorLogic.Eval

/-!
# TensorLogicHeyting — TensorLogic “heyting mode” operations

`HeytingLean.Compiler.TensorLogic` has a `Mode.heyting` which uses the Gödel t-norm:

* `and` is `min` (implemented as `if a < b then a else b`)
* `or`  is `max` (implemented as `if a > b then a else b`)

This file records the definitional equations as lemmas.  A richer bridge which relates these
Float-based operations to concrete Heyting algebras (e.g. the fixed points `Ω_R`) can build on
these stable facts.
-/

namespace HeytingLean
namespace LoF
namespace Bridge

open HeytingLean.Compiler.TensorLogic

@[simp] theorem tensorLogic_heyting_and (a b : Float) :
    (Ops.forConfig Mode.heyting).and a b = (if a < b then a else b) := rfl

@[simp] theorem tensorLogic_heyting_or (a b : Float) :
    (Ops.forConfig Mode.heyting).or a b = (if a > b then a else b) := rfl

end Bridge
end LoF
end HeytingLean

