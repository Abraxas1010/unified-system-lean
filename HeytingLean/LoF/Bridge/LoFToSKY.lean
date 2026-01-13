import HeytingLean.LoF.Correspondence.LoFSKY

/-!
# LoFToSKY — LoF ↔ SKY bridge (term/rewrite layer)

The repo already contains a concrete, minimal correspondence between:

* a tiny “LoF combinator” syntax (`HeytingLean.LoF.Correspondence.LoFTerm`), and
* the SKY combinators (`HeytingLean.LoF.Combinators.SKY.Comb`).

This file re-exports that correspondence under a dedicated `HeytingLean.LoF.Bridge` namespace,
so the unified-architecture docs have a stable import path for the “LoF→SKY” bridge.
-/

namespace HeytingLean
namespace LoF
namespace Bridge

open HeytingLean.LoF

namespace LoFToSKY

abbrev LoFTerm := HeytingLean.LoF.Correspondence.LoFTerm
abbrev Comb := HeytingLean.LoF.Comb

abbrev toSKY : LoFTerm → Comb :=
  HeytingLean.LoF.Correspondence.LoFTerm.toSKY

abbrev toSKY_spec : LoFTerm → Comb :=
  HeytingLean.LoF.Correspondence.LoFTerm.toSKY_spec

abbrev ofSKY : Comb → LoFTerm :=
  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY

abbrev ofSKY_spec : Comb → LoFTerm :=
  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY_spec

abbrev Step := HeytingLean.LoF.Correspondence.LoFStep.Step
abbrev Steps := HeytingLean.LoF.Correspondence.LoFStep.Steps

theorem step_toSKY {t u : LoFTerm} :
    Step t u → Comb.Step (toSKY t) (toSKY u) :=
  HeytingLean.LoF.Correspondence.LoFStep.step_toSKY

theorem steps_toSKY {t u : LoFTerm} :
    Steps t u → Comb.Steps (toSKY t) (toSKY u) :=
  HeytingLean.LoF.Correspondence.LoFStep.steps_toSKY

end LoFToSKY

end Bridge
end LoF
end HeytingLean
