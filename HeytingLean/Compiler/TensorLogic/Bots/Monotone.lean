import HeytingLean.Compiler.TensorLogic.Eval

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Bots

open HeytingLean.Compiler.TensorLogic (Mode RunConfig Program Facts RunResult run)

/-!
Monotone bot: only supports monotone/idempotent aggregation regimes.

Currently:
- `Mode.boolean` (0/1 with OR/AND)
- `Mode.heyting` (Gödel min/max)

It rejects `.f2` and `.fuzzy` because their default operators are not monotone/idempotent in the
way required for a clean least-fixed-point story.
-/

def runMonotone (cfg : RunConfig) (p : Program) (init : Facts) : Except String RunResult := do
  match cfg.mode with
  | .boolean | .heyting =>
      -- Force exact convergence (no epsilon “close enough”).
      let cfg' : RunConfig := { cfg with eps := 0.0 }
      pure (run cfg' p init)
  | .f2 =>
      throw "Monotone bot does not support mode=f2 (XOR is not monotone on recursive programs)."
  | .fuzzy =>
      throw "Monotone bot does not support mode=fuzzy (non-idempotent t-conorms)."

end Bots
end TensorLogic
end Compiler
end HeytingLean

