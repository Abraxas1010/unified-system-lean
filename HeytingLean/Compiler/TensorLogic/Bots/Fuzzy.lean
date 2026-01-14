import HeytingLean.Compiler.TensorLogic.Eval

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Bots

open HeytingLean.Compiler.TensorLogic (Mode RunConfig Program Facts RunResult run)

/-!
Fuzzy bot: wraps the current iterative evaluator.

This bot is explicitly heuristic for non-idempotent t-conorms. It relies on:
- base anchoring in the core engine (`stepFromBase`)
- convergence threshold `eps` and/or `maxIter`
- deterministic ordering in joins when requested (handled in the core engine)
-/

def runFuzzy (cfg : RunConfig) (p : Program) (init : Facts) : Except String RunResult := do
  match cfg.mode with
  | .fuzzy | .heyting | .boolean =>
      pure (run cfg p init)
  | .f2 =>
      throw "Fuzzy bot does not support mode=f2 (use the f2 solver/bot instead)."

end Bots
end TensorLogic
end Compiler
end HeytingLean

