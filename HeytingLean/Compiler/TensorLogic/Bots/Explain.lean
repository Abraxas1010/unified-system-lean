import HeytingLean.Compiler.TensorLogic.Eval

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Bots

open HeytingLean.Compiler.TensorLogic (RunConfig Program Facts RunResult run)

/-!
Explain bot: a minimal wrapper around the evaluator.

The detailed tracing/explanations live in `HeytingLean.Compiler.TensorLogic.Bot` so this module
stays dependency-light.
-/

def runExplain (cfg : RunConfig) (p : Program) (init : Facts) : Except String RunResult := do
  pure (run cfg p init)

end Bots
end TensorLogic
end Compiler
end HeytingLean

