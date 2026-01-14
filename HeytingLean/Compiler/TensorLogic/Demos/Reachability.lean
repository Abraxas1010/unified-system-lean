import HeytingLean.Compiler.TensorLogic.Demo.Program

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demos

open HeytingLean.Compiler.TensorLogic (Atom Program)

def reachabilityName : String := "reachability_v1"

def reachabilityProgram : Program :=
  HeytingLean.Compiler.TensorLogic.Demo.demoProgram

def reachabilityInputFacts : List (Atom × Float) :=
  HeytingLean.Compiler.TensorLogic.Demo.demoInputFacts

def reachabilityExpectedMonotone : List Atom :=
  HeytingLean.Compiler.TensorLogic.Demo.expectedMonotoneReach

end Demos
end TensorLogic
end Compiler
end HeytingLean

