import HeytingLean.Compiler.TensorLogic.AST
import HeytingLean.Compiler.TensorLogic.Demos.Reachability
import HeytingLean.Compiler.TensorLogic.Demos.ParityF2
import HeytingLean.Compiler.TensorLogic.Demos.ContractsPolicy
import HeytingLean.Compiler.TensorLogic.Demos.ContractsPolicyProof
import HeytingLean.Compiler.TensorLogic.Evidence.CanonicalProofs

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demos

open HeytingLean.Compiler.TensorLogic (Atom Program)

structure DemoSpec where
  name : String
  program : Program
  inputFacts : List (Atom × Float)
  /-- Optional: “expected” atoms under a monotone/boolean reading, used by selftests. -/
  expectedMonotone? : Option (List Atom) := none
  /-- Lean declaration names that justify demo-level claims. -/
  certRefs : Array String := #[]
  deriving Repr

def allDemos : List DemoSpec :=
  [ { name := reachabilityName
    , program := reachabilityProgram
    , inputFacts := reachabilityInputFacts
    , expectedMonotone? := some reachabilityExpectedMonotone
    , certRefs :=
        #[
          "HeytingLean.Compiler.TensorLogic.Evidence.factsToQ16Sorted_perm",
          "HeytingLean.Compiler.TensorLogic.Demo.demo_monotone_derives_expected"
        ]
    }
  , { name := parityF2Name
    , program := parityF2Program
    , inputFacts := parityF2InputFacts
    , expectedMonotone? := some parityF2Expected
    , certRefs := #["HeytingLean.Compiler.TensorLogic.Evidence.factsToQ16Sorted_perm"] }
  , { name := contractsPolicyName
    , program := contractsPolicyProgram
    , inputFacts := contractsPolicyInputFacts
    , expectedMonotone? := some contractsPolicyExpectedMonotone
    , certRefs :=
        #[
          "HeytingLean.Compiler.TensorLogic.Evidence.factsToQ16Sorted_perm",
          "HeytingLean.Compiler.TensorLogic.Demos.contractsPolicy_derives_notify"
        ] }
  ]

def findByName? (name : String) : Option DemoSpec :=
  allDemos.find? (fun d => d.name = name)

def names : List String :=
  allDemos.map (·.name)

end Demos
end TensorLogic
end Compiler
end HeytingLean
