import HeytingLean.Compiler.TensorLogic.AST

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demos

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)

def contractsPolicyName : String := "contracts_policy_v1"

def contractsPolicyAtom2 (pred a b : String) : Atom :=
  { pred := pred, args := [a, b] }

def contractsPolicyPat2 (pred a b : String) : AtomPat :=
  { pred := pred, args := [.const a, .const b] }

/-!
Contracts/policy closure toy:

Events imply obligations; obligations imply follow-on obligations.

Intended as a monotone (Boolean/Heyting) closure demo with an audit-friendly explanation trace.
-/
def contractsPolicyRuleNotify : Rule :=
  { head := contractsPolicyPat2 "obl" "notify" "counterparty"
  , body := [contractsPolicyPat2 "event" "signed" "contract"]
  , weight := some 1.0
  }

def contractsPolicyRuleRemedyFromNotify : Rule :=
  { head := contractsPolicyPat2 "obl" "remedy" "counterparty"
  , body := [contractsPolicyPat2 "obl" "notify" "counterparty"]
  , weight := some 1.0
  }

def contractsPolicyRuleRemedyFromBreach : Rule :=
  { head := contractsPolicyPat2 "obl" "remedy" "counterparty"
  , body := [contractsPolicyPat2 "event" "breach" "contract"]
  , weight := some 1.0
  }

def contractsPolicyProgram : Program :=
  { rules :=
      [ contractsPolicyRuleNotify
      , contractsPolicyRuleRemedyFromNotify
      , contractsPolicyRuleRemedyFromBreach
      ]
  }

def contractsPolicyInputFacts : List (Atom × Float) :=
  [ (contractsPolicyAtom2 "event" "signed" "contract", 1.0) ]

def contractsPolicyExpectedMonotone : List Atom :=
  [ contractsPolicyAtom2 "obl" "notify" "counterparty"
  , contractsPolicyAtom2 "obl" "remedy" "counterparty"
  ]

end Demos
end TensorLogic
end Compiler
end HeytingLean
