import HeytingLean.Compiler.TensorLogic.AST

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demos

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)

def parityF2Name : String := "parity_f2_v1"

private def atom1 (pred a : String) : Atom :=
  { pred := pred, args := [a] }

private def pat1 (pred a : String) : AtomPat :=
  { pred := pred, args := [.const a] }

/-!
A tiny *linear* (unary) program intended for the `F2Linear` bot:

- `[] -> p(x0)` sets `p(x0) = 1`
- `p(x0) -> p(x1)`
- `p(x1) -> p(x2)`

In Boolean/Heyting reading this is just reachability along a chain.
In `Mode.f2` it corresponds to linear equations over `F₂`.
-/
def parityF2Program : Program :=
  { rules :=
      [ { head := pat1 "p" "x0", body := [], weight := some 1.0 }
      , { head := pat1 "p" "x1", body := [pat1 "p" "x0"], weight := some 1.0 }
      , { head := pat1 "p" "x2", body := [pat1 "p" "x1"], weight := some 1.0 }
      ]
  }

def parityF2InputFacts : List (Atom × Float) :=
  []

def parityF2Expected : List Atom :=
  [atom1 "p" "x0", atom1 "p" "x1", atom1 "p" "x2"]

end Demos
end TensorLogic
end Compiler
end HeytingLean

