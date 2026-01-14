import HeytingLean.Compiler.TensorLogic.AST

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demo

open HeytingLean.Compiler.TensorLogic (Sym Atom AtomPat Rule Program)

def atom0 (pred : String) : Atom :=
  { pred := pred, args := [] }

def atom1 (pred : String) (a : String) : Atom :=
  { pred := pred, args := [a] }

def pat0 (pred : String) : AtomPat :=
  { pred := pred, args := [] }

def pat1 (pred : String) (a : String) : AtomPat :=
  { pred := pred, args := [Sym.const a] }

def pat2 (pred : String) (a b : String) : AtomPat :=
  { pred := pred, args := [Sym.const a, Sym.const b] }

/--
Flagship “applied-first” demo program.

Design constraints:
- **Same program** is run under Monotone/Fuzzy/F2Linear/Explain bots.
- Must be admissible for `F2Linear` ⇒ every rule body has length ≤ 1.
- Keep it ground + small to make a clean “certified expected facts” theorem feasible.

What it exercises:
- Monotone recursion: `reach` chain (`edge` seeds + recursive `reach` propagation).
- Fuzzy behavior: rule weights < 1.0 affect scores in fuzzy mode.
- F₂ parity + bot disagreement:
  - parity propagation (`even/odd`) is linear recursion;
  - XOR-cycle (`p/q`) yields a canonical-but-different solution under `f2linear` vs boolean closure.
-/
def demoProgram : Program :=
  { rules :=
      -- Reachability-by-unrolling (linear recursion)
      [ { head := pat1 "reach" "b", body := [pat2 "edge" "a" "b"], weight := some 0.95 }
      , { head := pat1 "reach" "c", body := [pat1 "reach" "b"], weight := some 0.90 }
      , { head := pat1 "reach" "d", body := [pat1 "reach" "c"], weight := some 0.85 }

      -- Parity propagation along the same chain (linear recursion)
      , { head := pat1 "even" "a", body := [pat1 "start" "a"] }
      , { head := pat1 "odd"  "b", body := [pat1 "even" "a"] }
      , { head := pat1 "even" "c", body := [pat1 "odd"  "b"] }
      , { head := pat1 "odd"  "d", body := [pat1 "even" "c"] }

      -- XOR-cycle: under boolean closure (idempotent OR) both persist;
      -- under `Mode.f2` + `f2linear`, the affine system admits two solutions and the bot picks
      -- the canonical one (free vars = 0), yielding a deterministic disagreement.
      , { head := pat0 "p", body := [pat0 "q"] }
      , { head := pat0 "q", body := [pat0 "p"] }
      ]
  }

/-- Demo base facts (used for all bots). -/
def demoInputFacts : List (Atom × Float) :=
  [ ({ pred := "start", args := ["a"] }, 1.0)
  , ({ pred := "edge", args := ["a", "b"] }, 0.90)
  , ({ pred := "edge", args := ["b", "c"] }, 0.80)
  , ({ pred := "edge", args := ["c", "d"] }, 0.70)
  , (atom0 "p", 1.0)
  , (atom0 "q", 1.0)
  ]

/-- Facts the Monotone run is expected to derive on the demo (boolean mode). -/
def expectedMonotoneReach : List Atom :=
  [ atom1 "reach" "b"
  , atom1 "reach" "c"
  , atom1 "reach" "d"
  ]

end Demo
end TensorLogic
end Compiler
end HeytingLean
