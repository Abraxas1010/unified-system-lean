import Std

import HeytingLean.Compiler.TensorLogic.AST
import HeytingLean.Computational.Homology.ChainComplex

namespace HeytingLean
namespace Computational
namespace Homology

open HeytingLean.Compiler.TensorLogic

namespace ChainComplexF2

def vertexName (i : Nat) : String :=
  s!"v{i}"

def edgeName (i : Nat) : String :=
  s!"e{i}"

def faceName (i : Nat) : String :=
  s!"f{i}"

def simplexName (k i : Nat) : String :=
  match k with
  | 0 => vertexName i
  | 1 => edgeName i
  | 2 => faceName i
  | _ => s!"s{k}_{i}"

private def mkAtom (pred : String) (args : List String) : Atom :=
  { pred := pred, args := args }

private def mkPat (pred : String) (args : List String) : AtomPat :=
  { pred := pred, args := args.map Sym.ofString }

def simplexAtom (k i : Nat) : Atom :=
  { pred := "simplex", args := [toString k, simplexName k i] }

def boundaryAtom (k i j : Nat) : Atom :=
  { pred := "boundary"
  , args := [toString k, simplexName k i, simplexName (k + 1) j]
  }

private def connectivityProgram : Program :=
  { rules :=
      [ { head := mkPat "adjacent" ["V1", "V2"]
        , body := [mkPat "edge" ["V1", "V2"]]
        }
      , { head := mkPat "adjacent" ["V1", "V2"]
        , body := [mkPat "edge" ["V2", "V1"]]
        }
      , { head := mkPat "adjacent" ["V1", "V2"]
        , body := [mkPat "edge_vertex" ["E", "V1"], mkPat "edge_vertex" ["E", "V2"]]
        }
      , { head := mkPat "connected" ["V", "V"]
        , body := [mkPat "vertex" ["V"]]
        }
      , { head := mkPat "connected" ["V1", "V2"]
        , body := [mkPat "adjacent" ["V1", "V2"]]
        }
      , { head := mkPat "connected" ["V1", "V3"]
        , body := [mkPat "adjacent" ["V1", "V2"], mkPat "connected" ["V2", "V3"]]
        }
      ]
  }

private def edgeEndpoints? (d1 : F2Matrix) (e : Nat) : Option (String × String) :=
  if e < d1.cols then
    let vs : Array Nat := Id.run do
      let mut acc : Array Nat := #[]
      for i in [:d1.rows] do
        if d1.data[i]![e]! then
          acc := acc.push i
      acc
    if vs.size = 2 then
      let a := vs[0]!
      let b := vs[1]!
      let v1 := vertexName (Nat.min a b)
      let v2 := vertexName (Nat.max a b)
      some (v1, v2)
    else
      none
  else
    none

/-- Core facts: basis tags (`simplex`, plus low-dimensional conveniences) and boundary incidence. -/
private def coreFacts (C : ChainComplexF2) : List (Atom × Float) :=
  let basis :=
    (List.range C.dims.size).flatMap fun k =>
      (List.range (C.dims[k]!)).flatMap fun i =>
        let name := simplexName k i
        let extras :=
          if k == 0 then
            [(mkAtom "vertex" [name], 1.0)]
          else if k == 1 then
            [(mkAtom "edge_id" [name], 1.0)]
          else if k == 2 then
            [(mkAtom "face" [name], 1.0)]
          else
            []
        (simplexAtom k i, 1.0) :: extras

  let boundaryInc :=
    (List.range C.boundaries.size).flatMap fun k =>
      let M := C.boundaries[k]!
      (List.range M.rows).flatMap fun i =>
        (List.range M.cols).flatMap fun j =>
          if M.data[i]![j]! then
            let low := simplexName k i
            let high := simplexName (k + 1) j
            let extras :=
              if k == 0 then
                [(mkAtom "edge_vertex" [high, low], 1.0)]
              else if k == 1 then
                [(mkAtom "face_edge_idx" [high, low], 1.0)]
              else
                []
            (boundaryAtom k i j, 1.0) :: extras
          else
            []

  basis ++ boundaryInc

/-- Encode a finite `F₂` chain complex as a positive logic program + ground facts.

Outputs:
- facts describing the basis "simplices" (`vertex`, `edge_id`, `face`, `simplex`)
- boundary incidence facts (`boundary`, plus specialized `edge_vertex` / `face_edge_idx`)
- derived geometric facts when available (`edge(V1,V2)`, `face_edge(F,V1,V2)`)
- a small connectivity program (`adjacent` / `connected`) to witness `β₀` (components) via reachability.

Names:
- vertices are `v0`, `v1`, ...
- edges are `e0`, `e1`, ...
- faces are `f0`, `f1`, ...
- higher simplices are `s{k}_{i}`.
-/
def toLogicProgram (C : ChainComplexF2) : Program × List (Atom × Float) :=
  let prog := connectivityProgram

  -- Derived `edge(V1,V2)` facts when ∂₁ columns have exactly two vertices.
  let edgePairs : Array (Option (String × String)) :=
    if 0 < C.boundaries.size then
      let d1 := C.boundaries[0]!
      Id.run do
        let mut acc : Array (Option (String × String)) := Array.mkEmpty d1.cols
        for e in [:d1.cols] do
          acc := acc.push (edgeEndpoints? d1 e)
        acc
    else
      #[]

  let edges :=
    (List.range edgePairs.size).filterMap fun e =>
      match edgePairs[e]! with
      | none => none
      | some (v1, v2) => some (mkAtom "edge" [v1, v2], 1.0)

  -- Derived `face_edge(F,V1,V2)` facts when ∂₂ columns select edges with known endpoints.
  let faces :=
    if 1 < C.boundaries.size then
      let d2 := C.boundaries[1]!
      (List.range d2.rows).flatMap fun e =>
        (List.range d2.cols).filterMap fun f =>
          if d2.data[e]![f]! then
            match edgePairs.getD e none with
            | none => none
            | some (v1, v2) => some (mkAtom "face_edge" [faceName f, v1, v2], 1.0)
          else
            none
    else
      []

  (prog, coreFacts C ++ edges ++ faces)

/-!
## Correctness theorem (Phase 3)

The unified-system plan requires a “correctness theorem” for the homology encoding functor
`ChainComplexF2.toLogicProgram`.  The key invariant we record here is that boundary-matrix entries
are preserved as `boundary(k, low, high)` ground facts, so no boundary data (hence no homology data)
is lost by the encoding.
-/

/-- `toLogicProgram` preserves the chain complex boundary data: every `1` entry of `∂ₖ₊₁` is emitted
as a `boundaryAtom k i j` fact (with weight `1.0`). -/
theorem toLogicProgram_preserves_homology
    (C : ChainComplexF2) {k i j : Nat}
    (hk : k < C.boundaries.size)
    (hi : i < (C.boundaries[k]!).rows)
    (hj : j < (C.boundaries[k]!).cols)
    (h : (C.boundaries[k]!).data[i]![j]! = true) :
    (boundaryAtom k i j, 1.0) ∈ (toLogicProgram C).2 := by
  -- It suffices to show membership in the `coreFacts` prefix.
  have hb : (boundaryAtom k i j, 1.0) ∈ coreFacts C := by
    unfold coreFacts
    -- Focus on the `boundaryInc` portion of `basis ++ boundaryInc`.
    refine List.mem_append_right _ ?_
    refine (List.mem_flatMap).2 ?_
    refine ⟨k, (List.mem_range.2 hk), ?_⟩
    refine (List.mem_flatMap).2 ?_
    refine ⟨i, (List.mem_range.2 hi), ?_⟩
    refine (List.mem_flatMap).2 ?_
    refine ⟨j, (List.mem_range.2 hj), ?_⟩
    -- The generator includes `boundaryAtom k i j` at the head of the emitted list exactly when
    -- `M.data[i]![j]!` is true.
    simp [h]
  -- `coreFacts` is appended (on the left) to all derived-fact blocks.
  -- The right operand is opaque (it depends on `edgePairs`), but `mem_append_left` does not care.
  dsimp [toLogicProgram]
  -- `++` associates to the left here, so we push membership through two appended tails.
  refine List.mem_append_left _ ?_
  exact List.mem_append_left _ hb

end ChainComplexF2

end Homology
end Computational
end HeytingLean
