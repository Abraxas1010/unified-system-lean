# Unified System — 6-Layer Verified Stack

<p align="center">
  <strong>Machine-checked unification of four repositories into a single coherent mathematical-computational stack</strong><br/>
  <em>
    Lean 4 formalization connecting LoF nuclei, SKY combinators, Grothendieck topologies, and TensorLogic inference
  </em>
</p>

<p align="center">
  <img src="https://img.shields.io/badge/Lean-4-blue" alt="Lean 4"/>
  <img src="https://img.shields.io/badge/sorry-0-brightgreen" alt="No sorry"/>
  <img src="https://img.shields.io/badge/declarations-286-informational" alt="286 declarations"/>
  <img src="https://img.shields.io/badge/status-verified-success" alt="Verified"/>
</p>

---

Part of the broader HeytingLean formal verification project: https://apoth3osis.io

## Overview

This repository unifies four previously separate formalizations into a single coherent 6-layer stack:

| Layer | Repository | Description |
|-------|------------|-------------|
| **Semantic** | generative-stack-lean | Nucleus, Frame, Heyting algebra from fixed points |
| **LoF Kernel** | generative-stack-lean | Spencer-Brown calculus → BDD → MuxNet → Gates |
| **SKY Combinator** | sky-combinator-multiway-lean | K/S/Y reductions, multiway exploration, branchial graphs |
| **Topos** | sky-combinator-multiway-lean | Sieves, Grothendieck topology, J.close as nucleus |
| **Compilation** | lean-kernel-sky | LambdaIR → MiniC → C verified pipeline |
| **Knowledge** | tensor-logic-homology-lean | Datalog inference with 4 modes, exact F₂ solver, homology encoding |

The unification centers on the **nucleus** as the universal algebraic structure connecting all layers.

## Quick Start

```bash
# 1. Ensure you have Lean 4 (elan recommended)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 2. Clone and build
git clone https://github.com/Abraxas1010/unified-system-lean.git
cd unified-system-lean
lake update
lake build --wfail

# 3. Verify with our script
./scripts/verify_unified.sh

# 4. Run the unified demo
lake exe unified_demo --rules data/unified_demo/rules.json --facts data/unified_demo/facts.tsv --mode heyting
```

## Key Theorems

| Theorem | Location | Significance |
|---------|----------|--------------|
| `bracket_sound` | `Combinators/BracketAbstractionCorrectness.lean:1068` | λ→SKY compilation soundness |
| `sieveNucleus_is_nucleus` | `Combinators/Topos/SieveNucleus.lean` | Grothendieck closure is a nucleus |
| `stepEdges_complete` | `Combinators/SKYMultiway.lean` | All SKY reductions enumerated |
| `toLambdaIR_correct` | `LeanCoreV2/ToLambdaIR.lean:135` | Compilation preserves semantics |
| `toLogicProgram_preserves_homology` | `TensorLogic/HomologyEncoding.lean:187` | Boundary data preserved |
| `eulerBoundary_isLeast` | `LoF/Nucleus.lean` | Minimal fixed point characterization |

## Architecture

```
                    ┌─────────────────────────────────────────┐
                    │           SEMANTIC LAYER                │
                    │   Nucleus ─► Frame ─► HeytingAlgebra    │
                    └─────────────────┬───────────────────────┘
                                      │ instantiates
         ┌────────────────────────────┼────────────────────────────┐
         │                            │                            │
         ▼                            ▼                            ▼
┌─────────────────┐        ┌─────────────────┐        ┌─────────────────┐
│   LOF KERNEL    │        │  SKY COMBINATOR │        │  KNOWLEDGE LAYER│
│ Expr→BDD→MuxNet │        │  K,S,Y + multi- │        │   TensorLogic   │
│ →Gates→AIG      │        │  way + topos    │        │   4 modes       │
└────────┬────────┘        └────────┬────────┘        └────────┬────────┘
         │                          │                          │
         │    Bridge Modules        │                          │
         └──────────►───────────────┴──────────◄───────────────┘
                              │
                    ┌─────────┴─────────┐
                    │ COMPILATION LAYER │
                    │ LambdaIR→MiniC→C  │
                    └───────────────────┘
```

## Bridge Modules

The cross-layer connections are explicit in Lean:

| Bridge | Connects | File |
|--------|----------|------|
| **NucleusBridge** | Reentry.nucleus ↔ J.close | `LoF/Bridge/NucleusBridge.lean` |
| **LoFToSKY** | LoFPrimary.Step ↔ Comb.Step | `LoF/Bridge/LoFToSKY.lean` |
| **TensorLogicHeyting** | Mode.heyting ↔ Ω_R operations | `LoF/Bridge/TensorLogicHeyting.lean` |
| **FactsAsSieves** | Facts database ↔ Sieves | `LoF/Bridge/FactsAsSieves.lean` |

## Proof Visualizations

Explore the proof structure in 2D and 3D:

<table>
<tr>
<td align="center" width="50%">
<strong>2D Proof Map</strong><br/>
<em>Pan, zoom, search 286 declarations</em><br/>
<a href="https://abraxas1010.github.io/unified-system-lean/artifacts/visuals/unified_2d.html">
  Open 2D Map
</a>
</td>
<td align="center" width="50%">
<strong>3D Proof Map</strong><br/>
<em>Rotate, zoom, explore clusters</em><br/>
<a href="https://abraxas1010.github.io/unified-system-lean/artifacts/visuals/unified_3d.html">
  Open 3D Map
</a>
</td>
</tr>
</table>

**Color Legend:**
- 🟣 **LoF** (Semantic layer)
- 🟪 **LoFKernel** (Gates)
- 🩷 **Combinator** (SKY)
- 🟠 **Topos** (Sieves)
- 🟢 **TensorLogic**
- 🟧 **Bridge**
- 🔵 **CLI**
- ⚫ **Test**

**UMAP note:** The visualization uses feature-based positioning; local neighborhoods are meaningful, but global distances are not proof-theoretic invariants.

## Directory Structure

```
HeytingLean/
├── LoF/                        # Laws of Form layer
│   ├── Nucleus.lean            # Reentry structure, Omega, eulerBoundary
│   ├── HeytingCore.lean        # Heyting algebra emergence
│   ├── BoundaryHeyting.lean    # HeytingAlgebra instance
│   ├── PrimaryAlgebra.lean     # Frame typeclass
│   ├── Bridge/                 # Cross-layer bridges
│   │   ├── NucleusBridge.lean
│   │   ├── LoFToSKY.lean
│   │   ├── TensorLogicHeyting.lean
│   │   └── FactsAsSieves.lean
│   ├── Combinators/            # SKY calculus
│   │   ├── SKY.lean            # K, S, Y, Step, Steps
│   │   ├── SKYMultiway.lean    # Labeled edge enumeration
│   │   ├── BracketAbstraction*.lean
│   │   ├── Denotational.lean   # SKYModel semantics
│   │   ├── EigenformBridge.lean
│   │   └── Topos/
│   │       └── SieveNucleus.lean
│   └── LoFPrimary/             # Spencer-Brown syntax → gates
│       ├── Syntax.lean
│       ├── Rewrite.lean
│       ├── MuxNet.lean
│       └── GateSpec.lean
├── Compiler/TensorLogic/       # Knowledge layer
│   ├── AST.lean                # Atom, Rule, Program
│   ├── Eval.lean               # 4 modes: boolean, f2, fuzzy, heyting
│   ├── Bot.lean                # Bot interface (legacy, monotone, f2solve, etc.)
│   ├── Bots/                   # Solver implementations
│   │   ├── F2Solve.lean        # Exact finite solver for XOR mode
│   │   ├── F2Linear.lean       # Linear algebra approach
│   │   ├── Monotone.lean       # Kleene iteration
│   │   └── Fuzzy.lean          # Fuzzy logic mode
│   ├── Demo/                   # Certified demo with evidence bundle
│   │   ├── Program.lean        # Demo Datalog program
│   │   ├── Schema.lean         # Canonical JSON + Q16 weights
│   │   ├── Main.lean           # Demo runner executable
│   │   └── Proof.lean          # Certified theorem (no sorry)
│   └── HomologyEncoding.lean   # ChainComplexF2 → LogicProgram
├── CLI/
│   └── UnifiedDemo.lean        # End-to-end demo executable
└── Tests/
    └── UnifiedMathSanity.lean
```

## Dependencies

- **Lean 4**: `leanprover/lean4:v4.16.0`
- **Mathlib**: `v4.24.0`
  - `Order.Nucleus`, `Order.Frame`
  - `CategoryTheory.Sites.Sieves`

## Verification

Run the full verification:

```bash
./scripts/verify_unified.sh
```

This checks:
1. No `sorry` or `admit` in source
2. Clean `lake build --wfail`
3. `unified_demo` executable builds and runs

## License

**Copyright (c) 2022-2026 Equation Capital LLC. All rights reserved.**

This software is available under a **dual licensing model**:
- **AGPL-3.0** for open source, academic, and personal use
- **Commercial License** available for proprietary use

See [LICENSE.md](LICENSE.md) for details. Contact: rgoodman@apoth3osis.io

## Citation

If you use this formalization in your research, please cite:

```bibtex
@software{unified_system_lean,
  title = {Unified System: A Lean 4 Formalization of the 6-Layer Stack},
  year = {2025},
  note = {Machine-checked unification of nuclei, combinators, topoi, and knowledge inference}
}
```

## Related Work

- [generative-stack-lean](https://github.com/Abraxas1010/generative-stack-lean) — Original LoF/eigenform formalization
- [sky-combinator-multiway-lean](https://github.com/Abraxas1010/sky-combinator-multiway-lean) — SKY multiway + topos layer
- [tensor-logic-homology-lean](https://github.com/Abraxas1010/tensor-logic-homology-lean) — TensorLogic inference
- [lean-kernel-sky](https://github.com/Abraxas1010/lean-kernel-sky) — Lean kernel on SKY

## Contact

For questions or issues, please open a GitHub issue or contact rgoodman@apoth3osis.io

---

<p align="center">
  <em>Part of the <a href="https://apoth3osis.io">HeytingLean</a> formal verification project</em>
</p>
