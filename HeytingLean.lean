/-!
# HeytingLean Unified System

This module re-exports the unified 6-layer architecture connecting:
1. **Semantic Layer**: Nucleus, Frame, Heyting algebras
2. **LoF Kernel**: Spencer-Brown primary algebra → BDD → MuxNet → Gates
3. **SKY Combinator Layer**: K/S/Y reductions, bracket abstraction, multiway
4. **Topos Layer**: Sieves, Grothendieck topology, J.close as nucleus
5. **Compilation Layer**: LambdaIR → MiniC → C
6. **Knowledge Layer**: TensorLogic with 4 inference modes
-/

-- Core LoF (Semantic Layer)
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.HeytingCore
import HeytingLean.LoF.BoundaryHeyting

-- LoF Primary (Syntax → Gates)
import HeytingLean.LoF.LoFPrimary.Syntax
import HeytingLean.LoF.LoFPrimary.Rewrite
import HeytingLean.LoF.LoFPrimary.MuxNet
import HeytingLean.LoF.LoFPrimary.GateSpec

-- SKY Combinators
import HeytingLean.LoF.Combinators.SKY
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.BracketAbstractionCorrectness
import HeytingLean.LoF.Combinators.Denotational
import HeytingLean.LoF.Combinators.EigenformBridge

-- Topos / Gluing
import HeytingLean.LoF.Combinators.Topos.SieveNucleus

-- Bridge Modules
import HeytingLean.LoF.Bridge

-- TensorLogic (Knowledge Layer)
import HeytingLean.Compiler.TensorLogic.AST
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.HomologyEncoding

-- Tests
import HeytingLean.Tests.UnifiedMathSanity
