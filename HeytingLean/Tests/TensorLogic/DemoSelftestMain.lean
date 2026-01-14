import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bot
import HeytingLean.Compiler.TensorLogic.Demo.Program
import HeytingLean.Compiler.TensorLogic.Demo.Schema
import HeytingLean.Compiler.TensorLogic.Demo.Proof

namespace HeytingLean.Tests.TensorLogic.DemoSelftestMain

open HeytingLean.Compiler.TensorLogic
open HeytingLean.Compiler.TensorLogic.Demo

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def assertTrue (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def mkInitFacts (mode : Mode) (tnorm : TNorm) (xs : List (Atom × Float)) : Facts :=
  let ops := Ops.forConfig mode tnorm
  match mode with
  | .boolean =>
      Facts.fromList ops (xs.map (fun (aw : Atom × Float) => (aw.1, 1.0)))
  | .f2 =>
      Facts.fromList ops (xs.map (fun (aw : Atom × Float) => (aw.1, if aw.2 == 0.0 then 0.0 else 1.0)))
  | .fuzzy =>
      Facts.fromList ops xs
  | .heyting =>
      Facts.fromList ops xs

private def mkBotRun
    (bot : BotKind) (mode : Mode) (tnorm : TNorm)
    (cfgBase : RunConfig)
    (deterministic : Bool)
    (trace : Bool) : Except String BotRunResult := do
  let cfg : RunConfig := { cfgBase with mode := mode, tnorm := tnorm }
  let init := mkInitFacts mode tnorm demoInputFacts
  let ec : EngineConfig := { bot := bot, cfg := cfg, deterministic := deterministic, trace := trace }
  let br ← runBot ec demoProgram init
  pure
    { bot := bot
    , mode := mode
    , tnorm := tnorm
    , outputFactsQ16 := factsFromRunResultQ16Sorted br.run
    , explanation? := br.explanation?
    }

private def mkBundleDeterministic : Except String EvidenceBundle := do
  let cfgBase : RunConfig := { mode := .boolean, tnorm := .product, maxIter := 50, eps := 1e-6, maxAtoms := 20 }
  let rMon ← mkBotRun .monotone .boolean .product cfgBase true false
  let rFuz ← mkBotRun .fuzzy .fuzzy .product cfgBase true false
  let rF2L ← mkBotRun .f2linear .f2 .product cfgBase true false
  let rExp ← mkBotRun .explain .fuzzy .product cfgBase true true
  let inputFactsQ16 := factsFromFactsQ16Sorted (mkInitFacts .fuzzy .product demoInputFacts)
  let cfgDemo := runConfigToDemoConfig cfgBase true
  let bundle0 : EvidenceBundle :=
    { timestamp? := none
    , program := demoProgram
    , inputFactsQ16 := inputFactsQ16
    , config := cfgDemo
    , results := [rMon, rFuz, rF2L, rExp]
    }
  pure (withComputedHash bundle0)

private def listContainsAtom (xs : List (Atom × Nat)) (a : Atom) : Bool :=
  xs.any (fun aw => aw.1 == a)

private def expectedReachPresent (mon : BotRunResult) : Bool :=
  expectedMonotoneReach.all (fun a => listContainsAtom mon.outputFactsQ16 a)

private def atom0 (pred : String) : Atom := { pred := pred, args := [] }

private def xorDisagrees (mon f2 : BotRunResult) : Bool :=
  let p := atom0 "p"
  let q := atom0 "q"
  let pMon := listContainsAtom mon.outputFactsQ16 p
  let qMon := listContainsAtom mon.outputFactsQ16 q
  let pF2 := listContainsAtom f2.outputFactsQ16 p
  let qF2 := listContainsAtom f2.outputFactsQ16 q
  (pMon && qMon) && (pF2 != qF2) && (pF2 || qF2)

def mainImpl (_args : List String) : IO UInt32 := do
  try
    let b1 ←
      match mkBundleDeterministic with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"bundle build error: {e}")
    let b2 ←
      match mkBundleDeterministic with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"bundle build error: {e}")

    let s1 := canonicalJsonString b1
    let s2 := canonicalJsonString b2
    assertTrue (s1 == s2) "determinism: canonical bundle JSON differed across identical runs"
    assertTrue (b1.bundleHash == b2.bundleHash) "determinism: bundleHash differed across identical runs"

    let some mon := b1.results.find? (fun r => r.bot == .monotone)
      | throw (IO.userError "missing monotone result")
    let some f2 := b1.results.find? (fun r => r.bot == .f2linear)
      | throw (IO.userError "missing f2linear result")

    assertTrue (expectedReachPresent mon) "expected reach facts missing from monotone output"
    assertTrue (xorDisagrees mon f2) "expected XOR-cycle disagreement (monotone vs f2linear) did not occur"
    pure 0
  catch e =>
    die s!"tensorlogic_demo_selftest: FAILED: {e}"

end HeytingLean.Tests.TensorLogic.DemoSelftestMain

open HeytingLean.Tests.TensorLogic.DemoSelftestMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.TensorLogic.DemoSelftestMain.mainImpl args

