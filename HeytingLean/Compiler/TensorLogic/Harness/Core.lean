import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bot
import HeytingLean.Compiler.TensorLogic.Demos.Registry
import HeytingLean.Compiler.TensorLogic.Evidence.BundleV2
import HeytingLean.Compiler.TensorLogic.Evidence.Canonical

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Harness

open HeytingLean.Compiler.TensorLogic
open HeytingLean.Compiler.TensorLogic.Demos
open HeytingLean.Compiler.TensorLogic.Evidence

def mkInitFacts (mode : Mode) (tnorm : TNorm) (xs : List (Atom × Float)) : Facts :=
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

def mkBotRun
    (bot : BotKind) (mode : Mode) (tnorm : TNorm)
    (cfgBase : RunConfig)
    (deterministic : Bool)
    (trace : Bool)
    (p : Program)
    (facts : List (Atom × Float)) : Except String Evidence.BotRunResult := do
  let cfg : RunConfig := { cfgBase with mode := mode, tnorm := tnorm }
  let init := mkInitFacts mode tnorm facts
  let ec : EngineConfig := { bot := bot, cfg := cfg, deterministic := deterministic, trace := trace }
  let br ← runBot ec p init
  pure
    { bot := bot
    , mode := mode
    , tnorm := tnorm
    , outputFactsQ16 := factsFromRunResultQ16Sorted br.run
    , explanation? := br.explanation?
    }

def standardBotRuns
    (cfgBase : RunConfig) (deterministic trace : Bool) (tnorm : TNorm)
    (p : Program) (facts : List (Atom × Float)) : Except String (List Evidence.BotRunResult) := do
  let rMon ← mkBotRun .monotone .boolean .product cfgBase deterministic trace p facts
  let rFuz ← mkBotRun .fuzzy .fuzzy tnorm cfgBase deterministic trace p facts
  let rF2L ← mkBotRun .f2linear .f2 .product cfgBase deterministic trace p facts
  let rExp ← mkBotRun .explain .fuzzy tnorm cfgBase deterministic true p facts
  pure [rMon, rFuz, rF2L, rExp]

def oneBotRun
    (bot : BotKind) (cfgBase : RunConfig) (deterministic trace : Bool) (tnorm : TNorm)
    (p : Program) (facts : List (Atom × Float)) : Except String (List Evidence.BotRunResult) := do
  match bot with
  | .monotone =>
      pure [← mkBotRun .monotone .boolean .product cfgBase deterministic trace p facts]
  | .fuzzy =>
      pure [← mkBotRun .fuzzy .fuzzy tnorm cfgBase deterministic trace p facts]
  | .f2linear =>
      pure [← mkBotRun .f2linear .f2 .product cfgBase deterministic trace p facts]
  | .f2solve =>
      pure [← mkBotRun .f2solve .f2 .product cfgBase deterministic trace p facts]
  | .explain =>
      pure [← mkBotRun .explain .fuzzy tnorm cfgBase deterministic true p facts]
  | .legacy =>
      pure [← mkBotRun .legacy cfgBase.mode cfgBase.tnorm cfgBase deterministic trace p facts]

def mkBundleForDemo
    (d : DemoSpec)
    (runs : List Evidence.BotRunResult)
    (cfgBase : RunConfig)
    (deterministic : Bool)
    (epsRaw : String)
    (ts? : Option String)
    (git? : Option String) : BundleV2 :=
  let inputFactsFuzzy := mkInitFacts .fuzzy cfgBase.tnorm d.inputFacts
  let inputFactsQ16 := factsFromFactsQ16Sorted inputFactsFuzzy
  let cfgDemo := runConfigToDemoConfig cfgBase deterministic epsRaw
  let bundle0 : BundleV2 :=
    { demo := d.name
    , timestamp? := ts?
    , gitCommit? := git?
    , program := d.program
    , inputFactsQ16 := inputFactsQ16
    , config := cfgDemo
    , results := runs
    , certRefs := d.certRefs
    }
  withComputedHash bundle0

end Harness
end TensorLogic
end Compiler
end HeytingLean
