import Lean
import Lean.Data.Json

import HeytingLean.CLI.Args
import HeytingLean.Compiler.TensorLogic.ParseFacts
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bot
import HeytingLean.Compiler.TensorLogic.Demo.Program
import HeytingLean.Compiler.TensorLogic.Demo.Schema

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Demo

open Lean
open HeytingLean.Compiler.TensorLogic

private def usage : String :=
  String.intercalate "\n"
    [ "tensorlogic_demo"
    , ""
    , "Run the flagship TensorLogic demo under multiple bots and emit a deterministic evidence bundle (canonical JSON)."
    , ""
    , "Usage:"
    , "  tensorlogic_demo [--deterministic true|false] [--out PATH] [--trace]"
    , ""
    , "Options:"
    , "  --deterministic true|false   (default: true)"
    , "  --out PATH                   (write canonical JSON to PATH; otherwise print to stdout)"
    , "  --tnorm product|lukasiewicz  (default: product; fuzzy/explain only)"
    , "  --max-iter N                 (default: 50)"
    , "  --eps E                      (default: 0.000001; fuzzy/explain only; decimal only)"
    , "  --max-atoms N                (default: 20; f2solve cap, unused here)"
    , "  --trace                      (include explanation summaries where available)"
    , "  --help"
    ]

structure Args where
  deterministic : Bool := true
  outPath : Option System.FilePath := none
  tnorm : TNorm := .product
  maxIter : Nat := 50
  eps : Float := 1e-6
  maxAtoms : Nat := 20
  trace : Bool := false
  help : Bool := false
  deriving Repr

private def parseBoolFlag (raw : String) : Except String Bool := do
  match raw.toLower with
  | "true" | "1" | "yes" | "y" => pure true
  | "false" | "0" | "no" | "n" => pure false
  | _ => throw s!"expected true/false, got '{raw}'"

private def parseTNorm (s : String) : Except String TNorm :=
  match s with
  | "product" => pure .product
  | "lukasiewicz" => pure .lukasiewicz
  | _ => throw s!"unknown t-norm '{s}'"

private partial def parseArgs (argv : List String) (acc : Args := {}) : Except String Args := do
  match argv with
  | [] => pure acc
  | "--help" :: rest => parseArgs rest { acc with help := true }
  | "--deterministic" :: b :: rest =>
      let b ← parseBoolFlag b
      parseArgs rest { acc with deterministic := b }
  | "--out" :: p :: rest =>
      parseArgs rest { acc with outPath := some (System.FilePath.mk p) }
  | "--tnorm" :: t :: rest =>
      let t ← parseTNorm t
      parseArgs rest { acc with tnorm := t }
  | "--max-iter" :: n :: rest =>
      match String.toNat? n with
      | some k => parseArgs rest { acc with maxIter := k }
      | none => throw s!"bad --max-iter '{n}'"
  | "--eps" :: e :: rest =>
      match HeytingLean.Compiler.TensorLogic.parseFloatLit e with
      | .ok v => parseArgs rest { acc with eps := v }
      | .error msg => throw s!"bad --eps '{e}': {msg}"
  | "--max-atoms" :: n :: rest =>
      match String.toNat? n with
      | some k => parseArgs rest { acc with maxAtoms := k }
      | none => throw s!"bad --max-atoms '{n}'"
  | "--trace" :: rest =>
      parseArgs rest { acc with trace := true }
  | x :: _ => throw s!"unknown argument '{x}' (try --help)"

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def resolveOutPath (p : System.FilePath) : IO System.FilePath := do
  if p.isAbsolute then
    return p
  let cwd ← IO.currentDir
  let base :=
    if cwd.fileName == some "lean" then
      cwd.parent.getD cwd
    else
      cwd
  return base / p

private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  let some parent := path.parent
    | throw <| IO.userError s!"could not compute parent directory for {path}"
  IO.FS.createDirAll parent
  IO.FS.writeFile path contents

private def ensureOutPathIsFile (path : System.FilePath) : IO Unit := do
  if (← path.pathExists) then
    if (← path.isDir) then
      throw <| IO.userError "out_path_is_directory"

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
    (trace : Bool)
    (p : Program)
    (facts : List (Atom × Float)) : Except String BotRunResult := do
  let cfg : RunConfig :=
    { cfgBase with mode := mode, tnorm := tnorm }
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

private def renderSummary (rs : List BotRunResult) : String :=
  let lines :=
    rs.map (fun r =>
      let n := r.outputFactsQ16.length
      let modeStr :=
        match r.mode with
        | .boolean => "boolean"
        | .f2 => "f2"
        | .fuzzy => "fuzzy"
        | .heyting => "heyting"
      s!"- {BotKind.toString r.bot} ({modeStr}): {n} facts")
  String.intercalate "\n" ("TensorLogic demo summary:" :: lines)

private def renderDisagreements (rs : List BotRunResult) : String :=
  let find? (k : BotKind) : Option BotRunResult :=
    rs.find? (fun r => r.bot == k)
  match find? .monotone, find? .f2linear with
  | some m, some x =>
      let mSet : Std.HashSet Atom :=
        m.outputFactsQ16.foldl (init := {}) (fun acc aw => acc.insert aw.1)
      let xSet : Std.HashSet Atom :=
        x.outputFactsQ16.foldl (init := {}) (fun acc aw => acc.insert aw.1)
      let onlyM :=
        m.outputFactsQ16.filterMap (fun aw => if xSet.contains aw.1 then none else some aw.1)
      let onlyX :=
        x.outputFactsQ16.filterMap (fun aw => if mSet.contains aw.1 then none else some aw.1)
      let showAtoms (xs : List Atom) : String :=
        let xs := xs.take 8
        if xs.isEmpty then "(none)"
        else String.intercalate ", " (xs.map (fun a => s!"{a.pred}{a.args}"))
      String.intercalate "\n"
        [ "Disagreements (monotone vs f2linear, first few atoms):"
        , s!"- only monotone: {showAtoms onlyM}"
        , s!"- only f2linear: {showAtoms onlyX}"
        ]
  | _, _ => "Disagreements: (bots missing?)"

def main (argvRaw : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argvRaw
  try
    let args ←
      match parseArgs argv with
      | .ok a => pure a
      | .error e => return (← die s!"{e}\n\n{usage}")

    if args.help then
      IO.println usage
      return 0

    let cfgBase : RunConfig :=
      { mode := .boolean
      , tnorm := args.tnorm
      , maxIter := args.maxIter
      , eps := args.eps
      , maxAtoms := args.maxAtoms
      }

    let runsE : Except String (List BotRunResult) := do
      let rMon ← mkBotRun .monotone .boolean .product cfgBase args.deterministic args.trace demoProgram demoInputFacts
      let rFuz ← mkBotRun .fuzzy .fuzzy args.tnorm cfgBase args.deterministic args.trace demoProgram demoInputFacts
      let rF2L ← mkBotRun .f2linear .f2 .product cfgBase args.deterministic args.trace demoProgram demoInputFacts
      let rExp ← mkBotRun .explain .fuzzy args.tnorm cfgBase args.deterministic true demoProgram demoInputFacts
      pure [rMon, rFuz, rF2L, rExp]

    let runs ←
      match runsE with
      | .ok rs => pure rs
      | .error e => return (← die s!"tensorlogic_demo: bot error: {e}")

    let inputFactsFuzzy := mkInitFacts .fuzzy args.tnorm demoInputFacts
    let inputFactsQ16 := factsFromFactsQ16Sorted inputFactsFuzzy
    let cfgDemo := runConfigToDemoConfig cfgBase args.deterministic
    let ts? ←
      if args.deterministic then
        pure none
      else
        pure (some (toString (← IO.monoMsNow)))

    let bundle0 : EvidenceBundle :=
      { timestamp? := ts?
      , program := demoProgram
      , inputFactsQ16 := inputFactsQ16
      , config := cfgDemo
      , results := runs
      }
    let bundle := withComputedHash bundle0
    let payload := canonicalJsonString bundle

    match args.outPath with
    | none =>
        IO.println payload
    | some p =>
        let out ← resolveOutPath p
        ensureOutPathIsFile out
        writeFile out (payload ++ "\n")
        IO.println s!"[tensorlogic_demo] wrote {out}"

    IO.eprintln (renderSummary runs)
    IO.eprintln (renderDisagreements runs)
    pure 0
  catch e =>
    die s!"tensorlogic_demo: FAILED: {e}"

end Demo
end TensorLogic
end Compiler
end HeytingLean

open HeytingLean.Compiler.TensorLogic.Demo in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Compiler.TensorLogic.Demo.main args
