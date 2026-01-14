import Lean
import Lean.Data.Json

import HeytingLean.CLI.Args
import HeytingLean.Compiler.TensorLogic.ParseFacts
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bot
import HeytingLean.Compiler.TensorLogic.Demos.Registry
import HeytingLean.Compiler.TensorLogic.Harness.Core
import HeytingLean.Compiler.TensorLogic.Evidence.BundleV2
import HeytingLean.Compiler.TensorLogic.Evidence.Canonical

namespace HeytingLean
namespace Compiler
namespace TensorLogic
namespace Harness

open Lean
open Std

open HeytingLean.Compiler.TensorLogic
open HeytingLean.Compiler.TensorLogic.Demos
open HeytingLean.Compiler.TensorLogic.Evidence

private def usage : String :=
  String.intercalate "\n"
    [ "tensorlogic_harness"
    , ""
    , "Run named TensorLogic demos under selected bot(s) and emit deterministic evidence bundles (canonical JSON)."
    , ""
    , "Usage:"
    , "  tensorlogic_harness --demo NAME [--bot BOT | --all-bots] [--deterministic true|false] [--out PATH]"
    , "  tensorlogic_harness --all [--all-bots] [--deterministic true|false] [--out PATH]"
    , ""
    , "Options:"
    , "  --demo NAME                  (run one demo)"
    , "  --all                        (run all demos; output is a JSON array of bundles)"
    , "  --bot BOT                    (legacy|monotone|fuzzy|f2linear|f2solve|explain; default: monotone)"
    , "  --all-bots                   (run standard bot suite for each demo)"
    , "  --deterministic true|false   (default: true)"
    , "  --out PATH                   (write JSON to PATH; otherwise print to stdout)"
    , "  --tnorm product|lukasiewicz  (default: product; fuzzy/explain only)"
    , "  --max-iter N                 (default: 50)"
    , "  --eps E                      (default: 0.000001; fuzzy/explain only; decimal only)"
    , "  --max-atoms N                (default: 20; f2solve cap)"
    , "  --trace                      (include explanation summaries where available)"
    , "  --help"
    ]

structure Args where
  demo? : Option String := none
  all : Bool := false
  bot : BotKind := .monotone
  allBots : Bool := false
  deterministic : Bool := true
  outPath : Option System.FilePath := none
  tnorm : TNorm := .product
  maxIter : Nat := 50
  epsRaw : String := "0.000001"
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
  | "--all" :: rest => parseArgs rest { acc with all := true }
  | "--demo" :: name :: rest => parseArgs rest { acc with demo? := some name }
  | "--bot" :: b :: rest =>
      let k ← BotKind.ofString b
      parseArgs rest { acc with bot := k }
  | "--all-bots" :: rest => parseArgs rest { acc with allBots := true }
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
      | .ok v => parseArgs rest { acc with epsRaw := e, eps := v }
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

private def checkOutPathIsFile (path : System.FilePath) : IO (Except String Unit) := do
  if (← path.pathExists) then
    if (← path.isDir) then
      return .error "out_path_is_directory"
  return .ok ()

private def writeFileChecked (path : System.FilePath) (contents : String) : IO (Except String Unit) := do
  try
    writeFile path contents
    return .ok ()
  catch e =>
    return .error s!"out_write_failed: {e}"

private def readFirstLineTrim (p : System.FilePath) : IO String := do
  let s ← IO.FS.readFile p
  return s.trim

private def gitCommit? : IO (Option String) := do
  let cwd ← IO.currentDir
  let root :=
    if cwd.fileName == some "lean" then
      cwd.parent.getD cwd
    else
      cwd
  let headPath := root / ".git" / "HEAD"
  if !(← headPath.pathExists) then
    return none
  let head ← readFirstLineTrim headPath
  if head.startsWith "ref:" then
    let ref := head.drop 4 |>.trim
    let refPath := root / ".git" / System.FilePath.mk ref
    if (← refPath.pathExists) then
      return some (← readFirstLineTrim refPath)
    else
      return none
  else
    return some head

def main (argvRaw : List String) : IO UInt32 := do
  let argv := HeytingLean.CLI.stripLakeArgs argvRaw
  try
    let args ←
      if argv.isEmpty then
        -- Default “happy path” for QA smoke runs: run all demos under the standard bot suite.
        pure ({ all := true, allBots := true } : Args)
      else
        match parseArgs argv with
        | .ok a => pure a
        | .error e => return (← die s!"{e}\n\n{usage}")

    if args.help then
      IO.println usage
      return 0

    if !args.all && args.demo?.isNone then
      return (← die s!"missing --demo NAME (or use --all)\n\n{usage}")

    let cfgBase : RunConfig :=
      { mode := .boolean
      , tnorm := args.tnorm
      , maxIter := args.maxIter
      , eps := args.eps
      , maxAtoms := args.maxAtoms
      }

    let ts? ←
      if args.deterministic then
        pure none
      else
        pure (some (toString (← IO.monoMsNow)))

    let git? ←
      if args.deterministic then
        pure none
      else
        gitCommit?

    let mkRuns (d : DemoSpec) : Except String (List Evidence.BotRunResult) :=
      if args.allBots then
        standardBotRuns cfgBase args.deterministic args.trace args.tnorm d.program d.inputFacts
      else
        oneBotRun args.bot cfgBase args.deterministic args.trace args.tnorm d.program d.inputFacts

    if args.all then
      let bundlesE : Except String (List BundleV2) := do
        let mut out : List BundleV2 := []
        for d in allDemos do
          let runs ← mkRuns d
          out := out.concat (mkBundleForDemo d runs cfgBase args.deterministic args.epsRaw ts? git?)
        pure out
      let bundles ←
        match bundlesE with
        | .ok bs => pure bs
        | .error e => return (← die s!"tensorlogic_harness: bot error: {e}")
      let payload :=
        Evidence.canonicalString <|
          Json.arr (bundles.map Evidence.toJson |>.toArray)
      match args.outPath with
      | none => IO.println payload
      | some p =>
          let out ← resolveOutPath p
          match (← checkOutPathIsFile out) with
          | .error cls => return (← die cls)
          | .ok () => pure ()
          match (← writeFileChecked out (payload ++ "\n")) with
          | .error msg => return (← die msg)
          | .ok () => pure ()
          IO.println s!"[tensorlogic_harness] wrote {out}"
      return 0
    else
      let name := args.demo?.getD ""
      let some d := findByName? name
        | return (← die s!"unknown demo '{name}'. Available: {String.intercalate ", " names}")
      let runs ←
        match mkRuns d with
        | .ok rs => pure rs
        | .error e => return (← die s!"tensorlogic_harness: bot error: {e}")
      let bundle := mkBundleForDemo d runs cfgBase args.deterministic args.epsRaw ts? git?
      let payload := Evidence.canonicalJsonString bundle
      match args.outPath with
      | none => IO.println payload
      | some p =>
          let out ← resolveOutPath p
          match (← checkOutPathIsFile out) with
          | .error cls => return (← die cls)
          | .ok () => pure ()
          match (← writeFileChecked out (payload ++ "\n")) with
          | .error msg => return (← die msg)
          | .ok () => pure ()
          IO.println s!"[tensorlogic_harness] wrote {out}"
      return 0
  catch e =>
    die s!"tensorlogic_harness: FAILED: {e}"

end Harness
end TensorLogic
end Compiler
end HeytingLean

open HeytingLean.Compiler.TensorLogic.Harness in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Compiler.TensorLogic.Harness.main args
