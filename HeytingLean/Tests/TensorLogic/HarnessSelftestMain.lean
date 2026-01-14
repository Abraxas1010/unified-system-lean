import Lean
import Lean.Data.Json

namespace HeytingLean.Tests.TensorLogic.HarnessSelftestMain

open Lean
open Lean.Json

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def rootDir : IO System.FilePath := do
  let cwd ← IO.currentDir
  pure <|
    if cwd.fileName == some "lean" then
      cwd.parent.getD cwd
    else
      cwd

private def requireExists (p : System.FilePath) : IO Unit := do
  if !(← p.pathExists) then
    throw <| IO.userError s!"missing_required_file: {p}"

private structure ProcOut where
  code : UInt32
  out : String
  err : String

private def runBin (cmd : System.FilePath) (args : Array String) : IO ProcOut := do
  let p ← IO.Process.output { cmd := cmd.toString, args := args }
  pure { code := p.exitCode, out := p.stdout.trim, err := p.stderr.trim }

def main (_argv : List String) : IO UInt32 := do
  try
    let root ← rootDir
    let binDir := root / "lean" / ".lake" / "build" / "bin"
    let exeHarness := binDir / "tensorlogic_harness"
    let exeVerify := binDir / "tensorlogic_verify_evidence"
    let exeReplay := binDir / "tensorlogic_replay"
    let exeTool := binDir / "tensorlogic_tool_runner"

    for exe in [exeHarness, exeVerify, exeReplay, exeTool] do
      requireExists exe

    let evDir := root / "evidence" / "tensorlogic"
    let bundles :=
      [ evDir / "reachability_v1.json"
      , evDir / "parity_f2_v1.json"
      , evDir / "contracts_policy_v1.json"
      ]
    for p in bundles do
      requireExists p

    -- Verify + replay all golden bundles.
    for p in bundles do
      let rV ← runBin exeVerify #[p.toString]
      if rV.code != 0 then
        return (← die s!"verify_failed: {p}\nstdout:\n{rV.out}\nstderr:\n{rV.err}")
      let rR ← runBin exeReplay #[p.toString]
      if rR.code != 0 then
        return (← die s!"replay_failed: {p}\nstdout:\n{rR.out}\nstderr:\n{rR.err}")

    -- Harness determinism: identical stdout on repeated runs (one demo, one bot).
    let hArgs := #["--demo", "reachability_v1", "--bot", "monotone", "--deterministic", "true"]
    let h1 ← runBin exeHarness hArgs
    let h2 ← runBin exeHarness hArgs
    if h1.code != 0 || h2.code != 0 then
      return (← die s!"harness_failed:\n1 stderr:\n{h1.err}\n2 stderr:\n{h2.err}")
    if h1.out != h2.out then
      return (← die s!"harness_nondeterministic:\n1:\n{h1.out}\n2:\n{h2.out}")

    -- Tool runner determinism: identical stdout on repeated runs.
    let tmpDir := root / "lean" / ".tmp" / "tensorlogic_harness_selftest"
    IO.FS.createDirAll tmpDir
    let queryPath := tmpDir / "query.json"
    let query := "{\"demo\":\"reachability_v1\",\"bot\":\"monotone\",\"deterministic\":true}\n"
    IO.FS.writeFile queryPath query
    let r1 ← runBin exeTool #["--file", queryPath.toString]
    let r2 ← runBin exeTool #["--file", queryPath.toString]
    if r1.code != 0 || r2.code != 0 then
      return (← die s!"tool_runner_failed:\n1 stderr:\n{r1.err}\n2 stderr:\n{r2.err}")
    if r1.out != r2.out then
      return (← die s!"tool_runner_nondeterministic:\n1:\n{r1.out}\n2:\n{r2.out}")

    -- Sanity: output parses and contains a bundle hash.
    let j ←
      match Json.parse r1.out with
      | .ok v => pure v
      | .error msg => return (← die s!"tool_runner_invalid_json: {msg}\n{r1.out}")
    let _ ←
      match j.getObjVal? "bundle_hash" with
      | .ok (.str _) => pure ()
      | _ => return (← die s!"tool_runner_missing_bundle_hash:\n{r1.out}")

    IO.println "OK"
    pure (0 : UInt32)
  catch e =>
    die s!"tensorlogic_harness_selftest: FAILED: {e}"

end HeytingLean.Tests.TensorLogic.HarnessSelftestMain

open HeytingLean.Tests.TensorLogic.HarnessSelftestMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.TensorLogic.HarnessSelftestMain.main args
