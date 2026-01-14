import Batteries.Data.String.Matcher

import HeytingLean.Util.SHA

namespace HeytingLean.Tests.TensorLogic.HarnessFaulttestMain

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def assertTrue (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private structure ProcOut where
  code : UInt32
  out : String
  err : String

private def runBin
    (cmd : System.FilePath)
    (args : Array String)
    (env : Array (String × Option String) := #[]) :
    IO ProcOut := do
  let p ← IO.Process.output { cmd := cmd.toString, args := args, env := env }
  pure { code := p.exitCode, out := p.stdout, err := p.stderr }

private def containsStr (s pat : String) : Bool :=
  s.containsSubstr pat.toSubstring

private def resolveLeanDir : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd.fileName == some "lean" then
    return cwd
  let leanDir := cwd / "lean"
  if (← leanDir.pathExists) then
    return leanDir
  throw <| IO.userError s!"could not locate 'lean' directory from cwd={cwd}"

private def resolveBin (name : String) : IO System.FilePath := do
  let leanDir ← resolveLeanDir
  let bin := leanDir / ".lake" / "build" / "bin" / name
  if (← bin.pathExists) then
    return bin
  throw <| IO.userError s!"missing binary at {bin} (did you run `lake build`?)"

private def testHarnessDeterminism (bin : System.FilePath) : IO Unit := do
  let args := #["--demo", "reachability_v1", "--bot", "monotone", "--deterministic", "true"]
  let r1 ← runBin bin args
  let r2 ← runBin bin args
  assertTrue (r1.code == 0) s!"harness determinism: expected exit 0, got {r1.code} (stderr={r1.err})"
  assertTrue (r2.code == 0) s!"harness determinism: expected exit 0, got {r2.code} (stderr={r2.err})"
  assertTrue (r1.out == r2.out) "harness determinism: stdout differed across identical runs"
  let h1 := HeytingLean.Util.SHA256.sha256Hex r1.out.toUTF8
  let h2 := HeytingLean.Util.SHA256.sha256Hex r2.out.toUTF8
  assertTrue (h1 == h2) "harness determinism: stdout sha256 differed across identical runs"

private def testHarnessLocaleAndPathIndependence (bin : System.FilePath) : IO Unit := do
  let args := #["--demo", "reachability_v1", "--bot", "monotone", "--deterministic", "true"]
  let base ← runBin bin args
  assertTrue (base.code == 0) s!"harness locale/path: base run failed (stderr={base.err})"

  let envC : Array (String × Option String) := #[("LC_ALL", some "C"), ("LANG", some "C")]
  let rC ← runBin bin args envC
  assertTrue (rC.code == 0) s!"harness locale/path: LC_ALL=C run failed (stderr={rC.err})"
  assertTrue (rC.out == base.out) "harness locale/path: deterministic output changed under LC_ALL=C"

  let rNoPath ← runBin bin args #[("PATH", some "")]
  assertTrue (rNoPath.code == 0) s!"harness locale/path: PATH='' run failed (stderr={rNoPath.err})"
  assertTrue (rNoPath.out == base.out) "harness locale/path: deterministic output changed under PATH=''"

private def testHarnessBadArgs (bin : System.FilePath) : IO Unit := do
  let r ← runBin bin #["--nope"]
  assertTrue (r.code != 0) "harness bad args: expected nonzero exit code"
  assertTrue (containsStr r.err "unknown argument") s!"harness bad args: missing 'unknown argument' in stderr: {r.err}"

private def testHarnessMissingDemo (bin : System.FilePath) : IO Unit := do
  let r ← runBin bin #[]
  assertTrue (r.code == 0) s!"harness default: expected exit 0, got {r.code} (stderr={r.err})"

  let r2 ← runBin bin #["--bot", "monotone"]
  assertTrue (r2.code != 0) "harness missing demo: expected nonzero exit code"
  assertTrue (containsStr r2.err "missing --demo") s!"harness missing demo: missing error in stderr: {r2.err}"

private def testHarnessOutIsDirectory (bin : System.FilePath) : IO Unit := do
  let leanDir ← resolveLeanDir
  let dir := leanDir / ".tmp" / "tensorlogic_harness_faulttest" / "outdir"
  IO.FS.createDirAll dir
  let r ← runBin bin #["--demo", "reachability_v1", "--deterministic", "true", "--out", dir.toString]
  assertTrue (r.code != 0) "harness out-is-dir: expected nonzero exit code"
  assertTrue (containsStr r.err "out_path_is_directory") s!"harness out-is-dir: missing error class in stderr: {r.err}"

private def testHarnessOutPermissionDenied (bin : System.FilePath) : IO Unit := do
  let out := (System.FilePath.mk "/tensorlogic_harness_forbidden.json")
  let r ← runBin bin #["--demo", "reachability_v1", "--deterministic", "true", "--out", out.toString]
  assertTrue (r.code != 0) "harness out-perm: expected nonzero exit code"
  assertTrue (containsStr r.err "out_write_failed") s!"harness out-perm: missing out_write_failed in stderr: {r.err}"

private def testToolRunnerMissingFile (bin : System.FilePath) : IO Unit := do
  let r ← runBin bin #["--file", "/no/such/file.json"]
  assertTrue (r.code == 0) s!"tool runner missing file: expected exit 0, got {r.code} (stderr={r.err})"
  assertTrue (containsStr r.out "\"error_class\"") s!"tool runner missing file: expected JSON error, got: {r.out}"
  assertTrue (containsStr r.out "file_read_failed") s!"tool runner missing file: expected file_read_failed, got: {r.out}"

private def testToolRunnerBadJson (bin : System.FilePath) : IO Unit := do
  let leanDir ← resolveLeanDir
  let tmpDir := leanDir / ".tmp" / "tensorlogic_harness_faulttest"
  IO.FS.createDirAll tmpDir
  let p := tmpDir / "bad.json"
  IO.FS.writeFile p "{not json"
  let r ← runBin bin #["--file", p.toString]
  assertTrue (r.code == 0) s!"tool runner bad json: expected exit 0, got {r.code} (stderr={r.err})"
  assertTrue (containsStr r.out "invalid_json") s!"tool runner bad json: expected invalid_json, got: {r.out}"

private def testToolRunnerBadEps (bin : System.FilePath) : IO Unit := do
  let leanDir ← resolveLeanDir
  let tmpDir := leanDir / ".tmp" / "tensorlogic_harness_faulttest"
  IO.FS.createDirAll tmpDir
  let p := tmpDir / "bad_eps.json"
  IO.FS.writeFile p "{\"demo\":\"reachability_v1\",\"bot\":\"monotone\",\"deterministic\":true,\"eps_raw\":\"NaN\"}\n"
  let r ← runBin bin #["--file", p.toString]
  assertTrue (r.code == 0) s!"tool runner bad eps: expected exit 0, got {r.code} (stderr={r.err})"
  assertTrue (containsStr r.out "invalid_request") s!"tool runner bad eps: expected invalid_request, got: {r.out}"

def mainImpl (_args : List String) : IO UInt32 := do
  try
    let binHarness ← resolveBin "tensorlogic_harness"
    let binTool ← resolveBin "tensorlogic_tool_runner"
    testHarnessDeterminism binHarness
    testHarnessLocaleAndPathIndependence binHarness
    testHarnessBadArgs binHarness
    testHarnessMissingDemo binHarness
    testHarnessOutIsDirectory binHarness
    testHarnessOutPermissionDenied binHarness
    testToolRunnerMissingFile binTool
    testToolRunnerBadJson binTool
    testToolRunnerBadEps binTool
    pure 0
  catch e =>
    die s!"tensorlogic_harness_faulttest: FAILED: {e}"

end HeytingLean.Tests.TensorLogic.HarnessFaulttestMain

open HeytingLean.Tests.TensorLogic.HarnessFaulttestMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.TensorLogic.HarnessFaulttestMain.mainImpl args

