import Batteries.Data.String.Matcher

import HeytingLean.Util.SHA

namespace HeytingLean.Tests.TensorLogic.DemoFaulttestMain

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

private def resolveDemoBin : IO System.FilePath := do
  let leanDir ← resolveLeanDir
  let bin := leanDir / ".lake" / "build" / "bin" / "tensorlogic_demo"
  if (← bin.pathExists) then
    return bin
  throw <| IO.userError s!"missing demo binary at {bin} (did you run `lake build`?)"

/-!
## Fault injection / robustness checks

We run the already-built `tensorlogic_demo` binary and assert:
- deterministic mode is byte-stable across runs (stdout),
- locale/PATH variations do not affect deterministic output,
- common failure modes exit nonzero and emit recognizable error classes.
-/

private def testDeterminism (bin : System.FilePath) : IO Unit := do
  let r1 ← runBin bin #["--deterministic", "true"]
  let r2 ← runBin bin #["--deterministic", "true"]
  assertTrue (r1.code == 0) s!"determinism: expected exit 0, got {r1.code} (stderr={r1.err})"
  assertTrue (r2.code == 0) s!"determinism: expected exit 0, got {r2.code} (stderr={r2.err})"
  assertTrue (r1.out == r2.out) "determinism: stdout differed across identical runs"
  let h1 := HeytingLean.Util.SHA256.sha256Hex r1.out.toUTF8
  let h2 := HeytingLean.Util.SHA256.sha256Hex r2.out.toUTF8
  assertTrue (h1 == h2) "determinism: stdout sha256 differed across identical runs"

private def testLocaleAndPathIndependence (bin : System.FilePath) : IO Unit := do
  let base ← runBin bin #["--deterministic", "true"]
  assertTrue (base.code == 0) s!"locale/path: base run failed (stderr={base.err})"

  let envC : Array (String × Option String) := #[("LC_ALL", some "C"), ("LANG", some "C")]
  let rC ← runBin bin #["--deterministic", "true"] envC
  assertTrue (rC.code == 0) s!"locale/path: LC_ALL=C run failed (stderr={rC.err})"
  assertTrue (rC.out == base.out) "locale/path: deterministic output changed under LC_ALL=C"

  -- If the toolchain shells out, an empty PATH can break determinism; we require it not to.
  let rNoPath ← runBin bin #["--deterministic", "true"] #[("PATH", some "")]
  assertTrue (rNoPath.code == 0) s!"locale/path: PATH='' run failed (stderr={rNoPath.err})"
  assertTrue (rNoPath.out == base.out) "locale/path: deterministic output changed under PATH=''"

private def testBadArgs (bin : System.FilePath) : IO Unit := do
  let r ← runBin bin #["--nope"]
  assertTrue (r.code != 0) "bad args: expected nonzero exit code"
  assertTrue (containsStr r.err "unknown argument") s!"bad args: missing 'unknown argument' in stderr: {r.err}"

private def testBadBool (bin : System.FilePath) : IO Unit := do
  let r ← runBin bin #["--deterministic", "maybe"]
  assertTrue (r.code != 0) "bad bool: expected nonzero exit code"
  assertTrue (containsStr r.err "expected true/false") s!"bad bool: missing parse error in stderr: {r.err}"

private def testOutIsDirectory (bin : System.FilePath) : IO Unit := do
  let leanDir ← resolveLeanDir
  let dir := leanDir / ".tmp" / "tensorlogic_demo_faulttest" / "outdir"
  IO.FS.createDirAll dir
  let r ← runBin bin #["--deterministic", "true", "--out", dir.toString]
  assertTrue (r.code != 0) "out-is-dir: expected nonzero exit code"
  assertTrue (containsStr r.err "out_path_is_directory") s!"out-is-dir: missing error class in stderr: {r.err}"

def mainImpl (_args : List String) : IO UInt32 := do
  try
    let bin ← resolveDemoBin
    testDeterminism bin
    testLocaleAndPathIndependence bin
    testBadArgs bin
    testBadBool bin
    testOutIsDirectory bin
    pure 0
  catch e =>
    die s!"tensorlogic_demo_faulttest: FAILED: {e}"

end HeytingLean.Tests.TensorLogic.DemoFaulttestMain

open HeytingLean.Tests.TensorLogic.DemoFaulttestMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.TensorLogic.DemoFaulttestMain.mainImpl args
