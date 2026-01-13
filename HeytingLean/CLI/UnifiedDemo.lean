import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
import HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres
import HeytingLean.Crypto.FHE.NoiseHomomorphicSpec
import HeytingLean.Crypto.KEM.MLKEMPKE
import HeytingLean.Crypto.Lattice.NoiseMLWE
import HeytingLean.Crypto.ZK.SISPoKDemo
import HeytingLean.CLI.PQCParamValidator
import HeytingLean.Compiler.TensorLogic.ParseFacts
import HeytingLean.Compiler.TensorLogic.ParseRulesJson
import HeytingLean.Compiler.TensorLogic.Validate
import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.ExportGraph
import HeytingLean.Compiler.TensorLogic.HomologyEncoding
import HeytingLean.Computational.Homology.ChainComplex
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.Quantum.QChannel
import HeytingLean.Quantum.Contextuality.MerminPeresRealization
import Lean.Data.Json

namespace HeytingLean
namespace CLI

open HeytingLean.LoF.CryptoSheaf.Quantum
open HeytingLean.Crypto
open HeytingLean.Crypto.FHE
open HeytingLean.Crypto.KEM.FIPS203.KPKE
open HeytingLean.Crypto.ZK
open HeytingLean.Quantum
open HeytingLean.Compiler
open HeytingLean.Computational

-- Physical-process evidence (proof hooks only; keep runtime computable)
private def physicalPayload : String :=
  let ok : Bool :=
    Id.run do
      let Φ : HeytingLean.Quantum.KrausChannel 1 1 := HeytingLean.Quantum.KrausChannel.id 1
      let ρ : HeytingLean.Quantum.Mat 1 := 0
      let _ := Φ.trace_map (ρ := ρ)
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod
      true
  "{\"qstate\":true,\"qchannel\":true,\"checks\":" ++ toString ok ++ "}"

-- Contextuality payload
private def contextualityPayload : String :=
  -- Keep this runtime-computable: the triangle demo cover has size 3.
  let coverSize : Nat := 3
  let ok : Bool :=
    Id.run do
      let _ := triangle_no_global
      let _ := HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres.no_assignment
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.row1_prod
      let _ := HeytingLean.Quantum.Contextuality.MerminPeres.col3_prod
      true
  "{\"contextual\":true," ++
    "\"cover_size\":" ++ toString coverSize ++ "," ++
    "\"witnesses\":{" ++
      "\"triangle\":{\"no_global\":true,\"kind\":\"possibilistic\"}," ++
      "\"mermin_peres\":{\"no_assignment\":true,\"quantum_realizable\":true}" ++
    "}," ++
    "\"checks\":" ++ toString ok ++ "}"

-- Valuation payload (cardinalities only)
private def valuationPayload : String :=
  -- Keep this runtime-computable (and schema-stable): the triangle witness supports are size 2.
  let sAB : Nat := 2
  let sBC : Nat := 2
  let sAC : Nat := 2
  let items :=
    "[{\"context\":\"ab\",\"size\":" ++ toString sAB ++ "}," ++
    "{\"context\":\"bc\",\"size\":" ++ toString sBC ++ "}," ++
    "{\"context\":\"ac\",\"size\":" ++ toString sAC ++ "}]"
  "{\"supports\":" ++ items ++ "}"

-- FHE smoke
namespace ToyFHE
open HeytingLean.Crypto.Lattice
open HeytingLean.Crypto.FHE
def P : MLWEParams := { n := 1, q := 17, k := 1 }
def S1 : ModVec P.k P.n P.q := fun _ _ => 1
def S2 : ModVec P.k P.n P.q := fun _ _ => 2
def Ct1 : MLWEInstance P := { A := 1, b := S1 }
def Ct2 : MLWEInstance P := { A := 1, b := S2 }
end ToyFHE

private def fhePayload : String :=
  let ok := Id.run do let _ := addCt ToyFHE.P ToyFHE.Ct1 ToyFHE.Ct2; true
  "{\"hom_add_demo\":" ++ toString ok ++ "}"

-- ZK smoke (SIS PoK)
private def zkPayload : String :=
  let p := (sisPoK toyParams 0)
  let verified := p.verify toyStmt (p.prove toyStmt (0) (by exact toyRelHolds))
  "{\"sis_pok_demo\":" ++ toString verified ++ "}"

-- PQC sentinel
private def pqcVerifiedIO : IO Bool := do
  let p1 := System.FilePath.mk "../.artifacts/pqc_verify_all.ok"
  let p2 := System.FilePath.mk ".artifacts/pqc_verify_all.ok"
  let e1 ← p1.pathExists
  if e1 then
    return true
  let e2 ← p2.pathExists
  return e2

private def readEvidenceHashIO : IO (Option String) := do
  let p1 := System.FilePath.mk "../.artifacts/pqc_verify_all.ok"
  let p2 := System.FilePath.mk ".artifacts/pqc_verify_all.ok"
  let tryRead (p : System.FilePath) : IO (Option String) := do
    if !(← p.pathExists) then return none
    try
      let s ← IO.FS.readFile p
      match Lean.Json.parse s with
      | Except.ok j =>
        match j.getObjVal? "evidence_hash" with
        | Except.ok (Lean.Json.str h) => return some h
        | _ => return none
      | _ => return none
    catch _ =>
      return none
  match (← tryRead p1) with
  | some h => return some h
  | none   => tryRead p2

private def pqcPayload (verified : Bool) (evid? : Option String) : String :=
  match evid? with
  | some h => "{\"verified\":" ++ toString verified ++ ",\"evidence_hash\":\"" ++ h ++ "\"}"
  | none    => "{\"verified\":" ++ toString verified ++ "}"

private def pqcParamsPayload : String :=
  toString (HeytingLean.CLI.PQCValidator.reportJson)

/-! ## TensorLogic + SKY pipeline (unified demo extension) -/

namespace UnifiedPipeline

open Std
open Lean
open Lean.Json
open HeytingLean.Compiler.TensorLogic
open HeytingLean.LoF

private def jsonNumOrStr (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | .inr n => Json.num n
  | .inl s => Json.str s

private def atomToJson (a : Atom) (w : Float) : Json :=
  Json.mkObj
    [ ("pred", Json.str a.pred)
    , ("args", Json.arr (a.args.map Json.str |>.toArray))
    , ("weight", jsonNumOrStr w)
    ]

private def lexLt (a b : List String) : Bool :=
  match a, b with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true
      else if x = y then lexLt xs ys
      else false

private def atomLt (a b : Atom) : Bool :=
  if a.pred < b.pred then true
  else if a.pred = b.pred then lexLt a.args b.args
  else false

private def factsToSortedJson (F : Facts) : Json :=
  let xs := F.toList.toArray.qsort (fun aw bw => atomLt aw.1 bw.1) |>.toList
  Json.arr (xs.map (fun (aw : Atom × Float) => atomToJson aw.1 aw.2) |>.toArray)

private def demoAtomPat (pred : String) (args : List String) : AtomPat :=
  { pred := pred, args := args.map Sym.ofString }

private def demoProgram : Program :=
  { rules :=
      [ { head := demoAtomPat "reachable" ["X", "Y"]
        , body := [demoAtomPat "edge" ["X", "Y"]]
        }
      , { head := demoAtomPat "reachable" ["X", "Z"]
        , body := [demoAtomPat "edge" ["X", "Y"], demoAtomPat "reachable" ["Y", "Z"]]
        }
      ]
  }

private def demoFacts : List (Atom × Float) :=
  [ ({ pred := "edge", args := ["a", "b"] }, 1.0)
  , ({ pred := "edge", args := ["b", "c"] }, 1.0)
  ]

private def loadProgramIO (rulesPath? : Option System.FilePath) : IO (Except String Program) := do
  match rulesPath? with
  | none => return .ok demoProgram
  | some fp =>
      try
        let rulesRaw ← IO.FS.readFile fp
        let rulesJson ←
          match Json.parse rulesRaw with
          | .ok j => pure j
          | .error e => return .error s!"rules JSON parse error: {e}"
        pure <| (parseProgramJson rulesJson >>= validateProgram)
      catch e =>
        return .error s!"rules read failed ({fp}): {e}"

private def loadFactsIO (factsPaths : List System.FilePath) : IO (Except String (List (Atom × Float))) := do
  if factsPaths.isEmpty then
    return .ok demoFacts
  let mut acc : List (Atom × Float) := []
  for fp in factsPaths do
    try
      let txt ← IO.FS.readFile fp
      match parseFactsTSV txt with
      | .ok xs => acc := acc ++ xs
      | .error e => return .error s!"facts parse error ({fp}): {e}"
    catch e =>
      return .error s!"facts read failed ({fp}): {e}"
  return .ok acc

private def tensorLogicPayloadIO (rulesPath? : Option System.FilePath) (factsPaths : List System.FilePath) : IO Json := do
  let progE ← loadProgramIO rulesPath?
  let factsE ← loadFactsIO factsPaths
  match progE, factsE with
  | .error e, _ => return Json.mkObj [("error", Json.str e)]
  | _, .error e => return Json.mkObj [("error", Json.str e)]
  | .ok prog, .ok baseFacts =>
      let cfg : RunConfig := { mode := .heyting, tnorm := .product, maxIter := 50, eps := 1e-6 }
      let ops := Ops.forConfig cfg.mode cfg.tnorm
      let init := Facts.fromList ops baseFacts
      let res := run cfg prog init
      let payload :=
        Json.mkObj
          [ ("mode", Json.str "heyting")
          , ("iters", Json.num (JsonNumber.fromNat res.iters))
          , ("converged", Json.bool res.converged)
          , ("delta", jsonNumOrStr res.delta)
          , ("facts", factsToSortedJson res.facts)
          ]
      return payload

private def tensorGraphPayloadIO (rulesPath? : Option System.FilePath) (factsPaths : List System.FilePath) : IO Json := do
  let progE ← loadProgramIO rulesPath?
  let factsE ← loadFactsIO factsPaths
  match progE, factsE with
  | .error e, _ => return Json.mkObj [("error", Json.str e)]
  | _, .error e => return Json.mkObj [("error", Json.str e)]
  | .ok prog, .ok baseFacts =>
      let cfg : RunConfig := { mode := .heyting, tnorm := .product, maxIter := 50, eps := 1e-6 }
      let sharpness : Float := 1.0
      match ExportGraph.tensorGraphJson cfg sharpness prog baseFacts with
      | .ok j => return j
      | .error e => return Json.mkObj [("error", Json.str e)]

/-! ### SKY multiway (bounded) -/

private def combToJson : Comb → Json
  | .K => Json.arr #[Json.num 0]
  | .S => Json.arr #[Json.num 1]
  | .Y => Json.arr #[Json.num 2]
  | .app f a => Json.arr #[Json.num 3, combToJson f, combToJson a]

private def pathToJson (p : Comb.RedexPath) : Json :=
  Json.arr ((p.map (fun d => Json.num d.toNat)).toArray)

private def eventToJson (ed : Comb.EventData) : Json :=
  Json.mkObj
    [ ("ruleIdx", Json.num ed.rule.toNat)
    , ("path", pathToJson ed.path) ]

private def demoSK : Comb :=
  Comb.app
    (Comb.app (Comb.app .K .K) .S)
    (Comb.app (Comb.app .K .S) .K)

private def demoY : Comb :=
  Comb.app
    (Comb.app .Y .K)
    (Comb.app (Comb.app .K .S) .K)

private def selectSkyDemo (name : String) : (String × Comb) :=
  let key := name.trim.toLower
  if key = "y" || key = "sky" then
    ("sky_demo_y", demoY)
  else
    ("sky_demo_sk", demoSK)

private def findIdxFuel {α : Type} [DecidableEq α] (arr : Array α) (x : α) (fuel i : Nat) :
    Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : i < arr.size then
        if arr[i] = x then some i else findIdxFuel arr x fuel (i + 1)
      else
        none

private def findIdx {α : Type} [DecidableEq α] (arr : Array α) (x : α) : Option Nat :=
  findIdxFuel arr x (arr.size + 1) 0

private def getIdx {α : Type} [DecidableEq α] (nodes : Array α) (x : α) : (Array α × Nat) :=
  match findIdx nodes x with
  | some i => (nodes, i)
  | none => (nodes.push x, nodes.size)

private def dedupArray {α : Type} [DecidableEq α] (xs : Array α) : Array α :=
  xs.foldl (init := (#[] : Array α)) (fun acc x => if acc.contains x then acc else acc.push x)

private def pairEdges (idxs : Array Nat) : Array (Nat × Nat) :=
  let n := idxs.size
  let rec outer (i : Nat) (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
    if i < n then
      let ii := idxs[i]!
      let rec inner (j : Nat) (acc2 : Array (Nat × Nat)) : Array (Nat × Nat) :=
        if j < n then
          let jj := idxs[j]!
          inner (j + 1) (acc2.push (ii, jj))
        else acc2
      outer (i + 1) (inner (i + 1) acc)
    else acc
  outer 0 #[]

private def getD (m : Std.HashMap Nat Nat) (k : Nat) (default : Nat) : Nat :=
  match m.get? k with
  | some v => v
  | none => default

private def incrCount (m : Std.HashMap Nat Nat) (k : Nat) (inc : Nat) : Std.HashMap Nat Nat :=
  let curr := getD m k 0
  m.insert k (curr + inc)

private def skyMultiwayPayload (demo : String) (maxDepth : Nat) : Json := Id.run do
  let (sysName, init) := selectSkyDemo demo
  let mut nodes : Array Comb := #[init]
  let mut edges : Array Json := #[]
  let mut branchial : Array Json := #[]
  let mut levels : Array (Array Nat) := #[#[0]]

  let mut curr : Array Comb := #[init]
  let mut countsCurr : Std.HashMap Nat Nat := (Std.HashMap.emptyWithCapacity 8).insert 0 1
  let mut pathCounts : Array Json :=
    #[Json.arr #[Json.mkObj [("id", Json.num 0), ("count", Json.num 1)]]]

  for _step in [0:maxDepth] do
    let mut nextRaw : Array Comb := #[]
    let mut countsNext : Std.HashMap Nat Nat := Std.HashMap.emptyWithCapacity 8
    for s in curr do
      let (nodes1, srcIdx) := getIdx nodes s
      nodes := nodes1
      let srcCount := getD countsCurr srcIdx 0
      let mut childIdxs : Array Nat := #[]
      for (ed, t) in (Comb.stepEdgesList s) do
        let (nodes2, dstIdx) := getIdx nodes t
        nodes := nodes2
        edges := edges.push <|
          Json.mkObj
            [ ("src", Json.num srcIdx)
            , ("dst", Json.num dstIdx)
            , ("label", eventToJson ed) ]
        childIdxs := childIdxs.push dstIdx
        nextRaw := nextRaw.push t
        countsNext := incrCount countsNext dstIdx srcCount
      let childIdxsDedup := dedupArray childIdxs
      for (i, j) in pairEdges childIdxsDedup do
        branchial := branchial.push <| Json.mkObj [("i", Json.num i), ("j", Json.num j)]

    let next := dedupArray nextRaw
    let nextIdxs : Array Nat :=
      next.map (fun s =>
        let (_, i) := getIdx nodes s
        i)
    levels := levels.push nextIdxs
    let countsJson :=
      nextIdxs.map (fun (i : Nat) =>
        Json.mkObj [("id", Json.num i), ("count", Json.num (getD countsNext i 0))])
    pathCounts := pathCounts.push (Json.arr countsJson)
    curr := next
    countsCurr := countsNext

  let nodesJson := Json.arr (nodes.map combToJson)
  let edgesJson := Json.arr edges
  let branchialJson := Json.arr branchial
  let levelsJson := Json.arr (levels.map (fun lvl => Json.arr (lvl.map (fun (i : Nat) => Json.num i))))
  let pathCountsJson := Json.arr pathCounts

  return Json.mkObj
    [ ("system", Json.str sysName)
    , ("maxDepth", Json.num maxDepth)
    , ("nodes", nodesJson)
    , ("edges", edgesJson)
    , ("levels", levelsJson)
    , ("branchial", branchialJson)
    , ("pathCounts", pathCountsJson) ]

end UnifiedPipeline

-- K-PKE (ML-KEM base encryption scheme) proof hook
private def kpkePayload : String :=
  let ok : Bool :=
    Id.run do
      let _ :=
        (fun {p : HeytingLean.Crypto.KEM.FIPS203.MLKEM203Params}
            (codec : MsgCodec p) (pk : PublicKey p) (sk : SecretKey p)
            (e : ModVec p) (ht : pk.t = pk.A.mulVec sk.s + e)
            (m : codec.Msg) (r e1 : ModVec p) (e2 : Rq p)
            (hgood : codec.good (dot e r + e2 - dot sk.s e1)) =>
          decrypt_encryptDet (codec := codec) (pk := pk) (sk := sk) (e := e) (ht := ht) (m := m)
            (r := r) (e1 := e1) (e2 := e2) (hgood := hgood))
      true
  "{\"spec\":true," ++
    "\"correctness_theorem\":\"FIPS203.KPKE.decrypt_encryptDet\"," ++
    "\"residual_noise\":\"<e,r> + e2 - <s,e1>\"," ++
    "\"checks\":" ++ toString ok ++ "}"

private structure Flags where
  quick : Bool := true
  full : Bool := false
  contextualityOnly : Bool := false
  valuationOnly : Bool := false
  fhezkOnly : Bool := false
  tensorRules : Option System.FilePath := none
  tensorFacts : List System.FilePath := []
  skyDemo : String := "sk"
  skyMaxDepth : Nat := 3

private partial def parseFlags (args : List String) (acc : Flags := {}) : Flags :=
  match args with
  | [] => acc
  | "--quick" :: rest => parseFlags rest { acc with quick := true, full := false }
  | "--full" :: rest => parseFlags rest { acc with quick := false, full := true }
  | "--contextuality" :: rest =>
      parseFlags rest { acc with contextualityOnly := true, valuationOnly := false, fhezkOnly := false }
  | "--valuation" :: rest =>
      parseFlags rest { acc with contextualityOnly := false, valuationOnly := true, fhezkOnly := false }
  | "--fhe-zk" :: rest =>
      parseFlags rest { acc with contextualityOnly := false, valuationOnly := false, fhezkOnly := true }
  | "--rules" :: fp :: rest =>
      parseFlags rest { acc with tensorRules := some (System.FilePath.mk fp) }
  | "--facts" :: fp :: rest =>
      parseFlags rest { acc with tensorFacts := acc.tensorFacts ++ [System.FilePath.mk fp] }
  | "--sky-demo" :: nm :: rest =>
      parseFlags rest { acc with skyDemo := nm }
  | "--sky-depth" :: n :: rest =>
      match n.toNat? with
      | some k => parseFlags rest { acc with skyMaxDepth := k }
      | none => parseFlags rest acc
  | _ :: rest => parseFlags rest acc

def UnifiedDemo.main (argv : List String) : IO UInt32 := do
  let flags := parseFlags argv
  if flags.contextualityOnly then
    IO.println contextualityPayload; return 0
  if flags.valuationOnly then
    IO.println valuationPayload; return 0
  if flags.fhezkOnly then
    IO.println ("{" ++ "\"fhe\":" ++ fhePayload ++ ",\"zk\":" ++ zkPayload ++ "}"); return 0
  let pqcV ← if flags.full then pqcVerifiedIO else pure false
  let evid ← if flags.full then readEvidenceHashIO else pure none

  let tensorPayload ←
    UnifiedPipeline.tensorLogicPayloadIO (rulesPath? := flags.tensorRules) (factsPaths := flags.tensorFacts)
  let tensorGraph ←
    UnifiedPipeline.tensorGraphPayloadIO (rulesPath? := flags.tensorRules) (factsPaths := flags.tensorFacts)
  let skyMultiway := UnifiedPipeline.skyMultiwayPayload flags.skyDemo flags.skyMaxDepth

  let payload := "{" ++
    "\"demo\":\"unified\"," ++
    "\"contextuality\":" ++ contextualityPayload ++ "," ++
    "\"physical\":" ++ physicalPayload ++ "," ++
    "\"valuation\":" ++ valuationPayload ++ "," ++
    "\"fhe\":" ++ fhePayload ++ "," ++
    "\"zk\":" ++ zkPayload ++ "," ++
    "\"kpke\":" ++ kpkePayload ++ "," ++
    "\"pqc\":" ++ pqcPayload pqcV evid ++ "," ++
    "\"pqc_params\":" ++ pqcParamsPayload ++ "," ++
    "\"tensorlogic\":" ++ toString tensorPayload ++ "," ++
    "\"tensor_graph\":" ++ toString tensorGraph ++ "," ++
    "\"sky_multiway\":" ++ toString skyMultiway ++ "}"
  IO.println payload
  return 0

end CLI
end HeytingLean

def main (argv : List String) : IO UInt32 := HeytingLean.CLI.UnifiedDemo.main argv
