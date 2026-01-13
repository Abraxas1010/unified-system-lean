window.UNIFIED_PROOFS = {
  "items": [
    {
      "name": "HeytingLean.CLI.physicalPayload",
      "kind": "def",
      "line": 34,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def physicalPayload : String :=\n  let ok : Bool :=\n    Id.run do\n      let \u03a6 : HeytingLean.Quantum.KrausChannel 1 1 := HeytingLean.Quantum.KrausChannel.id 1\n      let \u03c1 : HeytingLean.Quantum.Mat 1 := 0",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 209,
        "name_depth": 2
      },
      "pos": {
        "x": 0.5918280395373652,
        "y": 0.028403226566800083
      },
      "pos3": {
        "x": 0.19182803953736513,
        "y": 0.007503226566800081,
        "z": 0.4825087955107358
      }
    },
    {
      "name": "HeytingLean.CLI.contextualityPayload",
      "kind": "def",
      "line": 45,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def contextualityPayload : String :=\n  -- Keep this runtime-computable: the triangle demo cover has size 3.\n  let coverSize : Nat := 3\n  let ok : Bool :=\n    Id.run do",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 175,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4825087955107358,
        "y": 0.08446322144464682
      },
      "pos3": {
        "x": 0.06696322144464682,
        "y": 0.22094136424920371,
        "z": 0.6030098462268734
      }
    },
    {
      "name": "HeytingLean.CLI.valuationPayload",
      "kind": "def",
      "line": 64,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def valuationPayload : String :=\n  -- Keep this runtime-computable (and schema-stable): the triangle witness supports are size 2.\n  let sAB : Nat := 2\n  let sBC : Nat := 2\n  let sAC : Nat := 2",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 200,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6209413642492038,
        "y": 0.22300984622687337
      },
      "pos3": {
        "x": 0.2676538703114536,
        "y": 0.026081649788824844,
        "z": 0.5265765459055811
      }
    },
    {
      "name": "HeytingLean.CLI.ToyFHE.P",
      "kind": "def",
      "line": 79,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def P : MLWEParams := { n := 1, q := 17, k := 1 }\ndef S1 : ModVec P.k P.n P.q := fun _ _ => 1\ndef S2 : ModVec P.k P.n P.q := fun _ _ => 2\ndef Ct1 : MLWEInstance P := { A := 1, b := S1 }\ndef Ct2 : MLWEInstance P := { A := 1, b := S2 }",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 14,
        "tactics": 0,
        "length": 233,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8676538703114537,
        "y": 0.049381649788824845
      },
      "pos3": {
        "x": 0.008939165831421103,
        "y": 0.065591392441081,
        "z": 0.7516065864310089
      }
    },
    {
      "name": "HeytingLean.CLI.ToyFHE.S1",
      "kind": "def",
      "line": 80,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def S1 : ModVec P.k P.n P.q := fun _ _ => 1\ndef S2 : ModVec P.k P.n P.q := fun _ _ => 2\ndef Ct1 : MLWEInstance P := { A := 1, b := S1 }\ndef Ct2 : MLWEInstance P := { A := 1, b := S2 }\nend ToyFHE",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 10,
        "tactics": 0,
        "length": 194,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7265765459055812,
        "y": 0.028339165831421105
      },
      "pos3": {
        "x": 0.007960790905159087,
        "y": 0.05965129520599455,
        "z": 0.794965331333857
      }
    },
    {
      "name": "HeytingLean.CLI.ToyFHE.S2",
      "kind": "def",
      "line": 81,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def S2 : ModVec P.k P.n P.q := fun _ _ => 2\ndef Ct1 : MLWEInstance P := { A := 1, b := S1 }\ndef Ct2 : MLWEInstance P := { A := 1, b := S2 }\nend ToyFHE\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 8,
        "tactics": 0,
        "length": 151,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6655913924410811,
        "y": 0.16670658643100872
      },
      "pos3": {
        "x": 0.163482444180965,
        "y": 0.066132186612209,
        "z": 0.7767797051627727
      }
    },
    {
      "name": "HeytingLean.CLI.ToyFHE.Ct1",
      "kind": "def",
      "line": 82,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def Ct1 : MLWEInstance P := { A := 1, b := S1 }\ndef Ct2 : MLWEInstance P := { A := 1, b := S2 }\nend ToyFHE\n\nprivate def fhePayload : String :=",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 7,
        "tactics": 0,
        "length": 142,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6079607909051592,
        "y": 0.07385129520599455
      },
      "pos3": {
        "x": 0.242829137003348,
        "y": 0.001949627903418305,
        "z": 0.8417457755498424
      }
    },
    {
      "name": "HeytingLean.CLI.ToyFHE.Ct2",
      "kind": "def",
      "line": 83,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def Ct2 : MLWEInstance P := { A := 1, b := S2 }\nend ToyFHE\n\nprivate def fhePayload : String :=\n  let ok := Id.run do let _ := addCt ToyFHE.P ToyFHE.Ct1 ToyFHE.Ct2; true",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 168,
        "name_depth": 3
      },
      "pos": {
        "x": 0.794965331333857,
        "y": 0.180282444180965
      },
      "pos3": {
        "x": 0.20944181849646806,
        "y": 0.10207515495539755,
        "z": 0.6466438499435345
      }
    },
    {
      "name": "HeytingLean.CLI.fhePayload",
      "kind": "def",
      "line": 86,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def fhePayload : String :=\n  let ok := Id.run do let _ := addCt ToyFHE.P ToyFHE.Ct1 ToyFHE.Ct2; true\n  \"{\\\"hom_add_demo\\\":\" ++ toString ok ++ \"}\"\n\n-- ZK smoke (SIS PoK)",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 176,
        "name_depth": 2
      },
      "pos": {
        "x": 0.466132186612209,
        "y": 0.19437970516277261
      },
      "pos3": {
        "x": 0.28716392166203436,
        "y": 0.10097836353378803,
        "z": 0.4278237530140444
      }
    },
    {
      "name": "HeytingLean.CLI.zkPayload",
      "kind": "def",
      "line": 91,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def zkPayload : String :=\n  let p := (sisPoK toyParams 0)\n  let verified := p.verify toyStmt (p.prove toyStmt (0) (by exact toyRelHolds))\n  \"{\\\"sis_pok_demo\\\":\" ++ toString verified ++ \"}\"\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 197,
        "name_depth": 2
      },
      "pos": {
        "x": 0.642829137003348,
        "y": 0.12164962790341831
      },
      "pos3": {
        "x": 0.029014913050039202,
        "y": 0.35424830990423795,
        "z": 0.5811178094100673
      }
    },
    {
      "name": "HeytingLean.CLI.pqcVerifiedIO",
      "kind": "def",
      "line": 97,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def pqcVerifiedIO : IO Bool := do\n  let p1 := System.FilePath.mk \"../.artifacts/pqc_verify_all.ok\"\n  let p2 := System.FilePath.mk \".artifacts/pqc_verify_all.ok\"\n  let e1 \u2190 p1.pathExists\n  if e1 then",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 206,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6417457755498424,
        "y": 0.23004181849646807
      },
      "pos3": {
        "x": 0.24213848198231405,
        "y": 0.21891953600814537,
        "z": 0.5608684274364102
      }
    },
    {
      "name": "HeytingLean.CLI.readEvidenceHashIO",
      "kind": "def",
      "line": 106,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def readEvidenceHashIO : IO (Option String) := do\n  let p1 := System.FilePath.mk \"../.artifacts/pqc_verify_all.ok\"\n  let p2 := System.FilePath.mk \".artifacts/pqc_verify_all.ok\"\n  let tryRead (p : System.FilePath) : IO (Option String) := do\n    if !(\u2190 p.pathExists) then return none",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 289,
        "name_depth": 2
      },
      "pos": {
        "x": 0.5020751549553976,
        "y": 0.07554384994353447
      },
      "pos3": {
        "x": 0.2919347291938112,
        "y": 0.11356031316250603,
        "z": 0.5656121893819681
      }
    },
    {
      "name": "HeytingLean.CLI.pqcPayload",
      "kind": "def",
      "line": 125,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def pqcPayload (verified : Bool) (evid? : Option String) : String :=\n  match evid? with\n  | some h => \"{\\\"verified\\\":\" ++ toString verified ++ \",\\\"evidence_hash\\\":\\\"\" ++ h ++ \"\\\"}\"\n  | none    => \"{\\\"verified\\\":\" ++ toString verified ++ \"}\"\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 249,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6871639216620344,
        "y": 0.12587836353378803
      },
      "pos3": {
        "x": 0.24882139927589844,
        "y": 0.18555592570927382,
        "z": 0.6585120700932332
      }
    },
    {
      "name": "HeytingLean.CLI.pqcParamsPayload",
      "kind": "def",
      "line": 130,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def pqcParamsPayload : String :=\n  toString (HeytingLean.CLI.PQCValidator.reportJson)\n\n/-! ## TensorLogic + SKY pipeline (unified demo extension) -/\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 157,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4278237530140444,
        "y": 0.044714913050039204
      },
      "pos3": {
        "x": 0.1732056435770286,
        "y": 0.21137155086447704,
        "z": 0.4137473150966987
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.jsonNumOrStr",
      "kind": "def",
      "line": 143,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def jsonNumOrStr (x : Float) : Json :=\n  match JsonNumber.fromFloat? x with\n  | .inr n => Json.num n\n  | .inl s => Json.str s\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 134,
        "name_depth": 3
      },
      "pos": {
        "x": 0.854248309904238,
        "y": 0.1945178094100673
      },
      "pos3": {
        "x": 0.06836948269546406,
        "y": 0.08681638908063215,
        "z": 0.6239375930770883
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.atomToJson",
      "kind": "def",
      "line": 148,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def atomToJson (a : Atom) (w : Float) : Json :=\n  Json.mkObj\n    [ (\"pred\", Json.str a.pred)\n    , (\"args\", Json.arr (a.args.map Json.str |>.toArray))\n    , (\"weight\", jsonNumOrStr w)",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 191,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8421384819823141,
        "y": 0.23801953600814538
      },
      "pos3": {
        "x": 0.06983726590830905,
        "y": 0.030300428822918734,
        "z": 0.6833920809330277
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.lexLt",
      "kind": "def",
      "line": 155,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def lexLt (a b : List String) : Bool :=\n  match a, b with\n  | [], [] => false\n  | [], _ => true\n  | _, [] => false",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 122,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7608684274364104,
        "y": 0.3041347291938112
      },
      "pos3": {
        "x": 0.19070533327932004,
        "y": 0.10944965369102527,
        "z": 0.7110542901350649
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.atomLt",
      "kind": "def",
      "line": 165,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def atomLt (a b : Atom) : Bool :=\n  if a.pred < b.pred then true\n  else if a.pred = b.pred then lexLt a.args b.args\n  else false\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 137,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7135603131625061,
        "y": 0.17931218938196808
      },
      "pos3": {
        "x": 0.06285210923144631,
        "y": 0.08009334661473401,
        "z": 0.8809963763137483
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.factsToSortedJson",
      "kind": "def",
      "line": 170,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def factsToSortedJson (F : Facts) : Json :=\n  let xs := F.toList.toArray.qsort (fun aw bw => atomLt aw.1 bw.1) |>.toList\n  Json.arr (xs.map (fun (aw : Atom \u00d7 Float) => atomToJson aw.1 aw.2) |>.toArray)\n\nprivate def demoAtomPat (pred : String) (args : List String) : AtomPat :=",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 284,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8488213992758985,
        "y": 0.21395592570927383
      },
      "pos3": {
        "x": 0.19441061557397807,
        "y": 0.18273930170009645,
        "z": 0.6513415944594292
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.demoAtomPat",
      "kind": "def",
      "line": 174,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def demoAtomPat (pred : String) (args : List String) : AtomPat :=\n  { pred := pred, args := args.map Sym.ofString }\n\nprivate def demoProgram : Program :=\n  { rules :=",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 174,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8585120700932333,
        "y": 0.1906056435770286
      },
      "pos3": {
        "x": 0.21873803938510475,
        "y": 0.04902074812857852,
        "z": 0.7138366325272945
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.demoProgram",
      "kind": "def",
      "line": 177,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def demoProgram : Program :=\n  { rules :=\n      [ { head := demoAtomPat \"reachable\" [\"X\", \"Y\"]\n        , body := [demoAtomPat \"edge\" [\"X\", \"Y\"]]\n        }",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 162,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8113715508644771,
        "y": 0.029947315096698665
      },
      "pos3": {
        "x": 0.2968570051909786,
        "y": 0.19199992795622786,
        "z": 0.767084923132394
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.demoFacts",
      "kind": "def",
      "line": 188,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def demoFacts : List (Atom \u00d7 Float) :=\n  [ ({ pred := \"edge\", args := [\"a\", \"b\"] }, 1.0)\n  , ({ pred := \"edge\", args := [\"b\", \"c\"] }, 1.0)\n  ]\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 151,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6683694826954641,
        "y": 0.10191638908063215
      },
      "pos3": {
        "x": 0.20538427529696238,
        "y": 0.25285557605694287,
        "z": 0.8327999734638736
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.loadProgramIO",
      "kind": "def",
      "line": 193,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def loadProgramIO (rulesPath? : Option System.FilePath) : IO (Except String Program) := do\n  match rulesPath? with\n  | none => return .ok demoProgram\n  | some fp =>\n      try",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 182,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6239375930770883,
        "y": 0.08803726590830904
      },
      "pos3": {
        "x": 0.06871442158923131,
        "y": 0.009630073171211328,
        "z": 0.6946359144177247
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.loadFactsIO",
      "kind": "def",
      "line": 207,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def loadFactsIO (factsPaths : List System.FilePath) : IO (Except String (List (Atom \u00d7 Float))) := do\n  if factsPaths.isEmpty then\n    return .ok demoFacts\n  let mut acc : List (Atom \u00d7 Float) := []\n  for fp in factsPaths do",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 230,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6303004288229188,
        "y": 0.10639208093302763
      },
      "pos3": {
        "x": 0.08032226279271082,
        "y": 0.06329485307589794,
        "z": 0.8828729143005164
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.tensorLogicPayloadIO",
      "kind": "def",
      "line": 221,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def tensorLogicPayloadIO (rulesPath? : Option System.FilePath) (factsPaths : List System.FilePath) : IO Json := do\n  let progE \u2190 loadProgramIO rulesPath?\n  let factsE \u2190 loadFactsIO factsPaths\n  match progE, factsE with\n  | .error e, _ => return Json.mkObj [(\"error\", Json.str e)]",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 287,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7907053332793201,
        "y": 0.13814965369102528
      },
      "pos3": {
        "x": 0.26291028794180066,
        "y": 0.09440336423954337,
        "z": 0.7966315995884641
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.tensorGraphPayloadIO",
      "kind": "def",
      "line": 242,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def tensorGraphPayloadIO (rulesPath? : Option System.FilePath) (factsPaths : List System.FilePath) : IO Json := do\n  let progE \u2190 loadProgramIO rulesPath?\n  let factsE \u2190 loadFactsIO factsPaths\n  match progE, factsE with\n  | .error e, _ => return Json.mkObj [(\"error\", Json.str e)]",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 287,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7110542901350649,
        "y": 0.09155210923144631
      },
      "pos3": {
        "x": 0.11868957031819927,
        "y": 0.27436427692216303,
        "z": 0.7376555557762197
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.combToJson",
      "kind": "def",
      "line": 257,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def combToJson : Comb \u2192 Json\n  | .K => Json.arr #[Json.num 0]\n  | .S => Json.arr #[Json.num 1]\n  | .Y => Json.arr #[Json.num 2]\n  | .app f a => Json.arr #[Json.num 3, combToJson f, combToJson a]",
      "family": "CLI",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 202,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7800933466147341,
        "y": 0.3011963763137482
      },
      "pos3": {
        "x": 0.17946404994941573,
        "y": 0.07398825230819503,
        "z": 0.7684104402489453
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.pathToJson",
      "kind": "def",
      "line": 263,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def pathToJson (p : Comb.RedexPath) : Json :=\n  Json.arr ((p.map (fun d => Json.num d.toNat)).toArray)\n\nprivate def eventToJson (ed : Comb.EventData) : Json :=\n  Json.mkObj",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 180,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7944106155739782,
        "y": 0.20073930170009646
      },
      "pos3": {
        "x": 0.07882248255688058,
        "y": 0.17537579706706216,
        "z": 0.8693468650807432
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.eventToJson",
      "kind": "def",
      "line": 266,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def eventToJson (ed : Comb.EventData) : Json :=\n  Json.mkObj\n    [ (\"ruleIdx\", Json.num ed.rule.toNat)\n    , (\"path\", pathToJson ed.path) ]\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 148,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6513415944594292,
        "y": 0.23353803938510476
      },
      "pos3": {
        "x": 0.11982015154211917,
        "y": 0.065796227747185,
        "z": 0.8992612819485332
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.demoSK",
      "kind": "def",
      "line": 271,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def demoSK : Comb :=\n  Comb.app\n    (Comb.app (Comb.app .K .K) .S)\n    (Comb.app (Comb.app .K .S) .K)\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 110,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6490207481285786,
        "y": 0.12483663252729432
      },
      "pos3": {
        "x": 0.15285788810293935,
        "y": 0.027272823652138168,
        "z": 0.6141349126274205
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.demoY",
      "kind": "def",
      "line": 276,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def demoY : Comb :=\n  Comb.app\n    (Comb.app .Y .K)\n    (Comb.app (Comb.app .K .S) .K)\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 95,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8968570051909787,
        "y": 0.20149992795622787
      },
      "pos3": {
        "x": 0.032894739105197746,
        "y": 0.188233812510927,
        "z": 0.8376238093088892
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.selectSkyDemo",
      "kind": "def",
      "line": 281,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def selectSkyDemo (name : String) : (String \u00d7 Comb) :=\n  let key := name.trim.toLower\n  if key = \"y\" || key = \"sky\" then\n    (\"sky_demo_y\", demoY)\n  else",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 161,
        "name_depth": 3
      },
      "pos": {
        "x": 0.767084923132394,
        "y": 0.22148427529696238
      },
      "pos3": {
        "x": 0.1266479900399052,
        "y": 0.01905831184558714,
        "z": 0.7144857859519611
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.findIdxFuel",
      "kind": "def",
      "line": 288,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def findIdxFuel {\u03b1 : Type} [DecidableEq \u03b1] (arr : Array \u03b1) (x : \u03b1) (fuel i : Nat) :\n    Option Nat :=\n  match fuel with\n  | 0 => none\n  | fuel + 1 =>",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 157,
        "name_depth": 3
      },
      "pos": {
        "x": 0.852855576056943,
        "y": 0.24849997346387342
      },
      "pos3": {
        "x": 0.29883641407202904,
        "y": 0.1587343035297411,
        "z": 0.8913235132840855
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.findIdx",
      "kind": "def",
      "line": 298,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def findIdx {\u03b1 : Type} [DecidableEq \u03b1] (arr : Array \u03b1) (x : \u03b1) : Option Nat :=\n  findIdxFuel arr x (arr.size + 1) 0\n\nprivate def getIdx {\u03b1 : Type} [DecidableEq \u03b1] (nodes : Array \u03b1) (x : \u03b1) : (Array \u03b1 \u00d7 Nat) :=\n  match findIdx nodes x with",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 246,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6687144215892314,
        "y": 0.03423007317121133
      },
      "pos3": {
        "x": 0.2582339106703494,
        "y": 0.0034443065828458908,
        "z": 0.8162165458080585
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.getIdx",
      "kind": "def",
      "line": 301,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def getIdx {\u03b1 : Type} [DecidableEq \u03b1] (nodes : Array \u03b1) (x : \u03b1) : (Array \u03b1 \u00d7 Nat) :=\n  match findIdx nodes x with\n  | some i => (nodes, i)\n  | none => (nodes.push x, nodes.size)\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 186,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6946359144177247,
        "y": 0.09892226279271082
      },
      "pos3": {
        "x": 0.20451311070797243,
        "y": 0.16109109912263855,
        "z": 0.6800475569857629
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.dedupArray",
      "kind": "def",
      "line": 306,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def dedupArray {\u03b1 : Type} [DecidableEq \u03b1] (xs : Array \u03b1) : Array \u03b1 :=\n  xs.foldl (init := (#[] : Array \u03b1)) (fun acc x => if acc.contains x then acc else acc.push x)\n\nprivate def pairEdges (idxs : Array Nat) : Array (Nat \u00d7 Nat) :=\n  let n := idxs.size",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 258,
        "name_depth": 3
      },
      "pos": {
        "x": 0.663294853075898,
        "y": 0.3086729143005163
      },
      "pos3": {
        "x": 0.1922885395739424,
        "y": 0.03346565207876293,
        "z": 0.7304295752007316
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.pairEdges",
      "kind": "def",
      "line": 309,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def pairEdges (idxs : Array Nat) : Array (Nat \u00d7 Nat) :=\n  let n := idxs.size\n  let rec outer (i : Nat) (acc : Array (Nat \u00d7 Nat)) : Array (Nat \u00d7 Nat) :=\n    if i < n then\n      let ii := idxs[i]!",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 202,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8629102879418007,
        "y": 0.11460336423954337
      },
      "pos3": {
        "x": 0.13611711189876194,
        "y": 0.286144778256324,
        "z": 0.8627558821134582
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.getD",
      "kind": "def",
      "line": 323,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def getD (m : Std.HashMap Nat Nat) (k : Nat) (default : Nat) : Nat :=\n  match m.get? k with\n  | some v => v\n  | none => default\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 136,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7966315995884641,
        "y": 0.13228957031819927
      },
      "pos3": {
        "x": 0.07901671522532723,
        "y": 0.15017583391508948,
        "z": 0.6535955641590395
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.incrCount",
      "kind": "def",
      "line": 328,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def incrCount (m : Std.HashMap Nat Nat) (k : Nat) (inc : Nat) : Std.HashMap Nat Nat :=\n  let curr := getD m k 0\n  m.insert k (curr + inc)\n\nprivate def skyMultiwayPayload (demo : String) (maxDepth : Nat) : Json := Id.run do",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 230,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8743642769221631,
        "y": 0.16065555577621962
      },
      "pos3": {
        "x": 0.27378835180344613,
        "y": 0.26115557095103004,
        "z": 0.68953343743459
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedPipeline.skyMultiwayPayload",
      "kind": "def",
      "line": 332,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def skyMultiwayPayload (demo : String) (maxDepth : Nat) : Json := Id.run do\n  let (sysName, init) := selectSkyDemo demo\n  let mut nodes : Array Comb := #[init]\n  let mut edges : Array Json := #[]\n  let mut branchial : Array Json := #[]",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 243,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6794640499494158,
        "y": 0.09828825230819503
      },
      "pos3": {
        "x": 0.19168484845980155,
        "y": 0.1826910634314517,
        "z": 0.6458517805648906
      }
    },
    {
      "name": "HeytingLean.CLI.kpkePayload",
      "kind": "def",
      "line": 398,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private def kpkePayload : String :=\n  let ok : Bool :=\n    Id.run do\n      let _ :=\n        (fun {p : HeytingLean.Crypto.KEM.FIPS203.MLKEM203Params}",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 148,
        "name_depth": 2
      },
      "pos": {
        "x": 0.5684104402489453,
        "y": 0.09362248255688058
      },
      "pos3": {
        "x": 0.22875324002254538,
        "y": 0.1618137090358877,
        "z": 0.6335879435891675
      }
    },
    {
      "name": "HeytingLean.CLI.Flags",
      "kind": "structure",
      "line": 415,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "private structure Flags where\n  quick : Bool := true\n  full : Bool := false\n  contextualityOnly : Bool := false\n  valuationOnly : Bool := false",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 143,
        "name_depth": 2
      },
      "pos": {
        "x": 0.5753757970670622,
        "y": 0.28364686508074305
      },
      "pos3": {
        "x": 0.15910610165855324,
        "y": 0.00017156883838305158,
        "z": 0.49724681710140195
      }
    },
    {
      "name": "HeytingLean.CLI.UnifiedDemo.main",
      "kind": "def",
      "line": 449,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def UnifiedDemo.main (argv : List String) : IO UInt32 := do\n  let flags := parseFlags argv\n  if flags.contextualityOnly then\n    IO.println contextualityPayload; return 0\n  if flags.valuationOnly then",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 200,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7198201515421192,
        "y": 0.085796227747185
      },
      "pos3": {
        "x": 0.00584302271574969,
        "y": 0.2787295848793851,
        "z": 0.8636165633469554
      }
    },
    {
      "name": "main",
      "kind": "def",
      "line": 485,
      "path": "HeytingLean/CLI/UnifiedDemo.lean",
      "snippet": "def main (argv : List String) : IO UInt32 := HeytingLean.CLI.UnifiedDemo.main argv\n",
      "family": "CLI",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 83,
        "name_depth": 0
      },
      "pos": {
        "x": 0.2992612819485331,
        "y": 0.16115788810293935
      },
      "pos3": {
        "x": 0.2494996588083538,
        "y": 0.09225423762079843,
        "z": 0.017377549948256264
      }
    },
    {
      "name": "HeytingLean.LoF.instHeytingOmega",
      "kind": "instance",
      "line": 48,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "instance instHeytingOmega : HeytingAlgebra (R.Omega) := inferInstance\n\n/-- The standard Heyting adjunction transferred to the fixed-point algebra. -/\nlemma heyting_adjunction (a b c : R.Omega) :\n    a \u2293 b \u2264 c \u2194 a \u2264 b \u21e8 c :=",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 223,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4272728236521382,
        "y": 0.03643491262742037
      },
      "pos3": {
        "x": 0.2634028797612121,
        "y": 0.28408483358939823,
        "z": 0.4256960356203637
      }
    },
    {
      "name": "HeytingLean.LoF.heyting_adjunction",
      "kind": "lemma",
      "line": 51,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "lemma heyting_adjunction (a b c : R.Omega) :\n    a \u2293 b \u2264 c \u2194 a \u2264 b \u21e8 c :=\n  (le_himp_iff (a := a) (b := b) (c := c)).symm\n\n/-- Residuation restated in terms of the fixed-point Heyting structure. -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 197,
        "name_depth": 2
      },
      "pos": {
        "x": 0.43289473910519777,
        "y": 0.207933812510927
      },
      "pos3": {
        "x": 0.14579713899498412,
        "y": 0.020763755540515082,
        "z": 0.6281806495771695
      }
    },
    {
      "name": "HeytingLean.LoF.residuation",
      "kind": "lemma",
      "line": 56,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "lemma residuation (a b c : R.Omega) :\n    c \u2264 a \u21e8 b \u2194 c \u2293 a \u2264 b :=\n  (heyting_adjunction (R := R) c a b).symm\n\n/-! #### Residuation simp helpers -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 147,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6376238093088893,
        "y": 0.2413479900399052
      },
      "pos3": {
        "x": 0.2297503287920963,
        "y": 0.13851743934992883,
        "z": 0.5425847134296194
      }
    },
    {
      "name": "HeytingLean.LoF.double_neg",
      "kind": "lemma",
      "line": 109,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "lemma double_neg (a : R.Omega) :\n    a \u2264 ((a \u21e8 (\u22a5 : R.Omega)) \u21e8 (\u22a5 : R.Omega)) := by\n  have h\u2081 : (a \u21e8 (\u22a5 : R.Omega)) \u2264 a \u21e8 (\u22a5 : R.Omega) := le_rfl\n  have h\u2082 :\n      (a \u21e8 (\u22a5 : R.Omega)) \u2293 a \u2264 (\u22a5 : R.Omega) :=",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 2,
        "length": 207,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4190583118455872,
        "y": 0.335185785951961
      },
      "pos3": {
        "x": 0.16494107804848315,
        "y": 0.27951698868201774,
        "z": 0.6617299123255773
      }
    },
    {
      "name": "HeytingLean.LoF.inf_himp_le",
      "kind": "lemma",
      "line": 126,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "lemma inf_himp_le (a b : R.Omega) : a \u2293 (a \u21e8 b) \u2264 b := by\n  -- Using `inf_le_iff_le_himp` with `t := a \u21e8 b`, `u := a`, `v := b`.\n  have : (a \u21e8 b) \u2264 a \u21e8 b := le_rfl\n  -- Convert to `(a \u21e8 b) \u2293 a \u2264 b` then swap by commutativity of inf.\n  have h := (inf_le_iff_le_himp (R := R)",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 7,
        "tactics": 2,
        "length": 273,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6988364140720291,
        "y": 0.3860343035297411
      },
      "pos3": {
        "x": 0.12694138206026606,
        "y": 0.26353946163262465,
        "z": 0.5617888266338376
      }
    },
    {
      "name": "HeytingLean.LoF.booleanEquiv",
      "kind": "def",
      "line": 144,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "def booleanEquiv (h : \u2200 a : \u03b1, R a = a) : R.Omega \u2243 \u03b1 where\n  toFun := Subtype.val\n  invFun := fun a => Omega.mk (R := R) a (h a)\n  left_inv := by\n    intro a",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 1,
        "exists": 0,
        "eq": 6,
        "tactics": 1,
        "length": 158,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6913235132840855,
        "y": 0.3740339106703494
      },
      "pos3": {
        "x": 0.21897932072699286,
        "y": 0.16034531901690877,
        "z": 0.4935148873902685
      }
    },
    {
      "name": "HeytingLean.LoF.boolean_limit",
      "kind": "lemma",
      "line": 165,
      "path": "HeytingLean/LoF/HeytingCore.lean",
      "snippet": "lemma boolean_limit (h : \u2200 a : \u03b1, R a = a) (a : \u03b1) :\n    R ((booleanEquiv (R := R) h).symm a : R.Omega) = a := by\n  have hx : R a = a := h a\n  dsimp [booleanEquiv]\n  change R ((Omega.mk (R := R) a hx : R.Omega) : \u03b1) = a",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 1,
        "exists": 0,
        "eq": 8,
        "tactics": 1,
        "length": 219,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4034443065828459,
        "y": 0.3381165458080584
      },
      "pos3": {
        "x": 0.2985448069982684,
        "y": 0.29496341729183606,
        "z": 0.5314300251743512
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry",
      "kind": "structure",
      "line": 12,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "structure Reentry (\u03b1 : Type u) [PrimaryAlgebra \u03b1] where\n  nucleus : Nucleus \u03b1\n  primordial : \u03b1\n  counter : \u03b1\n  /-- Optional \u201csupport window\u201d used by some classical fragments. This",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 179,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6045131107079724,
        "y": 0.17899109912263855
      },
      "pos3": {
        "x": 0.1552727523106772,
        "y": 0.03630125876047972,
        "z": 0.4674092011094672
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.map_sup",
      "kind": "lemma",
      "line": 59,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma map_sup (R : Reentry \u03b1) (a b : \u03b1) :\n    R (a \u2294 b) = R ((R a) \u2294 (R b)) := by\n  classical\n  simpa [Reentry.coe_nucleus] using\n    (R.nucleus.toClosureOperator.closure_sup_closure (x := a) (y := b)).symm",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 206,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6800475569857629,
        "y": 0.2128885395739424
      },
      "pos3": {
        "x": 0.10142566864423659,
        "y": 0.17649261553717,
        "z": 0.6690344197789732
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.map_sup_le",
      "kind": "lemma",
      "line": 66,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma map_sup_le (R : Reentry \u03b1) (a b : \u03b1) :\n    R a \u2294 R b \u2264 R (a \u2294 b) := by\n  classical\n  exact R.nucleus.toClosureOperator.closure_sup_closure_le (x := a) (y := b)\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 166,
        "name_depth": 3
      },
      "pos": {
        "x": 0.633465652078763,
        "y": 0.2470295752007315
      },
      "pos3": {
        "x": 0.06606521533546784,
        "y": 0.12129792580270976,
        "z": 0.7893308871810297
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.map_himp_le",
      "kind": "lemma",
      "line": 72,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma map_himp_le (R : Reentry \u03b1) (a b : \u03b1) :\n    R (a \u21e8 b) \u2264 a \u21e8 R b := by\n  simpa [Reentry.coe_nucleus] using\n    R.nucleus.map_himp_le (x := a) (y := b)\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 156,
        "name_depth": 3
      },
      "pos": {
        "x": 0.736117111898762,
        "y": 0.301744778256324
      },
      "pos3": {
        "x": 0.06868253514334631,
        "y": 0.2716260039018384,
        "z": 0.857890620076124
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.Omega",
      "kind": "abbrev",
      "line": 109,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "abbrev Omega (R : Reentry \u03b1) : Type u := R.nucleus.toSublocale\n\n@[simp] lemma primordial_apply (R : Reentry \u03b1) :\n    R R.primordial = R.primordial :=\n  R.primordial_mem",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 168,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8627558821134582,
        "y": 0.19581671522532723
      },
      "pos3": {
        "x": 0.02125720496659603,
        "y": 0.17140139031069856,
        "z": 0.8006933334888843
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.primordial_le_of_fixed",
      "kind": "lemma",
      "line": 119,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma primordial_le_of_fixed (R : Reentry \u03b1) {x : \u03b1}\n    (hx_fix : R x = x) (hx_pos : \u22a5 < x) (hx_support : x \u2264 R.support) :\n    R.primordial \u2264 x :=\n  R.primordial_minimal hx_fix hx_pos hx_support\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 196,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7501758339150896,
        "y": 0.07319556415903941
      },
      "pos3": {
        "x": 0.06427104221113157,
        "y": 0.039693554617507495,
        "z": 0.8806542721742014
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.Omega.mk",
      "kind": "def",
      "line": 129,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "def mk (a : \u03b1) (h : R a = a) :\n    R.Omega := \u27e8a, \u27e8a, h\u27e9\u27e9\n\n@[simp] lemma coe_mk (a : \u03b1) (h : R a = a) :\n    ((Omega.mk (R := R) a h : R.Omega) : \u03b1) = a := rfl",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 1,
        "length": 158,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.37695557095103005
      },
      "pos3": {
        "x": 0.17131292799758532,
        "y": 0.24180130789353824,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process",
      "kind": "def",
      "line": 148,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "def process (R : Reentry \u03b1) : R.Omega :=\n  Omega.mk (R := R) R.primordial R.primordial_mem\n\n/-- The complementary fixed point capturing the counter-process. -/\ndef counterProcess (R : Reentry \u03b1) : R.Omega :=",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 207,
        "name_depth": 3
      },
      "pos": {
        "x": 0.68953343743459,
        "y": 0.21238484845980155
      },
      "pos3": {
        "x": 0.242249099329993,
        "y": 0.05712297430856331,
        "z": 0.629079244268647
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.counterProcess",
      "kind": "def",
      "line": 152,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "def counterProcess (R : Reentry \u03b1) : R.Omega :=\n  Omega.mk (R := R) R.counter R.counter_mem\n\n@[simp] lemma process_coe (R : Reentry \u03b1) :\n    ((R.process : R.Omega) : \u03b1) = R.primordial := rfl",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 1,
        "length": 190,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7826910634314518,
        "y": 0.16485178056489044
      },
      "pos3": {
        "x": 0.12931535472191324,
        "y": 0.22707358690597623,
        "z": 0.7401074004110025
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_inf_counter",
      "kind": "lemma",
      "line": 162,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_inf_counter (R : Reentry \u03b1) :\n    R.process \u2293 R.counterProcess = \u22a5 := by\n  have h_le : R.process \u2293 R.counterProcess \u2264 \u22a5 := by\n    change ((R.process \u2293 R.counterProcess : R.Omega) : \u03b1)\n        \u2264 ((\u22a5 : R.Omega) : \u03b1)",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 227,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8287532400225455,
        "y": 0.2845137090358877
      },
      "pos3": {
        "x": 0.21872275483795517,
        "y": 0.30200936418799046,
        "z": 0.8952495634097899
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_pos",
      "kind": "lemma",
      "line": 171,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_pos (R : Reentry \u03b1) : \u22a5 < ((R.process : R.Omega) : \u03b1) := by\n  change \u22a5 < R.primordial\n  exact R.primordial_nonbot\n\n/-- The primordial process lies inside the designated support window. -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 201,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8335879435891675,
        "y": 0.27920610165855325
      },
      "pos3": {
        "x": 0.029525361345587663,
        "y": 0.22078638463068062,
        "z": 0.7017907816184891
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_in_support",
      "kind": "lemma",
      "line": 176,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_in_support (R : Reentry \u03b1) :\n    ((R.process : R.Omega) : \u03b1) \u2264 R.support := by\n  -- This is just the `primordial_in_support` field transported to `\u03a9_R`.\n  simpa [process_coe] using R.primordial_in_support\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 219,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6001715688383832,
        "y": 0.11914681710140193
      },
      "pos3": {
        "x": 0.2585017609058373,
        "y": 0.07459690017608568,
        "z": 0.6570626725322435
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.counter_pos",
      "kind": "lemma",
      "line": 182,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma counter_pos (R : Reentry \u03b1) : \u22a5 < ((R.counterProcess : R.Omega) : \u03b1) := by\n  change \u22a5 < R.counter\n  exact R.counter_nonbot\n\n/-- Package the complementary fixed points generated by re-entry. -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 198,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6058430227157497,
        "y": 0.3985295848793851
      },
      "pos3": {
        "x": 0.13458406434993955,
        "y": 0.22656449195032125,
        "z": 0.6835635434000822
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.complementaryPair",
      "kind": "def",
      "line": 187,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "def complementaryPair (R : Reentry \u03b1) : R.Omega \u00d7 R.Omega :=\n  \u27e8R.process, R.counterProcess\u27e9\n\n@[simp] lemma complementaryPair_fst (R : Reentry \u03b1) :\n    (R.complementaryPair.fst : \u03b1) = R.primordial := rfl",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 203,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8636165633469554,
        "y": 0.3697996588083538
      },
      "pos3": {
        "x": 0.07494193436463015,
        "y": 0.3769796797828039,
        "z": 0.7329392235160371
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.boundaryCandidates",
      "kind": "def",
      "line": 202,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "def boundaryCandidates (R : Reentry \u03b1) : Set (R.Omega) :=\n  {x | \u22a5 < (x : \u03b1) \u2227 (x : \u03b1) \u2264 R.support}\n\n@[simp] lemma mem_boundaryCandidates (R : Reentry \u03b1) (x : R.Omega) :\n    x \u2208 R.boundaryCandidates \u2194",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 200,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6922542376207985,
        "y": 0.13737754994825627
      },
      "pos3": {
        "x": 0.25840473142854914,
        "y": 0.26509759373495445,
        "z": 0.6151764988574645
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_mem_boundaryCandidates",
      "kind": "lemma",
      "line": 210,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_mem_boundaryCandidates (R : Reentry \u03b1) :\n    R.process \u2208 R.boundaryCandidates := by\n  constructor\n  \u00b7 -- positivity\n    simpa [process_coe, boundaryCandidates] using R.process_pos",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 193,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8634028797612122,
        "y": 0.3033848335893982
      },
      "pos3": {
        "x": 0.299784740523818,
        "y": 0.25080827552398555,
        "z": 0.8906988771854254
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary",
      "kind": "def",
      "line": 221,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "noncomputable def eulerBoundary (R : Reentry \u03b1) : R.Omega :=\n  sInf (R.boundaryCandidates)\n\nlemma eulerBoundary_def (R : Reentry \u03b1) :\n    R.eulerBoundary = sInf (R.boundaryCandidates) := rfl",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 190,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6256960356203637,
        "y": 0.1647971389949841
      },
      "pos3": {
        "x": 0.2779100949024383,
        "y": 0.2546087203242916,
        "z": 0.6498933331811743
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_def",
      "kind": "lemma",
      "line": 224,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_def (R : Reentry \u03b1) :\n    R.eulerBoundary = sInf (R.boundaryCandidates) := rfl\n\n/-- Any boundary candidate dominates the Euler boundary. -/\nlemma eulerBoundary_le_of_candidate (R : Reentry \u03b1) {x : R.Omega}",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 225,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6207637555405152,
        "y": 0.25068064957716946
      },
      "pos3": {
        "x": 0.14569233763521552,
        "y": 0.0641241897597545,
        "z": 0.7203120877648359
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_le_of_candidate",
      "kind": "lemma",
      "line": 228,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_le_of_candidate (R : Reentry \u03b1) {x : R.Omega}\n    (hx : x \u2208 R.boundaryCandidates) : R.eulerBoundary \u2264 x := by\n  simpa [eulerBoundary_def] using sInf_le (a := x) hx\n\n/-- A lower bound of boundary candidates lies below the Euler boundary. -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 259,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8297503287920964,
        "y": 0.06441743934992884
      },
      "pos3": {
        "x": 0.017590619991653678,
        "y": 0.11369193569307483,
        "z": 0.8955926531339178
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.le_of_lower_bound",
      "kind": "lemma",
      "line": 233,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma le_of_lower_bound (R : Reentry \u03b1) {a : R.Omega}\n    (h : \u2200 \u2983x\u2984, x \u2208 R.boundaryCandidates \u2192 a \u2264 x) :\n    a \u2264 R.eulerBoundary := by\n  classical\n  refine le_sInf ?_",
      "family": "LoF",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 167,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8425847134296195,
        "y": 0.18164107804848315
      },
      "pos3": {
        "x": 0.1795609174516456,
        "y": 0.2352211805845708,
        "z": 0.7365025102017431
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_le_process",
      "kind": "lemma",
      "line": 242,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_le_process (R : Reentry \u03b1) :\n    R.eulerBoundary \u2264 R.process :=\n  eulerBoundary_le_of_candidate (R := R) (x := R.process)\n    (R.process_mem_boundaryCandidates)\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 181,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6795169886820178,
        "y": 0.27982991232557725
      },
      "pos3": {
        "x": 0.12690224579704887,
        "y": 0.28719529225790197,
        "z": 0.8986268068478143
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_le_of_candidate",
      "kind": "lemma",
      "line": 248,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_le_of_candidate (R : Reentry \u03b1) {x : R.Omega}\n    (hx : x \u2208 R.boundaryCandidates) :\n    R.process \u2264 x := by\n  -- Unpack the candidate conditions.\n  rcases hx with \u27e8hx_pos, hx_sup\u27e9",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 193,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7269413820602662,
        "y": 0.08283946163262461
      },
      "pos3": {
        "x": 0.16673049702168546,
        "y": 0.2155224825888978,
        "z": 0.6464390475822194
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.process_le_eulerBoundary",
      "kind": "lemma",
      "line": 259,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma process_le_eulerBoundary (R : Reentry \u03b1) :\n    R.process \u2264 R.eulerBoundary := by\n  refine R.le_of_lower_bound ?_\n  intro x hx\n  exact process_le_of_candidate (R := R) hx",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 2,
        "length": 175,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7617888266338376,
        "y": 0.4364793207269929
      },
      "pos3": {
        "x": 0.08901234764836925,
        "y": 0.49061280949074765,
        "z": 0.7737540872448769
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_pos",
      "kind": "lemma",
      "line": 276,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_pos (R : Reentry \u03b1) :\n    \u22a5 < ((R.eulerBoundary : R.Omega) : \u03b1) := by\n  simpa [eulerBoundary_eq_process] using (process_pos (R := R))\n\n/-- Consequently, the Euler boundary belongs to the candidate set. -/",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 224,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6603453190169088,
        "y": 0.11591488739026849
      },
      "pos3": {
        "x": 0.16265856041228227,
        "y": 0.22439266811371922,
        "z": 0.617149581872245
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_mem_candidates",
      "kind": "lemma",
      "line": 281,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_mem_candidates (R : Reentry \u03b1) :\n    R.eulerBoundary \u2208 R.boundaryCandidates := by\n  -- Positivity and support membership for `eulerBoundary` follow from the\n  -- corresponding properties of `process` together with\n  -- `eulerBoundary_le_process`.",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 266,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8985448069982684,
        "y": 0.22156341729183607
      },
      "pos3": {
        "x": 0.17525327833769136,
        "y": 0.15085511487585407,
        "z": 0.8558159676144856
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_isLeast",
      "kind": "lemma",
      "line": 303,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_isLeast (R : Reentry \u03b1) :\n    IsLeast (R.boundaryCandidates) (R.eulerBoundary) := by\n  refine \u27e8R.eulerBoundary_mem_candidates, ?_\u27e9\n  intro x hx\n  exact R.eulerBoundary_le_of_candidate hx",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 2,
        "length": 206,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7314300251743513,
        "y": 0.3758727523106772
      },
      "pos3": {
        "x": 0.04722981838184498,
        "y": 0.4882336709823351,
        "z": 0.6240334395721762
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_in_support",
      "kind": "lemma",
      "line": 310,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_in_support (R : Reentry \u03b1) :\n    ((R.eulerBoundary : R.Omega) : \u03b1) \u2264 R.support := by\n  -- Unpack the support component from membership in `boundaryCandidates`.\n  have h :=\n    (R.mem_boundaryCandidates (x := R.eulerBoundary)).1",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 247,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6363012587604798,
        "y": 0.19210920110946722
      },
      "pos3": {
        "x": 0.05574748829421696,
        "y": 0.2785105319350083,
        "z": 0.8025637660812271
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_minimal_nontrivial",
      "kind": "lemma",
      "line": 322,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_minimal_nontrivial (R : Reentry \u03b1) :\n    \u22a5 < ((R.eulerBoundary : R.Omega) : \u03b1) \u2227\n    R (((R.eulerBoundary : R.Omega) : \u03b1)) =\n      ((R.eulerBoundary : R.Omega) : \u03b1) \u2227\n    \u2200 {y : R.Omega},",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 1,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 207,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7014256686442367,
        "y": 0.19719261553717
      },
      "pos3": {
        "x": 0.07056116850027935,
        "y": 0.035965984184137254,
        "z": 0.8670861942388313
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_le_counter",
      "kind": "lemma",
      "line": 347,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_le_counter (R : Reentry \u03b1)\n    (hcounter_sup : (R.counter : \u03b1) \u2264 R.support) :\n    R.eulerBoundary \u2264 R.counterProcess := by\n  -- First show that the counter-process is itself a boundary candidate.\n  have hcand : R.counterProcess \u2208 R.boundaryCandidates := by",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 276,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6690344197789732,
        "y": 0.19366521533546788
      },
      "pos3": {
        "x": 0.07386460433658745,
        "y": 0.2783557460600323,
        "z": 0.785814453099631
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_complementary",
      "kind": "lemma",
      "line": 366,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_complementary (R : Reentry \u03b1) :\n    R.eulerBoundary \u2293 R.counterProcess = \u22a5 := by\n  calc\n    R.eulerBoundary \u2293 R.counterProcess\n        = R.process \u2293 R.counterProcess := by",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 191,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6212979258027098,
        "y": 0.20843088718102967
      },
      "pos3": {
        "x": 0.12576747460076174,
        "y": 0.1751016867873674,
        "z": 0.7568348146595878
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_unique_minimal",
      "kind": "lemma",
      "line": 378,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_unique_minimal (R : Reentry \u03b1) (x : R.Omega)\n    (hx_nontrivial : \u22a5 < (x : \u03b1))\n    (hx_support : (x : \u03b1) \u2264 R.support)\n    (hx_min : \u2200 y : R.Omega, \u22a5 < (y : \u03b1) \u2192 (x : \u03b1) \u2264 (y : \u03b1)) :\n    x = R.eulerBoundary := by",
      "family": "LoF",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 231,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7686825351433464,
        "y": 0.2947260039018384
      },
      "pos3": {
        "x": 0.3804118773209282,
        "y": 0.06127775982706093,
        "z": 0.8148575402368246
      }
    },
    {
      "name": "HeytingLean.LoF.Reentry.eulerBoundary_unique_minimal_support",
      "kind": "lemma",
      "line": 407,
      "path": "HeytingLean/LoF/Nucleus.lean",
      "snippet": "lemma eulerBoundary_unique_minimal_support (R : Reentry \u03b1) (x : R.Omega)\n    (hx_nontrivial : \u22a5 < (x : \u03b1))\n    (hx_support : (x : \u03b1) \u2264 R.support)\n    (hx_min :\n      \u2200 y : R.Omega, \u22a5 < (y : \u03b1) \u2192 (y : \u03b1) \u2264 R.support \u2192",
      "family": "LoF",
      "features": {
        "implies": 2,
        "forall": 1,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 216,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.042857204966596035
      },
      "pos3": {
        "x": 0.2716057857847538,
        "y": 0.11873575403737635,
        "z": 0.8015070668879914
      }
    },
    {
      "name": "HeytingLean.LoF.PrimaryAlgebra",
      "kind": "class",
      "line": 10,
      "path": "HeytingLean/LoF/PrimaryAlgebra.lean",
      "snippet": "class PrimaryAlgebra (\u03b1 : Type u) extends Order.Frame \u03b1\n\nend LoF\nend HeytingLean\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 81,
        "name_depth": 2
      },
      "pos": {
        "x": 0.4714013903106986,
        "y": 0.20879333348888415
      },
      "pos3": {
        "x": 0.08999912393962867,
        "y": 0.09485315888155621,
        "z": 0.6255593477243206
      }
    },
    {
      "name": "HeytingLean.LoF.BoundaryHeyting.boundary",
      "kind": "def",
      "line": 33,
      "path": "HeytingLean/LoF/BoundaryHeyting.lean",
      "snippet": "noncomputable def boundary (R : Reentry \u03b1) : R.Omega :=\n  R.eulerBoundary\n\n@[simp] theorem boundary_def (R : Reentry \u03b1) : boundary (R := R) = R.eulerBoundary := rfl\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 1,
        "length": 165,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6642710422111316,
        "y": 0.1561935546175075
      },
      "pos3": {
        "x": 0.021762934347947193,
        "y": 0.23748565678557584,
        "z": 0.8995363322563328
      }
    },
    {
      "name": "HeytingLean.LoF.BoundaryHeyting.boundary_isLeast",
      "kind": "theorem",
      "line": 39,
      "path": "HeytingLean/LoF/BoundaryHeyting.lean",
      "snippet": "theorem boundary_isLeast (R : Reentry \u03b1) : IsLeast (R.boundaryCandidates) (boundary (R := R)) := by\n  simpa [boundary] using R.eulerBoundary_isLeast\n\n/-- The Heyting structure on `\u03a9_R` (fixed points) is canonical. -/\ninstance (R : Reentry \u03b1) : HeytingAlgebra (R.Omega) := inferInstance",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 285,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8806542721742014,
        "y": 0.19981292799758532
      },
      "pos3": {
        "x": 0.2988289343565283,
        "y": 0.0219782163298899,
        "z": 0.6639462936801122
      }
    },
    {
      "name": "HeytingLean.LoF.BoundaryHeyting.boundary_modusPonens",
      "kind": "theorem",
      "line": 46,
      "path": "HeytingLean/LoF/BoundaryHeyting.lean",
      "snippet": "theorem boundary_modusPonens (R : Reentry \u03b1) (a b : R.Omega) : a \u2293 (a \u21e8 b) \u2264 b := by\n  exact Reentry.inf_himp_le (R := R) a b\n\nend BoundaryHeyting\n",
      "family": "LoF",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 147,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7418013078935384,
        "y": 0.35008582728722604
      },
      "pos3": {
        "x": 0.07956012442512041,
        "y": 0.37997781339811276,
        "z": 0.864259252105932
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.update",
      "kind": "def",
      "line": 29,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "def update (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) : Var \u2192 Comb :=\n  fun y => if y = x then v else \u03c1 y\n\n/-! ## `Comb.Steps` helpers -/\n",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 133,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.07042297430856331
      },
      "pos3": {
        "x": 0.46378107274536284,
        "y": 0.11085812662166518,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.steps_transitive",
      "kind": "theorem",
      "line": 34,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "private theorem steps_transitive {t u v : Comb} :\n    Comb.Steps t u \u2192 Comb.Steps u v \u2192 Comb.Steps t v := by\n  intro htu huv\n  induction htu with\n  | refl _ => simpa using huv",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 175,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.24681535472191324
      },
      "pos3": {
        "x": 0.4501234863919421,
        "y": 0.3110619775262113,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.steps_app_left",
      "kind": "theorem",
      "line": 41,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "private theorem steps_app_left {f f' a : Comb} :\n    Comb.Steps f f' \u2192 Comb.Steps (Comb.app f a) (Comb.app f' a) := by\n  intro h\n  induction h with\n  | refl t => exact Comb.Steps.refl (Comb.app t a)",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 2,
        "length": 198,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.3599074004110025
      },
      "pos3": {
        "x": 0.3961699190894513,
        "y": 0.3961928953132198,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.steps_app_right",
      "kind": "theorem",
      "line": 49,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "private theorem steps_app_right {f a a' : Comb} :\n    Comb.Steps a a' \u2192 Comb.Steps (Comb.app f a) (Comb.app f a') := by\n  intro h\n  induction h with\n  | refl t => exact Comb.Steps.refl (Comb.app f t)",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 2,
        "length": 199,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.42190936418799047
      },
      "pos3": {
        "x": 0.3451312405346385,
        "y": 0.28981362565999336,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.bracket_eq_appK_of_occurs_false",
      "kind": "theorem",
      "line": 59,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem bracket_eq_appK_of_occurs_false (x : Var) :\n    \u2200 e : CExp Var, occurs x e = false \u2192 bracket x e = CExp.app CExp.K e := by\n  intro e\n  induction e with\n  | var y =>",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 4,
        "tactics": 1,
        "length": 172,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.14672536134558767
      },
      "pos3": {
        "x": 0.38167900117813114,
        "y": 0.14028733431801033,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote_update_eq_of_occurs_false",
      "kind": "theorem",
      "line": 84,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem denote_update_eq_of_occurs_false (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) :\n    \u2200 e : CExp Var, occurs x e = false \u2192 denote (update \u03c1 x v) e = denote \u03c1 e := by\n  intro e\n  induction e with\n  | var y =>",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 1,
        "exists": 0,
        "eq": 4,
        "tactics": 1,
        "length": 206,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.22239078161848896
      },
      "pos3": {
        "x": 0.2321107933128253,
        "y": 0.2659670922654448,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.bracket_beta_join_of_occurs_false",
      "kind": "theorem",
      "line": 111,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem bracket_beta_join_of_occurs_false (\u03c1 : Var \u2192 Comb) (x : Var) (e : CExp Var) (v : Comb)\n    (hocc : occurs x e = false) :\n    \u2203 r : Comb, Comb.Steps (Comb.app (denote \u03c1 (bracket x e)) v) r \u2227\n      Comb.Steps (denote (update \u03c1 x v) e) r := by\n  refine \u27e8denote \u03c1 e, ?_, ?_\u27e9",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 1,
        "eq": 2,
        "tactics": 0,
        "length": 278,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.10239690017608569
      },
      "pos3": {
        "x": 0.2814489481090672,
        "y": 0.21528365614163938,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote_update_steps_of_bracket_eq_appK",
      "kind": "theorem",
      "line": 127,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem denote_update_steps_of_bracket_eq_appK (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) :\n    \u2200 e t : CExp Var,\n      bracket x e = CExp.app CExp.K t \u2192 Comb.Steps (denote (update \u03c1 x v) e) (denote \u03c1 t) := by\n  intro e\n  induction e with",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 1,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 233,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.25788406434993955
      },
      "pos3": {
        "x": 0.39027138766552394,
        "y": 0.1791951704891228,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote_update_steps_of_bracket_eq_IK",
      "kind": "theorem",
      "line": 337,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem denote_update_steps_of_bracket_eq_IK (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) :\n    \u2200 e : CExp Var,\n      (bracket x e = I \u2192 Comb.Steps (denote (update \u03c1 x v) e) v) \u2227\n      (bracket x e = CExp.K \u2192 Comb.Steps (denote (update \u03c1 x v) e) (Comb.app Comb.K v)) := by\n  intro e",
      "family": "Combinator",
      "features": {
        "implies": 3,
        "forall": 1,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 275,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.21106354340008215
      },
      "pos3": {
        "x": 0.5716009473237971,
        "y": 0.3538311139884567,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote_update_steps_of_bracket_eq_I",
      "kind": "theorem",
      "line": 847,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem denote_update_steps_of_bracket_eq_I (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) :\n    \u2200 e : CExp Var, bracket x e = I \u2192 Comb.Steps (denote (update \u03c1 x v) e) v := by\n  intro e hI\n  exact (denote_update_steps_of_bracket_eq_IK (\u03c1 := \u03c1) (x := x) (v := v) e).1 hI\n",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 1,
        "exists": 0,
        "eq": 5,
        "tactics": 2,
        "length": 261,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.5030796797828039
      },
      "pos3": {
        "x": 0.3270727317691179,
        "y": 0.2830040671916755,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote_update_steps_of_bracket_eq_K",
      "kind": "theorem",
      "line": 853,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem denote_update_steps_of_bracket_eq_K (\u03c1 : Var \u2192 Comb) (x : Var) (v : Comb) :\n    \u2200 e : CExp Var, bracket x e = CExp.K \u2192 Comb.Steps (denote (update \u03c1 x v) e) (Comb.app Comb.K v) := by\n  intro e hK\n  exact (denote_update_steps_of_bracket_eq_IK (\u03c1 := \u03c1) (x := x) (v := v) e).2 hK\n",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 1,
        "exists": 0,
        "eq": 5,
        "tactics": 2,
        "length": 284,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.4868047314285492
      },
      "pos3": {
        "x": 0.43133576690588815,
        "y": 0.39113401319041385,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.bracket_beta_join",
      "kind": "theorem",
      "line": 861,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem bracket_beta_join (\u03c1 : Var \u2192 Comb) (x : Var) :\n    \u2200 e : CExp Var, \u2200 v : Comb,\n      \u2203 r : Comb, Comb.Steps (Comb.app (denote \u03c1 (bracket x e)) v) r \u2227\n        Comb.Steps (denote (update \u03c1 x v) e) r := by\n  intro e",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 2,
        "exists": 1,
        "eq": 1,
        "tactics": 1,
        "length": 220,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.13717649885746439
      },
      "pos3": {
        "x": 0.32236927250437925,
        "y": 0.26550412633791737,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.bracket_sound",
      "kind": "theorem",
      "line": 1068,
      "path": "HeytingLean/LoF/Combinators/BracketAbstractionCorrectness.lean",
      "snippet": "theorem bracket_sound (\u03c1 : Var \u2192 Comb) (x : Var) (e : CExp Var) (v : Comb) :\n    \u2203 r : Comb, Comb.Steps (Comb.app (denote \u03c1 (bracket x e)) v) r \u2227\n      Comb.Steps (denote (update \u03c1 x v) e) r := by\n  simpa using (bracket_beta_join (\u03c1 := \u03c1) (x := x) (e := e) (v := v))\n",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 1,
        "eq": 5,
        "tactics": 0,
        "length": 267,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.27750827552398555
      },
      "pos3": {
        "x": 0.102900909882502,
        "y": 0.022573158022130113,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.SKYModel",
      "kind": "structure",
      "line": 36,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "structure SKYModel (\u03b1 : Type u) where\n  app : \u03b1 \u2192 \u03b1 \u2192 \u03b1\n  K : \u03b1\n  S : \u03b1\n  Y : \u03b1",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 79,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.2858100949024383
      },
      "pos3": {
        "x": 0.47117857146796793,
        "y": 0.16367708676165668,
        "z": 0.8503785059658051
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.SKYModel.denote",
      "kind": "def",
      "line": 49,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "def denote (M : SKYModel \u03b1) : Comb \u2192 \u03b1\n  | .K => M.K\n  | .S => M.S\n  | .Y => M.Y\n  | .app f a => M.app (denote M f) (denote M a)",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 128,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.0626933331811742
      },
      "pos3": {
        "x": 0.2747528699469382,
        "y": 0.04442813567024479,
        "z": 0.8382336557846417
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.SKYModel.denote_step",
      "kind": "theorem",
      "line": 61,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "theorem denote_step (M : SKYModel \u03b1) {t u : Comb} (h : Comb.Step t u) :\n    denote M t = denote M u := by\n  induction h with\n  | K_rule x y =>\n      simp [denote]",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 162,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9456923376352155,
        "y": 0.1803241897597545
      },
      "pos3": {
        "x": 0.0924775049790401,
        "y": 0.36969444662277695,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.SKYModel.denote_steps",
      "kind": "theorem",
      "line": 78,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "theorem denote_steps (M : SKYModel \u03b1) {t u : Comb} (h : Comb.Steps t u) :\n    denote M t = denote M u := by\n  induction h with\n  | refl t => rfl\n  | trans hstep _ ih =>",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 168,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9203120877648359,
        "y": 0.03439061999165368
      },
      "pos3": {
        "x": 0.2582107746002708,
        "y": 0.26967739095794235,
        "z": 0.8630229615019263
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.ScottSKYModel",
      "kind": "structure",
      "line": 91,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "structure ScottSKYModel (\u03b1 : Type u) [OmegaCompletePartialOrder \u03b1] [OrderBot \u03b1] where\n  D : ReflexiveDomain (\u03b1 := \u03b1)\n  K : \u03b1\n  S : \u03b1\n  Y : \u03b1",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 140,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7136919356930749,
        "y": 0.30959265313391776
      },
      "pos3": {
        "x": 0.07485892176687732,
        "y": 0.03083808650153569,
        "z": 0.8340348725614328
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.ScottSKYModel.toSKYModel",
      "kind": "def",
      "line": 104,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "def toSKYModel (M : ScottSKYModel \u03b1) : SKYModel \u03b1 where\n  app := fun f x => M.D.app f x\n  K := M.K\n  S := M.S\n  Y := M.Y",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 120,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8795609174516457,
        "y": 0.24722118058457082
      },
      "pos3": {
        "x": 0.26524041043530266,
        "y": 0.12191321694963503,
        "z": 0.9861984530452139
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.ScottSKYModel.denote_steps_sound",
      "kind": "theorem",
      "line": 113,
      "path": "HeytingLean/LoF/Combinators/Denotational.lean",
      "snippet": "theorem denote_steps_sound (M : ScottSKYModel \u03b1) {t u : Comb} (h : Comb.Steps t u) :\n    SKYModel.denote (M.toSKYModel) t = SKYModel.denote (M.toSKYModel) u :=\n  SKYModel.denote_steps (M := M.toSKYModel) h\n\nend ScottSKYModel",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 224,
        "name_depth": 4
      },
      "pos": {
        "x": 0.936502510201743,
        "y": 0.14930224579704887
      },
      "pos3": {
        "x": 0.04636600149966139,
        "y": 0.2789643047081023,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp",
      "kind": "inductive",
      "line": 26,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "inductive CExp (Var : Type) where\n  | var (v : Var)\n  | K\n  | S\n  | Y",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 69,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.30552680684781414
      },
      "pos3": {
        "x": 0.29286180987928884,
        "y": 0.24323151598211906,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.I",
      "kind": "def",
      "line": 38,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def I : CExp Var :=\n  .app (.app .S .K) .K\n\ndef occurs [DecidableEq Var] (x : Var) : CExp Var \u2192 Bool\n  | .var v => decide (v = x)",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 129,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.2284224825888978
      },
      "pos3": {
        "x": 0.10743590856945662,
        "y": 0.22096934152652462,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.occurs",
      "kind": "def",
      "line": 41,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def occurs [DecidableEq Var] (x : Var) : CExp Var \u2192 Bool\n  | .var v => decide (v = x)\n  | .K => false\n  | .S => false\n  | .Y => false",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 133,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.10231234764836926
      },
      "pos3": {
        "x": 0.3792447658144976,
        "y": 0.24067054168114166,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.opt",
      "kind": "def",
      "line": 48,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def opt [DecidableEq Var] : CExp Var \u2192 CExp Var\n  | .app (.app .S (.app .K e)) (.app .K f) => .app .K (.app e f)\n  | .app (.app .S (.app .K e)) a =>\n      if a = I then e else .app (.app .S (.app .K e)) a\n  | e => e",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 215,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.19525408724487686
      },
      "pos3": {
        "x": 0.3432247949723167,
        "y": 0.08004171287834161,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.bracket",
      "kind": "def",
      "line": 54,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def bracket [DecidableEq Var] (x : Var) : CExp Var \u2192 CExp Var\n  | .var v =>\n      if v = x then I else .app .K (.var v)\n  | .K => .app .K .K\n  | .S => .app .K .S",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 161,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.24049266811371922
      },
      "pos3": {
        "x": 0.13242868792088713,
        "y": 0.2616500348718269,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.denote",
      "kind": "def",
      "line": 66,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def denote (\u03c1 : Var \u2192 Comb) : CExp Var \u2192 Comb\n  | .var v => \u03c1 v\n  | .K => .K\n  | .S => .S\n  | .Y => .Y",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 102,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.18545327833769137
      },
      "pos3": {
        "x": 0.26673011526369933,
        "y": 0.2449759816790787,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.erase",
      "kind": "def",
      "line": 73,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def erase : CExp PEmpty \u2192 Comb\n  | .var v => nomatch v\n  | .K => .K\n  | .S => .S\n  | .Y => .Y",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 93,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.2651159676144856
      },
      "pos3": {
        "x": 0.19155726020158018,
        "y": 0.23860364974585851,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.CExp.erase?",
      "kind": "def",
      "line": 90,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def erase? : CExp Var \u2192 Option Comb\n  | .var _ => none\n  | .K => some .K\n  | .S => some .S\n  | .Y => some .Y",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 108,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.2990336709823351
      },
      "pos3": {
        "x": 0.10709933041043546,
        "y": 0.057938936498312596,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.Lam",
      "kind": "inductive",
      "line": 104,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "inductive Lam (Var : Type) where\n  | var (v : Var)\n  | app (f a : Lam Var)\n  | lam (x : Var) (body : Lam Var)\n  | K",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 115,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8240334395721761,
        "y": 0.06724748829421696
      },
      "pos3": {
        "x": 0.2593058826090859,
        "y": 0.2900667312145083,
        "z": 0.8837374978165615
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.Lam.compile",
      "kind": "def",
      "line": 117,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def compile : Lam Var \u2192 CExp Var\n  | .var v => .var v\n  | .app f a => .app (compile f) (compile a)\n  | .lam x body => CExp.bracket x (compile body)\n  | .K => .K",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 160,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.21856376608122702
      },
      "pos3": {
        "x": 0.2924445215822883,
        "y": 0.11990351530801825,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Bracket.Lam.compileClosed?",
      "kind": "def",
      "line": 125,
      "path": "HeytingLean/LoF/Combinators/BracketAbstraction.lean",
      "snippet": "def compileClosed? (t : Lam Var) : Option Comb :=\n  (compile t).erase?\n\nend Lam\n",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 80,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.043965984184137254
      },
      "pos3": {
        "x": 0.16086471974361657,
        "y": 0.2817711420974147,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Comb",
      "kind": "inductive",
      "line": 16,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "inductive Comb where\n  | K\n  | S\n  | Y\n  | app (f a : Comb)",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 59,
        "name_depth": 2
      },
      "pos": {
        "x": 0.6670861942388313,
        "y": 0.07976460433658746
      },
      "pos3": {
        "x": 0.2911201833066684,
        "y": 0.053570344851739095,
        "z": 0.6887602947284667
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Step",
      "kind": "inductive",
      "line": 27,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "inductive Step : Comb -> Comb -> Prop where\n  | K_rule (x y : Comb) :\n      Step (Comb.app (Comb.app .K x) y) x\n  | S_rule (x y z : Comb) :\n      Step (Comb.app (Comb.app (Comb.app .S x) y) z)",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 192,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9783557460600324,
        "y": 0.20501445309963093
      },
      "pos3": {
        "x": 0.2796399087568906,
        "y": 0.03252076416441333,
        "z": 0.7303691275693934
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Steps",
      "kind": "inductive",
      "line": 41,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "inductive Steps : Comb -> Comb -> Prop where\n  | refl (t : Comb) : Steps t t\n  | trans {t u v} : Step t u -> Steps u v -> Steps t v\n\n/-- Promote definitional equality of terms to the multi-step relation. -/",
      "family": "Combinator",
      "features": {
        "implies": 4,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 206,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.1957016867873674
      },
      "pos3": {
        "x": 0.6185635181958113,
        "y": 0.09410319425849736,
        "z": 0.7818626559918431
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Steps.of_eq",
      "kind": "theorem",
      "line": 46,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem Steps.of_eq {t u : Comb} (h : t = u) : Steps t u := by\n  subst h\n  exact Steps.refl _\n\n/-- A term is in normal form if it admits no `Step` successors. -/",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 161,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9568348146595878,
        "y": 0.3965118773209282
      },
      "pos3": {
        "x": 0.15342691790084342,
        "y": 0.21555863000341816,
        "z": 0.9729764130489799
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Normal",
      "kind": "def",
      "line": 51,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "def Normal (t : Comb) : Prop :=\n  \u2200 u : Comb, \u00ac Step t u\n\n/-- The combinator `K` is in normal form. -/\ntheorem K_normal : Normal Comb.K := by",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 1,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 141,
        "name_depth": 3
      },
      "pos": {
        "x": 0.661277759827061,
        "y": 0.22895754023682444
      },
      "pos3": {
        "x": 0.07641675184157458,
        "y": 0.2126355851502512,
        "z": 0.600507383465589
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.K_normal",
      "kind": "theorem",
      "line": 55,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem K_normal : Normal Comb.K := by\n  intro u h\n  cases h\n\n/-- The combinator `S` is in normal form. -/",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 2,
        "length": 106,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6716057857847539,
        "y": 0.32933575403737636
      },
      "pos3": {
        "x": 0.2776725496497248,
        "y": 0.3615355991278376,
        "z": 0.8158289997434538
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.S_normal",
      "kind": "theorem",
      "line": 60,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem S_normal : Normal Comb.S := by\n  intro u h\n  cases h\n\n/-- The combinator `Y` is in normal form. -/",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 2,
        "length": 106,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8015070668879914,
        "y": 0.3005991239396287
      },
      "pos3": {
        "x": 0.22258502335184296,
        "y": 0.40118855132989983,
        "z": 0.7092664415343793
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Y_normal",
      "kind": "theorem",
      "line": 65,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem Y_normal : Normal Comb.Y := by\n  intro u h\n  cases h\n\n/-- The combinator `K \u00b7 S` is in normal form. -/",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 2,
        "length": 110,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6948531588815563,
        "y": 0.43655934772432065
      },
      "pos3": {
        "x": 0.020992143337893055,
        "y": 0.39927130547338174,
        "z": 0.699060010812779
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.K_app_S_normal",
      "kind": "theorem",
      "line": 70,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem K_app_S_normal : Normal (Comb.app Comb.K Comb.S) := by\n  intro u h\n  cases h with\n  | app_left h' =>\n      -- The function part would need to step, but `K` is normal.",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 2,
        "length": 174,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6217629343479473,
        "y": 0.3548856567855758
      },
      "pos3": {
        "x": 0.0941746935175079,
        "y": 0.45440458385190063,
        "z": 0.8159262789041851
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.I",
      "kind": "def",
      "line": 83,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "def I : Comb := Comb.app (Comb.app .S .K) .K\n\n/-- One-step reduction from `I` applied to `t` to\n`(K` applied to `t)` applied again to `K` and `t`. -/\ntheorem I_step (t : Comb) :",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 177,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8995363322563328,
        "y": 0.3165289343565283
      },
      "pos3": {
        "x": 0.09009668046337925,
        "y": 0.09278539866259597,
        "z": 0.7225178725857652
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.I_step",
      "kind": "theorem",
      "line": 87,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem I_step (t : Comb) :\n  Step (Comb.app I t) (Comb.app (Comb.app .K t) (Comb.app .K t)) := by\n  -- This is an instance of the S-rule with `x = K`, `y = K`, `z = t`.\n  simpa [I] using\n    Step.S_rule (x := .K) (y := .K) (z := t)",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 7,
        "tactics": 0,
        "length": 232,
        "name_depth": 3
      },
      "pos": {
        "x": 0.62197821632989,
        "y": 0.08714629368011212
      },
      "pos3": {
        "x": 0.12072011611731738,
        "y": 0.08869656075778411,
        "z": 0.6381863397177461
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.K_app_app_step",
      "kind": "theorem",
      "line": 94,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem K_app_app_step (t : Comb) :\n  Step (Comb.app (Comb.app .K t) (Comb.app .K t)) t := by\n  -- Apply the K-rule with arguments `t` and `K \u00b7 t`.\n  simpa using Step.K_rule (x := t) (y := Comb.app .K t)\n",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 204,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6795601244251205,
        "y": 0.30037781339811276
      },
      "pos3": {
        "x": 0.12613390013187248,
        "y": 0.2821091012190549,
        "z": 0.80319538358182
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.I_reduces",
      "kind": "theorem",
      "line": 101,
      "path": "HeytingLean/LoF/Combinators/SKY.lean",
      "snippet": "theorem I_reduces (t : Comb) : Steps (Comb.app I t) t := by\n  refine Steps.trans (t := Comb.app I t)\n    (u := Comb.app (Comb.app .K t) (Comb.app .K t))\n    (v := t) ?h\u2081 ?h\u2082\n  \u00b7 exact I_step t",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 1,
        "length": 192,
        "name_depth": 3
      },
      "pos": {
        "x": 0.864259252105932,
        "y": 0.38298107274536286
      },
      "pos3": {
        "x": 0.2708416637197748,
        "y": 0.28465447478541417,
        "z": 0.6902849623696696
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.steps_transitive",
      "kind": "theorem",
      "line": 37,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "private theorem steps_transitive {t u v : Comb} : Steps t u \u2192 Steps u v \u2192 Steps t v := by\n  intro htu huv\n  induction htu with\n  | refl _ => simpa using huv\n  | trans hstep hsteps ih => exact Steps.trans hstep (ih huv)",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 2,
        "length": 218,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2691240497071696
      },
      "pos3": {
        "x": 0.36438116394070946,
        "y": 0.20012178190918628,
        "z": 0.8860741150606782
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Steps.app_left",
      "kind": "theorem",
      "line": 43,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem Steps.app_left {f f' a : Comb} : Steps f f' \u2192 Steps (Comb.app f a) (Comb.app f' a) := by\n  intro h\n  induction h with\n  | refl t => exact Steps.refl (Comb.app t a)\n  | trans hstep hsteps ih =>",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 2,
        "length": 200,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.4310619775262113
      },
      "pos3": {
        "x": 0.22896644499695037,
        "y": 0.37399543435870464,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Steps.app_right",
      "kind": "theorem",
      "line": 50,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem Steps.app_right {f a a' : Comb} : Steps a a' \u2192 Steps (Comb.app f a) (Comb.app f a') := by\n  intro h\n  induction h with\n  | refl t => exact Steps.refl (Comb.app f t)\n  | trans hstep hsteps ih =>",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 2,
        "length": 201,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.5162699190894513
      },
      "pos3": {
        "x": 0.23949645707410427,
        "y": 0.33264793979144225,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Y_step",
      "kind": "theorem",
      "line": 60,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem Y_step (f : Comb) :\n    Step (Comb.app .Y f) (Comb.app f (Comb.app .Y f)) := by\n  simpa using Step.Y_rule (f := f)\n\n/-- Multi-step Y-unfolding as an eigenform equation. -/",
      "family": "Bridge",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 179,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9961928953132199,
        "y": 0.020246932145647385
      },
      "pos3": {
        "x": 0.14195585577279787,
        "y": 0.2703542477484763,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Y_eigenform",
      "kind": "theorem",
      "line": 65,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem Y_eigenform (f : Comb) :\n    Steps (Comb.app .Y f) (Comb.app f (Comb.app .Y f)) := by\n  exact Steps.trans (Y_step f) (Steps.refl _)\n\n/-- Joinability statement: `Y f` and `f (Y f)` share a common reduct (namely `f (Y f)`). -/",
      "family": "Bridge",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 232,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.21301362565999338
      },
      "pos3": {
        "x": 0.050907418859416416,
        "y": 0.12543866101753653,
        "z": 0.954635602974565
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Y_produces_fixedpoint",
      "kind": "theorem",
      "line": 70,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem Y_produces_fixedpoint (f : Comb) :\n    \u2203 t : Comb, Steps (Comb.app .Y f) t \u2227 Steps (Comb.app f (Comb.app .Y f)) t := by\n  refine \u27e8Comb.app f (Comb.app .Y f), ?_, ?_\u27e9\n  \u00b7 exact Y_eigenform f\n  \u00b7 exact Steps.refl _",
      "family": "Bridge",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 1,
        "eq": 1,
        "tactics": 2,
        "length": 220,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9990166144898233,
        "y": 0.5036790011781311
      },
      "pos3": {
        "x": 0.1898822567297387,
        "y": 0.30055647662294027,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.omega",
      "kind": "def",
      "line": 79,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "def omega : Comb :=\n  Comb.app (Comb.app .S Comb.I) Comb.I\n\n/-- `\u03c9 t \u2192* t t`. -/\ntheorem omega_selfApply (t : Comb) :",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 117,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9402873343180104,
        "y": 0.046328601125730666
      },
      "pos3": {
        "x": 0.32534144126221964,
        "y": 0.2018387011671501,
        "z": 0.8673921997991865
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.omega_selfApply",
      "kind": "theorem",
      "line": 83,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem omega_selfApply (t : Comb) :\n    Steps (Comb.app omega t) (Comb.app t t) := by\n  -- `\u03c9 t = (S I I) t \u21a6 I t (I t) \u2192* t t`.\n  have h1 :\n      Step (Comb.app omega t) (Comb.app (Comb.app Comb.I t) (Comb.app Comb.I t)) := by",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 228,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9321107933128253,
        "y": 0.2887670922654448
      },
      "pos3": {
        "x": 0.159738979817973,
        "y": 0.10732761631804791,
        "z": 0.8734527632235051
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.gremlin",
      "kind": "def",
      "line": 101,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "def gremlin (f : Comb) : Comb :=\n  Comb.app (Comb.app .S (Comb.app .K f)) omega\n\n/-- `G x \u2192* f (x x)` where `G := gremlin f`. -/\ntheorem gremlin_apply (f x : Comb) :",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 165,
        "name_depth": 4
      },
      "pos": {
        "x": 0.981704463694445,
        "y": 0.19794894810906716
      },
      "pos3": {
        "x": 0.24254090326564154,
        "y": 0.25492130838741955,
        "z": 0.8218484687553708
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.gremlin_apply",
      "kind": "theorem",
      "line": 105,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem gremlin_apply (f x : Comb) :\n    Steps (Comb.app (gremlin f) x) (Comb.app f (Comb.app x x)) := by\n  -- `(S (K f) \u03c9) x \u21a6 (K f x) (\u03c9 x) \u21a6 f (\u03c9 x) \u2192* f (x x)`.\n  have hS :\n      Step (Comb.app (gremlin f) x)",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 212,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.18227919369823586
      },
      "pos3": {
        "x": 0.2243323032993158,
        "y": 0.28892961422131413,
        "z": 0.8583305710219128
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.gremlin_fixedpoint",
      "kind": "theorem",
      "line": 123,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem gremlin_fixedpoint (f : Comb) :\n    Steps (Comb.app (gremlin f) (gremlin f)) (Comb.app f (Comb.app (gremlin f) (gremlin f))) := by\n  -- `G G \u2192* f (G G)` is exactly `gremlin_apply f (gremlin f)` plus one \u03c9-step.\n  -- `gremlin_apply` gives `G G \u2192* f (G G)` already (since `x = G`).\n  simpa usin",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 300,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.10919517048912282
      },
      "pos3": {
        "x": 0.4089062751471515,
        "y": 0.14831315070313109,
        "z": 0.8731953318735317
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.EigenformBridge.Bauer.scottFix_isFixed'",
      "kind": "theorem",
      "line": 135,
      "path": "HeytingLean/LoF/Combinators/EigenformBridge.lean",
      "snippet": "theorem scottFix_isFixed' {\u03b1 : Type _} [OmegaCompletePartialOrder \u03b1] [OrderBot \u03b1] (f : \u03b1 \u2192\ud835\udc84 \u03b1) :\n    f (HeytingLean.LoF.Bauer.scottFix (\u03b1 := \u03b1) f) = HeytingLean.LoF.Bauer.scottFix (\u03b1 := \u03b1) f :=\n  HeytingLean.LoF.Bauer.scottFix_isFixed (\u03b1 := \u03b1) (f := f)\n\n/-!",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 257,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.29730094732379697
      },
      "pos3": {
        "x": 0.29681740333353523,
        "y": 0.0016634454414095278,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.RuleTag",
      "kind": "inductive",
      "line": 24,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "inductive RuleTag\n  | K\n  | S\n  | Y\n  deriving DecidableEq, Repr",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 64,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8538311139884567,
        "y": 0.03408954031382003
      },
      "pos3": {
        "x": 0.23101385657220752,
        "y": 0.03197618896906168,
        "z": 0.7275438581828203
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.RuleTag.toNat",
      "kind": "def",
      "line": 30,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def RuleTag.toNat : RuleTag \u2192 Nat\n  | .K => 0\n  | .S => 1\n  | .Y => 2\n",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 70,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.0900040671916755
      },
      "pos3": {
        "x": 0.15276600451195949,
        "y": 0.28738981268386193,
        "z": 0.9553873251331223
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Dir",
      "kind": "inductive",
      "line": 35,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "inductive Dir\n  | L\n  | R\n  deriving DecidableEq, Repr\n",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 55,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6010637067263348,
        "y": 0.23683576690588812
      },
      "pos3": {
        "x": 0.015065515542192275,
        "y": 0.07475948389799149,
        "z": 0.8545009042054981
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.Dir.toNat",
      "kind": "def",
      "line": 40,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def Dir.toNat : Dir \u2192 Nat\n  | .L => 0\n  | .R => 1\n\nabbrev RedexPath := List Dir",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 79,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.08648657873030446
      },
      "pos3": {
        "x": 0.23693854764105177,
        "y": 0.24042498051667932,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.RedexPath",
      "kind": "abbrev",
      "line": 44,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "abbrev RedexPath := List Dir\n\nstructure EventData where\n  rule : RuleTag\n  path : RedexPath",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 91,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8223692725043793,
        "y": 0.17460412633791736
      },
      "pos3": {
        "x": 0.29636773591993437,
        "y": 0.1786356955408259,
        "z": 0.8850118825329469
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.EventData",
      "kind": "structure",
      "line": 46,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "structure EventData where\n  rule : RuleTag\n  path : RedexPath\n  deriving DecidableEq, Repr\n",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 91,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7283060756942039,
        "y": 0.01200090988250199
      },
      "pos3": {
        "x": 0.2674277777431311,
        "y": 0.18379569682852884,
        "z": 0.8157821883827903
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.rootStep?",
      "kind": "def",
      "line": 53,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def rootStep? : Comb \u2192 Option (RuleTag \u00d7 Comb)\n  | Comb.app (Comb.app .K x) _y =>\n      some (RuleTag.K, x)\n  | Comb.app (Comb.app (Comb.app .S x) y) z =>\n      some (RuleTag.S, Comb.app (Comb.app x z) (Comb.app y z))",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 217,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7225731580221302,
        "y": 0.2866319179900429
      },
      "pos3": {
        "x": 0.2514334494473206,
        "y": 0.2491707509164245,
        "z": 0.7643615851832486
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.rootStep?_sound",
      "kind": "theorem",
      "line": 63,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem rootStep?_sound {t : Comb} {r : RuleTag} {u : Comb} :\n    rootStep? t = some (r, u) \u2192 Step t u := by\n  intro h\n  cases t with\n  | K =>",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 2,
        "length": 142,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9711785714679679,
        "y": 0.37787708676165666
      },
      "pos3": {
        "x": 0.3691624309699787,
        "y": 0.42309663264787545,
        "z": 0.7424023310469161
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.rootEdgesList",
      "kind": "def",
      "line": 114,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def rootEdgesList (t : Comb) : List (EventData \u00d7 Comb) :=\n  match rootStep? t with\n  | some (r, u) => [({ rule := r, path := [] }, u)]\n  | none => []\n",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 150,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8503785059658051,
        "y": 0.1897528699469382
      },
      "pos3": {
        "x": 0.0777574645395058,
        "y": 0.07417192125289786,
        "z": 0.791298431032847
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.liftLeft",
      "kind": "def",
      "line": 119,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def liftLeft (a : Comb) : (EventData \u00d7 Comb) \u2192 (EventData \u00d7 Comb)\n  | (ed, u) => ({ ed with path := Dir.L :: ed.path }, Comb.app u a)\n\ndef liftRight (f : Comb) : (EventData \u00d7 Comb) \u2192 (EventData \u00d7 Comb)\n  | (ed, u) => ({ ed with path := Dir.R :: ed.path }, Comb.app f u)",
      "family": "Combinator",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 269,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8444281356702449,
        "y": 0.06513365578464163
      },
      "pos3": {
        "x": 0.42974410528914964,
        "y": 0.15638994384839464,
        "z": 0.7880245310945344
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.liftRight",
      "kind": "def",
      "line": 122,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def liftRight (f : Comb) : (EventData \u00d7 Comb) \u2192 (EventData \u00d7 Comb)\n  | (ed, u) => ({ ed with path := Dir.R :: ed.path }, Comb.app f u)\n\n/-- Deterministic enumeration of all one-step reductions from `t`,\nincluding rule tag + redex path. -/",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 238,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7924775049790401,
        "y": 0.29349444662277696
      },
      "pos3": {
        "x": 0.1823792340752615,
        "y": 0.023245006159420743,
        "z": 0.6857184452589459
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdgesList",
      "kind": "def",
      "line": 127,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def stepEdgesList : Comb \u2192 List (EventData \u00d7 Comb)\n  | Comb.app f a =>\n      let t := Comb.app f a\n      rootEdgesList t ++\n        ((stepEdgesList f).map (liftLeft a) ++",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 170,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9388366914664126,
        "y": 0.2752107746002708
      },
      "pos3": {
        "x": 0.1815145321246554,
        "y": 0.09591287052562869,
        "z": 0.762045666755537
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdges",
      "kind": "def",
      "line": 137,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "def stepEdges (t : Comb) : Finset (EventData \u00d7 Comb) :=\n  (stepEdgesList t).toFinset\n\ntheorem mem_stepEdges_iff {t : Comb} {e : EventData \u00d7 Comb} :\n    e \u2208 stepEdges t \u2194 e \u2208 stepEdgesList t := by",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 195,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8696773909579425,
        "y": 0.08252296150192621
      },
      "pos3": {
        "x": 0.04151221845484671,
        "y": 0.06937844391845603,
        "z": 0.8081849436897157
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.mem_stepEdges_iff",
      "kind": "theorem",
      "line": 140,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem mem_stepEdges_iff {t : Comb} {e : EventData \u00d7 Comb} :\n    e \u2208 stepEdges t \u2194 e \u2208 stepEdgesList t := by\n  simp [stepEdges]\n\n/-! ## Soundness: enumerated edges are valid `Step`s -/",
      "family": "Combinator",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 185,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6748589217668775,
        "y": 0.14933808650153568
      },
      "pos3": {
        "x": 0.21192574250836566,
        "y": 0.11926865521416342,
        "z": 0.7222798108999761
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdgesList_sound",
      "kind": "theorem",
      "line": 146,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem stepEdgesList_sound :\n    \u2200 {t : Comb} {ed : EventData} {u : Comb},\n      (ed, u) \u2208 stepEdgesList t \u2192 Step t u := by\n  intro t\n  induction t with",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 1,
        "tactics": 1,
        "length": 153,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9340348725614329,
        "y": 0.3805404104353027
      },
      "pos3": {
        "x": 0.2627833421511746,
        "y": 0.22473227023094677,
        "z": 0.6620503168543231
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdges_sound",
      "kind": "theorem",
      "line": 195,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem stepEdges_sound {t : Comb} {ed : EventData} {u : Comb} :\n    (ed, u) \u2208 stepEdges t \u2192 Step t u := by\n  intro h\n  have h' : (ed, u) \u2208 stepEdgesList t := (mem_stepEdges_iff (t := t)).1 h\n  exact stepEdgesList_sound (t := t) (ed := ed) (u := u) h'",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 3,
        "length": 251,
        "name_depth": 3
      },
      "pos": {
        "x": 0.821913216949635,
        "y": 0.5112984530452139
      },
      "pos3": {
        "x": 0.22604305533202768,
        "y": 0.5714515435020531,
        "z": 0.7752238242612677
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdgesList_complete",
      "kind": "theorem",
      "line": 203,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem stepEdgesList_complete :\n    \u2200 {t u : Comb}, Step t u \u2192 \u2203 ed : EventData, (ed, u) \u2208 stepEdgesList t := by\n  intro t u h\n  induction h with\n  | K_rule x y =>",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 1,
        "eq": 2,
        "tactics": 1,
        "length": 164,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7463660014996615,
        "y": 0.3953643047081023
      },
      "pos3": {
        "x": 0.3086568959493904,
        "y": 0.3570196096911803,
        "z": 0.8296783728354209
      }
    },
    {
      "name": "HeytingLean.LoF.Comb.stepEdges_complete",
      "kind": "theorem",
      "line": 286,
      "path": "HeytingLean/LoF/Combinators/SKYMultiway.lean",
      "snippet": "theorem stepEdges_complete {t u : Comb} :\n    Step t u \u2192 \u2203 ed : EventData, (ed, u) \u2208 stepEdges t := by\n  intro h\n  rcases stepEdgesList_complete (t := t) (u := u) h with \u27e8ed, hmem\u27e9\n  refine \u27e8ed, (mem_stepEdges_iff (t := t)).2 hmem\u27e9",
      "family": "Combinator",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 1,
        "eq": 4,
        "tactics": 1,
        "length": 231,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9593817088659893,
        "y": 0.4159618098792889
      },
      "pos3": {
        "x": 0.2141143086783135,
        "y": 0.10176882507519792,
        "z": 0.7055276408015475
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.close_inf",
      "kind": "theorem",
      "line": 20,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "theorem close_inf (J : GrothendieckTopology C) {X : C} (S T : Sieve X) :\n    J.close (S \u2293 T) = J.close S \u2293 J.close T := by\n  ext Y f\n  change J.Covers (S \u2293 T) f \u2194 (J.Covers S f \u2227 J.Covers T f)\n  change (S \u2293 T).pullback f \u2208 J Y \u2194 (S.pullback f \u2208 J Y \u2227 T.pullback f \u2208 J Y)",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 270,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2914248613989973
      },
      "pos3": {
        "x": 0.22604253751781575,
        "y": 0.25603438517073135,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.sieveNucleus",
      "kind": "def",
      "line": 28,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "def sieveNucleus (J : GrothendieckTopology C) (X : C) : Nucleus (Sieve X) where\n  toInfHom :=\n    { toFun := J.close\n      map_inf' := by\n        intro S T",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 155,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8074359085694567,
        "y": 0.33646934152652463
      },
      "pos3": {
        "x": 0.12570638478894655,
        "y": 0.3242547006934152,
        "z": 0.9638396929201518
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.sieveNucleus_is_nucleus",
      "kind": "theorem",
      "line": 42,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "theorem sieveNucleus_is_nucleus (J : GrothendieckTopology C) (X : C) :\n    (\u2200 S : Sieve X, sieveNucleus (C := C) J X (sieveNucleus (C := C) J X S) = sieveNucleus (C := C) J X S) \u2227\n    (\u2200 S : Sieve X, S \u2264 sieveNucleus (C := C) J X S) \u2227\n    (\u2200 S T : Sieve X,\n      sieveNucleus (C := C) J X (S \u2293 T) = s",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 3,
        "exists": 0,
        "eq": 7,
        "tactics": 0,
        "length": 300,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8996556403839286,
        "y": 0.30924476581449767
      },
      "pos3": {
        "x": 0.18097577668237239,
        "y": 0.06616160829714567,
        "z": 0.8658264903864309
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.mem_fixedPoints_sieveNucleus_iff_isClosed",
      "kind": "theorem",
      "line": 56,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "theorem mem_fixedPoints_sieveNucleus_iff_isClosed (J : GrothendieckTopology C) {X : C}\n    (S : Sieve X) : (S \u2208 \u03a9_ (sieveNucleus (C := C) J X)) \u2194 J.IsClosed S := by\n  change (J.close S = S) \u2194 J.IsClosed S\n  simpa using (J.isClosed_iff_close_eq_self S).symm\n",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 257,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2849192085125838
      },
      "pos3": {
        "x": 0.13075079281399096,
        "y": 0.008707445984014572,
        "z": 0.9008388631095148
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.closedSieves_isSheaf",
      "kind": "theorem",
      "line": 62,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "theorem closedSieves_isSheaf (J : GrothendieckTopology C) :\n    Presieve.IsSheaf J (Functor.closedSieves J) :=\n  CategoryTheory.classifier_isSheaf (J\u2081 := J)\n\n/-- The sieve nucleus associated to the dense topology on the SKY reachability site. -/",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 245,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.1045417128783416
      },
      "pos3": {
        "x": 0.20374256550850492,
        "y": 0.12129500074129113,
        "z": 0.8495134193610527
      }
    },
    {
      "name": "HeytingLean.LoF.Combinators.Topos.stepsSieveNucleus",
      "kind": "abbrev",
      "line": 67,
      "path": "HeytingLean/LoF/Combinators/Topos/SieveNucleus.lean",
      "snippet": "abbrev stepsSieveNucleus (X : StepsCat) : Nucleus (Sieve X) :=\n  sieveNucleus (C := StepsCat) (J := stepsDenseTopology) X\n\nend Topos\nend Combinators",
      "family": "Topos",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 148,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.047228687920887136
      },
      "pos3": {
        "x": 0.14021704476969304,
        "y": 0.03828833918434821,
        "z": 0.9866770882922195
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.factsPresieve",
      "kind": "def",
      "line": 35,
      "path": "HeytingLean/LoF/Bridge/FactsAsSieves.lean",
      "snippet": "def factsPresieve (atomArrow : Atom \u2192 \u03a3 Y : C, (Y \u27f6 X)) (F : Facts) : Presieve X :=\n  fun {Y} (f : Y \u27f6 X) =>\n    \u2203 a : Atom, (Facts.get F a) \u2260 0.0 \u2227 atomArrow a = \u27e8Y, f\u27e9\n\n/-- The sieve generated by the presieve of \u201cobserved\u201d fact-arrows. -/",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 1,
        "eq": 3,
        "tactics": 0,
        "length": 240,
        "name_depth": 3
      },
      "pos": {
        "x": 0.961650034871827,
        "y": 0.2815779754013345
      },
      "pos3": {
        "x": 0.10808993557154131,
        "y": 0.11820607690191141,
        "z": 0.7693175949074323
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.factsSieve",
      "kind": "def",
      "line": 40,
      "path": "HeytingLean/LoF/Bridge/FactsAsSieves.lean",
      "snippet": "def factsSieve (atomArrow : Atom \u2192 \u03a3 Y : C, (Y \u27f6 X)) (F : Facts) : Sieve X :=\n  Sieve.generate (factsPresieve (X := X) atomArrow F)\n\ntheorem factsPresieve_le_factsSieve (atomArrow : Atom \u2192 \u03a3 Y : C, (Y \u27f6 X)) (F : Facts) :\n    factsPresieve (X := X) atomArrow F \u2264 factsSieve (X := X) atomArrow F := by",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 299,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8667301152636994,
        "y": 0.2748759816790787
      },
      "pos3": {
        "x": 0.20813061390209375,
        "y": 0.19282489440280073,
        "z": 0.6407098461691694
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.factsPresieve_le_factsSieve",
      "kind": "theorem",
      "line": 43,
      "path": "HeytingLean/LoF/Bridge/FactsAsSieves.lean",
      "snippet": "theorem factsPresieve_le_factsSieve (atomArrow : Atom \u2192 \u03a3 Y : C, (Y \u27f6 X)) (F : Facts) :\n    factsPresieve (X := X) atomArrow F \u2264 factsSieve (X := X) atomArrow F := by\n  simpa [factsSieve] using (Sieve.le_generate (factsPresieve (X := X) atomArrow F))\n\ntheorem atomArrow_mem_factsSieve",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 284,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8380909704036827,
        "y": 0.11995726020158018
      },
      "pos3": {
        "x": 0.2385095332154535,
        "y": 0.015085390046588265,
        "z": 0.7137311592564419
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.atomArrow_mem_factsSieve",
      "kind": "theorem",
      "line": 47,
      "path": "HeytingLean/LoF/Bridge/FactsAsSieves.lean",
      "snippet": "theorem atomArrow_mem_factsSieve\n    (atomArrow : Atom \u2192 \u03a3 Y : C, (Y \u27f6 X)) (F : Facts)\n    (a : Atom) (h : (Facts.get F a) \u2260 0.0) :\n    factsSieve (X := X) atomArrow F (atomArrow a).2 := by\n  have hpre :",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 203,
        "name_depth": 3
      },
      "pos": {
        "x": 0.9386036497458585,
        "y": 0.18857864622233111
      },
      "pos3": {
        "x": 0.16349808526344445,
        "y": 0.19805374146439259,
        "z": 0.8283689123682082
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.LoFTerm",
      "kind": "abbrev",
      "line": 23,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev LoFTerm := HeytingLean.LoF.Correspondence.LoFTerm\nabbrev Comb := HeytingLean.LoF.Comb\n\nabbrev toSKY : LoFTerm \u2192 Comb :=\n  HeytingLean.LoF.Correspondence.LoFTerm.toSKY",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 173,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9070993304104354,
        "y": 0.07523893649831259
      },
      "pos3": {
        "x": 0.21373786466924088,
        "y": 0.22560294706643544,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.Comb",
      "kind": "abbrev",
      "line": 24,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev Comb := HeytingLean.LoF.Comb\n\nabbrev toSKY : LoFTerm \u2192 Comb :=\n  HeytingLean.LoF.Correspondence.LoFTerm.toSKY\n",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 117,
        "name_depth": 4
      },
      "pos": {
        "x": 0.998478585359312,
        "y": 0.27100588260908587
      },
      "pos3": {
        "x": 0.1756814595347142,
        "y": 0.024571869828492764,
        "z": 0.8058149861150032
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.toSKY",
      "kind": "abbrev",
      "line": 26,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev toSKY : LoFTerm \u2192 Comb :=\n  HeytingLean.LoF.Correspondence.LoFTerm.toSKY\n\nabbrev toSKY_spec : LoFTerm \u2192 Comb :=\n  HeytingLean.LoF.Correspondence.LoFTerm.toSKY_spec",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 170,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.10073749781656142
      },
      "pos3": {
        "x": 0.36182571437676014,
        "y": 0.2999723485527628,
        "z": 0.9049881031160553
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.toSKY_spec",
      "kind": "abbrev",
      "line": 29,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev toSKY_spec : LoFTerm \u2192 Comb :=\n  HeytingLean.LoF.Correspondence.LoFTerm.toSKY_spec\n\nabbrev ofSKY : Comb \u2192 LoFTerm :=\n  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 170,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.13690351530801825
      },
      "pos3": {
        "x": 0.3950432279749625,
        "y": 0.23436991488326847,
        "z": 0.9955263965731669
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.ofSKY",
      "kind": "abbrev",
      "line": 32,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev ofSKY : Comb \u2192 LoFTerm :=\n  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY\n\nabbrev ofSKY_spec : Comb \u2192 LoFTerm :=\n  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY_spec",
      "family": "Bridge",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 170,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.17786471974361656
      },
      "pos3": {
        "x": 0.4262699612178579,
        "y": 0.28488351981479665,
        "z": 0.85980820470876
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.ofSKY_spec",
      "kind": "abbrev",
      "line": 35,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev ofSKY_spec : Comb \u2192 LoFTerm :=\n  HeytingLean.LoF.Correspondence.LoFTerm.ofSKY_spec\n\nabbrev Step := HeytingLean.LoF.Correspondence.LoFStep.Step\nabbrev Steps := HeytingLean.LoF.Correspondence.LoFStep.Steps",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 210,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.05560252555542827
      },
      "pos3": {
        "x": 0.1061140051960997,
        "y": 0.04571470373543711,
        "z": 0.837866292462262
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.Step",
      "kind": "abbrev",
      "line": 38,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev Step := HeytingLean.LoF.Correspondence.LoFStep.Step\nabbrev Steps := HeytingLean.LoF.Correspondence.LoFStep.Steps\n\ntheorem step_toSKY {t u : LoFTerm} :\n    Step t u \u2192 Comb.Step (toSKY t) (toSKY u) :=",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 205,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.07407034485173909
      },
      "pos3": {
        "x": 0.30083765338597324,
        "y": 0.16919087457900572,
        "z": 0.8653893622719512
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.Steps",
      "kind": "abbrev",
      "line": 39,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "abbrev Steps := HeytingLean.LoF.Correspondence.LoFStep.Steps\n\ntheorem step_toSKY {t u : LoFTerm} :\n    Step t u \u2192 Comb.Step (toSKY t) (toSKY u) :=\n  HeytingLean.LoF.Correspondence.LoFStep.step_toSKY",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 198,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.09943990875689059
      },
      "pos3": {
        "x": 0.30983949137384525,
        "y": 0.23006942950687223,
        "z": 0.8503367430103407
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.step_toSKY",
      "kind": "theorem",
      "line": 41,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "theorem step_toSKY {t u : LoFTerm} :\n    Step t u \u2192 Comb.Step (toSKY t) (toSKY u) :=\n  HeytingLean.LoF.Correspondence.LoFStep.step_toSKY\n\ntheorem steps_toSKY {t u : LoFTerm} :",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 175,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9325207641644133,
        "y": 0.1478691275693933
      },
      "pos3": {
        "x": 0.28217424816727954,
        "y": 0.22437769558658574,
        "z": 0.8343598614136694
      }
    },
    {
      "name": "HeytingLean.LoF.Bridge.LoFToSKY.steps_toSKY",
      "kind": "theorem",
      "line": 45,
      "path": "HeytingLean/LoF/Bridge/LoFToSKY.lean",
      "snippet": "theorem steps_toSKY {t u : LoFTerm} :\n    Steps t u \u2192 Comb.Steps (toSKY t) (toSKY u) :=\n  HeytingLean.LoF.Correspondence.LoFStep.steps_toSKY\n\nend LoFToSKY",
      "family": "Bridge",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 154,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.10950319425849736
      },
      "pos3": {
        "x": 0.34579035229332555,
        "y": 0.2894162319102263,
        "z": 0.832429624897282
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.WireId",
      "kind": "abbrev",
      "line": 22,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "abbrev WireId := Nat\n\n/-- Gate types for combinational logic. -/\ninductive Gate where\n  | const (out : WireId) (b : Bool)           -- constant 0 or 1",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 150,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9818626559918431,
        "y": 0.16842691790084344
      },
      "pos3": {
        "x": 0.007703527649239805,
        "y": 0.09358717331840856,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Gate",
      "kind": "inductive",
      "line": 25,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "inductive Gate where\n  | const (out : WireId) (b : Bool)           -- constant 0 or 1\n  | input (out : WireId) (v : Nat)            -- primary input (variable index)\n  | not   (out : WireId) (a : WireId)         -- NOT gate\n  | and2  (out : WireId) (a b : WireId)       -- 2-input AND",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 284,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9155586300034182,
        "y": 0.20137641304897985
      },
      "pos3": {
        "x": 0.28745185146176877,
        "y": 0.1189963324549882,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Netlist",
      "kind": "structure",
      "line": 35,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "structure Netlist where\n  gates : List Gate\n  output : WireId\nderiving Repr\n",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 76,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8764167518415746,
        "y": 0.22023558515025118
      },
      "pos3": {
        "x": 0.02279894335291799,
        "y": 0.2071843247798941,
        "z": 0.9881727186803133
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.WireEnv",
      "kind": "abbrev",
      "line": 41,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "abbrev WireEnv := WireId \u2192 Option Bool\n\n/-- Output wire of a gate. -/\ndef Gate.out : Gate \u2192 WireId\n  | .const out _ => out",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 122,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2898725496497248
      },
      "pos3": {
        "x": 0.23057039163379298,
        "y": 0.2317442654853672,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Gate.out",
      "kind": "def",
      "line": 44,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def Gate.out : Gate \u2192 WireId\n  | .const out _ => out\n  | .input out _ => out\n  | .not out _ => out\n  | .and2 out _ _ => out",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 123,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.22812899974345366
      },
      "pos3": {
        "x": 0.28012348444505325,
        "y": 0.03631651952019453,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Gate.eval",
      "kind": "def",
      "line": 53,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def Gate.eval (inputs : Nat \u2192 Bool) (g : Gate) (env : WireEnv) : WireEnv := fun w =>\n  match g with\n  | .const out b =>\n      if w = out then some b else env w\n  | .input out v =>",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 179,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.21908855132989985
      },
      "pos3": {
        "x": 0.33479060390830584,
        "y": 0.10416112959253469,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.evalGates",
      "kind": "def",
      "line": 82,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def evalGates (inputs : Nat \u2192 Bool) : List Gate \u2192 WireEnv \u2192 WireEnv\n  | [], env => env\n  | g :: gs, env => evalGates inputs gs (g.eval inputs env)\n\n/-- `evalGates` distributes over list append. -/",
      "family": "LoFKernel",
      "features": {
        "implies": 3,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 196,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.04059214333789306
      },
      "pos3": {
        "x": 0.4111712628654169,
        "y": 0.15178823690312337,
        "z": 0.902369352458385
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.evalGates_append",
      "kind": "theorem",
      "line": 87,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "theorem evalGates_append (inputs : Nat \u2192 Bool) :\n    \u2200 (gs\u2081 gs\u2082 : List Gate) (env : WireEnv),\n      evalGates inputs (gs\u2081 ++ gs\u2082) env = evalGates inputs gs\u2082 (evalGates inputs gs\u2081 env)\n  | [], gs\u2082, env => rfl\n  | g :: gs\u2081, gs\u2082, env => by",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 236,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.12266001081277891
      },
      "pos3": {
        "x": 0.35487268809987316,
        "y": 0.24669927542701742,
        "z": 0.8316616611931996
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Netlist.eval",
      "kind": "def",
      "line": 95,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def Netlist.eval (nl : Netlist) (inputs : Nat \u2192 Bool) : Option Bool :=\n  let finalEnv := evalGates inputs nl.gates (fun _ => none)\n  finalEnv nl.output\n\nprivate theorem Gate.eval_of_ne_out (inputs : Nat \u2192 Bool) (g : Gate) (env : WireEnv)",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 237,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.2781045838519006
      },
      "pos3": {
        "x": 0.4882362701643736,
        "y": 0.19067553183043376,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.Gate.eval_of_ne_out",
      "kind": "theorem",
      "line": 99,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem Gate.eval_of_ne_out (inputs : Nat \u2192 Bool) (g : Gate) (env : WireEnv)\n    {w : WireId} (hw : w \u2260 g.out) :\n    g.eval inputs env w = env w := by\n  cases g with\n  | const out b =>",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 192,
        "name_depth": 5
      },
      "pos": {
        "x": 1,
        "y": 0.20929668046337924
      },
      "pos3": {
        "x": 0.31219259311182307,
        "y": 0.2306461435023031,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.evalGates_preserve",
      "kind": "theorem",
      "line": 122,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem evalGates_preserve (inputs : Nat \u2192 Bool) :\n    \u2200 (gs : List Gate) (env : WireEnv) (w : WireId),\n      (\u2200 g \u2208 gs, g.out \u2260 w) \u2192\n      evalGates inputs gs env w = env w\n  | [], env, w, _ => rfl",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 2,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 206,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.14311787258576505
      },
      "pos3": {
        "x": 0.4896421193714233,
        "y": 0.08102471891622025,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.evalGates_preserve_lt",
      "kind": "theorem",
      "line": 136,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem evalGates_preserve_lt (inputs : Nat \u2192 Bool) (gs : List Gate) (env : WireEnv)\n    (k w : WireId) (hw : w < k) (hge : \u2200 g \u2208 gs, k \u2264 g.out) :\n    evalGates inputs gs env w = env w := by\n  apply evalGates_preserve (inputs := inputs) (gs := gs) (env := env) (w := w)\n  intro g hg",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 6,
        "tactics": 2,
        "length": 290,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.31769656075778413
      },
      "pos3": {
        "x": 0.2614518719344767,
        "y": 0.3450492511649589,
        "z": 0.9306723479011683
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.CompileState",
      "kind": "structure",
      "line": 148,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "structure CompileState (n : Nat) where\n  nextWire : WireId\n  gates : List Gate\n  inputWires : Fin n \u2192 WireId  -- maps variables to their input wires\n",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 149,
        "name_depth": 4
      },
      "pos": {
        "x": 0.938186339717746,
        "y": 0.14103390013187247
      },
      "pos3": {
        "x": 0.3193078642915367,
        "y": 0.0805186614147676,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.mkInputGates",
      "kind": "def",
      "line": 154,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private def mkInputGates : Nat \u2192 List Gate\n  | 0 => []\n  | n + 1 => mkInputGates n ++ [Gate.input n n]\n\n/-- Create initial state with input wires for all variables. -/",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 167,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.21989538358181987
      },
      "pos3": {
        "x": 0.349219305667181,
        "y": 0.02599886941670232,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.initCompileState",
      "kind": "def",
      "line": 159,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def initCompileState (n : Nat) : CompileState n :=\n  { nextWire := n\n    gates := mkInputGates n\n    inputWires := fun v => v.val }\n",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 132,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.19785447478541415
      },
      "pos3": {
        "x": 0.07315903175728679,
        "y": 0.1394125399809695,
        "z": 0.9830995112691563
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compilePure",
      "kind": "def",
      "line": 166,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private def compilePure {n : Nat} (inputWires : Fin n \u2192 WireId) :\n    MuxNet.Net n \u2192 WireId \u2192 (WireId \u00d7 WireId \u00d7 List Gate)\n  | .const b, k => (k, k + 1, [Gate.const k b])\n  | .mux v lo hi, k =>\n      let (loOut, k\u2081, gLo) := compilePure inputWires lo k",
      "family": "LoFKernel",
      "features": {
        "implies": 3,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 252,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.18958116394070945
      },
      "pos3": {
        "x": 0.41369679123847924,
        "y": 0.008609999331026874,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compileMuxNet",
      "kind": "def",
      "line": 176,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def compileMuxNet {n : Nat} (net : MuxNet.Net n) : StateM (CompileState n) WireId :=\n  fun s =>\n    let (outWire, nextWire, newGates) := compilePure s.inputWires net s.nextWire\n    (outWire, { s with nextWire := nextWire, gates := s.gates ++ newGates })\n",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 254,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8001217819091863,
        "y": 0.11147411506067816
      },
      "pos3": {
        "x": 0.05455195714730754,
        "y": 0.0636359550539217,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.toNetlist",
      "kind": "def",
      "line": 182,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def toNetlist {n : Nat} (net : MuxNet.Net n) : Netlist :=\n  let (outWire, s') := compileMuxNet net (initCompileState n)\n  { gates := s'.gates, output := outWire }\n\nprivate theorem compilePure_next_eq_out_succ {n : Nat} (inputWires : Fin n \u2192 WireId)",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 248,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.19879543435870461
      },
      "pos3": {
        "x": 0.20210165294928512,
        "y": 0.26409599392746763,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compilePure_next_eq_out_succ",
      "kind": "theorem",
      "line": 186,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem compilePure_next_eq_out_succ {n : Nat} (inputWires : Fin n \u2192 WireId)\n    (net : MuxNet.Net n) (k : WireId) :\n    (compilePure inputWires net k).2.1 = (compilePure inputWires net k).1 + 1 := by\n  induction net generalizing k with\n  | const b => simp [compilePure]",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 278,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.26729645707410427
      },
      "pos3": {
        "x": 0.18288057272685548,
        "y": 0.10304533433160314,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compilePure_out_ge_start",
      "kind": "theorem",
      "line": 194,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem compilePure_out_ge_start {n : Nat} (inputWires : Fin n \u2192 WireId)\n    (net : MuxNet.Net n) (k : WireId) :\n    k \u2264 (compilePure inputWires net k).1 := by\n  induction net generalizing k with\n  | const b => simp [compilePure]",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 237,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.1878104202967301
      },
      "pos3": {
        "x": 0.1256838885874064,
        "y": 0.3160223992312583,
        "z": 0.9465733540546363
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compilePure_outs_ge_start",
      "kind": "theorem",
      "line": 221,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem compilePure_outs_ge_start {n : Nat} (inputWires : Fin n \u2192 WireId)\n    (net : MuxNet.Net n) (k : WireId) :\n    \u2200 g \u2208 (compilePure inputWires net k).2.2, k \u2264 g.out := by\n  induction net generalizing k with\n  | const b =>",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 1,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 234,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.29375424774847625
      },
      "pos3": {
        "x": 0.3274493960447399,
        "y": 0.2071828018339569,
        "z": 0.9937708699222857
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.inputsOf",
      "kind": "def",
      "line": 272,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private def inputsOf {n : Nat} (\u03c1 : Fin n \u2192 Bool) : Nat \u2192 Bool :=\n  fun i => if h : i < n then \u03c1 \u27e8i, h\u27e9 else false\n\nprivate theorem evalGates_mkInputGates {n : Nat} (inputs : Nat \u2192 Bool) (i : Nat) (hi : i < n) :\n    evalGates inputs (mkInputGates n) (fun _ => none) i = some (inputs i) := by",
      "family": "LoFKernel",
      "features": {
        "implies": 3,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 291,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.08000741885941642
      },
      "pos3": {
        "x": 0.4472464005235759,
        "y": 0.23787986043969522,
        "z": 0.8279160051664015
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.evalGates_mkInputGates",
      "kind": "theorem",
      "line": 275,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem evalGates_mkInputGates {n : Nat} (inputs : Nat \u2192 Bool) (i : Nat) (hi : i < n) :\n    evalGates inputs (mkInputGates n) (fun _ => none) i = some (inputs i) := by\n  induction n generalizing i with\n  | zero => cases (Nat.not_lt_zero _ hi)\n  | succ n ih =>",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 1,
        "length": 267,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9254386610175366,
        "y": 0.28133560297456495
      },
      "pos3": {
        "x": 0.16647892014175905,
        "y": 0.30753614658856054,
        "z": 0.8918618090390266
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.eval_compilePure",
      "kind": "theorem",
      "line": 297,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "private theorem eval_compilePure {n : Nat} (inputWires : Fin n \u2192 WireId)\n    (inputs : Nat \u2192 Bool) (net : MuxNet.Net n) (\u03c1 : Fin n \u2192 Bool) :\n    \u2200 (k : WireId) (env0 : WireEnv),\n      (\u2200 v : Fin n, env0 (inputWires v) = some (\u03c1 v)) \u2192\n      (\u2200 v : Fin n, inputWires v < k) \u2192",
      "family": "LoFKernel",
      "features": {
        "implies": 5,
        "forall": 3,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 273,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.12785647662294028
      },
      "pos3": {
        "x": 0.6744666755997102,
        "y": 0.14197814662785743,
        "z": 0.9592765793437303
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.toNetlist_correct",
      "kind": "theorem",
      "line": 380,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "theorem toNetlist_correct {n : Nat} (net : MuxNet.Net n) (\u03c1 : Fin n \u2192 Bool) :\n    (toNetlist (n := n) net).eval (inputsOf \u03c1) = some (MuxNet.eval net \u03c1) := by\n  -- Unfold `toNetlist` / `compileMuxNet` and reduce to `eval_compilePure` starting from the input environment.\n  let inputs := inputsOf \u03c1\n  l",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 300,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2553414412622197
      },
      "pos3": {
        "x": 0.22765114381156443,
        "y": 0.22378063101408288,
        "z": 0.899237389158779
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.compileMuxNet_correct",
      "kind": "theorem",
      "line": 404,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "theorem compileMuxNet_correct {n : Nat} (net : MuxNet.Net n) (\u03c1 : Fin n \u2192 Bool) :\n    let inputs := inputsOf \u03c1\n    let (outWire, s') := compileMuxNet (n := n) net (initCompileState n)\n    (evalGates inputs s'.gates (fun _ => none)) outWire = some (MuxNet.eval net \u03c1) := by\n  -- `toNetlist_correct` is",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 300,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.09739219979918648
      },
      "pos3": {
        "x": 0.3108564826557307,
        "y": 0.0812749280928589,
        "z": 0.8754211028602825
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.GateSpec.loFToGates_correct",
      "kind": "theorem",
      "line": 413,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "theorem loFToGates_correct {n : Nat} (A : Expr n) (\u03c1 : Fin n \u2192 Bool) :\n    (toNetlist (n := n) (MuxNet.toMuxNet (n := n) A)).eval (inputsOf \u03c1) =\n      some (LoFPrimary.eval A \u03c1) := by\n  have h := toNetlist_correct (n := n) (net := MuxNet.toMuxNet (n := n) A) (\u03c1 := \u03c1)\n  simpa [MuxNet.eval_toMuxNet] u",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 9,
        "tactics": 1,
        "length": 300,
        "name_depth": 4
      },
      "pos": {
        "x": 0.959738979817973,
        "y": 0.1373276163180479
      },
      "pos3": {
        "x": 0.13619676542569176,
        "y": 0.1577752880354552,
        "z": 0.8358664223765159
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.toNetlist",
      "kind": "def",
      "line": 424,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "def toNetlist {n : Nat} (net : Net n) : GateSpec.Netlist :=\n  GateSpec.toNetlist (n := n) net\n\ntheorem toNetlist_correct {n : Nat} (net : Net n) (\u03c1 : Fin n \u2192 Bool) :\n    (toNetlist (n := n) net).eval (GateSpec.inputsOf \u03c1) = some (eval net \u03c1) := by",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 247,
        "name_depth": 4
      },
      "pos": {
        "x": 0.973452763223505,
        "y": 0.16724090326564153
      },
      "pos3": {
        "x": 0.26075918961512495,
        "y": 0.2286568828452309,
        "z": 0.8555449527312986
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.toNetlist_correct",
      "kind": "theorem",
      "line": 427,
      "path": "HeytingLean/LoF/LoFPrimary/GateSpec.lean",
      "snippet": "theorem toNetlist_correct {n : Nat} (net : Net n) (\u03c1 : Fin n \u2192 Bool) :\n    (toNetlist (n := n) net).eval (GateSpec.inputsOf \u03c1) = some (eval net \u03c1) := by\n  simpa [toNetlist] using (GateSpec.toNetlist_correct (n := n) (net := net) (\u03c1 := \u03c1))\n\nend MuxNet",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 250,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.04684846875537073
      },
      "pos3": {
        "x": 0.1649153919635817,
        "y": 0.1452595761638126,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.Expr",
      "kind": "inductive",
      "line": 24,
      "path": "HeytingLean/LoF/LoFPrimary/Syntax.lean",
      "snippet": "inductive Expr (n : Nat) where\n  | void : Expr n\n  | var : Fin n \u2192 Expr n\n  | mark : Expr n \u2192 Expr n\n  | juxt : Expr n \u2192 Expr n \u2192 Expr n",
      "family": "LoFKernel",
      "features": {
        "implies": 4,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 136,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.2025296142213141
      },
      "pos3": {
        "x": 0.6929821068649171,
        "y": 0.15739106073258236,
        "z": 0.6848996109824866
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.Expr.marked",
      "kind": "def",
      "line": 36,
      "path": "HeytingLean/LoF/LoFPrimary/Syntax.lean",
      "snippet": "def marked : Expr n :=\n  mark void\n\nend Expr\n",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 45,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8583305710219128,
        "y": 0.21340627514715146
      },
      "pos3": {
        "x": 0.030157832427237227,
        "y": 0.05823527342732203,
        "z": 0.8682449490447665
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.Net",
      "kind": "inductive",
      "line": 27,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "inductive Net (n : Nat) where\n  | const (b : Bool)\n  | mux (v : Fin n) (lo hi : Net n)\nderiving Repr, DecidableEq\n",
      "family": "LoFKernel",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 114,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9483131507031312,
        "y": 0.08459533187353166
      },
      "pos3": {
        "x": 0.053832463105620995,
        "y": 0.0042445101768191495,
        "z": 0.960240526780299
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.ofBDD",
      "kind": "def",
      "line": 38,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "def ofBDD : LoFPrimary.Optimize.BDD n \u2192 Net n\n  | .leaf b => .const b\n  | .node v lo hi => .mux v (ofBDD lo) (ofBDD hi)\n\ntheorem eval_ofBDD (b : LoFPrimary.Optimize.BDD n) (\u03c1 : Fin n \u2192 Bool) :",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 192,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.02086344544140953
      },
      "pos3": {
        "x": 0.2822933980349802,
        "y": 0.29228847933082136,
        "z": 0.9660076900395825
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_ofBDD",
      "kind": "theorem",
      "line": 42,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_ofBDD (b : LoFPrimary.Optimize.BDD n) (\u03c1 : Fin n \u2192 Bool) :\n    eval (ofBDD b) \u03c1 = b.eval \u03c1 := by\n  induction b with\n  | leaf b => rfl\n  | node v lo hi ihLo ihHi =>",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 176,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.24861385657220753
      },
      "pos3": {
        "x": 0.30922521787305834,
        "y": 0.03788384788752267,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_mkROBDD_default",
      "kind": "theorem",
      "line": 49,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_mkROBDD_default (A : Expr n) (\u03c1 : Fin n \u2192 Bool) :\n    eval (ofBDD (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) A)) \u03c1 =\n      LoFPrimary.eval A \u03c1 := by\n  have h1 :=\n    eval_ofBDD (b := LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) A) (\u03c1 := \u03c1)",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 1,
        "length": 295,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9319761889690616,
        "y": 0.2570438581828203
      },
      "pos3": {
        "x": 0.24726360835713365,
        "y": 0.36181592049956035,
        "z": 0.9722192658878998
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_mkROBDD_simplify_default",
      "kind": "theorem",
      "line": 57,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_mkROBDD_simplify_default (A : Expr n) (\u03c1 : Fin n \u2192 Bool) :\n    eval\n        (ofBDD\n          (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n)\n            (LoFPrimary.Optimize.simplify A))) \u03c1 =",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 222,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9527660045119595,
        "y": 0.30958981268386193
      },
      "pos3": {
        "x": 0.24081908347915307,
        "y": 0.13214063944080306,
        "z": 0.8553091011170245
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.toMuxNet",
      "kind": "def",
      "line": 67,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "def toMuxNet (A : Expr n) : Net n :=\n  ofBDD (LoFPrimary.Optimize.mkROBDD (LoFPrimary.Optimize.defaultOrder n) (LoFPrimary.Optimize.simplify A))\n\ntheorem eval_toMuxNet (A : Expr n) (\u03c1 : Fin n \u2192 Bool) :\n    eval (toMuxNet (n := n) A) \u03c1 = LoFPrimary.eval A \u03c1 := by",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 262,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.04126551554219228
      },
      "pos3": {
        "x": 0.11541301515507335,
        "y": 0.28231907903043096,
        "z": 0.9433187561797063
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_toMuxNet",
      "kind": "theorem",
      "line": 70,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_toMuxNet (A : Expr n) (\u03c1 : Fin n \u2192 Bool) :\n    eval (toMuxNet (n := n) A) \u03c1 = LoFPrimary.eval A \u03c1 := by\n  simpa [toMuxNet] using eval_mkROBDD_simplify_default (A := A) (\u03c1 := \u03c1)\n\n/-- Convert a MuxNet to a MiniC expression (0/1 boolean encoding). -/",
      "family": "LoFKernel",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 260,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9747594838979915,
        "y": 0.28050090420549795
      },
      "pos3": {
        "x": 0.3466346935898291,
        "y": 0.12021223267558193,
        "z": 0.822224651076692
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.toMiniCExpr",
      "kind": "def",
      "line": 75,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "def toMiniCExpr (nameOf : Fin n \u2192 String) : Net n \u2192 MiniC.Expr\n  | .const true  => MiniC.Expr.boolLit true\n  | .const false => MiniC.Expr.boolLit false\n  | .mux v lo hi =>\n      -- ITE(v, hi, lo) = (v && hi) || (!v && lo)",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 221,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.26252498051667933
      },
      "pos3": {
        "x": 0.38883371208559947,
        "y": 0.01608272228775994,
        "z": 0.8447592753420966
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.StoreCorresponds",
      "kind": "def",
      "line": 87,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "def StoreCorresponds (nameOf : Fin n \u2192 String) (\u03c3 : MiniC.TotalStore) (\u03c1 : Fin n \u2192 Bool) : Prop :=\n  \u2200 v : Fin n, (\u03c3 (nameOf v) \u2260 0) \u2194 (\u03c1 v = true)\n\ntheorem eval_toMiniCExpr (nameOf : Fin n \u2192 String) (net : Net n)\n    (\u03c3 : MiniC.TotalStore) (\u03c1 : Fin n \u2192 Bool)",
      "family": "LoFKernel",
      "features": {
        "implies": 4,
        "forall": 1,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 259,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.32226773591993435
      },
      "pos3": {
        "x": 0.5688518791253693,
        "y": 0.0911506535526683,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_toMiniCExpr",
      "kind": "theorem",
      "line": 90,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_toMiniCExpr (nameOf : Fin n \u2192 String) (net : Net n)\n    (\u03c3 : MiniC.TotalStore) (\u03c1 : Fin n \u2192 Bool)\n    (hCorr : StoreCorresponds (n := n) nameOf \u03c3 \u03c1) :\n    (MiniC.Expr.eval (toMiniCExpr (n := n) nameOf net) \u03c3 \u2260 0) \u2194 (eval net \u03c1 = true) := by\n  induction net with",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 274,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.31241188253294677
      },
      "pos3": {
        "x": 0.2355354686634385,
        "y": 0.22933303359785825,
        "z": 0.9818952953728889
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.MuxNet.eval_loFToMiniC",
      "kind": "theorem",
      "line": 102,
      "path": "HeytingLean/LoF/LoFPrimary/MuxNet.lean",
      "snippet": "theorem eval_loFToMiniC (nameOf : Fin n \u2192 String) (A : Expr n)\n    (\u03c3 : MiniC.TotalStore) (\u03c1 : Fin n \u2192 Bool)\n    (hCorr : StoreCorresponds (n := n) nameOf \u03c3 \u03c1) :\n    (MiniC.Expr.eval (toMiniCExpr (n := n) nameOf (toMuxNet (n := n) A)) \u03c3 \u2260 0) \u2194\n      (LoFPrimary.eval A \u03c1 = true) := by",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 284,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.21219569682852885
      },
      "pos3": {
        "x": 0.43722224895302586,
        "y": 0.06770614111951039,
        "z": 0.9567717605390654
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.Step",
      "kind": "inductive",
      "line": 28,
      "path": "HeytingLean/LoF/LoFPrimary/Rewrite.lean",
      "snippet": "inductive Step : Expr n \u2192 Expr n \u2192 Prop where\n  | calling (A : Expr n) : Step (Expr.juxt A A) A\n  | crossing (A : Expr n) : Step (Expr.mark (Expr.mark A)) A\n  | void_left (A : Expr n) : Step (Expr.juxt Expr.void A) A\n  | void_right (A : Expr n) : Step (Expr.juxt A Expr.void) A",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 277,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.1791334494473206
      },
      "pos3": {
        "x": 0.3351543394666263,
        "y": 0.1328163012057985,
        "z": 0.8580499997478541
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.Steps",
      "kind": "inductive",
      "line": 39,
      "path": "HeytingLean/LoF/LoFPrimary/Rewrite.lean",
      "snippet": "inductive Steps : Expr n \u2192 Expr n \u2192 Prop where\n  | refl (A : Expr n) : Steps A A\n  | trans {A B C : Expr n} : Step A B \u2192 Steps B C \u2192 Steps A C\n\nnamespace Steps",
      "family": "LoFKernel",
      "features": {
        "implies": 4,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 159,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.1802615851832485
      },
      "pos3": {
        "x": 0.6970093781400394,
        "y": 0.09161407329580812,
        "z": 0.7863081963216446
      }
    },
    {
      "name": "HeytingLean.LoF.LoFPrimary.Steps.transitive",
      "kind": "theorem",
      "line": 45,
      "path": "HeytingLean/LoF/LoFPrimary/Rewrite.lean",
      "snippet": "theorem transitive {A B C : Expr n} : Steps A B \u2192 Steps B C \u2192 Steps A C := by\n  intro hAB hBC\n  induction hAB with\n  | refl _ =>\n      simpa using hBC",
      "family": "LoFKernel",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 1,
        "length": 150,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.3380966326478755
      },
      "pos3": {
        "x": 0.3828892736735391,
        "y": 0.3220267916453635,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Subst",
      "kind": "abbrev",
      "line": 10,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "abbrev Subst := List (String \u00d7 String)\n\nnamespace Subst\n\ndef lookup (s : Subst) (v : String) : Option String :=",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 111,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7424023310469161,
        "y": 0.0888574645395058
      },
      "pos3": {
        "x": 0.0623363717470654,
        "y": 0.0633075585916179,
        "z": 0.7981284411576111
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Subst.lookup",
      "kind": "def",
      "line": 14,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def lookup (s : Subst) (v : String) : Option String :=\n  (s.find? (fun kv => kv.1 = v)).map (\u00b7.2)\n\ndef bindVar (s : Subst) (v : String) (c : String) : Option Subst :=\n  match lookup s v with",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 190,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8741719212528979,
        "y": 0.21029843103284687
      },
      "pos3": {
        "x": 0.04711712801426314,
        "y": 0.05214406449793034,
        "z": 0.8225194606703504
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Subst.bindVar",
      "kind": "def",
      "line": 17,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def bindVar (s : Subst) (v : String) (c : String) : Option Subst :=\n  match lookup s v with\n  | none => some ((v, c) :: s)\n  | some c' => if c' = c then some s else none\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 170,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.17338994384839462
      },
      "pos3": {
        "x": 0.0008027167808657198,
        "y": 0.13515111138531072,
        "z": 0.978143358535869
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.clamp01",
      "kind": "def",
      "line": 24,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def clamp01 (x : Float) : Float :=\n  if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x\n\nprivate def maxF (a b : Float) : Float :=\n  if a < b then b else a",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 164,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7880245310945344,
        "y": 0.09877923407526149
      },
      "pos3": {
        "x": 0.08737778670930828,
        "y": 0.06944287036680775,
        "z": 0.81208674896371
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.maxF",
      "kind": "def",
      "line": 27,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def maxF (a b : Float) : Float :=\n  if a < b then b else a\n\nprivate def bit (x : Float) : Bool :=\n  x != 0.0",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 116,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6232450061594208,
        "y": 0.09731844525894574
      },
      "pos3": {
        "x": 0.21089626742811515,
        "y": 0.13620939792211298,
        "z": 0.8062154760213729
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.bit",
      "kind": "def",
      "line": 30,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def bit (x : Float) : Bool :=\n  x != 0.0\n\nprivate def bitToFloat (b : Bool) : Float :=\n  if b then 1.0 else 0.0",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 119,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6815145321246555,
        "y": 0.10781287052562868
      },
      "pos3": {
        "x": 0.2771733133447646,
        "y": 0.2363484079940194,
        "z": 0.7875174021492667
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.bitToFloat",
      "kind": "def",
      "line": 33,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def bitToFloat (b : Bool) : Float :=\n  if b then 1.0 else 0.0\n\ninductive Mode where\n  | boolean",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 103,
        "name_depth": 3
      },
      "pos": {
        "x": 0.762045666755537,
        "y": 0.05181221845484671
      },
      "pos3": {
        "x": 0.19835491285601034,
        "y": 0.280100537533654,
        "z": 0.7275416898312635
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Mode",
      "kind": "inductive",
      "line": 36,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "inductive Mode where\n  | boolean\n  | f2      -- F\u2082 semiring: AND = Boolean AND, OR = XOR (addition mod 2)\n  | fuzzy\n  | heyting  -- G\u00f6del t-norm: min/max with intuitionistic implication",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 185,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6693784439184561,
        "y": 0.2266849436897157
      },
      "pos3": {
        "x": 0.1633687136131736,
        "y": 0.1942904170207442,
        "z": 0.8725234335637819
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.TNorm",
      "kind": "inductive",
      "line": 43,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "inductive TNorm where\n  | product\n  | lukasiewicz\n  deriving Repr, BEq, DecidableEq\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 84,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8119257425083657,
        "y": 0.027668655214163423
      },
      "pos3": {
        "x": 0.24798934789501786,
        "y": 0.021422951056744244,
        "z": 0.6497768367662174
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Ops",
      "kind": "structure",
      "line": 48,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "structure Ops where\n  and : Float \u2192 Float \u2192 Float\n  or : Float \u2192 Float \u2192 Float\n\nnamespace Ops",
      "family": "TensorLogic",
      "features": {
        "implies": 4,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 93,
        "name_depth": 3
      },
      "pos": {
        "x": 1,
        "y": 0.1720833421511746
      },
      "pos3": {
        "x": 0.49228354378426975,
        "y": 0.22468731662088698,
        "z": 0.7707621147957278
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Ops.forConfig",
      "kind": "def",
      "line": 54,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def forConfig (mode : Mode) (tn : TNorm := .product) : Ops :=\n  match mode with\n  | .boolean =>\n      { and := fun a b => if (a == 0.0) || (b == 0.0) then 0.0 else 1.0\n      , or := fun a b => if (a == 0.0) && (b == 0.0) then 0.0 else 1.0",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 15,
        "tactics": 0,
        "length": 238,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9247322702309468,
        "y": 0.08585031685432307
      },
      "pos3": {
        "x": 0.08658317649175253,
        "y": 0.037306097452412465,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts",
      "kind": "abbrev",
      "line": 86,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "abbrev Facts := HashMap Atom Float\n\nnamespace Facts\n\ndef empty : Facts := {}",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 76,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7260430553320277,
        "y": 0.2790515435020531
      },
      "pos3": {
        "x": 0.2099201054927152,
        "y": 0.2828028722232122,
        "z": 0.7501416531353777
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.empty",
      "kind": "def",
      "line": 90,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def empty : Facts := {}\n\ndef get (F : Facts) (a : Atom) : Float :=\n  F.getD a 0.0\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 82,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9752238242612676,
        "y": 0.21685689594939042
      },
      "pos3": {
        "x": 0.14813856580352527,
        "y": 0.02413255556979029,
        "z": 0.8119582352550839
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.get",
      "kind": "def",
      "line": 92,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def get (F : Facts) (a : Atom) : Float :=\n  F.getD a 0.0\n\ndef addOr (ops : Ops) (F : Facts) (a : Atom) (w : Float) : Facts :=\n  if w == 0.0 then",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 144,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.24407837283542083
      },
      "pos3": {
        "x": 0.12960859924823176,
        "y": 0.09669647500748998,
        "z": 0.8751103707236012
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.addOr",
      "kind": "def",
      "line": 95,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def addOr (ops : Ops) (F : Facts) (a : Atom) (w : Float) : Facts :=\n  if w == 0.0 then\n    F\n  else\n    let w' := ops.or (F.get a) w",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 132,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9141143086783136,
        "y": 0.014968825075197922
      },
      "pos3": {
        "x": 0.02739806598929556,
        "y": 0.288573330657851,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.fromList",
      "kind": "def",
      "line": 105,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def fromList (ops : Ops) (xs : List (Atom \u00d7 Float)) : Facts :=\n  xs.foldl (fun acc (p : Atom \u00d7 Float) => addOr ops acc p.1 p.2) empty\n\ndef indexByPred (F : Facts) : HashMap String (List (Atom \u00d7 Float)) :=\n  F.fold (init := ({} : HashMap String (List (Atom \u00d7 Float))))",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 267,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9055276408015475,
        "y": 0.2527425375178157
      },
      "pos3": {
        "x": 0.17255973276597913,
        "y": 0.2852358833419057,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.indexByPred",
      "kind": "def",
      "line": 108,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def indexByPred (F : Facts) : HashMap String (List (Atom \u00d7 Float)) :=\n  F.fold (init := ({} : HashMap String (List (Atom \u00d7 Float))))\n    (fun acc atom w =>\n      if w == 0.0 then\n        acc",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 190,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.3050291015410319
      },
      "pos3": {
        "x": 0.20168447529097178,
        "y": 0.08085330779011617,
        "z": 0.8120695019433849
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Facts.maxDelta",
      "kind": "def",
      "line": 117,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def maxDelta (A B : Facts) : Float :=\n  let step (acc : Float) (atom : Atom) (wA : Float) : Float :=\n    let d := Float.abs (wA - (B.get atom))\n    maxF acc d\n  let acc1 := A.fold (init := 0.0) step",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 198,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9257063847889466,
        "y": 0.24405470069341523
      },
      "pos3": {
        "x": 0.22688064912376713,
        "y": 0.14115024697549006,
        "z": 0.9954528468301059
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.unifyArg",
      "kind": "def",
      "line": 129,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def unifyArg (s : Subst) (p : Sym) (c : String) : Option Subst :=\n  match p with\n  | .const k => if k = c then some s else none\n  | .var v => Subst.bindVar s v c\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 170,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7638396929201519,
        "y": 0.19797577668237237
      },
      "pos3": {
        "x": 0.27482183637803026,
        "y": 0.054446744166937774,
        "z": 0.7755988875833564
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.unifyArgs",
      "kind": "def",
      "line": 134,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def unifyArgs (s : Subst) : List Sym \u2192 List String \u2192 Option Subst\n  | [], [] => some s\n  | p :: ps, c :: cs => do\n      let s' \u2190 unifyArg s p c\n      unifyArgs s' ps cs",
      "family": "TensorLogic",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 176,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8661616082971457,
        "y": 0.08342649038643085
      },
      "pos3": {
        "x": 0.3904354158362261,
        "y": 0.147517740657304,
        "z": 0.6273727218881482
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.unify",
      "kind": "def",
      "line": 141,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def unify (pat : AtomPat) (atom : Atom) (s : Subst := []) : Option Subst := do\n  if pat.pred != atom.pred then\n    none\n  else if pat.arity != atom.arity then\n    none",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 167,
        "name_depth": 3
      },
      "pos": {
        "x": 0.730750792813991,
        "y": 0.025407445984014572
      },
      "pos3": {
        "x": 0.10438831688839513,
        "y": 0.0999925180995276,
        "z": 0.8010400528563557
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.instantiateArg",
      "kind": "def",
      "line": 149,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def instantiateArg (s : Subst) : Sym \u2192 Option String\n  | .const c => some c\n  | .var v => Subst.lookup s v\n\ndef instantiate (pat : AtomPat) (s : Subst) : Option Atom := do",
      "family": "TensorLogic",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 179,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8008388631095148,
        "y": 0.22164256550850492
      },
      "pos3": {
        "x": 0.35731992832010573,
        "y": 0.09894109907368961,
        "z": 0.8081021021950299
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.instantiate",
      "kind": "def",
      "line": 153,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def instantiate (pat : AtomPat) (s : Subst) : Option Atom := do\n  let args \u2190 pat.args.mapM (instantiateArg s)\n  pure { pred := pat.pred, args := args }\n\nprivate def extendMatches (ops : Ops) (facts : List (Atom \u00d7 Float)) (lit : AtomPat)",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 236,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7212950007412913,
        "y": 0.07311341936105265
      },
      "pos3": {
        "x": 0.08646533860843672,
        "y": 0.28355806186896315,
        "z": 0.8440698104213918
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.extendMatches",
      "kind": "def",
      "line": 157,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def extendMatches (ops : Ops) (facts : List (Atom \u00d7 Float)) (lit : AtomPat)\n    (acc : List (Subst \u00d7 Float)) : List (Subst \u00d7 Float) :=\n  acc.flatMap (fun (m : Subst \u00d7 Float) =>\n    facts.filterMap (fun (fw : Atom \u00d7 Float) =>\n      match unify lit fw.1 m.1 with",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 268,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7402170447696932,
        "y": 0.06508833918434821
      },
      "pos3": {
        "x": 0.16502898269153488,
        "y": 0.13644777258051882,
        "z": 0.6943551471510505
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.evalBody",
      "kind": "def",
      "line": 167,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def evalBody\n    (ops : Ops)\n    (idx : HashMap String (List (Atom \u00d7 Float)))\n    (body : List AtomPat) :\n    List (Subst \u00d7 Float) :=",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 141,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7866770882922195,
        "y": 0.022189935571541308
      },
      "pos3": {
        "x": 0.0969821358827984,
        "y": 0.2910554180425731,
        "z": 0.7212525171002238
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.RunConfig",
      "kind": "structure",
      "line": 176,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "structure RunConfig where\n  mode : Mode := .boolean\n  tnorm : TNorm := .product\n  maxIter : Nat := 50\n  eps : Float := 1e-6",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 123,
        "name_depth": 3
      },
      "pos": {
        "x": 0.7182060769019115,
        "y": 0.18161759490743223
      },
      "pos3": {
        "x": 0.15437887569873152,
        "y": 0.29643576443452624,
        "z": 0.7972981159449388
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.RunResult",
      "kind": "structure",
      "line": 182,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "structure RunResult where\n  facts : Facts\n  iters : Nat\n  delta : Float\n  converged : Bool",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 90,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6081306139020938,
        "y": 0.20182489440280074
      },
      "pos3": {
        "x": 0.16277807830715849,
        "y": 0.12397427123979644,
        "z": 0.6562747624183582
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.applyRule",
      "kind": "def",
      "line": 188,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def applyRule (ops : Ops) (idx : HashMap String (List (Atom \u00d7 Float))) (r : Rule)\n    (F : Facts) : Facts :=\n  let ms := evalBody ops idx r.body\n  ms.foldl\n    (fun acc (m : Subst \u00d7 Float) =>",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 199,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6407098461691694,
        "y": 0.1584095332154535
      },
      "pos3": {
        "x": 0.10853380774550257,
        "y": 0.2269329462166721,
        "z": 0.7876226226435028
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.step",
      "kind": "def",
      "line": 201,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def step (ops : Ops) (p : Program) (F : Facts) : Facts :=\n  let idx := Facts.indexByPred F\n  p.rules.foldl (fun acc r => applyRule ops idx r acc) F\n\n/-- One iteration of the immediate consequence operator, *anchored* at a fixed base fact set.",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 250,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6150853900465884,
        "y": 0.13873115925644186
      },
      "pos3": {
        "x": 0.22799716081830507,
        "y": 0.061067471505082155,
        "z": 0.7647658917255996
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.stepFromBase",
      "kind": "def",
      "line": 210,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "private def stepFromBase (ops : Ops) (p : Program) (base cur : Facts) : Facts :=\n  let idx := Facts.indexByPred cur\n  p.rules.foldl (fun acc r => applyRule ops idx r acc) base\n\ndef run (cfg : RunConfig) (p : Program) (init : Facts) : RunResult :=",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 246,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6634980852634446,
        "y": 0.12265374146439256
      },
      "pos3": {
        "x": 0.2783018282533343,
        "y": 0.13143482852171348,
        "z": 0.8094750087366518
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.run",
      "kind": "def",
      "line": 214,
      "path": "HeytingLean/Compiler/TensorLogic/Eval.lean",
      "snippet": "def run (cfg : RunConfig) (p : Program) (init : Facts) : RunResult :=\n  let ops := Ops.forConfig cfg.mode cfg.tnorm\n  let rec loop (fuel : Nat) (iters : Nat) (lastDelta : Float) (cur : Facts) : RunResult :=\n    match fuel with\n    | 0 =>",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 237,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8283689123682082,
        "y": 0.13743786466924088
      },
      "pos3": {
        "x": 0.03642782500878595,
        "y": 0.2919440447465083,
        "z": 0.7826615001245896
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.vertexName",
      "kind": "def",
      "line": 14,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def vertexName (i : Nat) : String :=\n  s!\"v{i}\"\n\ndef edgeName (i : Nat) : String :=\n  s!\"e{i}\"",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 94,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.2589772855465818
      },
      "pos3": {
        "x": 0.07178923869829511,
        "y": 0.04751344914156972,
        "z": 0.965251702100801
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.edgeName",
      "kind": "def",
      "line": 17,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def edgeName (i : Nat) : String :=\n  s!\"e{i}\"\n\ndef faceName (i : Nat) : String :=\n  s!\"f{i}\"",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 92,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8756814595347142,
        "y": 0.033771869828492763
      },
      "pos3": {
        "x": 0.1656754227161199,
        "y": 0.027962760384456765,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.faceName",
      "kind": "def",
      "line": 20,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def faceName (i : Nat) : String :=\n  s!\"f{i}\"\n\ndef simplexName (k i : Nat) : String :=\n  match k with",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 101,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8058149861150032,
        "y": 0.1719257143767601
      },
      "pos3": {
        "x": 0.2738789635452504,
        "y": 0.138434368253635,
        "z": 0.8352398447268673
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.simplexName",
      "kind": "def",
      "line": 23,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def simplexName (k i : Nat) : String :=\n  match k with\n  | 0 => vertexName i\n  | 1 => edgeName i\n  | 2 => faceName i",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 116,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.11658810311605518
      },
      "pos3": {
        "x": 0.24964295213067036,
        "y": 0.14951265141215858,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.mkAtom",
      "kind": "def",
      "line": 30,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "private def mkAtom (pred : String) (args : List String) : Atom :=\n  { pred := pred, args := args }\n\nprivate def mkPat (pred : String) (args : List String) : AtomPat :=\n  { pred := pred, args := args.map Sym.ofString }",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 217,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9950432279749626,
        "y": 0.25606991488326847
      },
      "pos3": {
        "x": 0.1526616045208535,
        "y": 0.08202746901398225,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.mkPat",
      "kind": "def",
      "line": 33,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "private def mkPat (pred : String) (args : List String) : AtomPat :=\n  { pred := pred, args := args.map Sym.ofString }\n\ndef simplexAtom (k i : Nat) : Atom :=\n  { pred := \"simplex\", args := [toString k, simplexName k i] }",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 6,
        "tactics": 0,
        "length": 219,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9955263965731669,
        "y": 0.24816996121785787
      },
      "pos3": {
        "x": 0.2940733897810126,
        "y": 0.0731192718225415,
        "z": 0.9653795230641409
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.simplexAtom",
      "kind": "def",
      "line": 36,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def simplexAtom (k i : Nat) : Atom :=\n  { pred := \"simplex\", args := [toString k, simplexName k i] }\n\ndef boundaryAtom (k i j : Nat) : Atom :=\n  { pred := \"boundary\"",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 165,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.07630820470875987
      },
      "pos3": {
        "x": 0.11507580397414496,
        "y": 0.2765604449794685,
        "z": 0.9524722674778683
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.boundaryAtom",
      "kind": "def",
      "line": 39,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def boundaryAtom (k i j : Nat) : Atom :=\n  { pred := \"boundary\"\n  , args := [toString k, simplexName k i, simplexName (k + 1) j]\n  }\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 133,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8061140051960998,
        "y": 0.05901470373543711
      },
      "pos3": {
        "x": 0.2637978765439428,
        "y": 0.25920808032857645,
        "z": 0.8828742208466124
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.connectivityProgram",
      "kind": "def",
      "line": 44,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "private def connectivityProgram : Program :=\n  { rules :=\n      [ { head := mkPat \"adjacent\" [\"V1\", \"V2\"]\n        , body := [mkPat \"edge\" [\"V1\", \"V2\"]]\n        }",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 4,
        "tactics": 0,
        "length": 161,
        "name_depth": 4
      },
      "pos": {
        "x": 0.837866292462262,
        "y": 0.2169376533859732
      },
      "pos3": {
        "x": 0.23700185460093404,
        "y": 0.12448272706540353,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.edgeEndpoints?",
      "kind": "def",
      "line": 67,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "private def edgeEndpoints? (d1 : F2Matrix) (e : Nat) : Option (String \u00d7 String) :=\n  if e < d1.cols then\n    let vs : Array Nat := Id.run do\n      let mut acc : Array Nat := #[]\n      for i in [:d1.rows] do",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 206,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9691908745790058,
        "y": 0.08598936227195109
      },
      "pos3": {
        "x": 0.15232130274289693,
        "y": 0.2461648419556735,
        "z": 0.8848516949848481
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.coreFacts",
      "kind": "def",
      "line": 87,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "private def coreFacts (C : ChainComplexF2) : List (Atom \u00d7 Float) :=\n  let basis :=\n    (List.range C.dims.size).flatMap fun k =>\n      (List.range (C.dims[k]!)).flatMap fun i =>\n        let name := simplexName k i",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 5,
        "tactics": 0,
        "length": 213,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.25136942950687224
      },
      "pos3": {
        "x": 0.08956675493153016,
        "y": 0.17608131672424832,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.toLogicProgram",
      "kind": "def",
      "line": 138,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "def toLogicProgram (C : ChainComplexF2) : Program \u00d7 List (Atom \u00d7 Float) :=\n  let prog := connectivityProgram\n\n  -- Derived `edge(V1,V2)` facts when \u2202\u2081 columns have exactly two vertices.\n  let edgePairs : Array (Option (String \u00d7 String)) :=",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 1,
        "length": 239,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8503367430103407,
        "y": 0.3060742481672795
      },
      "pos3": {
        "x": 0.1468921039967103,
        "y": 0.14457862551483674,
        "z": 0.9615741733111621
      }
    },
    {
      "name": "HeytingLean.Computational.Homology.ChainComplexF2.toLogicProgram_preserves_homology",
      "kind": "theorem",
      "line": 187,
      "path": "HeytingLean/Compiler/TensorLogic/HomologyEncoding.lean",
      "snippet": "theorem toLogicProgram_preserves_homology\n    (C : ChainComplexF2) {k i j : Nat}\n    (hk : k < C.boundaries.size)\n    (hi : i < (C.boundaries[k]!).rows)\n    (hj : j < (C.boundaries[k]!).cols)",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 191,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.053459861413669305
      },
      "pos3": {
        "x": 0.10353718250790225,
        "y": 0.16557522512124329,
        "z": 0.963029018887602
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym",
      "kind": "inductive",
      "line": 8,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "inductive Sym where\n  | var (name : String)\n  | const (name : String)\n  deriving Repr, BEq, DecidableEq\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 104,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8457903522933257,
        "y": 0.2998162319102263
      },
      "pos3": {
        "x": 0.13660338505995032,
        "y": 0.09653320506871123,
        "z": 0.6565957121121317
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym.stripQuotes",
      "kind": "def",
      "line": 15,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "private def stripQuotes (s : String) : Option String :=\n  if s.length \u2265 2 then\n    if (s.startsWith \"'\" && s.endsWith \"'\") || (s.startsWith \"\\\"\" && s.endsWith \"\\\"\") then\n      some ((s.drop 1).dropRight 1)\n    else",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 214,
        "name_depth": 4
      },
      "pos": {
        "x": 0.832429624897282,
        "y": 0.02910352764923981
      },
      "pos3": {
        "x": 0.2092495282861714,
        "y": 0.17153929259547032,
        "z": 0.8700687338173679
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym.isVarName",
      "kind": "def",
      "line": 24,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "private def isVarName (s : String) : Bool :=\n  if s.isEmpty then\n    false\n  else\n    let c := s.front",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 102,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8935871733184086,
        "y": 0.21340418605512262
      },
      "pos3": {
        "x": 0.23266334252977763,
        "y": 0.013094189729190575,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym.ofString",
      "kind": "def",
      "line": 39,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def ofString (raw : String) : Sym :=\n  match stripQuotes raw with\n  | some s => Sym.const s\n  | none =>\n      if raw.startsWith \"?\" then",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 3,
        "tactics": 0,
        "length": 136,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.1325963324549882
      },
      "pos3": {
        "x": 0.21156836430750076,
        "y": 0.24342267076946306,
        "z": 0.9158236257472947
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym.vars",
      "kind": "def",
      "line": 50,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def vars : Sym \u2192 List String\n  | .var v => [v]\n  | .const _ => []\n\ndef consts : Sym \u2192 List String",
      "family": "TensorLogic",
      "features": {
        "implies": 2,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 97,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.03249894335291799
      },
      "pos3": {
        "x": 0.3991066488453604,
        "y": 0.2462242655128665,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Sym.consts",
      "kind": "def",
      "line": 54,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def consts : Sym \u2192 List String\n  | .var _ => []\n  | .const c => [c]\n\nend Sym",
      "family": "TensorLogic",
      "features": {
        "implies": 1,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 76,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.19577271868031332
      },
      "pos3": {
        "x": 0.24859859488492705,
        "y": 0.011105883403672856,
        "z": 0.9506873450398898
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Atom",
      "kind": "structure",
      "line": 61,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "structure Atom where\n  pred : String\n  args : List String\n  deriving Repr, BEq, Hashable, DecidableEq\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 102,
        "name_depth": 3
      },
      "pos": {
        "x": 0.630570391633793,
        "y": 0.24194426548536718
      },
      "pos3": {
        "x": 0.1770541287928701,
        "y": 0.2609100940086646,
        "z": 0.8622571122162925
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Atom.arity",
      "kind": "def",
      "line": 68,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def arity (a : Atom) : Nat := a.args.length\n\nend Atom\n\n/-- A pattern atom (may contain variables). -/",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 101,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.19022348444505324
      },
      "pos3": {
        "x": 0.13209186293120315,
        "y": 0.15778532604226841,
        "z": 0.9370784223422727
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.AtomPat",
      "kind": "structure",
      "line": 73,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "structure AtomPat where\n  pred : String\n  args : List Sym\n  deriving Repr, BEq, DecidableEq\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 92,
        "name_depth": 3
      },
      "pos": {
        "x": 0.6363165195201946,
        "y": 0.30435330545440137
      },
      "pos3": {
        "x": 0.21673314827119278,
        "y": 0.12299358592390931,
        "z": 0.7964343979283202
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.AtomPat.arity",
      "kind": "def",
      "line": 80,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def arity (a : AtomPat) : Nat := a.args.length\n\ndef vars (a : AtomPat) : List String :=\n  a.args.flatMap Sym.vars\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 114,
        "name_depth": 4
      },
      "pos": {
        "x": 1,
        "y": 0.1155611295925347
      },
      "pos3": {
        "x": 0.046308365631464656,
        "y": 0.14084718029541957,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.AtomPat.vars",
      "kind": "def",
      "line": 82,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def vars (a : AtomPat) : List String :=\n  a.args.flatMap Sym.vars\n\ndef consts (a : AtomPat) : List String :=\n  a.args.flatMap Sym.consts",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 136,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9285134039704234,
        "y": 0.12477126286541686
      },
      "pos3": {
        "x": 0.1015683702154295,
        "y": 0.2078113795760646,
        "z": 0.9949509957737819
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.AtomPat.consts",
      "kind": "def",
      "line": 85,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def consts (a : AtomPat) : List String :=\n  a.args.flatMap Sym.consts\n\nend AtomPat\n",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 83,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9517882369031234,
        "y": 0.11066935245838495
      },
      "pos3": {
        "x": 0.2555295877052074,
        "y": 0.25570240096976793,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Rule",
      "kind": "structure",
      "line": 91,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "structure Rule where\n  head : AtomPat\n  body : List AtomPat\n  /-- Optional rule weight (used in fuzzy mode). -/\n  weight : Option Float := none",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 143,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8548726880998733,
        "y": 0.2609992754270174
      },
      "pos3": {
        "x": 0.1140028192567965,
        "y": 0.0949983461800199,
        "z": 0.815615227566895
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Rule.varsHead",
      "kind": "def",
      "line": 100,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def varsHead (r : Rule) : List String := r.head.vars\n\ndef varsBody (r : Rule) : List String := r.body.flatMap AtomPat.vars\n\nend Rule",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 2,
        "tactics": 0,
        "length": 132,
        "name_depth": 4
      },
      "pos": {
        "x": 0.8316616611931996,
        "y": 0.3014362701643736
      },
      "pos3": {
        "x": 0.22782054280030908,
        "y": 0.26171490521956087,
        "z": 0.810769729951306
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Rule.varsBody",
      "kind": "def",
      "line": 102,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "def varsBody (r : Rule) : List String := r.body.flatMap AtomPat.vars\n\nend Rule\n\nstructure Program where",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 1,
        "tactics": 0,
        "length": 103,
        "name_depth": 4
      },
      "pos": {
        "x": 0.9906755318304338,
        "y": 0.25891219330073745
      },
      "pos3": {
        "x": 0.020526224154465433,
        "y": 0.18934830505639216,
        "z": 1
      }
    },
    {
      "name": "HeytingLean.Compiler.TensorLogic.Program",
      "kind": "structure",
      "line": 106,
      "path": "HeytingLean/Compiler/TensorLogic/AST.lean",
      "snippet": "structure Program where\n  rules : List Rule\n  deriving Repr\n\nend TensorLogic",
      "family": "TensorLogic",
      "features": {
        "implies": 0,
        "forall": 0,
        "exists": 0,
        "eq": 0,
        "tactics": 0,
        "length": 76,
        "name_depth": 3
      },
      "pos": {
        "x": 0.8121925931118231,
        "y": 0.1382461435023031
      },
      "pos3": {
        "x": 0.2992277768868646,
        "y": 0.2240299100213781,
        "z": 0.7301914415769378
      }
    }
  ],
  "edges": [
    [
      0,
      10
    ],
    [
      0,
      52
    ],
    [
      0,
      58
    ],
    [
      0,
      47
    ],
    [
      0,
      176
    ],
    [
      1,
      8
    ],
    [
      1,
      19
    ],
    [
      1,
      73
    ],
    [
      1,
      126
    ],
    [
      1,
      127
    ],
    [
      2,
      36
    ],
    [
      2,
      42
    ],
    [
      2,
      45
    ],
    [
      2,
      253
    ],
    [
      2,
      26
    ],
    [
      3,
      236
    ],
    [
      3,
      128
    ],
    [
      3,
      38
    ],
    [
      3,
      248
    ],
    [
      3,
      256
    ],
    [
      4,
      80
    ],
    [
      4,
      130
    ],
    [
      4,
      155
    ],
    [
      4,
      45
    ],
    [
      4,
      56
    ],
    [
      5,
      21
    ],
    [
      5,
      151
    ],
    [
      5,
      40
    ],
    [
      5,
      166
    ],
    [
      5,
      181
    ],
    [
      6,
      41
    ],
    [
      6,
      239
    ],
    [
      6,
      122
    ],
    [
      6,
      150
    ],
    [
      6,
      250
    ],
    [
      7,
      103
    ],
    [
      7,
      246
    ],
    [
      7,
      55
    ],
    [
      7,
      244
    ],
    [
      7,
      228
    ],
    [
      8,
      127
    ],
    [
      8,
      214
    ],
    [
      8,
      245
    ],
    [
      8,
      19
    ],
    [
      9,
      45
    ],
    [
      9,
      56
    ],
    [
      9,
      63
    ],
    [
      9,
      253
    ],
    [
      10,
      52
    ],
    [
      10,
      58
    ],
    [
      10,
      266
    ],
    [
      10,
      47
    ],
    [
      10,
      129
    ],
    [
      11,
      24
    ],
    [
      11,
      25
    ],
    [
      11,
      85
    ],
    [
      11,
      18
    ],
    [
      11,
      169
    ],
    [
      12,
      254
    ],
    [
      12,
      77
    ],
    [
      12,
      33
    ],
    [
      12,
      198
    ],
    [
      12,
      255
    ],
    [
      13,
      32
    ],
    [
      13,
      54
    ],
    [
      13,
      180
    ],
    [
      13,
      162
    ],
    [
      13,
      31
    ],
    [
      14,
      37
    ],
    [
      14,
      264
    ],
    [
      14,
      273
    ],
    [
      14,
      17
    ],
    [
      14,
      240
    ],
    [
      15,
      66
    ],
    [
      15,
      72
    ],
    [
      15,
      269
    ],
    [
      15,
      67
    ],
    [
      15,
      80
    ],
    [
      16,
      251
    ],
    [
      16,
      105
    ],
    [
      16,
      185
    ],
    [
      16,
      231
    ],
    [
      16,
      184
    ],
    [
      17,
      37
    ],
    [
      17,
      280
    ],
    [
      17,
      273
    ],
    [
      17,
      104
    ],
    [
      18,
      169
    ],
    [
      18,
      85
    ],
    [
      18,
      222
    ],
    [
      18,
      24
    ],
    [
      18,
      25
    ],
    [
      19,
      126
    ],
    [
      19,
      171
    ],
    [
      19,
      214
    ],
    [
      20,
      31
    ],
    [
      20,
      265
    ],
    [
      20,
      102
    ],
    [
      20,
      84
    ],
    [
      20,
      111
    ],
    [
      21,
      151
    ],
    [
      21,
      40
    ],
    [
      21,
      166
    ],
    [
      21,
      181
    ],
    [
      22,
      71
    ],
    [
      22,
      27
    ],
    [
      22,
      34
    ],
    [
      22,
      233
    ],
    [
      22,
      247
    ],
    [
      23,
      38
    ],
    [
      23,
      81
    ],
    [
      23,
      60
    ],
    [
      23,
      68
    ],
    [
      23,
      135
    ],
    [
      24,
      25
    ],
    [
      24,
      85
    ],
    [
      24,
      169
    ],
    [
      25,
      85
    ],
    [
      25,
      169
    ],
    [
      26,
      36
    ],
    [
      26,
      64
    ],
    [
      26,
      129
    ],
    [
      26,
      170
    ],
    [
      27,
      71
    ],
    [
      27,
      247
    ],
    [
      27,
      134
    ],
    [
      28,
      40
    ],
    [
      28,
      86
    ],
    [
      28,
      166
    ],
    [
      28,
      181
    ],
    [
      28,
      46
    ],
    [
      29,
      125
    ],
    [
      29,
      226
    ],
    [
      29,
      123
    ],
    [
      29,
      124
    ],
    [
      29,
      212
    ],
    [
      30,
      257
    ],
    [
      30,
      147
    ],
    [
      30,
      278
    ],
    [
      30,
      148
    ],
    [
      30,
      258
    ],
    [
      31,
      265
    ],
    [
      31,
      111
    ],
    [
      31,
      102
    ],
    [
      31,
      116
    ],
    [
      32,
      54
    ],
    [
      32,
      162
    ],
    [
      33,
      165
    ],
    [
      33,
      255
    ],
    [
      33,
      77
    ],
    [
      33,
      254
    ],
    [
      34,
      233
    ],
    [
      34,
      67
    ],
    [
      34,
      156
    ],
    [
      34,
      71
    ],
    [
      35,
      69
    ],
    [
      35,
      164
    ],
    [
      35,
      218
    ],
    [
      35,
      142
    ],
    [
      35,
      197
    ],
    [
      36,
      64
    ],
    [
      36,
      129
    ],
    [
      36,
      42
    ],
    [
      37,
      273
    ],
    [
      37,
      280
    ],
    [
      37,
      264
    ],
    [
      38,
      60
    ],
    [
      38,
      81
    ],
    [
      38,
      138
    ],
    [
      38,
      160
    ],
    [
      39,
      255
    ],
    [
      39,
      165
    ],
    [
      39,
      208
    ],
    [
      39,
      77
    ],
    [
      40,
      166
    ],
    [
      40,
      46
    ],
    [
      40,
      86
    ],
    [
      40,
      151
    ],
    [
      41,
      239
    ],
    [
      41,
      282
    ],
    [
      41,
      122
    ],
    [
      42,
      65
    ],
    [
      42,
      253
    ],
    [
      42,
      61
    ],
    [
      43,
      281
    ],
    [
      43,
      83
    ],
    [
      43,
      234
    ],
    [
      43,
      238
    ],
    [
      43,
      117
    ],
    [
      44,
      74
    ],
    [
      44,
      68
    ],
    [
      44,
      106
    ],
    [
      44,
      216
    ],
    [
      44,
      62
    ],
    [
      45,
      56
    ],
    [
      45,
      243
    ],
    [
      45,
      253
    ],
    [
      46,
      86
    ],
    [
      46,
      166
    ],
    [
      47,
      58
    ],
    [
      47,
      76
    ],
    [
      47,
      52
    ],
    [
      48,
      79
    ],
    [
      48,
      221
    ],
    [
      48,
      152
    ],
    [
      48,
      161
    ],
    [
      48,
      203
    ],
    [
      49,
      57
    ],
    [
      49,
      54
    ],
    [
      50,
      262
    ],
    [
      50,
      261
    ],
    [
      50,
      62
    ],
    [
      50,
      131
    ],
    [
      51,
      127
    ],
    [
      51,
      134
    ],
    [
      51,
      247
    ],
    [
      52,
      58
    ],
    [
      52,
      266
    ],
    [
      52,
      129
    ],
    [
      53,
      55
    ],
    [
      53,
      84
    ],
    [
      53,
      246
    ],
    [
      53,
      229
    ],
    [
      53,
      102
    ],
    [
      54,
      162
    ],
    [
      54,
      180
    ],
    [
      55,
      103
    ],
    [
      55,
      246
    ],
    [
      55,
      84
    ],
    [
      56,
      155
    ],
    [
      56,
      63
    ],
    [
      57,
      162
    ],
    [
      57,
      265
    ],
    [
      58,
      266
    ],
    [
      58,
      78
    ],
    [
      59,
      67
    ],
    [
      59,
      80
    ],
    [
      59,
      130
    ],
    [
      59,
      227
    ],
    [
      59,
      242
    ],
    [
      60,
      138
    ],
    [
      60,
      68
    ],
    [
      60,
      74
    ],
    [
      61,
      65
    ],
    [
      61,
      63
    ],
    [
      61,
      64
    ],
    [
      61,
      170
    ],
    [
      62,
      149
    ],
    [
      62,
      136
    ],
    [
      62,
      216
    ],
    [
      62,
      74
    ],
    [
      63,
      65
    ],
    [
      64,
      129
    ],
    [
      64,
      170
    ],
    [
      65,
      253
    ],
    [
      66,
      72
    ],
    [
      66,
      155
    ],
    [
      66,
      119
    ],
    [
      67,
      80
    ],
    [
      67,
      227
    ],
    [
      67,
      242
    ],
    [
      68,
      74
    ],
    [
      68,
      106
    ],
    [
      69,
      164
    ],
    [
      69,
      218
    ],
    [
      69,
      220
    ],
    [
      69,
      217
    ],
    [
      70,
      194
    ],
    [
      70,
      139
    ],
    [
      70,
      154
    ],
    [
      70,
      246
    ],
    [
      71,
      247
    ],
    [
      71,
      134
    ],
    [
      72,
      155
    ],
    [
      72,
      119
    ],
    [
      73,
      126
    ],
    [
      73,
      88
    ],
    [
      73,
      127
    ],
    [
      74,
      106
    ],
    [
      74,
      216
    ],
    [
      75,
      249
    ],
    [
      75,
      241
    ],
    [
      75,
      161
    ],
    [
      75,
      152
    ],
    [
      76,
      78
    ],
    [
      77,
      255
    ],
    [
      77,
      254
    ],
    [
      77,
      165
    ],
    [
      78,
      266
    ],
    [
      79,
      199
    ],
    [
      79,
      223
    ],
    [
      79,
      93
    ],
    [
      79,
      95
    ],
    [
      79,
      161
    ],
    [
      80,
      130
    ],
    [
      80,
      227
    ],
    [
      81,
      201
    ],
    [
      81,
      160
    ],
    [
      81,
      94
    ],
    [
      82,
      149
    ],
    [
      82,
      271
    ],
    [
      82,
      110
    ],
    [
      82,
      131
    ],
    [
      83,
      234
    ],
    [
      83,
      100
    ],
    [
      83,
      117
    ],
    [
      83,
      238
    ],
    [
      84,
      246
    ],
    [
      84,
      263
    ],
    [
      85,
      169
    ],
    [
      85,
      182
    ],
    [
      86,
      166
    ],
    [
      86,
      181
    ],
    [
      87,
      109
    ],
    [
      87,
      264
    ],
    [
      87,
      108
    ],
    [
      87,
      240
    ],
    [
      88,
      179
    ],
    [
      88,
      245
    ],
    [
      88,
      126
    ],
    [
      88,
      171
    ],
    [
      89,
      90
    ],
    [
      89,
      132
    ],
    [
      89,
      178
    ],
    [
      89,
      133
    ],
    [
      90,
      132
    ],
    [
      90,
      133
    ],
    [
      90,
      178
    ],
    [
      91,
      171
    ],
    [
      91,
      228
    ],
    [
      91,
      214
    ],
    [
      91,
      244
    ],
    [
      92,
      191
    ],
    [
      92,
      177
    ],
    [
      92,
      266
    ],
    [
      93,
      199
    ],
    [
      93,
      223
    ],
    [
      93,
      95
    ],
    [
      93,
      221
    ],
    [
      94,
      201
    ],
    [
      94,
      135
    ],
    [
      94,
      188
    ],
    [
      94,
      189
    ],
    [
      95,
      221
    ],
    [
      95,
      199
    ],
    [
      95,
      204
    ],
    [
      96,
      218
    ],
    [
      96,
      217
    ],
    [
      96,
      142
    ],
    [
      96,
      203
    ],
    [
      97,
      222
    ],
    [
      97,
      169
    ],
    [
      97,
      192
    ],
    [
      98,
      136
    ],
    [
      98,
      216
    ],
    [
      98,
      131
    ],
    [
      98,
      149
    ],
    [
      99,
      203
    ],
    [
      99,
      241
    ],
    [
      99,
      152
    ],
    [
      99,
      249
    ],
    [
      99,
      217
    ],
    [
      100,
      146
    ],
    [
      100,
      285
    ],
    [
      100,
      117
    ],
    [
      100,
      183
    ],
    [
      101,
      108
    ],
    [
      101,
      240
    ],
    [
      101,
      185
    ],
    [
      101,
      195
    ],
    [
      101,
      109
    ],
    [
      102,
      121
    ],
    [
      102,
      265
    ],
    [
      103,
      228
    ],
    [
      103,
      246
    ],
    [
      103,
      244
    ],
    [
      104,
      250
    ],
    [
      104,
      122
    ],
    [
      104,
      282
    ],
    [
      105,
      231
    ],
    [
      105,
      251
    ],
    [
      105,
      260
    ],
    [
      105,
      185
    ],
    [
      106,
      216
    ],
    [
      107,
      144
    ],
    [
      107,
      143
    ],
    [
      107,
      183
    ],
    [
      107,
      285
    ],
    [
      107,
      237
    ],
    [
      108,
      109
    ],
    [
      108,
      240
    ],
    [
      108,
      264
    ],
    [
      109,
      195
    ],
    [
      109,
      240
    ],
    [
      109,
      264
    ],
    [
      110,
      267
    ],
    [
      110,
      149
    ],
    [
      110,
      261
    ],
    [
      110,
      271
    ],
    [
      110,
      176
    ],
    [
      111,
      116
    ],
    [
      111,
      265
    ],
    [
      112,
      272
    ],
    [
      112,
      259
    ],
    [
      112,
      114
    ],
    [
      112,
      277
    ],
    [
      112,
      284
    ],
    [
      113,
      257
    ],
    [
      113,
      258
    ],
    [
      113,
      147
    ],
    [
      113,
      274
    ],
    [
      114,
      226
    ],
    [
      114,
      123
    ],
    [
      114,
      124
    ],
    [
      115,
      212
    ],
    [
      115,
      279
    ],
    [
      115,
      137
    ],
    [
      115,
      172
    ],
    [
      115,
      230
    ],
    [
      116,
      265
    ],
    [
      117,
      238
    ],
    [
      117,
      281
    ],
    [
      117,
      146
    ],
    [
      118,
      145
    ],
    [
      118,
      143
    ],
    [
      118,
      144
    ],
    [
      118,
      211
    ],
    [
      119,
      213
    ],
    [
      119,
      269
    ],
    [
      120,
      191
    ],
    [
      121,
      265
    ],
    [
      122,
      250
    ],
    [
      122,
      282
    ],
    [
      123,
      124
    ],
    [
      123,
      125
    ],
    [
      123,
      232
    ],
    [
      123,
      270
    ],
    [
      124,
      125
    ],
    [
      124,
      232
    ],
    [
      124,
      270
    ],
    [
      125,
      226
    ],
    [
      125,
      212
    ],
    [
      127,
      134
    ],
    [
      127,
      179
    ],
    [
      127,
      245
    ],
    [
      128,
      160
    ],
    [
      130,
      190
    ],
    [
      130,
      227
    ],
    [
      131,
      149
    ],
    [
      131,
      219
    ],
    [
      131,
      136
    ],
    [
      132,
      133
    ],
    [
      134,
      247
    ],
    [
      135,
      201
    ],
    [
      136,
      216
    ],
    [
      137,
      172
    ],
    [
      137,
      212
    ],
    [
      137,
      230
    ],
    [
      137,
      260
    ],
    [
      138,
      160
    ],
    [
      139,
      194
    ],
    [
      139,
      229
    ],
    [
      139,
      263
    ],
    [
      140,
      271
    ],
    [
      140,
      176
    ],
    [
      140,
      267
    ],
    [
      140,
      149
    ],
    [
      141,
      205
    ],
    [
      141,
      168
    ],
    [
      141,
      206
    ],
    [
      141,
      207
    ],
    [
      141,
      163
    ],
    [
      142,
      164
    ],
    [
      142,
      218
    ],
    [
      142,
      197
    ],
    [
      142,
      209
    ],
    [
      143,
      145
    ],
    [
      143,
      144
    ],
    [
      143,
      285
    ],
    [
      144,
      275
    ],
    [
      144,
      146
    ],
    [
      144,
      237
    ],
    [
      144,
      183
    ],
    [
      145,
      211
    ],
    [
      146,
      275
    ],
    [
      146,
      238
    ],
    [
      146,
      237
    ],
    [
      147,
      148
    ],
    [
      147,
      252
    ],
    [
      147,
      278
    ],
    [
      147,
      258
    ],
    [
      148,
      252
    ],
    [
      148,
      278
    ],
    [
      148,
      258
    ],
    [
      149,
      261
    ],
    [
      150,
      250
    ],
    [
      150,
      282
    ],
    [
      151,
      166
    ],
    [
      151,
      181
    ],
    [
      152,
      249
    ],
    [
      152,
      241
    ],
    [
      152,
      161
    ],
    [
      152,
      203
    ],
    [
      152,
      221
    ],
    [
      153,
      200
    ],
    [
      153,
      167
    ],
    [
      153,
      248
    ],
    [
      153,
      256
    ],
    [
      153,
      188
    ],
    [
      154,
      173
    ],
    [
      154,
      174
    ],
    [
      154,
      175
    ],
    [
      154,
      244
    ],
    [
      154,
      194
    ],
    [
      156,
      233
    ],
    [
      157,
      180
    ],
    [
      157,
      162
    ],
    [
      157,
      181
    ],
    [
      157,
      225
    ],
    [
      158,
      209
    ],
    [
      158,
      254
    ],
    [
      158,
      197
    ],
    [
      158,
      198
    ],
    [
      158,
      208
    ],
    [
      159,
      229
    ],
    [
      161,
      249
    ],
    [
      161,
      241
    ],
    [
      162,
      180
    ],
    [
      163,
      206
    ],
    [
      163,
      205
    ],
    [
      163,
      207
    ],
    [
      163,
      168
    ],
    [
      164,
      197
    ],
    [
      164,
      218
    ],
    [
      165,
      255
    ],
    [
      165,
      198
    ],
    [
      166,
      181
    ],
    [
      167,
      268
    ],
    [
      167,
      248
    ],
    [
      167,
      256
    ],
    [
      168,
      205
    ],
    [
      168,
      206
    ],
    [
      168,
      215
    ],
    [
      168,
      207
    ],
    [
      169,
      222
    ],
    [
      171,
      179
    ],
    [
      171,
      214
    ],
    [
      172,
      230
    ],
    [
      172,
      260
    ],
    [
      172,
      279
    ],
    [
      173,
      174
    ],
    [
      173,
      175
    ],
    [
      173,
      194
    ],
    [
      173,
      228
    ],
    [
      174,
      175
    ],
    [
      174,
      194
    ],
    [
      174,
      228
    ],
    [
      175,
      194
    ],
    [
      175,
      228
    ],
    [
      176,
      177
    ],
    [
      176,
      266
    ],
    [
      177,
      266
    ],
    [
      179,
      214
    ],
    [
      179,
      245
    ],
    [
      180,
      181
    ],
    [
      181,
      193
    ],
    [
      181,
      225
    ],
    [
      183,
      285
    ],
    [
      183,
      237
    ],
    [
      183,
      275
    ],
    [
      184,
      185
    ],
    [
      184,
      251
    ],
    [
      185,
      251
    ],
    [
      186,
      247
    ],
    [
      186,
      214
    ],
    [
      187,
      213
    ],
    [
      188,
      201
    ],
    [
      188,
      248
    ],
    [
      188,
      189
    ],
    [
      188,
      200
    ],
    [
      189,
      200
    ],
    [
      189,
      248
    ],
    [
      189,
      256
    ],
    [
      190,
      213
    ],
    [
      191,
      266
    ],
    [
      192,
      202
    ],
    [
      192,
      215
    ],
    [
      192,
      222
    ],
    [
      193,
      225
    ],
    [
      195,
      240
    ],
    [
      195,
      264
    ],
    [
      195,
      283
    ],
    [
      196,
      254
    ],
    [
      196,
      197
    ],
    [
      196,
      198
    ],
    [
      196,
      209
    ],
    [
      197,
      209
    ],
    [
      198,
      208
    ],
    [
      198,
      209
    ],
    [
      198,
      255
    ],
    [
      199,
      221
    ],
    [
      199,
      223
    ],
    [
      200,
      268
    ],
    [
      200,
      201
    ],
    [
      202,
      215
    ],
    [
      202,
      222
    ],
    [
      203,
      241
    ],
    [
      203,
      249
    ],
    [
      203,
      217
    ],
    [
      204,
      221
    ],
    [
      204,
      223
    ],
    [
      205,
      206
    ],
    [
      205,
      207
    ],
    [
      206,
      207
    ],
    [
      208,
      209
    ],
    [
      208,
      255
    ],
    [
      209,
      254
    ],
    [
      210,
      280
    ],
    [
      210,
      273
    ],
    [
      212,
      279
    ],
    [
      214,
      245
    ],
    [
      216,
      219
    ],
    [
      217,
      218
    ],
    [
      217,
      241
    ],
    [
      219,
      262
    ],
    [
      226,
      279
    ],
    [
      226,
      230
    ],
    [
      227,
      242
    ],
    [
      228,
      244
    ],
    [
      230,
      260
    ],
    [
      230,
      231
    ],
    [
      230,
      279
    ],
    [
      231,
      251
    ],
    [
      232,
      284
    ],
    [
      232,
      270
    ],
    [
      232,
      276
    ],
    [
      232,
      272
    ],
    [
      232,
      277
    ],
    [
      234,
      281
    ],
    [
      234,
      238
    ],
    [
      234,
      252
    ],
    [
      235,
      278
    ],
    [
      235,
      252
    ],
    [
      236,
      256
    ],
    [
      236,
      268
    ],
    [
      237,
      275
    ],
    [
      237,
      285
    ],
    [
      238,
      281
    ],
    [
      239,
      282
    ],
    [
      240,
      264
    ],
    [
      240,
      283
    ],
    [
      241,
      249
    ],
    [
      243,
      253
    ],
    [
      244,
      246
    ],
    [
      248,
      256
    ],
    [
      250,
      282
    ],
    [
      252,
      278
    ],
    [
      252,
      258
    ],
    [
      257,
      258
    ],
    [
      257,
      274
    ],
    [
      258,
      278
    ],
    [
      259,
      272
    ],
    [
      259,
      277
    ],
    [
      259,
      284
    ],
    [
      259,
      276
    ],
    [
      260,
      279
    ],
    [
      261,
      262
    ],
    [
      261,
      267
    ],
    [
      262,
      267
    ],
    [
      264,
      283
    ],
    [
      267,
      271
    ],
    [
      270,
      276
    ],
    [
      270,
      284
    ],
    [
      272,
      277
    ],
    [
      272,
      284
    ],
    [
      272,
      276
    ],
    [
      273,
      280
    ],
    [
      275,
      285
    ],
    [
      276,
      277
    ],
    [
      276,
      284
    ],
    [
      277,
      284
    ]
  ]
}