import HeytingLean.Compiler.TensorLogic.Eval
import HeytingLean.Compiler.TensorLogic.Bots.Monotone
import HeytingLean.Compiler.TensorLogic.Bots.Fuzzy
import HeytingLean.Compiler.TensorLogic.Bots.Explain
import HeytingLean.Compiler.TensorLogic.Bots.F2Linear
import HeytingLean.Compiler.TensorLogic.Bots.F2Solve

namespace HeytingLean
namespace Compiler
namespace TensorLogic

/-!
# TensorLogic bots

This layer provides a small “bot” interface on top of `Eval.run`, to make the
verified-vs-heuristic boundaries explicit (see `TRUST_CONTRACT.md`).
-/

inductive BotKind where
  | legacy     -- use `Eval.run` directly (compat)
  | monotone   -- boolean/heyting only (eps forced to 0)
  | fuzzy      -- fuzzy/heyting/boolean (heuristic when fuzzy)
  | f2linear   -- reserved for a restricted XOR solver (implemented separately)
  | f2solve    -- exact finite solver for general `Mode.f2` programs (capped search)
  | explain    -- like `legacy`, but returns a small explanation summary
  deriving Repr, BEq, DecidableEq

namespace BotKind

def ofString (raw : String) : Except String BotKind := do
  match raw.toLower with
  | "legacy" => pure .legacy
  | "monotone" => pure .monotone
  | "fuzzy" => pure .fuzzy
  | "f2linear" | "f2-linear" | "xor-linear" => pure .f2linear
  | "f2solve" | "f2-solve" | "xor-solve" | "xor" => pure .f2solve
  | "explain" | "trace" => pure .explain
  | _ => throw s!"unknown bot '{raw}'"

def toString : BotKind → String
  | .legacy => "legacy"
  | .monotone => "monotone"
  | .fuzzy => "fuzzy"
  | .f2linear => "f2linear"
  | .f2solve => "f2solve"
  | .explain => "explain"

end BotKind

structure EngineConfig where
  bot : BotKind := .legacy
  cfg : RunConfig := {}
  /-- Request stable ordering in user-facing outputs. -/
  deterministic : Bool := true
  /-- Request diagnostic information (when supported by the bot). -/
  trace : Bool := false

structure Explanation where
  bot : BotKind
  iters : Nat
  delta : Float
  converged : Bool
  rules : Nat
  deriving Repr

structure BotResult where
  run : RunResult
  explanation? : Option Explanation := none

private def mkExplanation (bot : BotKind) (p : Program) (r : RunResult) : Explanation :=
  { bot := bot
  , iters := r.iters
  , delta := r.delta
  , converged := r.converged
  , rules := p.rules.length
  }

def runBot (ec : EngineConfig) (p : Program) (init : Facts) : Except String BotResult := do
  match ec.bot with
  | .legacy =>
      let r := run ec.cfg p init
      let expl := if ec.trace then some (mkExplanation .legacy p r) else none
      pure { run := r, explanation? := expl }
  | .monotone =>
      let r ← Bots.runMonotone ec.cfg p init
      let expl := if ec.trace then some (mkExplanation .monotone p r) else none
      pure { run := r, explanation? := expl }
  | .fuzzy =>
      let r ← Bots.runFuzzy ec.cfg p init
      let expl := if ec.trace then some (mkExplanation .fuzzy p r) else none
      pure { run := r, explanation? := expl }
  | .f2linear =>
      let r ← Bots.runF2Linear ec.cfg p init
      let expl := if ec.trace then some (mkExplanation .f2linear p r) else none
      pure { run := r, explanation? := expl }
  | .f2solve =>
      let r ← Bots.runF2Solve ec.cfg p init
      let expl := if ec.trace then some (mkExplanation .f2solve p r) else none
      pure { run := r, explanation? := expl }
  | .explain =>
      let r ← Bots.runExplain ec.cfg p init
      pure { run := r, explanation? := some (mkExplanation .explain p r) }

end TensorLogic
end Compiler
end HeytingLean
