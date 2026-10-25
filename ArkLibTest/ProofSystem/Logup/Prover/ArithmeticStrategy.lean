/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Prover.ArithmeticStrategy
import ArkLibTest.ProofSystem.Logup.Prover.Completeness
import Lean.Compiler.IR

/-! # Actual measured default at the retained-source endpoint -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped ENNReal ProbabilityTheory
namespace ArithmeticStrategyTests
abbrev F := LogupStateTest.F

/-- External generic code selects all measured private phases through the actual default. -/
def caller {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n T ell : Nat}
    (f : B →+* E) (cfg : Logup.Interaction.Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :=
  Logup.Prover.Honest.prover f cfg data ambient

namespace Cubic
abbrev combined := LogupHonestTest.Cubic.combined
abbrev ambient := LogupHonestTest.Cubic.ambientSpec

def run : OracleComp ambient LogupHonestTest.Cubic.Result :=
  executeStrategiesLogged ambient combined.tree combined.roles combined.oracles
    LogupStateTest.access LogupStateTest.impl
    (Logup.Prover.Honest.prover (RingHom.id F) LogupStateTest.cfg LogupStateTest.data ambient)
    (Logup.Interaction.verifier (RingHom.id F) 1 2 1 LogupStateTest.cfg ambient
      (LogupHonestTest.Cubic.event 0) LogupHonestTest.Cubic.jointDraw
      (LogupHonestTest.Cubic.event 4) LogupStateTest.access LogupStateTest.view)

def summary (alpha : F) := LogupHonestTest.Cubic.summarize
  ((simulateQ (LogupHonestTest.Cubic.logger alpha) run).run [])
end Cubic

def uniform : ProbComp Bool :=
  Logup.Interaction.uniformExecute (RingHom.id F) 1 2 1 LogupStateTest.cfg
    LogupStateTest.access LogupStateTest.view LogupStateTest.impl
    (Logup.Prover.Honest.prover (RingHom.id F) LogupStateTest.cfg LogupStateTest.data unifSpec)

theorem uniform_failure : Pr{let accepted ← uniform}[accepted = false] ≤ (2 : ℝ≥0∞) / 17 := by
  unfold uniform
  rw [Logup.Prover.Honest.prover_eq_honestWith]
  exact LogupHonestTest.actual_uniform_failure

theorem uniform_success : (15 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniform}[accepted = true] := by
  unfold uniform
  rw [Logup.Prover.Honest.prover_eq_honestWith]
  exact LogupHonestTest.actual_uniform_success

theorem uniform_total : Pr{let _ ← uniform}[True] = 1 := by
  unfold uniform
  rw [Logup.Prover.Honest.prover_eq_honestWith]
  exact LogupHonestTest.actual_uniform_total

namespace TwoRound
open LogupHonestTest.TwoRound

def run (alpha : F) : OracleComp ambient Bool :=
  Logup.Interaction.execute (RingHom.id F) 2 2 1 cfg ambient (pure alpha)
    (pure ((![3, 7] : Fin 2 → F), (![4, 6] : Fin 2 → F))) round access view impl
    (Logup.Prover.Honest.prover (RingHom.id F) cfg data ambient)
def summary (alpha : F) : Bool × Nat := (simulateQ logger (run alpha)).run 0
end TwoRound

namespace ZeroRound
open LogupHonestTest.ZeroRound

def run (alpha : F) : OracleComp LogupHonestTest.TwoRound.ambient Bool :=
  Logup.Interaction.execute (RingHom.id F) 0 2 1 cfg LogupHonestTest.TwoRound.ambient
    (pure alpha) (pure (Fin.elim0, (![4, 6] : Fin 2 → F))) LogupHonestTest.TwoRound.round
    access view impl (Logup.Prover.Honest.prover (RingHom.id F) cfg data
      LogupHonestTest.TwoRound.ambient)
def summary (alpha : F) : Bool × Nat :=
  (simulateQ LogupHonestTest.TwoRound.logger (run alpha)).run 0
end ZeroRound

open Lean Elab Command in
run_cmd do
  unless Cubic.summary 2 ==
      (true, #[0, 2, 10, 5], #v[#v[9, 1], #v[-9, -1]], 9, [0, 1, 2, 3, 4]) do
    throwError "actual default lost the nonzero cubic, retained helper or source/effect order"
  unless Cubic.summary 0 ==
      (false, #[13, 10, 4, 7], #v[#v[0, -1], #v[0, 1]], 2, [0, 1, 2, 3]) do
    throwError "actual default retried a pole or sampled a native challenge after abort"
  unless TwoRound.summary 5 == (true, 2) && TwoRound.summary 0 == (false, 0) &&
      LogupHonestTest.TwoRound.originalFinal == 10 do
    throwError "two-round default failed original nonzero terminal-source authentication"
  unless ZeroRound.summary 2 == (true, 0) && ZeroRound.summary 0 == (false, 0) do
    throwError "zero-round default failed original-source terminal authentication"
  for name in #[``Logup.Prover.Honest.arithmeticBuilder, ``Logup.Prover.Honest.nativeArithmetic,
      ``Logup.Prover.Honest.startNativeArithmetic, ``Logup.Prover.Honest.prover,
      ``caller, ``Cubic.run, ``Cubic.summary, ``TwoRound.run, ``ZeroRound.run, ``uniform] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable default compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.Prover.Honest.arithmeticBuilder_eq_pureBuilder,
      ``Logup.Prover.Honest.nativeArithmetic_eq_nativeWith,
      ``Logup.Prover.Honest.startNativeArithmetic_eq_nativeWith,
      ``Logup.Prover.Honest.prover_eq_honestWith,
      ``uniform_failure, ``uniform_success, ``uniform_total] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected default correctness axiom in `{name}`"
  logInfo "measured weighted default: cubic, poles, n0/n2 and uniform bounds passed"

end ArithmeticStrategyTests
