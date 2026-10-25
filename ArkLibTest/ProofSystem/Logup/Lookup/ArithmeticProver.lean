/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.ArithmeticProver
import ArkLibTest.ProofSystem.Logup.Lookup.Completeness
import Lean.Compiler.IR

/-! # Actual histogram sender composed with the measured weighted default -/

open Interaction.Oracle OracleComp OracleSpec CompPoly
open scoped ENNReal ProbabilityTheory
namespace ArithmeticLookupTests
namespace Small
open LogupScalarHonestTest.Small

def run (witness : Vector (Fin 4) 2) : OracleComp ambient Result :=
  executeStrategiesLogged ambient combined.tree combined.roles combined.oracles access impl
    (Logup.Lookup.Honest.prover f cfg data witness ambient)
    (Logup.Lookup.verifier f 1 1 2 1 cfg ambient (event 0) joint (event 5) access view)
def summary (alpha : F) (witness : Vector (Fin 4) 2 := indices) :=
  summarize ((simulateQ (logger alpha) (run witness)).run [])

def uniform : ProbComp Bool := Logup.Lookup.uniformExecute f 1 1 2 1 cfg access view impl
  (Logup.Lookup.Honest.prover f cfg data indices unifSpec)

theorem uniform_failure : Pr{let accepted ← uniform}[accepted = false] ≤ (3 : ℝ≥0∞) / 17 := by
  unfold uniform
  rw [Logup.Lookup.Honest.prover_eq_proverWith]
  exact failure

theorem uniform_success : (14 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniform}[accepted = true] := by
  unfold uniform
  rw [Logup.Lookup.Honest.prover_eq_proverWith]
  exact success

theorem uniform_total : Pr{let _ ← uniform}[True] = 1 := by
  unfold uniform
  rw [Logup.Lookup.Honest.prover_eq_proverWith]
  exact total
end Small

namespace TwoRound
open LogupScalarHonestTest.TwoRound

def run : OracleComp ambient Bool := Logup.Lookup.execute f 2 2 1 1 cfg ambient (pure 5)
  (pure ((![3, 7] : Fin 2 → F), (![4, 9, 6] : Fin 3 → F))) round access view impl
  (Logup.Lookup.Honest.prover f cfg data indices ambient)
def summary : Bool × Nat := (simulateQ logger run).run 0
end TwoRound

namespace ZeroRound
open LogupScalarHonestTest.ZeroRound

def run (alpha : F) : OracleComp ambient Bool := Logup.Lookup.execute f 0 1 2 1 cfg ambient
  (pure alpha) (pure (Fin.elim0, (![4, 9, 6] : Fin 3 → F))) round access view impl
  (Logup.Lookup.Honest.prover f cfg data indices ambient)
def summary (alpha : F) : Bool × Nat := (simulateQ logger (run alpha)).run 0
end ZeroRound

namespace NoQueries
open LogupScalarHonestTest.NoQueries

def run (alpha : F) : OracleComp LogupScalarHonestTest.ZeroRound.ambient Bool :=
  Logup.Lookup.execute f 1 0 1 1 cfg LogupScalarHonestTest.ZeroRound.ambient (pure alpha)
    (pure ((fun _ => 2), (fun _ => 4))) LogupScalarHonestTest.ZeroRound.round access view impl
    (Logup.Lookup.Honest.prover f cfg data indices LogupScalarHonestTest.ZeroRound.ambient)
def summary (alpha : F) : Bool × Nat :=
  (simulateQ LogupScalarHonestTest.ZeroRound.logger (run alpha)).run 0
end NoQueries

open Lean Elab Command in
run_cmd do
  unless Small.summary 2 ==
      (true, (#v[#v[0, 0], #v[1, 1]], #[0, 9, 11, 14]), 11, [0, 1, 2, 3, 4, 5]) &&
      Small.summary 3 ==
      (true, (#v[#v[0, 0], #v[1, 1]], #[0, 2, 10, 5]), 11, [0, 1, 2, 3, 4, 5]) do
    throwError "actual scalar default changed histogram, cubic or unused-pole acceptance"
  unless Small.summary 5 ==
      (false, (#v[#v[0, 0], #v[1, 1]], #[13, 10, 4, 7]), 2, [0, 1, 2, 3, 4]) &&
      !(Small.summary 2 #v[0, 1]).1 do
    throwError "actual scalar default lost active-pole abort or invalid-index rejection"
  unless TwoRound.summary == (true, 2) && LogupScalarHonestTest.TwoRound.originalFinal == 21 do
    throwError "actual two-round scalar default lost nonzero terminal Q21"
  unless ZeroRound.summary 2 == (true, 0) && ZeroRound.summary 7 == (false, 0) &&
      ZeroRound.summary 5 == (true, 0) do
    throwError "zero-round scalar default changed active/unused poles or terminal authentication"
  for alpha in List.finRange 17 do
    unless NoQueries.summary (alpha.val : LogupScalarHonestTest.NoQueries.F) == (true, 1) do
      throwError "empty-query measured default failed at a pole"
  for name in #[``Logup.Lookup.Honest.prover, ``Small.run, ``Small.uniform,
      ``TwoRound.run, ``ZeroRound.run, ``NoQueries.run] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected actual scalar default compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.Lookup.Honest.prover_eq_proverWith,
      ``Small.uniform_failure, ``Small.uniform_success, ``Small.uniform_total] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected actual scalar default axiom in `{name}`"
  logInfo "measured scalar default: histogram, n0/n1/n2, poles, empty query and bounds passed"

end ArithmeticLookupTests
