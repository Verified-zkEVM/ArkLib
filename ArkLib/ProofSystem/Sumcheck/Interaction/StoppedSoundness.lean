/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.StateRestorationSoundness
public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget

/-!
# Sumcheck with challenge queries stopped by failed sum checks

The sum guard is evaluated before querying its field challenge. It uses the current public
polynomial and the current target; a failed guard stops every remaining challenge query.
The certificate is the existing ordinary truth predicate with a Unit witness. Consequently,
this application proves ordinary soundness, not a substantive knowledge-extraction claim.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal

namespace Sumcheck.Interaction.Restoration

open SingleRound MultivariateRound
open Interaction.Oracle.Security.StateRestoration

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n deg : ℕ)

/-- The actual Sumcheck sum test, before the challenge for this polynomial is requested. -/
noncomputable def sumcheckGuards {Input Salt : Type} {m : ℕ} (D : Fin m ↪ F) :
    (count start : ℕ) → (finish : start + count = n) →
    (Input → Spec.StatementRound F n ⟨start, by omega⟩) →
    GuardSchedule Input Salt (rounds F deg count)
  | 0, _, _, _ => PUnit.unit
  | count + 1, start, _, stmt =>
      (fun z q _ => decide
        (((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = (stmt z).target),
       fun q _ r => sumcheckGuards D count (start + 1) (by omega)
         (fun z => ⟨q.val.eval r, Fin.snoc (stmt z).challenges r⟩))

variable {Input Salt : Type} [DecidableEq Input] [DecidableEq Salt]
variable {m : ℕ} (D : Fin m ↪ F)
variable (A : PFunctor)
variable (stmt : Input → Spec.StatementRound F n ⟨0, by omega⟩)
variable (p : Input → Spec.OracleStatement F n deg ())
variable (originalOracle : Input →
  VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
variable (impl : Input → QueryImpl (OracleSpec.ofPFunctor A) Id)

/-- A stopped accepted path has a false initial claim and a true actual closed native output. -/
def stoppedFalseAccepts :
    Option (Input × (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath ×
      Unit) → Prop
  | none => False
  | some (z, path, _) =>
      ¬ initialClaimTrue F n deg D stmt p z ∧
        ∃ output, nativeObservedOutput F n deg D A stmt originalOracle impl z path =
          some output ∧ Native.outputRelation F n deg output

/-- The certificate bounds false acceptance by distinct queries of the actual stopped program.
The stateless source handler is matched to the original polynomial realization explicitly. -/
theorem stoppedSumcheck_expected_soundness
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg n)) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) adversary) ∅)}[
      stoppedFalseAccepts F n deg D A stmt p originalOracle impl joint.1.1.1] ≤
    expectedFreshQueryCharge
      (randomizedStoppedRestoredExecutionWithAdversaryLog (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) adversary)
      (keyError (fun _ : Fin (rounds F deg n).length => fieldError F deg)) := by
  let state := fun z => claimState F n deg D ⟨0, by omega⟩ (stmt z) (p z) True
  let extractor := fun z => certificate F n deg D (p z) n 0 (by omega) (stmt z) True
  let Rin := fun z (_ : Unit) => initialClaimTrue F n deg D stmt p z
  let Rout := fun z path (_ : Unit) =>
    ∃ output, nativeObservedOutput F n deg D A stmt originalOracle impl z path =
      some output ∧ Native.outputRelation F n deg output
  let terminalWitness := fun z path =>
    terminalWitnessEquiv F n deg D (p z) n 0 (by omega) (stmt z) True path
  have howner := randomizedStopped_badRelation_le_expectedFreshCharge
    (rounds F deg n) (sumcheckGuards F n deg D n 0 (by omega) stmt)
    (fun _ => fieldError F deg) adversary state extractor Set.univ
    (by intro z _; exact certificate_preserving F n deg D (p z) n 0 (by omega) (stmt z) True)
    (by intro z _; exact certificate_bounded_constant F n deg D (p z) (stmt z))
    Rin Rout (fun z path => (terminalWitness z path).toFun)
    (by intro z w; exact initial_certificate_holds_iff F n deg D stmt p z w)
    (by intro z path w
        exact (terminal_certificate_holds_iff_native F n deg D A stmt p originalOracle impl
          sourceLaw z path w).mpr)
  have hevent := prEvent_congr
    (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) adversary) ∅)
    (fun joint => stoppedFalseAccepts F n deg D A stmt p originalOracle impl joint.1.1.1)
    (fun joint => badStoppedRelation state extractor Rin Rout
      (fun z path => (terminalWitness z path).toFun) Set.univ joint.1.1.1)
    (by
      intro joint
      cases h : joint.1.1.1 with
      | none => rfl
      | some selected =>
          rcases selected with ⟨z, path, witness⟩
          simp only [stoppedFalseAccepts, badStoppedRelation, Set.mem_univ, true_and]
          exact and_comm)
  exact hevent.le.trans howner

/-- The expected Sumcheck bound charges only challenge rounds actually reached by the verifier.
Its coarse consequence is the usual field error times the expected adversary cost plus `n`. -/
theorem stoppedSumcheck_expected_round_bound
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p z))
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg n)) :
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedStoppedRestoredExecutionWithAdversaryLog (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) adversary) ∅)}[
      stoppedFalseAccepts F n deg D A stmt p originalOracle impl joint.1.1.1] ≤
      fieldError F deg * expectedAdversaryFreshKeys (rounds F deg n) adversary +
        expectedStoppedVerifierRoundCost (rounds F deg n)
          (sumcheckGuards F n deg D n 0 (by omega) stmt) (fun _ => fieldError F deg)
          adversary ∧
    expectedStoppedVerifierRoundCost (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) (fun _ => fieldError F deg)
        adversary ≤ (n : ENNReal) * fieldError F deg := by
  have hcost := expectedStoppedFreshCharge_le_actualRounds (rounds F deg n)
    (sumcheckGuards F n deg D n 0 (by omega) stmt) (fun _ => fieldError F deg) adversary
  rw [expectedStoppedJointAdversaryKeys_eq_expectedAdversaryFreshKeys] at hcost
  have hmax : Finset.univ.sup
      (fun _ : Fin (rounds F deg n).length => fieldError F deg) ≤ fieldError F deg :=
    Finset.sup_le fun _ _ => le_rfl
  constructor
  · apply ((stoppedSumcheck_expected_soundness F n deg D A stmt p originalOracle impl
      sourceLaw adversary).trans hcost).trans
    gcongr
  · simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      rounds_length] using
      expectedStoppedVerifierRoundCost_le_sum (rounds F deg n)
        (sumcheckGuards F n deg D n 0 (by omega) stmt) (fun _ => fieldError F deg) adversary

end Sumcheck.Interaction.Restoration
