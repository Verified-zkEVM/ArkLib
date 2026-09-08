/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.VerifierSemantics
import Mathlib.LinearAlgebra.Pi

/-!
# Regression clients for the production packing verifier

A faithful tensor profile over a finite product ring tests the algebra without a domain
assumption. The verifier clients exercise zero multipliers, invalid source claims, absorbing
rejection, and the knowledge states at accidental roots.
-/
open RingSwitching Module MvPolynomial Sumcheck.Structured OracleSpec OracleComp ProtocolSpec
open Polynomial

noncomputable section
namespace RingSwitching.LegacyTest

abbrev I := Fin 1 → Fin 2
abbrev K := ZMod 2
abbrev L := I → K

def profile : RingSwitchingProfile K L 1 := binaryTowerProfile 1 K L (Pi.basisFun K I)

def oracles : AbstractOStmtIn L 1 where
  ιₛᵢ := Empty
  OStmtIn := fun i => nomatch i
  Oₛᵢ := fun i => nomatch i
  initialCompatibility := fun p => p.1 = 0

def emptyOracles : ∀ i, oracles.OStmtIn i := fun i => nomatch i

def ctx : RingSwitchingBaseContext 1 L K 2 profile := ⟨⟨0, 0⟩, 0, 0⟩

def start (target : L) : Statement (L := L) (ℓ := 1)
    (RingSwitchingBaseContext 1 L K 2 profile) 0 := ⟨target, Fin.elim0, ctx⟩

def finish (target : L) : Statement (L := L) (ℓ := 1)
    (RingSwitchingBaseContext 1 L K 2 profile) (Fin.last 1) := ⟨target, 1, ctx⟩

def affineCoords (z : L) (u : I) : L := fun v => if u = v then z v else 1

def diagonalCoords (z : L) (u : I) : L := fun v => if u = v then z v else 0

lemma affine_reconstruction (z : L) :
    ∑ u, affineCoords z u * (Pi.basisFun K I) u = z := by
  ext v
  simp [affineCoords, Pi.basisFun_apply, Pi.single_apply]

lemma diagonal_reconstruction (z : L) :
    ∑ u, diagonalCoords z u * (Pi.basisFun K I) u = z := by
  ext v
  simp [diagonalCoords, Pi.basisFun_apply, Pi.single_apply]

lemma affine_zero_invalid : affineCoords 0 ≠ 0 := by
  intro h
  have hc := congrFun (congrFun h (fun _ => 0)) (fun _ => 1)
  have hne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1) := by decide
  simp [affineCoords, hne] at hc

lemma diagonal_tuple_inverse_invalid :
    ¬ ∀ c : I → L, diagonalCoords (∑ u, c u * (Pi.basisFun K I) u) = c := by
  intro h
  have hc := congrFun (congrFun (h (fun _ => 1)) (fun _ => 0)) (fun _ => 1)
  have hne : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1) := by decide
  simp [diagonalCoords, hne] at hc

-- Genuine two-sided tensor coordinates reconstruct arbitrary tuples, even over a product ring.
example (c : I → L) :
    profile.decomposeRows (∑ u, profile.φ₀ (c u) * profile.φ₁ (profile.basis u)) = c :=
  profile.decomposeRows_recompose c

example : profile.decomposeRows 0 = 0 := profile.decomposeRows_zero

example : oracles.Functional := fun _ _ _ h₁ h₂ => h₁.trans h₂.symm

lemma final_multiplier_zero :
    compute_final_eq_value 1 L K profile 2 1 rfl 0 1 0 = 0 := by
  simp [compute_final_eq_value, compute_final_eq_tensor, eqTilde, eqWeightedCoordSum]

-- The accepted opening is 1 although the checked product is 0.
example :
    (SumcheckPhase.finalSumcheckVerifier 1 L K profile 2 1 rfl oracles).toVerifier.verify
      (finish 0, emptyOracles) (fun | ⟨0, _⟩ => (1 : L)) =
      pure (⟨1, 1⟩, emptyOracles) := by
  rw [final_verify]
  simp [finish, ctx, FullTranscript.messages, final_multiplier_zero]

lemma final_rejects :
    (SumcheckPhase.finalSumcheckVerifier 1 L K profile 2 1 rfl oracles).toVerifier.verify
      (finish 1, emptyOracles) (fun | ⟨0, _⟩ => (0 : L)) = failure := by
  rw [final_verify]
  simp [finish, FullTranscript.messages]

-- In particular, the valid opening of the zero polynomial cannot replace a failed check.
example : ((⟨0, 0⟩, emptyOracles), ⟨0⟩) ∈ AbstractOStmtIn.toRelInput L 1 oracles := by
  change (0 : L) = (MvPolynomial.eval 0) 0 ∧ (0 : MultilinearPoly L 1) = 0
  simp

lemma zero_packing : packMLE 1 L K 2 1 rfl profile.basis 0 = 0 := by
  apply Subtype.ext
  simp [packMLE, MLE]

example : BatchingPhase.batchingInputRelationProp 1 L K profile 2 1 rfl oracles
    ⟨0, 0⟩ emptyOracles ⟨0, 0⟩ := by
  simp [BatchingPhase.batchingInputRelationProp, zero_packing, oracles]

lemma batching_rejects :
    (BatchingPhase.oracleVerifier 1 L K profile 2 1 rfl oracles).toVerifier.verify
      (⟨0, 1⟩, emptyOracles) (FullTranscript.mk2 (0 : profile.A) (0 : Fin 1 → L)) = failure := by
  rw [batching_verify]
  simp [FullTranscript.messages, FullTranscript.mk2, performCheckOriginalEvaluation,
    eqWeightedCoordSum]

lemma projected_zero (i : Fin 2) (r : Fin i → L) :
    (projectToMidSumcheckPolyWithParam 1
      (RingSwitching_SumcheckMultParam 1 L K profile 2 1 rfl) ctx 0 i r).val = 0 := by
  simp [projectToMidSumcheckPolyWithParam, computeRoundPoly,
    RingSwitching_SumcheckMultParam, fixFirstVariablesOfMQP]

lemma zero_round_relation (i : Fin 2) (r : Fin i → L) :
    sumcheckRoundRelationProp 1 L K profile 2 1 rfl oracles i
      ⟨0, r, ctx⟩ emptyOracles ⟨0, 0⟩ := by
  simp [sumcheckRoundRelationProp, masterKStateProp, witnessStructuralInvariant,
    projected_zero, sumcheckConsistencyProp, oracles]

lemma one_target_has_no_witness (i : Fin 2) (r : Fin i → L)
    (wit : RingSwitching.SumcheckWitness L 1 i) :
    ¬ sumcheckRoundRelationProp 1 L K profile 2 1 rfl oracles i
      ⟨1, r, ctx⟩ emptyOracles wit := by
  rintro ⟨_, hH, hsum, hcompat⟩
  have ht : wit.t' = 0 := hcompat
  have hzero : wit.H.val = 0 := by
    change wit.H.val = _ at hH
    rw [ht] at hH
    exact hH.trans (projected_zero i r)
  have hbad : (1 : L) = 0 := by
    simpa only [sumcheckConsistencyProp, hzero, map_zero, Finset.sum_const_zero] using hsum
  exact one_ne_zero hbad

/-- A nonzero residual polynomial over zero remaining variables. -/
def residualOne : L⦃≤ 2⦄[X Fin 0] :=
  ⟨1, by rw [mem_restrictDegree_iff_degreeOf_le]; intro i; exact Fin.elim0 i⟩

lemma final_wrong_residual :
    ¬ SumcheckPhase.finalSumcheckKStateProp 1 L K profile 2 1 rfl oracles
      (m := 1) (fun | ⟨0, _⟩ => (0 : L)) (finish 0) ⟨0, residualOne⟩ emptyOracles := by
  simp [SumcheckPhase.finalSumcheckKStateProp, witnessStructuralInvariant,
    finish, projected_zero, residualOne]

def roundX : L⦃≤ 2⦄[X] := ⟨Polynomial.X, by simp [Polynomial.mem_degreeLE]⟩

lemma loop_rejects :
    (SumcheckPhase.iteratedSumcheckOracleVerifier 1 L K profile 2 1 oracles 0).toVerifier.verify
      (start 1, emptyOracles) (FullTranscript.mk2 (0 : L⦃≤ 2⦄[X]) (0 : L)) = failure := by
  rw [round_verify]
  simp [start, FullTranscript.messages, FullTranscript.mk2]

lemma loop_accidental_root :
    (SumcheckPhase.iteratedSumcheckOracleVerifier 1 L K profile 2 1 oracles 0).toVerifier.verify
      (start 1, emptyOracles) (FullTranscript.mk2 roundX (0 : L)) =
      pure (⟨0, 0, ctx⟩, emptyOracles) := by
  rw [round_verify]
  simp [start, roundX, FullTranscript.messages, FullTranscript.challenges, FullTranscript.mk2]
  rfl

lemma loop_accidental_root_knowledge :
    SumcheckPhase.iteratedSumcheckKStateProp 1 L K profile 2 1 rfl oracles 0 2
      (FullTranscript.mk2 roundX (0 : L)) (start 1) ⟨0, 0⟩ emptyOracles := by
  simp [SumcheckPhase.iteratedSumcheckKStateProp, witnessStructuralInvariant, start,
    projected_zero, oracles, getSumcheckRoundPoly, roundX, FullTranscript.mk2,
    Transcript.equivMessagesChallenges, Transcript.toMessagesChallenges,
    Transcript.toMessagesUpTo, Transcript.toChallengesUpTo]

local instance : ∀ i, OracleInterface ((pSpecFinalSumcheck L).Message i) := by
  change ∀ i, OracleInterface ((pSpecMessage L).Message i)
  infer_instance

local instance : ∀ i,
    OracleInterface (((pSpecFinalSumcheck L) ++ₚ !p[]).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend

-- An accepting identity verifier appended after the final step cannot revive rejection.
example :
    (OracleVerifier.append
      (SumcheckPhase.finalSumcheckVerifier 1 L K profile 2 1 rfl oracles)
      OracleVerifier.id).toVerifier.verify (finish 1, emptyOracles)
      ((fun | ⟨0, _⟩ => (0 : L)) ++ₜ (fun i => Fin.elim0 i)) = failure := by
  apply append_verify_failure
  convert final_rejects using 1
  congr 1

end RingSwitching.LegacyTest
