/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.BatchedFri.EndToEnd
import Mathlib.Algebra.Field.ZMod

/-!
# Batched FRI acceptance tests

Check virtual batching, executable witness combination, rejection of an invalid word,
nonvacuous soundness parameters, and the axioms of the round security theorems.
-/

open CoreDefinitions OracleSpec Domain BatchedFri.Spec BatchedFri.Spec.BatchingRound
open scoped NNReal

namespace BatchedFriTest

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private instance : NonBinaryField (ZMod 17) where
  toField := inferInstance
  char_neq_2 := by decide

private def root : (ZMod 17)ˣ := ⟨4, 13, by decide, by decide⟩

private def domain : SmoothCosetFftDomain 2 (ZMod 17) where
  subgroupDomain :=
    { toFun := fun i ↦ root ^ i.toAdd.val
      map_one' := by decide
      map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := ⟨3, 6, by decide, by decide⟩

private def schedule : Fin 1 → ℕ+ := fun _ ↦ 1

example :
    (batchVerifier (ω := domain) schedule 1
      (AffineSpaceGenerator (ZMod 17) 1)).toVerifier.IsGuarded :=
  inferInstance

-- With no coefficients, the original word is preserved at every coordinate.
example (os : ∀ j, OracleStatement 0 domain j) (cs : Fin 0 → ZMod 17)
    (x : (domain.subdomain 0).toFinset) :
    combinedOracle schedule 0 (AffineSpaceGenerator (ZMod 17) 0) cs os 0 x =
      os 0 (initialDomainPoint schedule 0 x) := by
  simp [combinedOracle, AffineSpaceGenerator, List.finRange_succ]

private def twoWords : ∀ j, OracleStatement 1 domain j := fun i _ ↦ if i = 0 then 0 else 1

-- The implemented virtual oracle depends on the coefficient when m = 1.
example : combinedOracle schedule 1 (AffineSpaceGenerator (ZMod 17) 1) (fun _ ↦ 0)
    twoWords 0 (Fri.Spec.initialQuery 0) = 0 := by
  decide +kernel

example : combinedOracle schedule 1 (AffineSpaceGenerator (ZMod 17) 1) (fun _ ↦ 1)
    twoWords 0 (Fri.Spec.initialQuery 0) = 1 := by
  decide +kernel

run_cmd do
  unless combinedOracle schedule 1 (AffineSpaceGenerator (ZMod 17) 1) (fun _ ↦ 7)
    twoWords 0 (Fri.Spec.initialQuery 0) == 7 do
    throwError "The virtual word returned an incorrect batched coordinate."

private def zeroWitnesses : Witness (ZMod 17) schedule 1 1 :=
  fun _ ↦ ⟨0, CompPoly.CPolynomial.zero_mem_degreeLT _⟩

-- The extracted honest witness computation also runs as executable code.
run_cmd do
  unless (combinedWitness schedule 1 1 (AffineSpaceGenerator (ZMod 17) 1) (fun _ ↦ 7)
      zeroWitnesses).val.eval 3 == 0 do
    throwError "The combined zero polynomial evaluated to a nonzero value."

-- A word supported at just one of four coordinates cannot be the evaluation of a
-- degree-<2 polynomial. This rejects every possible input witness, not just zero.
private def badWords : ∀ j, OracleStatement 0 domain j :=
  fun _ x ↦ if x.val = 3 then 1 else 0

example : ((), badWords) ∉ (BatchingRound.inputRelation schedule 1 0 0).language := by
  intro h
  obtain ⟨ps, S, hS, hagree⟩ := (Set.mem_language_iff _ _).mp h
  have hScard : (Finset.univ : Finset (Fin 4)).card ≤ S.card := by
    exact_mod_cast (show (4 : ℝ≥0) ≤ S.card by simpa using hS)
  have hSuniv : S = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ S) hScard
  have heval (z : Fin 4) : (ps 0).1.toPoly.eval (domain z) =
      if domain z = 3 then 1 else 0 := by
    have hz := hagree 0 z (by rw [hSuniv]; exact Finset.mem_univ _)
    rw [CompPoly.CPolynomial.eval_toPoly] at hz
    exact hz.symm
  have h₁ : domain 1 = 12 := by decide
  have h₂ : domain 2 = 14 := by decide
  have hd : (ps 0).1.toPoly.degree < 2 := by
    have hd : (ps 0).1.toPoly ∈ Polynomial.degreeLT (ZMod 17)
        (2 ^ (∑ i : Fin 1, (schedule i).val) * (1 : ℕ+).val) :=
      CompPoly.CPolynomial.degreeLT_toPoly.mp (ps 0).2
    rw [show 2 ^ (∑ i : Fin 1, (schedule i).val) * (1 : ℕ+).val = 2 by decide] at hd
    exact Polynomial.mem_degreeLT.mp hd
  have hpzero : (ps 0).1.toPoly = 0 := by
    by_cases hp : (ps 0).1.toPoly = 0
    · exact hp
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      _ ({12, 14} : Finset (ZMod 17))
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa only [h₁, ite_eq_right (by decide : (12 : ZMod 17) ≠ 3)] using heval 1
      · simpa only [h₂, ite_eq_right (by decide : (14 : ZMod 17) ≠ 3)] using heval 2
    · rw [show ({12, 14} : Finset (ZMod 17)).card = 2 by decide]
      exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hd
  have h₀ : domain 0 = 3 := by decide
  have hz := heval 0
  rw [hpzero] at hz
  norm_num [h₀] at hz

-- The soundness premises have a nontrivial small-field instance: rate 1/2,
-- radius 1/8, and affine-space error 4/17 < 1.
private theorem toyParameters :
    (1 / 8 : ℝ≥0) < 1 - ReedSolomon.sqrtRate 2 (domain : Fin 4 ↪ ZMod 17) ∧
    ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17) = 4 / 17 ∧
    ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17) < 1 := by
  have hcut : (1 - (1 / 2 : ℝ≥0)) / 2 = 1 / 4 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_div, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
    norm_num
  have herr : ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17) = 4 / 17 := by
    norm_num [ProximityGap.errorBound, ReedSolomon.rateOfLinearCode_eq_min_div, hcut]
  refine ⟨?_, herr, by rw [herr]; norm_num⟩
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub (ReedSolomon.sqrtRate_le_one _ _)]
  have hsq : (ReedSolomon.sqrtRate 2 (domain : Fin 4 ↪ ZMod 17) : ℝ) ^ 2 = 1 / 2 := by
    rw [ReedSolomon.sqrtRate_sq]
    norm_num
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at ⊢
  nlinarith

-- The public ordinary-soundness API applies with all premises discharged together.
noncomputable local instance : SampleableType (ZMod 17) := SampleableType.ofFintype _

example {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchVerifier (ω := domain) schedule 1 (AffineSpaceGenerator (ZMod 17) 1)).soundness init impl
      (BatchingRound.inputRelation schedule 1 1 (1 / 8)).language
      (BatchingRound.outputRelation schedule 1 (by decide) (1 / 8)).language
      (ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17)) := by
  apply soundness_affineSpace schedule 1 1 (by decide) (1 / 8) (by norm_num)
  exact toyParameters.1

-- The composite API accepts the same concrete domain, schedule, and radius.
example {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := domain) 0 schedule 1 (by decide) 1 1
      (AffineSpaceGenerator (ZMod 17) 1)).verifier.soundness
      init impl (BatchingRound.inputRelation schedule 1 1 (1 / 8)).language
      (Fri.Spec.outputRelation 0 schedule 1 (by decide) (1 / 8)).language
      (ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17) +
        Fri.Spec.soundnessError (ω := domain) schedule 1 1 (1 / 2) (1 / 8)) := by
  exact batchedFRI_soundness_affineSpace schedule 1 (by decide) 1 1 (1 / 2) (1 / 8)
    (by norm_num) toyParameters.1 init impl

-- Powers and tensor monomials execute at the same virtual-oracle interface.
private def fourWords : ∀ j, OracleStatement 3 domain j := fun i _ => (i.val + 1 : ℕ)

example : combinedOracle schedule 3 (univariatePowersGenerator (ZMod 17) 3)
    2 fourWords 0 (Fri.Spec.initialQuery 0) = 15 := by
  decide +kernel

example : combinedOracle schedule 3 (multilinearBatchGenerator (ZMod 17) 2)
    ![2, 3] fourWords 0 (Fri.Spec.initialQuery 0) = 3 := by
  decide +kernel

run_cmd do
  unless combinedOracle schedule 3 (multilinearBatchGenerator (ZMod 17) 2)
      ![2, 3] fourWords 0 (Fri.Spec.initialQuery 0) == 3 do
    throwError "The tensor monomial combination has the wrong coefficient order."

example {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := domain) 0 schedule 1 (by decide) 1 3
      (univariatePowersGenerator (ZMod 17) 3)).verifier.soundness
      init impl (BatchingRound.inputRelation schedule 1 3 (1 / 8)).language
      (Fri.Spec.outputRelation 0 schedule 1 (by decide) (1 / 8)).language
      (3 * ProximityGap.errorBound (1 / 8) 2 (domain : Fin 4 ↪ ZMod 17) +
        Fri.Spec.soundnessError (ω := domain) schedule 1 1 (1 / 2) (1 / 8)) := by
  exact batchedFRI_soundness_powers schedule 1 (by decide) 1 3 (1 / 2) (1 / 8)
    (by norm_num) toyParameters.1 init impl

private theorem toyUniqueDecoding : (1 / 8 : ℝ≥0) ≤
    Code.relativeUniqueDecodingRadius (ReedSolomon.code (domain : Fin 4 ↪ ZMod 17) 2).carrier := by
  have hd : Code.dist (ReedSolomon.code (domain : Fin 4 ↪ ZMod 17) 2).carrier = 3 :=
    ReedSolomon.dist_eq_of_le (by decide)
  change (1 / 8 : ℝ≥0) ≤ ((Code.dist
    (ReedSolomon.code (domain : Fin 4 ↪ ZMod 17) 2).carrier : ℝ≥0) - 1) / 2 / 4
  rw [hd]
  have hs : (3 : ℝ≥0) - 1 = 2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num)]
    norm_num
  norm_num [hs]
  apply NNReal.coe_le_coe.mp
  norm_num

example {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (batchedFRIreduction (ω := domain) 0 schedule 1 (by decide) 1 3
      (multilinearBatchGenerator (ZMod 17) 2)).verifier.soundness
      init impl (BatchingRound.inputRelation schedule 1 3 (1 / 8)).language
      (Fri.Spec.outputRelation 0 schedule 1 (by decide) (1 / 8)).language
      (2 * (4 / 17) + Fri.Spec.soundnessError (ω := domain) schedule 1 1 (1 / 2) (1 / 8)) := by
  simpa only [ZMod.card, Nat.cast_ofNat, Nat.reducePow, Nat.reduceSub,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    show (2 : ℝ≥0) ^ 2 = 4 by norm_num] using
    batchedFRI_soundness_multilinear schedule 1 (by decide) 1 2 (1 / 2) (1 / 8)
    (by norm_num) toyUniqueDecoding init impl

end BatchedFriTest

/--
info: 'BatchedFri.Spec.batchedFRI_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_soundness

/--
info: 'BatchedFri.Spec.BatchingRound.combined_mem_outputRelation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.combined_mem_outputRelation

/--
info: 'BatchedFri.Spec.BatchingRound.perfect_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.perfect_completeness

/--
info: 'BatchedFri.Spec.BatchingRound.batching_error' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.batching_error

/--
info: 'BatchedFri.Spec.BatchingRound.round_soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.round_soundness

/--
info: 'BatchedFri.Spec.BatchingRound.soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.soundness

/--
info: 'ProximityGap.correlatedAgreement_affine_coefficients' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.correlatedAgreement_affine_coefficients

/--
info: 'Fri.Spec.relHammingDist_le_of_mem_inputRelation' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.relHammingDist_le_of_mem_inputRelation

/--
info: 'BatchedFri.Spec.batchedFRI_perfectCompleteness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_perfectCompleteness

/--
info: 'BatchedFri.Spec.batchedFRI_soundness_affineSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_soundness_affineSpace

/--
info: 'BatchedFri.Spec.batchedFRI_soundness_powers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_soundness_powers

/--
info: 'BatchedFri.Spec.batchedFRI_soundness_multilinear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_soundness_multilinear

/--
info: 'ProximityGap.caError_affineSpace_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_affineSpace_le

/--
info: 'ProximityGap.caError_powers_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_powers_le

/--
info: 'ProximityGap.caError_multilinear_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_multilinear_le

/--
info: 'ProximityGap.caError_multilinearBatch_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_multilinearBatch_le

/--
info: 'CoreDefinitions.isMCAGenerator_multilinear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CoreDefinitions.isMCAGenerator_multilinear

/--
info: 'BatchedFri.Spec.BatchingRound.batching_error_affineSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.batching_error_affineSpace

/--
info: 'BatchedFri.Spec.BatchingRound.round_soundness_affineSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.round_soundness_affineSpace

/--
info: 'BatchedFri.Spec.BatchingRound.soundness_affineSpace' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.soundness_affineSpace

/--
info: 'BatchedFri.Spec.BatchingRound.batching_error_powers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.batching_error_powers

/--
info: 'BatchedFri.Spec.BatchingRound.round_soundness_powers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.round_soundness_powers

/--
info: 'BatchedFri.Spec.BatchingRound.soundness_powers' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.soundness_powers

/--
info: 'BatchedFri.Spec.BatchingRound.round_soundness_multilinear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.round_soundness_multilinear

/--
info: 'BatchedFri.Spec.BatchingRound.soundness_multilinear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.soundness_multilinear

/--
info: 'ProximityGap.caError_multilinearBatch_le_of_mca' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_multilinearBatch_le_of_mca

/--
info: 'ProximityGap.caError_multilinearBatch_le_johnson' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.caError_multilinearBatch_le_johnson

/--
info: 'BatchedFri.Spec.BatchingRound.soundness_multilinear_johnson' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.BatchingRound.soundness_multilinear_johnson

/--
info: 'BatchedFri.Spec.batchedFRI_soundness_multilinear_johnson' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BatchedFri.Spec.batchedFRI_soundness_multilinear_johnson

/--
info: 'ProximityGap.relativeUniqueDecodingRadius_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ProximityGap.relativeUniqueDecodingRadius_le_one
