/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.BatchedFri.Security
import Mathlib.Algebra.Field.ZMod

/-!
# Batched FRI acceptance tests

Check virtual batching, executable witness combination, rejection of an invalid word,
nonvacuous soundness parameters, and the axioms of the round security theorems.
-/

open Domain BatchedFri.Spec BatchedFri.Spec.BatchingRound
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

example : (batchVerifier (ω := domain) schedule 1).toVerifier.IsGuarded := inferInstance

-- With no coefficients, the original word is preserved at every coordinate.
example (os : ∀ j, OracleStatement 0 domain j) (cs : Fin 0 → ZMod 17)
    (x : (domain.subdomain 0).toFinset) :
    combinedOracle schedule 0 cs os 0 x = os 0 (initialDomainPoint schedule 0 x) := by
  simp [combinedOracle]

private def twoWords : ∀ j, OracleStatement 1 domain j := fun i _ ↦ if i = 0 then 0 else 1

-- The implemented virtual oracle depends on the coefficient when m = 1.
example : combinedOracle schedule 1 (fun _ ↦ 0) twoWords 0 (Fri.Spec.initialQuery 0) = 0 := by
  decide +kernel

example : combinedOracle schedule 1 (fun _ ↦ 1) twoWords 0 (Fri.Spec.initialQuery 0) = 1 := by
  decide +kernel

run_cmd do
  unless combinedOracle schedule 1 (fun _ ↦ 7) twoWords 0 (Fri.Spec.initialQuery 0) == 7 do
    throwError "The virtual word returned an incorrect batched coordinate."

private def zeroWitnesses : Witness (ZMod 17) schedule 1 1 :=
  fun _ ↦ ⟨0, CompPoly.CPolynomial.zero_mem_degreeLT _⟩

-- The extracted honest witness computation also runs as executable code.
run_cmd do
  unless (combinedWitness schedule 1 1 (fun _ ↦ 7) zeroWitnesses).val.eval 3 == 0 do
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
example :
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

end BatchedFriTest

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
