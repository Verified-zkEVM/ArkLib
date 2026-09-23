/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for symbolic equations on the rational Taylor chart

These examples specialize algebra-valued equations to fields and exercise regular and singular
initial jets, as well as sufficient and insufficient denominator exponents.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

private abbrev parameterEquation : DifferentialPolynomial (Polynomial ℚ) 1 := X (some 1)

private abbrev rationalId : ℚ →ₐ[ℚ] ℚ := AlgHom.id ℚ ℚ

/-- Specializing a parameter in an algebra-valued cut gives the field-valued cut with the same
explicit exponent. -/
example (a : ℚ) (τ : ℕ) :
    map (Polynomial.aeval a).toRingHom
        (taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ) parameterEquation 2
          Polynomial.X Polynomial.X (τ := τ)) =
      taylorAgreementEquation (0 : ℚ) (X (some 1) : DifferentialPolynomial ℚ 1)
        2 τ a a := by
  simpa using map_taylorAgreementEquationOver_eq (F := ℚ) (Polynomial.aeval a)
    (0 : Polynomial ℚ) parameterEquation 2 Polynomial.X Polynomial.X τ

/-- The mapped initial equation evaluates as the mapped differential polynomial. -/
example (a : ℚ) (jet : Fin 2 → ℚ) :
    aeval jet (map (Polynomial.aeval a).toRingHom
      (initialJetEquation (0 : Polynomial ℚ) parameterEquation)) =
      jetEvaluation (map (Polynomial.aeval a).toRingHom parameterEquation) 0 jet := by
  simpa using aeval_map_initialJetEquation (Polynomial.aeval a).toRingHom
    (0 : Polynomial ℚ) parameterEquation jet

private abbrev constantJetEquation : DifferentialPolynomial ℚ 1 := X (some 1)

private def constantJet : Fin 2 → ℚ := fun i ↦ if i.val = 0 then 1 else 0

/-- At the regular jet `(1, 0)`, the symbolic agreement equation vanishes at the value `1`. -/
example :
    aeval constantJet
        (map rationalId.toRingHom
          (taylorAgreementEquationOver (F := ℚ) 0 constantJetEquation 1 4 1)) = 0 := by
  have hS : aeval constantJet
      (map rationalId.toRingHom (initialJetSeparant 0 constantJetEquation)) ≠ 0 := by
    norm_num [rationalId, map_initialJetSeparant, initialJetSeparant, separant,
      constantJetEquation, constantJet]
  apply (aeval_map_taylorAgreementEquationOver_eq_zero_iff (F := ℚ) rationalId
    0 constantJetEquation 1 constantJet hS 4 1).2
  have h0 : rationalTaylorCoefficient 0 constantJetEquation constantJet 0 = 1 := by
    simpa [constantJet] using
      rationalTaylorCoefficient_initial 0 constantJetEquation constantJet ⟨0, by omega⟩
  rw [eval_rationalTaylorPolynomial, Fin.sum_univ_one]
  simp [h0]

private abbrev singularEquation : DifferentialPolynomial ℚ 1 :=
  X (some 1) ^ 2

/-- The separant vanishes at the zero jet for `(y')² = 0`. -/
private theorem jetEvaluation_separant_singularEquation :
    jetEvaluation (separant singularEquation (Fin.last 1)) 0 (![0, 0] : Fin 2 → ℚ) = 0 := by
  simp [jetEvaluation, separant, singularEquation, pderiv_X, Fin.last]

/-- At a singular jet the agreement equation can vanish although the reconstruction does not
take the prescribed value. -/
example : TaylorExponentSufficient 1 2 1 ∧
    aeval (![0, 0] : Fin 2 → ℚ) (taylorAgreementEquation 0 singularEquation 2 1 0 1) = 0 ∧
    (rationalTaylorPolynomial 0 singularEquation 2 ![0, 0]).eval 0 ≠ 1 := by
  refine ⟨fun l ↦ by have := l.isLt; omega, ?_, ?_⟩
  · have hS : aeval (![0, 0] : Fin 2 → ℚ) (initialJetSeparant 0 singularEquation) = 0 := by
      rw [aeval_initialJetSeparant, jetEvaluation_separant_singularEquation]
    simp only [taylorAgreementEquation, commonTaylorNumerator, Fin.sum_univ_two, map_sub,
      map_add, map_mul, map_pow, hS]
    simp
  · have h0 : rationalTaylorCoefficient 0 singularEquation ![0, 0] 0 = 0 := by
      simpa using rationalTaylorCoefficient_initial 0 singularEquation ![0, 0] 0
    have h1 : rationalTaylorCoefficient 0 singularEquation ![0, 0] 1 = 0 := by
      simpa using rationalTaylorCoefficient_initial 0 singularEquation ![0, 0] 1
    simp [eval_rationalTaylorPolynomial, Fin.sum_univ_two, h0, h1]

/-- The exponent zero is insufficient for a length-two chart of order zero. -/
example :
    ¬TaylorExponentSufficient 0 2 0 := by
  intro hτ
  have h := hτ ⟨1, by omega⟩
  norm_num at h

private abbrev scaledEquation : DifferentialPolynomial ℚ 0 :=
  C (2 : ℚ) * X (some 0) - X none

private abbrev scaledSolution : Polynomial ℚ := Polynomial.C (1 / 2 : ℚ) * Polynomial.X

private def zeroJet0 : Fin 1 → ℚ := fun _ ↦ 0

/-- The scaled equation is solved by the linear polynomial `X / 2`. -/
private theorem scaledSolution_sol :
    differentialSpecialization scaledEquation scaledSolution = 0 := by
  simp only [differentialSpecialization, differentialSpecializationHom, Nat.reduceAdd,
    Fin.val_eq_zero, Polynomial.hasseDeriv_zero, scaledSolution, one_div, LinearMap.id_coe,
    id_eq, scaledEquation, Fin.isValue, map_sub, map_mul, algHom_C,
    Polynomial.algebraMap_eq, aeval_X]
  rw [← mul_assoc, ← Polynomial.C_mul]
  norm_num

/-- The separant of the scaled equation is `2` at the zero jet. -/
private theorem initialJetSeparant_scaledEquation :
    aeval zeroJet0 (initialJetSeparant 0 scaledEquation) = 2 := by
  norm_num [initialJetSeparant, separant, scaledEquation, zeroJet0]

/-- At exponent zero the agreement cut is `1`, while the reconstructed discrepancy is `1 / 2`;
the sufficient exponent condition is therefore needed. -/
example :
    aeval zeroJet0 (taylorAgreementEquation 0 scaledEquation 2 0 1 0) ≠
      aeval zeroJet0 (initialJetSeparant 0 scaledEquation) ^ 0 *
        ((rationalTaylorPolynomial 0 scaledEquation 2 zeroJet0).eval 1 - 0) := by
  have hS : aeval zeroJet0 (initialJetSeparant 0 scaledEquation) ≠ 0 := by
    rw [initialJetSeparant_scaledEquation]
    norm_num
  have hsolutionJet : polynomialJet 0 scaledSolution = zeroJet0 := by
    funext i
    fin_cases i
    simp [polynomialJet, scaledSolution, zeroJet0]
  have hsep : jetEvaluation (separant scaledEquation (Fin.last 0)) 0
      (polynomialJet 0 scaledSolution) ≠ 0 := by
    rw [hsolutionJet]
    norm_num [jetEvaluation, separant, scaledEquation, zeroJet0]
  have hc1 : rationalTaylorCoefficient 0 scaledEquation zeroJet0 1 = (1 / 2 : ℚ) := by
    rw [← hsolutionJet, rationalTaylorCoefficient_eq_solution 0 scaledEquation scaledSolution
      scaledSolution_sol hsep 1 (by intro i hi hle; simp)]
    norm_num [scaledSolution]
  have hc0 : rationalTaylorCoefficient 0 scaledEquation zeroJet0 0 = 0 := by
    simpa [zeroJet0] using
      rationalTaylorCoefficient_initial 0 scaledEquation zeroJet0 ⟨0, by omega⟩
  have hnum1 : aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 1 1) = 1 := by
    rw [aeval_commonTaylorNumerator 0 scaledEquation zeroJet0 (by norm_num) hS]
    rw [initialJetSeparant_scaledEquation, hc1]
    norm_num
  have hnum0 : aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 0) = 0 := by
    simp [commonTaylorNumerator, rationalTaylorNumerator, zeroJet0]
  have hnum1' : aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 1) = 1 := by
    simpa [commonTaylorNumerator] using hnum1
  have hnum0Fin :
      aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 (0 : Fin 2).val) = 0 := by
    change aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 0) = 0
    exact hnum0
  have hnum1Fin :
      aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 (1 : Fin 2).val) = 1 := by
    change aeval zeroJet0 (commonTaylorNumerator 0 scaledEquation 0 1) = 1
    exact hnum1'
  have hcut : aeval zeroJet0 (taylorAgreementEquation 0 scaledEquation 2 0 1 0) = 1 := by
    simp only [taylorAgreementEquation, Fin.sum_univ_two, map_sub, map_add, map_mul, map_pow,
      map_zero, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hnum0Fin, hnum1Fin]
    norm_num
  have hrec : (rationalTaylorPolynomial 0 scaledEquation 2 zeroJet0).eval 1 = (1 / 2 : ℚ) := by
    rw [eval_rationalTaylorPolynomial, Fin.sum_univ_two]
    simp [hc0, hc1]
  rw [hcut, initialJetSeparant_scaledEquation, hrec]
  norm_num

/-- Vanishing regular symbolic high cuts force the concrete reconstruction to have degree below
one. -/
example (a : ℚ) :
    (rationalTaylorPolynomial 0 (X (some 1) : DifferentialPolynomial ℚ 1) 2 constantJet).degree
      < 1 := by
  have hSval : aeval constantJet (map (Polynomial.aeval a).toRingHom
      (initialJetSeparant 0 parameterEquation)) = 1 := by
    rw [map_initialJetSeparant]
    norm_num [initialJetSeparant, separant, parameterEquation, constantJet]
  have hS : aeval constantJet (map (Polynomial.aeval a).toRingHom
      (initialJetSeparant 0 parameterEquation)) ≠ 0 := by
    rw [hSval]
    norm_num
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val →
      aeval constantJet (map (Polynomial.aeval a).toRingHom
        (commonTaylorNumeratorOver ℚ 0 parameterEquation 4 l.val)) = 0 := by
    intro l hl
    have hl1 : l = 1 := by fin_cases l <;> simp_all
    subst l
    rw [map_commonTaylorNumeratorOver_eq]
    norm_num [commonTaylorNumerator, rationalTaylorNumerator, initialJetSeparant, separant,
      parameterEquation, constantJet]
  simpa [parameterEquation] using
    degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts (F := ℚ) (Polynomial.aeval a)
      0 parameterEquation 2 1 constantJet hS hhigh

end

end PolynomialDifferential
