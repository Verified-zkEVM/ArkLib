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

private abbrev parameterizedEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  C (Polynomial.X + 1) * X (some 1) + X none

private abbrev rationalId : ℚ →ₐ[ℚ] ℚ := AlgHom.id ℚ ℚ

/-- Evaluating the parameter `X` at `2` computes the agreement cut as `Y₀ + 2Y₁ - 2`. -/
example :
    map (Polynomial.aeval (2 : ℚ)).toRingHom
        (taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ) parameterEquation 2
          Polynomial.X Polynomial.X) =
      X (0 : Fin 2) + C (2 : ℚ) * X (1 : Fin 2) - C (2 : ℚ) := by
  have hnum0 : commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ) parameterEquation 4 0 =
      X (0 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, parameterEquation,
      initialJetSeparant, separant]
  have hnum1 : commonTaylorNumeratorOver ℚ (0 : Polynomial ℚ) parameterEquation 4 1 =
      X (1 : Fin 2) := by
    simp [commonTaylorNumeratorOver, rationalTaylorNumeratorOver, parameterEquation,
      initialJetSeparant, separant]
  have hcut : taylorAgreementEquationOver (F := ℚ) (0 : Polynomial ℚ) parameterEquation 2
      Polynomial.X Polynomial.X =
        X (0 : Fin 2) + C Polynomial.X * X (1 : Fin 2) - C Polynomial.X := by
    simp [taylorAgreementEquationOver, hnum0, hnum1, initialJetSeparant,
      parameterEquation, separant]
  rw [hcut]
  simp only [map_sub, map_add, map_mul, map_C, map_X, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Polynomial.aeval_X]

/-- Mapping the initial equation evaluates the polynomial coefficient `X + 1` at `2`. -/
example :
    map (Polynomial.aeval (2 : ℚ)).toRingHom
        (initialJetEquation (Polynomial.X : Polynomial ℚ) parameterizedEquation) =
      C (3 : ℚ) * X (1 : Fin 2) + C (2 : ℚ) := by
  norm_num [initialJetEquation, parameterizedEquation]
  rw [← C_1, ← C_add]
  norm_num

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

/-- The first rational Taylor coefficient of the regular zero jet is `1 / 2`. -/
private theorem rationalTaylorCoefficient_scaledEquation_one :
    rationalTaylorCoefficient 0 scaledEquation zeroJet0 1 = (1 / 2 : ℚ) := by
  have hsolutionJet : polynomialJet 0 scaledSolution = zeroJet0 := by
    funext i
    fin_cases i
    simp [polynomialJet, scaledSolution, zeroJet0]
  have hsep : jetEvaluation (separant scaledEquation (Fin.last 0)) 0
      (polynomialJet 0 scaledSolution) ≠ 0 := by
    rw [hsolutionJet]
    norm_num [jetEvaluation, separant, scaledEquation, zeroJet0]
  rw [← hsolutionJet, rationalTaylorCoefficient_eq_solution 0 scaledEquation scaledSolution
      scaledSolution_sol hsep 1 (by intro i hi hle; simp)]
  norm_num [scaledSolution]

/-- The common-numerator theorem computes coefficient `1` of the reconstructed `X / 2`. -/
example :
    aeval zeroJet0 (map rationalId.toRingHom
      (commonTaylorNumeratorOver ℚ 0 scaledEquation 4 1)) = 8 := by
  have hS0 : aeval zeroJet0 (initialJetSeparant 0 scaledEquation) ≠ 0 := by
    rw [initialJetSeparant_scaledEquation]
    norm_num
  have hS : aeval zeroJet0 (map rationalId.toRingHom
      (initialJetSeparant 0 scaledEquation)) ≠ 0 := by
    simpa [rationalId] using hS0
  have hcoeff : (Polynomial.taylor 0
      (rationalTaylorPolynomial 0 scaledEquation 2 zeroJet0)).coeff 1 = (1 / 2 : ℚ) := by
    rw [coeff_taylor_rationalTaylorPolynomial]
    simp [rationalTaylorCoefficient_scaledEquation_one]
  have hnum := aeval_map_commonTaylorNumeratorOver_reconstruction (F := ℚ) rationalId
    0 scaledEquation 2 zeroJet0 hS ⟨1, by omega⟩
  have hSval : aeval zeroJet0
      (map rationalId.toRingHom (initialJetSeparant 0 scaledEquation)) = 2 := by
    simpa [rationalId] using initialJetSeparant_scaledEquation
  have hcoeff' : (Polynomial.taylor (rationalId 0)
      (rationalTaylorPolynomial (rationalId 0) (map rationalId.toRingHom scaledEquation) 2
        zeroJet0)).coeff 1 = (1 / 2 : ℚ) := by
    simpa [rationalId] using hcoeff
  rw [hSval, hcoeff'] at hnum
  norm_num at hnum ⊢
  exact hnum

/-- At exponent zero the agreement cut is `1`, while the reconstructed discrepancy is `1 / 2`;
the sufficient exponent condition is therefore needed. -/
example :
    aeval zeroJet0 (taylorAgreementEquation 0 scaledEquation 2 0 1 0) ≠
      aeval zeroJet0 (initialJetSeparant 0 scaledEquation) ^ 0 *
        ((rationalTaylorPolynomial 0 scaledEquation 2 zeroJet0).eval 1 - 0) := by
  have hS : aeval zeroJet0 (initialJetSeparant 0 scaledEquation) ≠ 0 := by
    rw [initialJetSeparant_scaledEquation]
    norm_num
  have hc1 := rationalTaylorCoefficient_scaledEquation_one
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

private abbrev coordinateEquation : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

example : jointTotalDegree (initialJetEquation (Polynomial.C 0) coordinateEquation) ≤ 1 := by
  apply jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE 0 coordinateEquation 1 0
  · rw [jetTotalDegree_le_iff]
    intro u hu
    simp only [coordinateEquation, support_X, Finset.mem_singleton] at hu
    subst u
    simp [totalJetDegree, Finsupp.weight_single]
  · exact coeffNatDegreeLE_X (some 0)

private abbrev independentVariableEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  X (none : Option (Fin 1))

/-- A nonconstant center contributes its parameter degree to the initial equation. -/
example : jointTotalDegree (initialJetEquation Polynomial.X independentVariableEquation) ≤ 1 := by
  have hjet : jetTotalDegree independentVariableEquation ≤ 0 := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    simp only [independentVariableEquation, support_X, Finset.mem_singleton] at hu
    subst u
    simp [totalJetDegree, Finsupp.weight_single]
  have hEq : initialJetEquation Polynomial.X independentVariableEquation = C Polynomial.X := by
    simp [initialJetEquation, independentVariableEquation]
  have hcoeff :
      CoeffNatDegreeLE (initialJetEquation Polynomial.X independentVariableEquation) 1 := by
    rw [hEq]
    exact coeffNatDegreeLE_C (p := Polynomial.X) (by simp)
  exact jointTotalDegree_initialJetEquation_le Polynomial.X independentVariableEquation 0 1 hjet
    (fun m _ ↦ hcoeff m)

/-- A zero-length agreement cut still has degree one from its affine received value. -/
example :
    jointTotalDegree (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0)
      coordinateEquation 0 (Polynomial.C 0) (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)) ≤
      1 := by
  have hjet : jetTotalDegree coordinateEquation ≤ 1 := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    simp only [coordinateEquation, support_X, Finset.mem_singleton] at hu
    subst u
    simp [totalJetDegree, Finsupp.weight_single]
  have hQ : CoeffNatDegreeLE coordinateEquation 0 := coeffNatDegreeLE_X (some 0)
  simpa only [Polynomial.C_1, mul_one] using
    jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE (F := ℚ) (r := 0)
      0 0 0 1 coordinateEquation 1 0 0 hjet hQ

private abbrev firstDerivativeEquation : DifferentialPolynomial (Polynomial ℚ) 1 :=
  X (some (1 : Fin 2))

example (i : ℕ) (hi : ¬2 ∣ i) :
    (Polynomial.taylor (0 : ℚ)
      (rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom firstDerivativeEquation)
        2 (fun _ ↦ 0))).coeff i = 0 := by
  have hS : aeval (fun _ : Fin 2 ↦ (0 : ℚ))
      (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
        (initialJetSeparant (Polynomial.C (0 : ℚ)) firstDerivativeEquation)) ≠ 0 := by
    rw [map_initialJetSeparant]
    simp [firstDerivativeEquation, initialJetSeparant, separant]
  have hcuts : ∀ l : Fin 2, ¬2 ∣ l.val →
      aeval (fun _ : Fin 2 ↦ (0 : ℚ))
        (map (Polynomial.aeval (R := ℚ) (0 : ℚ)).toRingHom
          (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) firstDerivativeEquation
            4 l.val)) = 0 := by
    intro l hl
    fin_cases l
    · exact (hl (by decide)).elim
    · rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver,
        rationalTaylorNumeratorOver_eq]
      simp [rationalTaylorNumerator, firstDerivativeEquation, initialJetSeparant, separant]
  simpa using sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ := Polynomial.aeval (R := ℚ) (0 : ℚ)) (center := Polynomial.C (0 : ℚ))
    (Q := firstDerivativeEquation) (K := 2) (s := 2) (τ := 4)
    (hτ := taylorExponentSufficient_two_mul 1 2) (jet := fun _ ↦ (0 : ℚ)) hS hcuts i hi

end

end PolynomialDifferential
