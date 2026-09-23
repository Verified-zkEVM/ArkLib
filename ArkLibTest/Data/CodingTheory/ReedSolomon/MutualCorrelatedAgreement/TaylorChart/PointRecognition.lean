/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for symbolic Taylor chart recognition

For the order-zero equation `y = 0`, one-point samples fix the base-field pair. Regular chart
points reconstruct that pair, including when the second received value and challenge are nonzero
and a nonvacuous high Taylor cut is required.
-/

open MvPolynomial Polynomial
open PolynomialDifferential

namespace ReedSolomon

noncomputable section

private def pointDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, by
    intro i j _
    exact Subsingleton.elim _ _⟩

private theorem pointDomain_zero : pointDomain (0 : Fin 1) = 0 := rfl

/-- The order-zero equation `y = 0` over the challenge polynomial ring. -/
private abbrev valueEquation : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

/-- The shifted order-zero equation has the constant solution `2`. -/
private abbrev shiftedValueEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  X (some 0) - MvPolynomial.C (Polynomial.C (2 : ℚ))

/-- A regular one-point chart instance returns the pair fixed by its sample. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 0 ∧
      rationalTaylorPolynomial (0 : ℚ) (map (Polynomial.evalRingHom 0) valueEquation) 1
          (fun _ : Fin 1 ↦ 0) =
        P₀.map (RingHom.id ℚ) + Polynomial.C 0 * P₁.map (RingHom.id ℚ) ∧
      (fun _ : Fin 1 ↦ 0) = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          (0 : ℚ) * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 1,
        aeval (fun _ : Fin 1 ↦ 0)
            (map (Polynomial.evalRingHom 0)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) valueEquation 2 l.val)) =
          aeval (fun _ : Fin 1 ↦ 0)
              (map (Polynomial.evalRingHom 0)
                (initialJetSeparant (Polynomial.C 0) valueEquation)) ^ 2 *
            (Polynomial.taylor (0 : ℚ) (P₀.map (RingHom.id ℚ) +
              Polynomial.C 0 * P₁.map (RingHom.id ℚ))).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample (n := 1) (k := 1) (K := 1) (r := 0)
      pointDomain (fun _ ↦ 0) (fun _ ↦ 0) Finset.univ (by simp) (RingHom.id ℚ) 0
      valueEquation (by omega)
  let jet : Fin 1 → ℚ := fun _ ↦ 0
  have hS : aeval jet (map (Polynomial.evalRingHom 0)
      (initialJetSeparant (Polynomial.C 0) valueEquation)) ≠ 0 := by
    simp [jet, valueEquation, initialJetSeparant, separant, Fin.last]
  have hhigh : ∀ l : Fin 1, 1 ≤ l.val → aeval jet
      (map (Polynomial.evalRingHom 0)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) valueEquation 2 l.val)) = 0 := by
    intro l hl
    omega
  have hcuts : ∀ i ∈ Finset.univ, aeval jet
      (map (Polynomial.evalRingHom 0)
        (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) valueEquation 1
          (Polynomial.C (pointDomain i))
          (Polynomial.C 0 + Polynomial.X * Polynomial.C 0))) = 0 := by
    intro i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    simp [jet, valueEquation, taylorAgreementEquationOver, commonTaylorNumeratorOver,
      initialJetSeparant, separant, rationalTaylorNumeratorOver, Fin.last]
  have hresult := hrecognize 0 jet hS hhigh hcuts
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, hresult.1, hresult.2.1, hresult.2.2⟩
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.1
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.2

/-- A nonzero challenge uses the second received value and satisfies the high cut at `l = 1`. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 1 ∧
      (Polynomial.C 2 * P₁.map (RingHom.id ℚ)).eval 0 = 2 ∧
      aeval (fun _ : Fin 1 ↦ (2 : ℚ))
          (map (Polynomial.evalRingHom 2)
            (commonTaylorNumeratorOver ℚ (Polynomial.C 0) shiftedValueEquation 4 1)) = 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
          (map (Polynomial.evalRingHom 2) shiftedValueEquation) 2
          (fun _ : Fin 1 ↦ (2 : ℚ)) =
        P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) ∧
      (fun _ : Fin 1 ↦ (2 : ℚ)) = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          2 * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 2,
        aeval (fun _ : Fin 1 ↦ (2 : ℚ))
            (map (Polynomial.evalRingHom 2)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) shiftedValueEquation 4 l.val)) =
          aeval (fun _ : Fin 1 ↦ (2 : ℚ))
              (map (Polynomial.evalRingHom 2)
                (initialJetSeparant (Polynomial.C 0) shiftedValueEquation)) ^ 4 *
            (Polynomial.taylor (0 : ℚ) (P₀.map (RingHom.id ℚ) +
              Polynomial.C 2 * P₁.map (RingHom.id ℚ))).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample (n := 1) (k := 1) (K := 2) (r := 0)
      pointDomain (fun _ ↦ 0) (fun _ ↦ 1) Finset.univ (by simp) (RingHom.id ℚ) 0
      shiftedValueEquation (by omega)
  let jet : Fin 1 → ℚ := fun _ ↦ 2
  let φ : Polynomial ℚ →ₐ[ℚ] ℚ := Polynomial.aeval (2 : ℚ)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (2 : ℚ) := by
    ext p <;> simp [φ, Polynomial.evalRingHom]
  have hS : aeval jet (map (Polynomial.evalRingHom 2)
      (initialJetSeparant (Polynomial.C 0) shiftedValueEquation)) ≠ 0 := by
    simp [jet, shiftedValueEquation, initialJetSeparant, separant, Fin.last]
  have hSφ : aeval jet (map φ.toRingHom
      (initialJetSeparant (Polynomial.C 0) shiftedValueEquation)) ≠ 0 := by
    simpa only [hφ] using hS
  have hjet : polynomialJet (d := 0) (0 : ℚ) (Polynomial.C 2 : ℚ[X]) = jet := by
    funext j
    fin_cases j
    simp [jet, polynomialJet, Polynomial.hasseJet_apply]
  have hsolution :
      differentialSpecialization (map φ.toRingHom shiftedValueEquation)
        (Polynomial.C 2 : ℚ[X]) = 0 := by
    simp [shiftedValueEquation, φ, differentialSpecialization,
      differentialSpecializationHom]
  have hseparant :
      jetEvaluation
        (separant (map φ.toRingHom shiftedValueEquation) (Fin.last 0)) 0
        (polynomialJet (d := 0) 0 (Polynomial.C 2 : ℚ[X])) ≠ 0 := by
    rw [hjet]
    norm_num [jetEvaluation, separant, shiftedValueEquation, φ]
  have hpoly :
      rationalTaylorPolynomial 0 (map φ.toRingHom shiftedValueEquation) 2 jet =
        Polynomial.C 2 := by
    rw [← hjet]
    exact rationalTaylorPolynomial_polynomialJet 0
      (map φ.toRingHom shiftedValueEquation) (Polynomial.C 2) hsolution hseparant
      (by norm_num) (by intro i hi hiK; norm_num)
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val → aeval jet
      (map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) shiftedValueEquation 4 l.val)) = 0 := by
    intro l hl
    have hl_one : l = (1 : Fin 2) := Fin.ext (by omega)
    subst l
    have hnum := aeval_map_commonTaylorNumeratorOver_reconstruction (F := ℚ) φ
      (Polynomial.C 0) shiftedValueEquation 2 jet hSφ ⟨1, by omega⟩
    have hcoeff :
        (Polynomial.taylor (φ (Polynomial.C 0))
          (rationalTaylorPolynomial (φ (Polynomial.C 0))
            (map φ.toRingHom shiftedValueEquation) 2 jet)).coeff 1 = 0 := by
      rw [show φ (Polynomial.C (0 : ℚ)) = 0 by simp [φ], hpoly]
      simp
    rw [hcoeff] at hnum
    simp only [mul_zero] at hnum
    rw [← hφ]
    have hExponent : 2 * 2 = 4 := by norm_num
    simpa only [hExponent, Fin.val_one] using hnum
  have hcuts : ∀ i ∈ Finset.univ, aeval jet
      (map (Polynomial.evalRingHom 2)
        (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) shiftedValueEquation 2
          (Polynomial.C (pointDomain i))
          (Polynomial.C 0 + Polynomial.X * Polynomial.C 1))) = 0 := by
    intro i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    have hcut :=
      (aeval_map_taylorAgreementEquationOver_eq_zero_iff (F := ℚ) φ
        (Polynomial.C 0) shiftedValueEquation 2 jet hSφ
        (Polynomial.C (pointDomain 0))
        (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)).2 (by
          have hcenter : φ (Polynomial.C (0 : ℚ)) = 0 := by simp [φ]
          have hx : φ (Polynomial.C (pointDomain 0)) = 0 := by
            simp [φ, pointDomain_zero]
          rw [hcenter, hx, hpoly]
          simp [φ])
    simpa only [hφ] using hcut
  have hresult := hrecognize 2 jet hS hhigh hcuts
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, ?_, ?_, hresult.1, hresult.2.1, hresult.2.2⟩
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.1
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.2
  · have h := hsample 0 (by simp)
    have hP₁ : P₁.eval 0 = 1 := by simpa only [pointDomain_zero] using h.2
    simp [hP₁]
  · simpa [jet] using hhigh 1 (by norm_num)

end

end ReedSolomon
