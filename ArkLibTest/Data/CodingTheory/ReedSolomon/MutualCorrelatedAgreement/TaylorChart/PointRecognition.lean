/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for symbolic Taylor chart recognition

For the order-zero equation `y = 0`, a one-point sample fixes the base-field pair. The regular
chart point with zero initial value reconstructs that pair, its initial jet, and its cleared
Taylor coefficient.
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

end

end ReedSolomon
