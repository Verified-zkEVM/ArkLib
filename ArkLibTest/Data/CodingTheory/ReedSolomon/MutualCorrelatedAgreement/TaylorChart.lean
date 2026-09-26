/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PairCounting
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.Incidence
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ExceptionalChallenges
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.RegularEquation
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.DerivativeTupleCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for symbolic Taylor chart recognition

The default and exponent-aware point theorems use the same concrete sample and regular chart
point. The sample values `(0, 1)`, challenge `2`, and high cut at `l = 1` make reconstruction
nonvacuous when `K = 2` and `k = 1`. A characteristic-two sample also checks sparse Frobenius
Taylor-chart recognition.
-/

open MvPolynomial Polynomial
open PolynomialDifferential
open ReedSolomon.HiddenDerivative

namespace ReedSolomon

noncomputable section

private def pointDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, by
    intro i j _
    exact Subsingleton.elim _ _⟩

private theorem pointDomain_zero : pointDomain (0 : Fin 1) = 0 := rfl

/-- The concrete differential equation used by the Taylor-chart acceptance examples. -/
def quadraticJetSampleEquation : DifferentialPolynomial (Polynomial ℚ) 0 :=
  let Δ := X (some 0) - MvPolynomial.C (Polynomial.C (2 : ℚ))
  Δ + X none * Δ ^ 2

private def concreteJet : Fin 1 → ℚ := fun _ ↦ 2

private def challengeHom : Polynomial ℚ →ₐ[ℚ] ℚ := Polynomial.aeval (2 : ℚ)

private theorem challengeHom_toRingHom :
    challengeHom.toRingHom = Polynomial.evalRingHom (2 : ℚ) := by
  ext p <;> simp [challengeHom, Polynomial.evalRingHom]

private theorem exponentOneSufficient : TaylorExponentSufficient 0 2 1 := by
  intro l
  fin_cases l <;> norm_num [TaylorExponentSufficient]

private theorem initialJetSeparant_quadraticJetSampleEquation :
    initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation = 1 := by
  simp [initialJetSeparant, quadraticJetSampleEquation, separant, Fin.last]

/-- The order-one common Taylor numerator of `quadraticJetSampleEquation` equals
`-(Y₀ - 2)²`. -/
theorem quadraticJetSampleEquation_highNumerator_eq (τ : ℕ) :
    commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation τ 1 =
      -(MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2 := by
  have hcoeff :
      (optionEquivLeft (Polynomial ℚ) (Fin 1)
        (universalTaylorResidual 1 (Polynomial.C 0) quadraticJetSampleEquation)).coeff 1 =
        (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2 := by
    have hres : optionEquivLeft (Polynomial ℚ) (Fin 1)
        (universalTaylorResidual 1 (Polynomial.C 0) quadraticJetSampleEquation) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) +
          Polynomial.X * Polynomial.C
            ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2) := by
      simp [universalTaylorResidual, quadraticJetSampleEquation, optionEquivLeft_X_none,
        optionEquivLeft_universalTaylorJet]
    rw [hres, Polynomial.coeff_add]
    simp only [Polynomial.coeff_C, Polynomial.coeff_X_mul]
    norm_num
  have hsubst : MvPolynomial.clearedSubstitution
      (MvPolynomial.C : Polynomial ℚ →+* MvPolynomial (Fin 1) (Polynomial ℚ))
      1 (fun _ : Fin 1 ↦ MvPolynomial.X 0) (fun _ ↦ 0) 0
      ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2) =
        (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2 := by
    calc
      _ = MvPolynomial.eval₂ (MvPolynomial.C : Polynomial ℚ →+*
          MvPolynomial (Fin 1) (Polynomial ℚ)) (fun _ : Fin 1 ↦ MvPolynomial.X 0)
          ((MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2) := by
        unfold MvPolynomial.clearedSubstitution
        rw [MvPolynomial.eval₂_eq]
        simp only [one_pow, mul_one]
      _ = _ := by simp
  have hnumerator : rationalTaylorNumeratorOver ℚ (Polynomial.C 0)
      quadraticJetSampleEquation 1 =
        -(MvPolynomial.X (0 : Fin 1) - MvPolynomial.C (Polynomial.C (2 : ℚ))) ^ 2 := by
    rw [rationalTaylorNumeratorOver, dite_eq_right (by omega), hcoeff]
    rw [initialJetSeparant_quadraticJetSampleEquation]
    have hN : (fun i : Fin 1 ↦ rationalTaylorNumeratorOver ℚ (Polynomial.C 0)
        quadraticJetSampleEquation i.val) = fun _ : Fin 1 ↦ MvPolynomial.X (0 : Fin 1) := by
      funext i
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      simp [rationalTaylorNumeratorOver]
    have hd : (fun i : Fin 1 ↦ 2 * (i.val - 0) - 1) = fun _ ↦ 0 := by
      funext i
      omega
    rw [hN, hd]
    norm_num [Nat.choose_zero_right]
    rw [hsubst]
  rw [commonTaylorNumeratorOver, hnumerator, initialJetSeparant_quadraticJetSampleEquation, one_pow,
    mul_one]

private theorem quadraticJetSampleEquation_highNumerator_ne (τ : ℕ) :
    MvPolynomial.map (Polynomial.evalRingHom (2 : ℚ))
      (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation τ 1) ≠ 0 := by
  have hvalue : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ℚ))
      (MvPolynomial.map (Polynomial.evalRingHom (2 : ℚ))
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation τ 1)) = -4 := by
    rw [quadraticJetSampleEquation_highNumerator_eq]
    norm_num
  intro hzero
  rw [hzero] at hvalue
  norm_num at hvalue

private theorem concreteTaylorChartSetup (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 2 τ) :
    MvPolynomial.aeval concreteJet
        (MvPolynomial.map (Polynomial.evalRingHom 2)
          (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 ∧
      (∀ l : Fin 2, 1 ≤ l.val →
        MvPolynomial.aeval concreteJet
          (MvPolynomial.map (Polynomial.evalRingHom 2)
            (commonTaylorNumeratorOver ℚ (Polynomial.C 0)
              quadraticJetSampleEquation τ l.val)) = 0) ∧
      (∀ i ∈ Finset.univ, MvPolynomial.aeval concreteJet
        (MvPolynomial.map (Polynomial.evalRingHom 2)
          (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) quadraticJetSampleEquation 2
            (Polynomial.C (pointDomain i)) (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)
            (τ := τ))) = 0) ∧
      rationalTaylorPolynomial (0 : ℚ)
        (MvPolynomial.map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        Polynomial.C 2 := by
  let φ : Polynomial ℚ →ₐ[ℚ] ℚ := challengeHom
  have hφ : φ.toRingHom = Polynomial.evalRingHom (2 : ℚ) := challengeHom_toRingHom
  have hS : MvPolynomial.aeval concreteJet
      (MvPolynomial.map (Polynomial.evalRingHom 2)
        (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 := by
    rw [initialJetSeparant_quadraticJetSampleEquation, map_one, map_one]
    exact one_ne_zero
  have hSφ : MvPolynomial.aeval concreteJet
      (MvPolynomial.map φ.toRingHom
        (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 := by
    simpa only [hφ] using hS
  have hjet : polynomialJet (d := 0) (0 : ℚ) (Polynomial.C 2 : ℚ[X]) = concreteJet := by
    funext j
    fin_cases j
    simp [concreteJet, polynomialJet, Polynomial.hasseJet_apply]
  have hsolution :
    differentialSpecialization (MvPolynomial.map φ.toRingHom quadraticJetSampleEquation)
        (Polynomial.C 2 : ℚ[X]) = 0 := by
    simp [quadraticJetSampleEquation, φ, differentialSpecialization,
      differentialSpecializationHom, challengeHom]
  have hseparant :
      jetEvaluation
          (separant (MvPolynomial.map φ.toRingHom quadraticJetSampleEquation) (Fin.last 0)) 0
        (polynomialJet (d := 0) 0 (Polynomial.C 2 : ℚ[X])) ≠ 0 := by
    have hsep := map_initialJetSeparant φ.toRingHom (Polynomial.C 0) quadraticJetSampleEquation
    rw [initialJetSeparant_quadraticJetSampleEquation, map_one, Polynomial.C_0, map_zero] at hsep
    rw [hjet, ← aeval_initialJetSeparant, ← hsep, map_one]
    exact one_ne_zero
  have hpoly :
      rationalTaylorPolynomial 0 (MvPolynomial.map φ.toRingHom quadraticJetSampleEquation) 2
        concreteJet =
      Polynomial.C 2 := by
    rw [← hjet]
    exact rationalTaylorPolynomial_polynomialJet 0
      (MvPolynomial.map φ.toRingHom quadraticJetSampleEquation) (Polynomial.C 2) hsolution hseparant
      (by norm_num) (by intro i hi hiK; norm_num)
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val → MvPolynomial.aeval concreteJet
      (MvPolynomial.map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0)
          quadraticJetSampleEquation τ l.val)) = 0 := by
    intro l hl
    have hl_one : l = (1 : Fin 2) := Fin.ext (by omega)
    subst l
    have hnum := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      (F := ℚ) φ (Polynomial.C 0) quadraticJetSampleEquation 2 τ hτ concreteJet hSφ
      ⟨1, by omega⟩
    have hcoeff :
        (Polynomial.taylor (φ (Polynomial.C (0 : ℚ)))
          (rationalTaylorPolynomial (φ (Polynomial.C 0))
            (MvPolynomial.map φ.toRingHom quadraticJetSampleEquation) 2
            concreteJet)).coeff 1 = 0 := by
      rw [show φ (Polynomial.C (0 : ℚ)) = 0 by simp [φ, challengeHom], hpoly]
      simp
    rw [hcoeff] at hnum
    simp only [mul_zero] at hnum
    rw [← hφ]
    simpa only [Fin.val_one] using hnum
  have hcuts : ∀ i ∈ Finset.univ, MvPolynomial.aeval concreteJet
      (MvPolynomial.map (Polynomial.evalRingHom 2)
        (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) quadraticJetSampleEquation 2
          (Polynomial.C (pointDomain i)) (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)
          (τ := τ))) = 0 := by
    intro i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    have hcut :=
      (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent (F := ℚ) φ
        (Polynomial.C 0) quadraticJetSampleEquation 2 τ hτ concreteJet hSφ
        (Polynomial.C (pointDomain 0)) (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)).2 (by
          have hcenter : φ (Polynomial.C (0 : ℚ)) = 0 := by
            simp [φ, challengeHom]
          have hx : φ (Polynomial.C (pointDomain 0)) = 0 := by
            simp [φ, challengeHom, pointDomain_zero]
          rw [hcenter, hx, hpoly]
          simp [φ, challengeHom])
    simpa only [hφ] using hcut
  exact ⟨hS, hhigh, hcuts, by simpa only [hφ] using hpoly⟩

/-- The exponent-aware theorem recognizes the same pair at the sufficient exponent `1`. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 1 ∧
      (Polynomial.C 2 * P₁.map (RingHom.id ℚ)).eval 0 = 2 ∧
      MvPolynomial.aeval concreteJet
        (MvPolynomial.map (Polynomial.evalRingHom 2)
          (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 1)) = 0 ∧
      MvPolynomial.map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 1) ≠ 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
          (MvPolynomial.map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) ∧
      concreteJet = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          2 * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval concreteJet
            (MvPolynomial.map (Polynomial.evalRingHom 2)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 l.val)) =
          MvPolynomial.aeval concreteJet
              (MvPolynomial.map (Polynomial.evalRingHom 2)
                (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ^ 1 *
            (Polynomial.taylor (0 : ℚ) (P₀.map (RingHom.id ℚ) +
              Polynomial.C 2 * P₁.map (RingHom.id ℚ))).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample_of_exponent
      (n := 1) (k := 1) (K := 2) (r := 0)
      pointDomain (fun _ ↦ 0) (fun _ ↦ 1) Finset.univ (by simp) (RingHom.id ℚ) 0
      quadraticJetSampleEquation (by omega) 1 exponentOneSufficient
  have hsetup := concreteTaylorChartSetup 1 exponentOneSufficient
  have hresult := hrecognize 2 concreteJet hsetup.1 hsetup.2.1 hsetup.2.2.1
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, ?_, ?_, ?_, hresult.1, hresult.2.1,
    hresult.2.2⟩
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.1
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.2
  · have h := hsample 0 (by simp)
    have hP₁ : P₁.eval 0 = 1 := by simpa only [pointDomain_zero] using h.2
    simp [hP₁]
  · simpa only [Fin.val_one] using hsetup.2.1 1 (by norm_num)
  · exact quadraticJetSampleEquation_highNumerator_ne 1

/-- The default-exponent theorem recognizes the same pair at exponent `2K`. -/
example :
    ∃ P₀ P₁ : ℚ[X], P₀.degree < 1 ∧ P₁.degree < 1 ∧
      P₀.eval 0 = 0 ∧ P₁.eval 0 = 1 ∧
      (Polynomial.C 2 * P₁.map (RingHom.id ℚ)).eval 0 = 2 ∧
      MvPolynomial.aeval concreteJet
        (MvPolynomial.map (Polynomial.evalRingHom 2)
          (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 1)) = 0 ∧
      MvPolynomial.map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 1) ≠ 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
          (MvPolynomial.map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) ∧
      concreteJet = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          2 * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval concreteJet
            (MvPolynomial.map (Polynomial.evalRingHom 2)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 l.val)) =
          MvPolynomial.aeval concreteJet
              (MvPolynomial.map (Polynomial.evalRingHom 2)
                (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ^ 4 *
            (Polynomial.taylor (0 : ℚ) (P₀.map (RingHom.id ℚ) +
              Polynomial.C 2 * P₁.map (RingHom.id ℚ))).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsample, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample (n := 1) (k := 1) (K := 2) (r := 0)
      pointDomain (fun _ ↦ 0) (fun _ ↦ 1) Finset.univ (by simp) (RingHom.id ℚ) 0
      quadraticJetSampleEquation (by omega)
  have hsetup := concreteTaylorChartSetup 4 (taylorExponentSufficient_two_mul 0 2)
  have hresult := hrecognize 2 concreteJet hsetup.1 hsetup.2.1 hsetup.2.2.1
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, ?_, ?_, hsetup.2.1 1 (by norm_num),
    quadraticJetSampleEquation_highNumerator_ne 4, hresult.1,
    hresult.2.1, hresult.2.2⟩
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.1
  · have h := hsample 0 (by simp)
    simpa only [pointDomain_zero] using h.2
  · have h := hsample 0 (by simp)
    have hP₁ : P₁.eval 0 = 1 := by simpa only [pointDomain_zero] using h.2
    simp [hP₁]

private def frobeniusSampleDomain : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 1, by intro i j _; exact Subsingleton.elim _ _⟩

private def frobeniusSampleEquation : DifferentialPolynomial (Polynomial (ZMod 2)) 0 :=
  MvPolynomial.X (some 0)

private def frobeniusSampleJet : Fin 1 → ZMod 2 := fun _ ↦ 0

/-- A nonzero sample over `ZMod 2` determines its sparse Frobenius Taylor chart. -/
example :
    ∃ F₀ G₀ : (ZMod 2)[X], F₀.degree < 1 ∧ G₀.degree < 1 ∧
      F₀.eval 1 = 1 ∧ G₀.eval 1 = 1 ∧
      rationalTaylorPolynomial (0 : ZMod 2)
          (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 2)) frobeniusSampleEquation) 1
          frobeniusSampleJet =
        expand (ZMod 2) (2 ^ 1)
          (F₀.map (RingHom.id (ZMod 2)) +
            Polynomial.C ((1 : ZMod 2) ^ (2 ^ 1)) * G₀.map (RingHom.id (ZMod 2))) ∧
      frobeniusSampleJet 0 =
        (F₀.map (RingHom.id (ZMod 2))).eval ((0 : ZMod 2) ^ (2 ^ 1)) +
          1 ^ (2 ^ 1) * (G₀.map (RingHom.id (ZMod 2))).eval (0 : ZMod 2) := by
  let φ : Polynomial (ZMod 2) →ₐ[ZMod 2] ZMod 2 := Polynomial.aeval (1 : ZMod 2)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (1 : ZMod 2) := by
    ext a <;> simp [φ, Polynomial.evalRingHom]
  have hdom : frobeniusSampleDomain (0 : Fin 1) = 1 := rfl
  obtain ⟨F₀, G₀, hF, hG, hsample, hrecognize⟩ :=
    exists_frobeniusGraphLine_of_symbolic_sample
      (domain := frobeniusSampleDomain) (f := fun _ : Fin 1 ↦ (1 : ZMod 2))
      (g := fun _ : Fin 1 ↦ (1 : ZMod 2)) (sample := Finset.univ) (by simp)
      (RingHom.id (ZMod 2)) (p := 2) (e := 1) (roots := fun _ ↦ (1 : ZMod 2))
      (by
        intro i hi
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        rw [RingHom.id_apply, hdom]
        norm_num) (center := 0)
      (Q := frobeniusSampleEquation) (k := 1) (K := 1) (by omega) (by norm_num) 2
      (taylorExponentSufficient_two_mul 0 1)
  have hS : MvPolynomial.aeval frobeniusSampleJet
      (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 2))
        (initialJetSeparant (Polynomial.C (0 : ZMod 2)) frobeniusSampleEquation)) ≠ 0 := by
    simp [frobeniusSampleEquation, initialJetSeparant, separant]
  have hsparse : ∀ l : Fin 1, ¬2 ^ 1 ∣ l.val →
      MvPolynomial.aeval frobeniusSampleJet
        (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 2))
          (commonTaylorNumeratorOver (F := ZMod 2) (Polynomial.C 0)
            frobeniusSampleEquation 2 l.val)) = 0 := by
    intro l hl
    have hl0 : l.val = 0 := by omega
    have hdiv : 2 ^ 1 ∣ l.val := by rw [hl0]; exact dvd_zero _
    exact (hl hdiv).elim
  have hcuts : ∀ i : Fin 1, i ∈ Finset.univ →
      MvPolynomial.aeval frobeniusSampleJet
        (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 2))
          (taylorAgreementEquationOver (F := ZMod 2) (Polynomial.C 0)
            frobeniusSampleEquation 1 (Polynomial.C (1 : ZMod 2))
            (Polynomial.C (1 : ZMod 2) + Polynomial.X ^ (2 ^ 1) *
              Polynomial.C (1 : ZMod 2)) (τ := 2))) = 0 := by
    intro i hi
    have hvalue :
        (rationalTaylorPolynomial (φ (Polynomial.C (0 : ZMod 2)))
          (MvPolynomial.map φ.toRingHom frobeniusSampleEquation) 1 frobeniusSampleJet).eval
            (φ (Polynomial.C (1 : ZMod 2))) =
          φ (Polynomial.C (1 : ZMod 2) + Polynomial.X ^ (2 ^ 1) *
            Polynomial.C (1 : ZMod 2)) := by
      have hcenter : φ (Polynomial.C (0 : ZMod 2)) = 0 := by simp [φ]
      have hx : φ (Polynomial.C (1 : ZMod 2)) = 1 := by simp [φ]
      have hc : rationalTaylorCoefficient (0 : ZMod 2)
          (MvPolynomial.map φ.toRingHom frobeniusSampleEquation) frobeniusSampleJet 0 = 0 := by
        simpa [frobeniusSampleJet] using
          rationalTaylorCoefficient_initial (0 : ZMod 2)
            (MvPolynomial.map φ.toRingHom frobeniusSampleEquation) frobeniusSampleJet (0 : Fin 1)
      have hcEval : rationalTaylorCoefficient (0 : ZMod 2)
          (MvPolynomial.map (Polynomial.evalRingHom (1 : ZMod 2)) frobeniusSampleEquation)
            frobeniusSampleJet 0 = 0 := by
        simpa only [hφ] using hc
      have hsum : (1 : ZMod 2) + 1 = 0 := by
        exact ZMod.natCast_self' 1
      rw [hcenter, hx, eval_rationalTaylorPolynomial]
      simp [hcEval, hsum, φ]
    have hSφ : MvPolynomial.aeval frobeniusSampleJet
        (MvPolynomial.map φ.toRingHom
          (initialJetSeparant (Polynomial.C (0 : ZMod 2)) frobeniusSampleEquation)) ≠ 0 := by
      simpa only [hφ] using hS
    have hcut := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent
      (F := ZMod 2) φ (Polynomial.C 0) frobeniusSampleEquation 1 2
      (taylorExponentSufficient_two_mul 0 1) frobeniusSampleJet hSφ
      (Polynomial.C (1 : ZMod 2))
      (Polynomial.C (1 : ZMod 2) + Polynomial.X ^ (2 ^ 1) *
        Polynomial.C (1 : ZMod 2))).2 hvalue
    simpa only [hφ] using hcut
  have hchart := hrecognize (1 : ZMod 2) frobeniusSampleJet hS hsparse hcuts
  have hsample0 := hsample (0 : Fin 1) (by simp)
  refine ⟨F₀, G₀, hF, hG, ?_, ?_, hchart.1, hchart.2⟩
  · simpa only [hdom] using hsample0.1
  · simpa only [hdom] using hsample0.2

end

end ReedSolomon

namespace ReedSolomon

noncomputable section

/-- The specialization of a concrete degree-one pair has degree below two. -/
example :
    (correlatedPairSpecialization (RingHom.id ℚ) (3 : ℚ)
      (Polynomial.X, Polynomial.C (2 : ℚ))).degree < 2 := by
  exact degree_correlatedPairSpecialization_lt (RingHom.id ℚ) 3
    (Polynomial.X, Polynomial.C (2 : ℚ))
    (by norm_num [Polynomial.degree_X]) (by norm_num [Polynomial.degree_C])

private abbrev PairCountingField := AlgebraicClosure ℚ

private def pairCountingEquation :
    DifferentialPolynomial (Polynomial PairCountingField) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private def pairCountingPair : Polynomial ℚ × Polynomial ℚ := (0, 0)

private def pairCountingIota : ℚ →+* PairCountingField := algebraMap ℚ PairCountingField

private theorem pairCountingSeparantEval :
    (chartPairPullback pairCountingIota (0 : PairCountingField) pairCountingPair
      (jointInitialJetSeparant 0 pairCountingEquation)).eval 0 ≠ 0 := by
  rw [jointInitialJetSeparant, eval_chartPairPullback_symbolic]
  simp [initialJetSeparant, pairCountingEquation, pairCountingPair, separant]

private theorem pairCountingAdmissible :
    IsAdmissibleChartPair pointDomain (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota 0
      pairCountingEquation 1 1 1 pairCountingPair := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pairCountingPair]
  · simp [pairCountingPair]
  · norm_num [pairCountingPair, pointDomain, commonPolynomialAgreementSet]
  · simp [chartPairPullback, jointInitialJetEquation, initialJetEquation,
      pairCountingEquation, pairCountingPair, affinePairCurve, polynomialJet]
  · intro l hl
    omega
  · intro hzero
    apply pairCountingSeparantEval
    simpa using congrArg (fun p : PairCountingField[X] ↦ p.eval 0) hzero
  · intro l
    fin_cases l
    simp [chartPairPullback, jointTaylorReconstructionError, jointCommonTaylorNumerator,
      jointInitialJetSeparant, commonTaylorNumeratorOver, pairCountingEquation,
      pairCountingPair, rationalTaylorNumeratorOver, affinePairCurve, polynomialJet]

private def pairCountingPairs : Finset (Polynomial ℚ × Polynomial ℚ) :=
  {pairCountingPair}

private def incidenceEquation :
    DifferentialPolynomial (Polynomial PairCountingField) 0 :=
  MvPolynomial.C (Polynomial.X : Polynomial PairCountingField) +
    MvPolynomial.X (some (0 : Fin 1))

private def incidencePoint : Option (Fin 1) → PairCountingField := fun _ ↦ 0

private def incidencePoints : Finset (Option (Fin 1) → PairCountingField) := by
  classical
  exact {incidencePoint}

private theorem incidencePoint_not_mem_pairGraph :
    incidencePoint ∉ admissibleChartPairGraphLocus pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota 0 incidenceEquation 1 0 0 := by
  classical
  rintro ⟨pair, hp, z, hz⟩
  have hleft : pair.1 = 0 := by
    apply Polynomial.degree_eq_bot.mp
    exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp.degree_left)
  have hright : pair.2 = 0 := by
    apply Polynomial.degree_eq_bot.mp
    exact Nat.WithBot.lt_zero_iff.mp (by simpa using hp.degree_right)
  have hpair : pair = (0, 0) := Prod.ext hleft hright
  subst pair
  have hzero : chartPairPullback pairCountingIota 0 (0, 0)
      (jointInitialJetEquation 0 incidenceEquation) = 0 := hp.initial
  have hX : (Polynomial.X : PairCountingField[X]) = 0 := by
    simp [chartPairPullback, jointInitialJetEquation, initialJetEquation,
      incidenceEquation, affinePairCurve, polynomialJet] at hzero
  exact Polynomial.X_ne_zero hX

private theorem incidencePoint_conditions :
    ∀ x ∈ incidencePoints,
      aeval x (jointInitialJetEquation 0 incidenceEquation) = 0 ∧
      aeval x (jointInitialJetSeparant 0 incidenceEquation) ≠ 0 ∧
      (∀ l : Fin 1, 0 ≤ l.val →
        aeval x (jointCommonTaylorNumerator 0 incidenceEquation 2 l) = 0) ∧
      x ∉ admissibleChartPairGraphLocus pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
        pairCountingIota 0 incidenceEquation 1 0 0 := by
  intro x hx
  have hx' : x = incidencePoint := by simpa [incidencePoints] using hx
  subst x
  refine ⟨?_, ?_, ?_, incidencePoint_not_mem_pairGraph⟩
  · simp [incidencePoint, jointInitialJetEquation, initialJetEquation, incidenceEquation]
  · rw [jointInitialJetSeparant, aeval_optionEquivRight_symm]
    simp [initialJetSeparant, incidenceEquation, incidencePoint, separant]
  · intro l hl
    have hl0 : l = 0 := Fin.ext (by omega)
    subst l
    simp [incidencePoint, jointCommonTaylorNumerator, commonTaylorNumeratorOver,
      rationalTaylorNumeratorOver, initialJetSeparant, incidenceEquation]

private theorem incidenceJetDegree : jetTotalDegree incidenceEquation ≤ 1 := by
  classical
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree
  simp only [Finset.sup_le_iff]
  intro m hm
  change m ∈ (MvPolynomial.C (Polynomial.X : Polynomial PairCountingField) +
    MvPolynomial.X (some (0 : Fin 1))).support at hm
  have hm' : m ∈ (MvPolynomial.C (Polynomial.X : Polynomial PairCountingField)).support ∪
      (MvPolynomial.X (some (0 : Fin 1)) :
        MvPolynomial (Option (Fin 1)) (Polynomial PairCountingField)).support :=
    MvPolynomial.support_add hm
  rcases Finset.mem_union.mp hm' with hmC | hmX
  · have hm0 : 0 = m := by simpa using hmC
    have hm0 := hm0.symm
    subst m
    simp
  · rw [MvPolynomial.support_X] at hmX
    have hmSingle : m = Finsupp.single (some (0 : Fin 1)) 1 := by
      simpa only [Finset.mem_singleton] using hmX
    subst m
    rw [Finsupp.weight_single]
    simp [jetDegreeWeight]

private theorem incidenceHeight : CoeffNatDegreeLE incidenceEquation 1 := by
  apply CoeffNatDegreeLE.add
  · exact coeffNatDegreeLE_C (p := Polynomial.X) (by simp)
  · exact (coeffNatDegreeLE_X (some (0 : Fin 1))).mono (by omega)

/-- The total-degree incidence bound applies to a concrete nonempty set of chart points. -/
example : incidencePoints.Nonempty ∧ (incidencePoints.card : ℚ) ≤ 6 := by
  refine ⟨by simp [incidencePoints], ?_⟩
  have hinit : jointInitialJetEquation 0 incidenceEquation ≠ 0 := by
    intro h
    have heval := congrArg
      (MvPolynomial.aeval (fun j : Option (Fin 1) ↦
        if j = none then (1 : PairCountingField) else 0)) h
    norm_num [jointInitialJetEquation, initialJetEquation, incidenceEquation] at heval
  have hbound := finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le
    (K := 1) (k := 0) (L := 0) (A := 0) (initialDegree := 2) (cutDegree := 3)
    pointDomain (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota 0 incidenceEquation
    (by omega) (by omega) (by omega) (by omega) hinit
    (by
      simpa [jointInitialJetEquation, jointTotalDegree] using
        jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE
          (0 : PairCountingField) incidenceEquation 1 1 incidenceJetDegree incidenceHeight)
    (by
      intro l hl
      have hlτ : 2 * (l.val - 0) - 1 ≤ 2 := by omega
      simpa [jointCommonTaylorNumerator, jointTotalDegree] using
        jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE
          (0 : PairCountingField) incidenceEquation 1 1 2 l.val hlτ
          incidenceJetDegree incidenceHeight)
    (by
      intro i
      simpa [jointTaylorAgreementEquation, jointTotalDegree] using
        jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent
          (0 : PairCountingField) (pointDomain i) (0 : ℚ) (0 : ℚ) incidenceEquation
          1 1 1 2 (taylorExponentSufficient_two_mul 0 1)
          incidenceJetDegree incidenceHeight)
    incidencePoints incidencePoint_conditions (by
      intro x hx
      exact Nat.zero_le _)
  exact hbound.trans (by norm_num [incidencePoints])

/-- The jet-degree incidence bound applies to the same concrete nonempty chart-point set. -/
example : incidencePoints.Nonempty ∧ (incidencePoints.card : ℚ) ≤ 6 := by
  refine ⟨by simp [incidencePoints], ?_⟩
  have hinit : jointInitialJetEquation 0 incidenceEquation ≠ 0 := by
    intro h
    have heval := congrArg
      (MvPolynomial.aeval (fun j : Option (Fin 1) ↦
        if j = none then (1 : PairCountingField) else 0)) h
    norm_num [jointInitialJetEquation, initialJetEquation, incidenceEquation] at heval
  have hbound := finite_regularJointTaylorChartPoints_off_admissiblePairGraphs_card_le_of_jetDegree
    (K := 1) (k := 0) (L := 0) (A := 0) (v := 1) (h := 1)
    pointDomain (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota 0 incidenceEquation
    (by omega) (by omega) (by omega) (by omega) hinit incidenceJetDegree incidenceHeight
    incidencePoints incidencePoint_conditions (by
      intro x hx
      exact Nat.zero_le _)
  exact hbound.trans (by norm_num [incidencePoints])

/-- A regular challenge specializes a concrete admissible pair to its Taylor reconstruction. -/
example :
    rationalTaylorPolynomial (0 : PairCountingField)
      (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) pairCountingEquation)
      1 (chartPairJet pairCountingIota 0 0 pairCountingPair) =
        correlatedPairSpecialization pairCountingIota 0 pairCountingPair := by
  exact (pairCountingAdmissible.specialize (by omega) 0 (by
    exact pairCountingSeparantEval)).2.2.2

/-- The finite-set incidence bound applies to a nonempty concrete admissible-pair set. -/
example : pairCountingPair ∈ pairCountingPairs ∧ (pairCountingPairs.card : ℚ) ≤ 1 := by
  constructor
  · simp [pairCountingPairs]
  · have hbound := admissibleChartPairs_card_le pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [pairCountingEquation, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_X])
      pairCountingPairs (by
        intro pair hp
        have hpair : pair = pairCountingPair := by simpa [pairCountingPairs] using hp
        subst pair
        exact pairCountingAdmissible)
    simpa using hbound

/-- The filtered family of concrete admissible pairs obeys the same incidence bound. -/
example :
    pairCountingPair ∈ admissibleChartPairFamily pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 ∧
    ((admissibleChartPairFamily pointDomain (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota
      (0 : PairCountingField) pairCountingEquation 1 1 1).card : ℚ) ≤ 1 := by
  constructor
  · exact (mem_admissibleChartPairFamily_iff pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 (by norm_num)
      pairCountingPair).2 pairCountingAdmissible
  · have hbound := admissibleChartPairFamily_card_le pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [pairCountingEquation, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_X])
    simpa using hbound

/-- The sharp pair bound applies to a concrete nonempty admissible-pair set. -/
example : pairCountingPair ∈ pairCountingPairs ∧ (pairCountingPairs.card : ℚ) ≤ 1 := by
  constructor
  · simp [pairCountingPairs]
  · have hbound := admissibleChartPairs_card_le_sharp pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [pairCountingEquation, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_X]) pairCountingPairs (by
        intro pair hp
        have hpair : pair = pairCountingPair := by simpa [pairCountingPairs] using hp
        subst pair
        exact pairCountingAdmissible)
    simpa using hbound

/-- The explicit family of concrete admissible pairs satisfies the sharp graph-count bound. -/
example : pairCountingPair ∈ admissibleChartPairFamily pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 ∧
    ((admissibleChartPairFamily pointDomain (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota
      (0 : PairCountingField) pairCountingEquation 1 1 1).card : ℚ) ≤ 1 := by
  constructor
  · exact (mem_admissibleChartPairFamily_iff pointDomain (fun _ ↦ 0) (fun _ ↦ 0)
      pairCountingIota (0 : PairCountingField) pairCountingEquation 1 1 1 (by norm_num)
      pairCountingPair).2 pairCountingAdmissible
  · have hbound := admissibleChartPairFamily_card_le_sharp pointDomain
      (fun _ ↦ 0) (fun _ ↦ 0) pairCountingIota (0 : PairCountingField)
      pairCountingEquation 1 1 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [pairCountingEquation, MvPolynomial.weightedTotalDegree,
        MvPolynomial.support_X])
    simpa using hbound

private def challengeBoundDomain : Fin 4 ↪ ℚ :=
  ⟨fun i ↦ i.val, by
    intro i j h
    apply Fin.ext
    exact_mod_cast (show (i.val : ℚ) = (j.val : ℚ) from h)⟩

private def challengeBoundFirstWord : Fin 4 → ℚ := fun i ↦ if i.val = 3 then 1 else 0

private def challengeBoundSecondWord : Fin 4 → ℚ := fun i ↦ if i.val = 2 then 1 else 0

private def challengeBoundEquation : DifferentialPolynomial (Polynomial PairCountingField) 1 :=
  MvPolynomial.X (some (1 : Fin 2))

private def challengeBoundJet : Fin 2 → PairCountingField :=
  polynomialJet 0 (0 : PairCountingField[X])

private def challengeBoundChallenges : Finset PairCountingField := {0}

/-- The bad-challenge bound includes a concrete challenge with three agreements and no matching
common-agreement set from a degree-bounded polynomial pair. -/
example : challengeBoundChallenges.Nonempty ∧
    (challengeBoundChallenges.card : ℚ) ≤ 12 := by
  classical
  have hsolution : differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) challengeBoundEquation)
      (0 : PairCountingField[X]) = 0 := by
    simp [differentialSpecialization, differentialSpecializationHom, challengeBoundEquation]
  have hseparant : jetEvaluation
      (separant
        (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) challengeBoundEquation)
        (Fin.last 1)) 0 challengeBoundJet ≠ 0 := by
    norm_num [jetEvaluation, separant, challengeBoundEquation, challengeBoundJet,
      polynomialJet]
  have hpolynomial : rationalTaylorPolynomial 0
      (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) challengeBoundEquation)
      2 challengeBoundJet = 0 := by
    exact rationalTaylorPolynomial_polynomialJet 0
      (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) challengeBoundEquation)
      (0 : PairCountingField[X]) hsolution hseparant
      (by exact WithBot.bot_lt_coe 2)
      (by intro i hi hiK; omega)
  have hchart : ∀ z ∈ challengeBoundChallenges,
      let Qz := MvPolynomial.map (Polynomial.evalRingHom z) challengeBoundEquation
      (0 : PairCountingField[X]).degree < 2 ∧
        aeval challengeBoundJet (initialJetEquation (0 : PairCountingField) Qz) = 0 ∧
        aeval challengeBoundJet (initialJetSeparant (0 : PairCountingField) Qz) ≠ 0 ∧
        (∀ l : Fin 2, 2 ≤ l.val →
          aeval challengeBoundJet (commonTaylorNumerator 0 Qz 4 l) = 0) ∧
        rationalTaylorPolynomial 0 Qz 2 challengeBoundJet = 0 := by
    intro z hz
    have hz0 : z = 0 := Finset.mem_singleton.mp hz
    subst z
    dsimp only
    refine ⟨WithBot.bot_lt_coe 2, ?_, ?_, ?_, hpolynomial⟩
    · exact aeval_initialJetEquation_polynomialJet 0
        (MvPolynomial.map (Polynomial.evalRingHom (0 : PairCountingField)) challengeBoundEquation)
        (0 : PairCountingField[X]) hsolution
    · norm_num [challengeBoundEquation, initialJetSeparant, separant]
    · intro l hl
      omega
  have hagree : ∀ z ∈ challengeBoundChallenges,
      3 ≤ (polynomialAgreementSet
        (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
        (fun i ↦ pairCountingIota (challengeBoundFirstWord i) + z *
          pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X])).card := by
    intro z hz
    have hz0 : z = 0 := Finset.mem_singleton.mp hz
    subst z
    have hset : polynomialAgreementSet
        (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
        (fun i ↦ pairCountingIota (challengeBoundFirstWord i) +
          0 * pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X]) =
        Finset.univ.filter fun i : Fin 4 ↦ i.val ≠ 3 := by
      ext i
      simp [polynomialAgreementSet, challengeBoundDomain, challengeBoundFirstWord,
        challengeBoundSecondWord, pairCountingIota]
    rw [hset]
    decide
  have hbad : ∀ z ∈ challengeBoundChallenges, ¬ ∃ pair : ℚ[X] × ℚ[X],
      pair.1.degree < 2 ∧ pair.2.degree < 2 ∧
      (0 : PairCountingField[X]) = correlatedPairSpecialization pairCountingIota z pair ∧
      polynomialAgreementSet
          (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
          (fun i ↦ pairCountingIota (challengeBoundFirstWord i) + z *
            pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X]) =
        commonPolynomialAgreementSet challengeBoundDomain challengeBoundFirstWord
          challengeBoundSecondWord pair.1 pair.2 := by
    intro z hz
    have hz0 : z = 0 := Finset.mem_singleton.mp hz
    subst z
    rintro ⟨pair, _, hdegree, hspecialize, hsets⟩
    have hmapped : pair.1.map pairCountingIota = 0 := by
      simpa [correlatedPairSpecialization] using hspecialize.symm
    have hleft : pair.1 = 0 := by
      apply Polynomial.map_injective pairCountingIota pairCountingIota.injective
      simpa using hmapped
    have hQ0 : pair.2.eval 0 = 0 := by
      have hi : (0 : Fin 4) ∈ polynomialAgreementSet
          (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
          (fun i ↦ pairCountingIota (challengeBoundFirstWord i) +
            0 * pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X]) := by
        norm_num [polynomialAgreementSet, challengeBoundDomain, challengeBoundFirstWord,
          challengeBoundSecondWord, pairCountingIota]
      have hc : (0 : Fin 4) ∈ commonPolynomialAgreementSet challengeBoundDomain
          challengeBoundFirstWord challengeBoundSecondWord pair.1 pair.2 := by
        rw [← hsets]
        exact hi
      have hq := (mem_commonPolynomialAgreementSet ..).mp hc |>.2
      change pair.2.eval (challengeBoundDomain (0 : Fin 4)) = challengeBoundSecondWord 0 at hq
      norm_num [challengeBoundDomain, challengeBoundSecondWord] at hq
      exact hq
    have hQ1 : pair.2.eval 1 = 0 := by
      have hi : (1 : Fin 4) ∈ polynomialAgreementSet
          (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
          (fun i ↦ pairCountingIota (challengeBoundFirstWord i) +
            0 * pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X]) := by
        norm_num [polynomialAgreementSet, challengeBoundDomain, challengeBoundFirstWord,
          challengeBoundSecondWord, pairCountingIota]
      have hc : (1 : Fin 4) ∈ commonPolynomialAgreementSet challengeBoundDomain
          challengeBoundFirstWord challengeBoundSecondWord pair.1 pair.2 := by
        rw [← hsets]
        exact hi
      have hq := (mem_commonPolynomialAgreementSet ..).mp hc |>.2
      change pair.2.eval (challengeBoundDomain (1 : Fin 4)) = challengeBoundSecondWord 1 at hq
      norm_num [challengeBoundDomain, challengeBoundSecondWord] at hq
      exact hq
    have hQzero : pair.2 = 0 := by
      refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero ({(0 : ℚ), 1}) ?_ ?_
      · simpa using hdegree
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hQ0
        · exact hQ1
    have hQ2 : pair.2.eval 2 = 1 := by
      have hi : (2 : Fin 4) ∈ polynomialAgreementSet
          (challengeBoundDomain.trans ⟨pairCountingIota, pairCountingIota.injective⟩)
          (fun i ↦ pairCountingIota (challengeBoundFirstWord i) +
            0 * pairCountingIota (challengeBoundSecondWord i)) (0 : PairCountingField[X]) := by
        norm_num [polynomialAgreementSet, challengeBoundDomain, challengeBoundFirstWord,
          challengeBoundSecondWord, pairCountingIota]
      have hc : (2 : Fin 4) ∈ commonPolynomialAgreementSet challengeBoundDomain
          challengeBoundFirstWord challengeBoundSecondWord pair.1 pair.2 := by
        rw [← hsets]
        exact hi
      have hq := (mem_commonPolynomialAgreementSet ..).mp hc |>.2
      change pair.2.eval (challengeBoundDomain (2 : Fin 4)) = challengeBoundSecondWord 2 at hq
      norm_num [challengeBoundDomain, challengeBoundSecondWord] at hq
      exact hq
    norm_num [hQzero] at hQ2
  have hjet : challengeBoundEquation.weightedTotalDegree
      (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
    norm_num [challengeBoundEquation, MvPolynomial.weightedTotalDegree, MvPolynomial.support_X]
  have hheight : CoeffNatDegreeLE challengeBoundEquation 0 :=
    coeffNatDegreeLE_X (some (1 : Fin 2))
  have hbound := finite_symbolicTaylorChart_badChallenges_card_le
    (F := ℚ) (E := PairCountingField) (n := 4) (r := 1) challengeBoundDomain
    challengeBoundFirstWord challengeBoundSecondWord pairCountingIota 0 challengeBoundEquation
    2 2 2 3 1 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hjet hheight challengeBoundChallenges (fun _ ↦ 0) (fun _ ↦ challengeBoundJet)
    hchart hagree hbad
  refine ⟨by simp [challengeBoundChallenges], ?_⟩
  norm_num [challengeBoundChallenges] at hbound ⊢

private abbrev AlgebraicClosureField := AlgebraicClosure ℚ

private def regularEquationDomain : Fin 1 ↪ ℚ :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

private def regularEquationSample : DifferentialPolynomial (Polynomial AlgebraicClosureField) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

local instance : DecidableEq AlgebraicClosureField := Classical.decEq AlgebraicClosureField

/-- A zero solution of `P = 0` has an exact pair at every regular challenge. -/
example :
    ∃ exceptional : Finset AlgebraicClosureField,
      (exceptional.card : ℚ) ≤ regularSymbolicAgreementBound 1 0 1 1 1 1 1 0 ∧
      ∀ z ∉ exceptional, ∀ P : AlgebraicClosureField[X], P.degree < 1 →
        1 ≤ (polynomialAgreementSet
          (regularEquationDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
            (algebraMap ℚ AlgebraicClosureField).injective⟩)
          (fun _ ↦ algebraMap ℚ AlgebraicClosureField (0 : ℚ) +
            z * algebraMap ℚ AlgebraicClosureField 0) P).card →
        differentialSpecialization (challengeSpecialization regularEquationSample z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization regularEquationSample z) (Fin.last 0)) P ≠ 0 →
        HasExactCorrelatedPair regularEquationDomain (fun _ ↦ (0 : ℚ)) (fun _ ↦ 0)
          (algebraMap ℚ AlgebraicClosureField) 1 z P := by
  let iota : ℚ →+* AlgebraicClosureField := algebraMap ℚ AlgebraicClosureField
  have hheight : CoeffNatDegreeLE regularEquationSample 0 := by
    simpa [regularEquationSample] using
      (coeffNatDegreeLE_X (R := AlgebraicClosureField) (σ := JetVariable 0)
        (some (0 : Fin 1)))
  have hjet : regularEquationSample.weightedTotalDegree
      (fun i : JetVariable 0 ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
    norm_num [regularEquationSample, MvPolynomial.weightedTotalDegree, MvPolynomial.support_X]
  exact exists_exceptional_regularSymbolicCorrelatedAgreement regularEquationDomain
    (fun _ ↦ 0) (fun _ ↦ 0) iota regularEquationSample 1 1 1 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hjet hheight (by
      intro i hi hiK
      omega)

private def regularBadDomain : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ i.val, by
    intro i j hij
    change (i.val : ℚ) = (j.val : ℚ) at hij
    apply Fin.ext
    exact_mod_cast hij⟩

private def regularBadFirstWord : Fin 3 → ℚ := fun i ↦ if i.val = 1 then 1 else 0

private def regularBadSecondWord : Fin 3 → ℚ :=
  fun i ↦ if i.val = 1 then -1 else if i.val = 2 then 1 else 0

private def regularBadEquation : DifferentialPolynomial (Polynomial AlgebraicClosureField) 0 :=
  MvPolynomial.X (some (0 : Fin 1))

private def regularBadChallenge : AlgebraicClosureField :=
  algebraMap ℚ AlgebraicClosureField 1

private def regularBadChallengeLine (z : AlgebraicClosureField) : Fin 3 → AlgebraicClosureField :=
  fun i ↦ algebraMap ℚ AlgebraicClosureField (regularBadFirstWord i) +
    z * algebraMap ℚ AlgebraicClosureField (regularBadSecondWord i)

private theorem regularBadAgreementSet :
    polynomialAgreementSet
      (regularBadDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
        (algebraMap ℚ AlgebraicClosureField).injective⟩)
      (regularBadChallengeLine regularBadChallenge) (0 : AlgebraicClosureField[X]) = {0, 1} := by
  ext i
  fin_cases i <;>
    norm_num [polynomialAgreementSet, regularBadDomain, regularBadChallengeLine,
      regularBadFirstWord, regularBadSecondWord, regularBadChallenge]

private theorem regularBadChallenge_mem :
    regularBadChallenge ∈ regularSymbolicBadChallenges regularBadDomain regularBadFirstWord
      regularBadSecondWord (algebraMap ℚ AlgebraicClosureField) regularBadEquation 1 2 := by
  refine ⟨0, by simp, ?_, ?_, ?_, ?_⟩
  · change 2 ≤ (polynomialAgreementSet
      (regularBadDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
        (algebraMap ℚ AlgebraicClosureField).injective⟩)
      (regularBadChallengeLine regularBadChallenge) (0 : AlgebraicClosureField[X])).card
    rw [regularBadAgreementSet]
    norm_num
  · simp [regularBadEquation, challengeSpecialization, differentialSpecialization,
      differentialSpecializationHom]
  · simp [regularBadEquation, challengeSpecialization, separant, differentialSpecialization,
      differentialSpecializationHom]
  · intro hexact
    obtain ⟨pair, hleft, _, _, hsets⟩ := hexact
    have hzero : (0 : Fin 3) ∈ polynomialAgreementSet
        (regularBadDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
          (algebraMap ℚ AlgebraicClosureField).injective⟩)
        (regularBadChallengeLine regularBadChallenge) (0 : AlgebraicClosureField[X]) := by
      norm_num [polynomialAgreementSet, regularBadDomain, regularBadChallengeLine,
        regularBadFirstWord, regularBadSecondWord, regularBadChallenge]
    have hone : (1 : Fin 3) ∈ polynomialAgreementSet
        (regularBadDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
          (algebraMap ℚ AlgebraicClosureField).injective⟩)
        (regularBadChallengeLine regularBadChallenge) (0 : AlgebraicClosureField[X]) := by
      norm_num [polynomialAgreementSet, regularBadDomain, regularBadChallengeLine,
        regularBadFirstWord, regularBadSecondWord, regularBadChallenge]
    have hsets' : polynomialAgreementSet
        (regularBadDomain.trans ⟨algebraMap ℚ AlgebraicClosureField,
          (algebraMap ℚ AlgebraicClosureField).injective⟩)
        (regularBadChallengeLine regularBadChallenge) (0 : AlgebraicClosureField[X]) =
        commonPolynomialAgreementSet regularBadDomain regularBadFirstWord regularBadSecondWord
          pair.1 pair.2 := by
      exact hsets
    rw [hsets'] at hzero hone
    have hzeroEval := (mem_commonPolynomialAgreementSet ..).mp hzero
    have honeEval := (mem_commonPolynomialAgreementSet ..).mp hone
    norm_num [regularBadDomain, regularBadFirstWord, regularBadSecondWord] at hzeroEval honeEval
    have hdegree : pair.1.degree ≤ 0 := by
      by_cases hp : pair.1 = 0
      · simp [hp]
      · have hnat : pair.1.natDegree < 1 :=
          (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hleft
        have hnat0 : pair.1.natDegree = 0 := by omega
        rw [Polynomial.eq_C_of_natDegree_eq_zero hnat0]
        exact Polynomial.degree_C_le
    have heval : pair.1.eval (regularBadDomain 0) = pair.1.eval (regularBadDomain 1) := by
      rw [Polynomial.eq_C_of_degree_le_zero hdegree]
      simp
    have hzeroP : pair.1.eval (regularBadDomain 0) = 0 := by
      simpa [regularBadDomain] using hzeroEval.1
    have honeP : pair.1.eval (regularBadDomain 1) = 1 := by
      simpa [regularBadDomain] using honeEval.1
    rw [hzeroP, honeP] at heval
    norm_num at heval

private theorem regularBadEquation_weightedDegree :
    regularBadEquation.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
  norm_num [regularBadEquation, MvPolynomial.weightedTotalDegree, MvPolynomial.support_X]

private theorem regularBadEquation_height : CoeffNatDegreeLE regularBadEquation 0 := by
  exact coeffNatDegreeLE_X (R := AlgebraicClosureField) (σ := JetVariable 0)
    (some (0 : Fin 1))

private theorem regularBadBinomial :
    ∀ i : ℕ, 0 < i → i < 1 → (i.choose 0 : AlgebraicClosureField) ≠ 0 := by
  intro i hi hiK
  omega

/-- The finite-family bound includes a concrete nonempty singleton of bad challenges. -/
example :
    ({regularBadChallenge} : Finset AlgebraicClosureField).Nonempty ∧
      (({regularBadChallenge} : Finset AlgebraicClosureField).card : ℚ) ≤
        regularSymbolicAgreementBound 3 0 1 1 1 2 1 0 := by
  classical
  have hsubset : ↑({regularBadChallenge} : Finset AlgebraicClosureField) ⊆
      regularSymbolicBadChallenges regularBadDomain regularBadFirstWord regularBadSecondWord
        (algebraMap ℚ AlgebraicClosureField) regularBadEquation 1 2 := by
    intro z hz
    have hz' : z = regularBadChallenge := by simpa using hz
    rw [hz']
    exact regularBadChallenge_mem
  have hbound := finite_regularSymbolicBadChallenges_card_le regularBadDomain regularBadFirstWord
    regularBadSecondWord (algebraMap ℚ AlgebraicClosureField) regularBadEquation
    1 1 1 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) regularBadEquation_weightedDegree regularBadEquation_height regularBadBinomial
    {regularBadChallenge} hsubset
  refine ⟨by simp, ?_⟩
  norm_num [regularSymbolicAgreementBound] at hbound ⊢

/-- The full bad-challenge set is finite and contains the displayed regular challenge. -/
example :
    regularBadChallenge ∈ regularSymbolicBadChallenges regularBadDomain regularBadFirstWord
      regularBadSecondWord (algebraMap ℚ AlgebraicClosureField) regularBadEquation 1 2 ∧
    (regularSymbolicBadChallenges regularBadDomain regularBadFirstWord regularBadSecondWord
      (algebraMap ℚ AlgebraicClosureField) regularBadEquation 1 2).Finite := by
  constructor
  · exact regularBadChallenge_mem
  · exact regularSymbolicBadChallenges_finite regularBadDomain regularBadFirstWord
      regularBadSecondWord (algebraMap ℚ AlgebraicClosureField) regularBadEquation
      1 1 1 2 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) regularBadEquation_weightedDegree regularBadEquation_height regularBadBinomial

private abbrev derivativeTupleEquation :
    DifferentialPolynomial (Polynomial PairCountingField) 1 :=
  MvPolynomial.X (some (Fin.last 1))

private abbrev derivativeTuple : Fin 1 → ℚ[X] := fun _ ↦ 0

private abbrev derivativeTupleWords : Fin 1 → Fin 1 → ℚ := fun _ _ ↦ 0

private theorem derivativeTuplePullback_coordinate (j : Fin 2) :
    chartTuplePullback (algebraMap ℚ PairCountingField) 0 derivativeTuple
      (MvPolynomial.X (some j)) = 0 := by
  simp [chartTuplePullback, derivativeTuple, powerBatchedJetGraphMap,
    powerBatchedJetGraph, powerBatchedCoordinate, polynomialJet]

private theorem derivativeTuplePullback_separant :
    chartTuplePullback (algebraMap ℚ PairCountingField) 0 derivativeTuple
      (jointInitialJetSeparant 0 derivativeTupleEquation) = 1 := by
  simp [chartTuplePullback, jointInitialJetSeparant, initialJetSeparant,
    derivativeTupleEquation, separant, Fin.last]

private theorem derivativeTupleCommonNumerator_eq (l : Fin 2) :
    jointCommonTaylorNumerator 0 derivativeTupleEquation 1 l =
      MvPolynomial.X (some l) := by
  fin_cases l <;>
    simp [jointCommonTaylorNumerator, commonTaylorNumeratorOver,
      rationalTaylorNumeratorOver, initialJetSeparant, derivativeTupleEquation,
      separant, Fin.last]

private theorem derivativeTupleAdmissible :
    IsAdmissibleChartTupleAtExponent pointDomain derivativeTupleWords
      (algebraMap ℚ PairCountingField) 0 derivativeTupleEquation 2 1 1 1 derivativeTuple := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simp [derivativeTuple]
  · norm_num [commonCurveAgreementSet, derivativeTupleWords, derivativeTuple, pointDomain]
  · rw [show jointInitialJetEquation 0 derivativeTupleEquation =
      MvPolynomial.X (some (1 : Fin 2)) by
        simp [jointInitialJetEquation, initialJetEquation, derivativeTupleEquation]]
    exact derivativeTuplePullback_coordinate 1
  · intro l hl
    have hl' : l = 1 := Fin.ext (by omega)
    subst l
    rw [derivativeTupleCommonNumerator_eq]
    exact derivativeTuplePullback_coordinate 1
  · rw [derivativeTuplePullback_separant]
    norm_num
  · intro l
    rw [derivativeTupleCommonNumerator_eq, derivativeTuplePullback_coordinate,
      derivativeTuplePullback_separant]
    simp [powerBatchedTaylorCoefficient, powerBatchedCoordinate, derivativeTuple]

/-- The derivative-capped tuple bounds apply to a concrete nonempty admissible family. -/
example :
    ({derivativeTuple} : Finset (Fin 1 → ℚ[X])).Nonempty ∧
      (({derivativeTuple} : Finset (Fin 1 → ℚ[X])).card : ℚ) ≤
        firstOrderCurveFiberStageOne 2 1 1 1 ∧
      (admissibleChartTupleFamilyAtExponent pointDomain derivativeTupleWords
        (algebraMap ℚ PairCountingField) 0 derivativeTupleEquation 2 1 1 1).Nonempty ∧
      ((admissibleChartTupleFamilyAtExponent pointDomain derivativeTupleWords
        (algebraMap ℚ PairCountingField) 0 derivativeTupleEquation 2 1 1 1).card : ℚ) ≤
        firstOrderCurveFiberStageOne 2 1 1 1 := by
  classical
  have hτ : TaylorExponentSufficient 1 2 1 := by
    intro l
    fin_cases l <;> norm_num [TaylorExponentSufficient]
  have hjet : derivativeTupleEquation.weightedTotalDegree
      (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ 1 := by
    norm_num [derivativeTupleEquation, MvPolynomial.weightedTotalDegree,
      MvPolynomial.support_X]
  have hderiv : derivativeTupleEquation.degreeOf (some 1) ≤ 1 := by
    norm_num [derivativeTupleEquation, MvPolynomial.degreeOf_X]
  have hmem : derivativeTuple ∈ admissibleChartTupleFamilyAtExponent pointDomain
      derivativeTupleWords (algebraMap ℚ PairCountingField) 0 derivativeTupleEquation 2 1 1 1 :=
    (mem_admissibleChartTupleFamilyAtExponent_iff pointDomain derivativeTupleWords
      (algebraMap ℚ PairCountingField) 0 derivativeTupleEquation 2 1 1 1 (by omega)
      derivativeTuple).2 derivativeTupleAdmissible
  refine ⟨by simp, ?_, ⟨derivativeTuple, hmem⟩, ?_⟩
  · have h := admissibleChartTuples_card_le_derivativeCapped_of_exponent
      pointDomain derivativeTupleWords (algebraMap ℚ PairCountingField) 0
      derivativeTupleEquation 2 1 1 1 1 1 hτ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hjet hderiv {derivativeTuple}
      (by simpa using derivativeTupleAdmissible)
    simpa using h
  · simpa using admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped
      pointDomain derivativeTupleWords (algebraMap ℚ PairCountingField) 0
      derivativeTupleEquation 2 1 1 1 1 1 hτ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hjet hderiv

end

end ReedSolomon
