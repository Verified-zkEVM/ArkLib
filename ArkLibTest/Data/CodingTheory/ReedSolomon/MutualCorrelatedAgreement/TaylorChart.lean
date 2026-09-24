/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PairCounting
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
    rw [show initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation = 1 by
      simp [initialJetSeparant, quadraticJetSampleEquation, separant, Fin.last]]
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
  rw [commonTaylorNumeratorOver, hnumerator]
  simp [initialJetSeparant, quadraticJetSampleEquation, separant, Fin.last]

private theorem quadraticJetSampleEquation_highNumerator_ne (τ : ℕ) :
    map (Polynomial.evalRingHom (2 : ℚ))
      (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation τ 1) ≠ 0 := by
  have hvalue : MvPolynomial.aeval (fun _ : Fin 1 ↦ (0 : ℚ))
      (map (Polynomial.evalRingHom (2 : ℚ))
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation τ 1)) = -4 := by
    rw [quadraticJetSampleEquation_highNumerator_eq]
    norm_num
  intro hzero
  rw [hzero] at hvalue
  norm_num at hvalue

private theorem concreteTaylorChartSetup (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 2 τ) :
    MvPolynomial.aeval concreteJet
        (map (Polynomial.evalRingHom 2)
          (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 ∧
      (∀ l : Fin 2, 1 ≤ l.val →
        MvPolynomial.aeval concreteJet
          (map (Polynomial.evalRingHom 2)
            (commonTaylorNumeratorOver ℚ (Polynomial.C 0)
              quadraticJetSampleEquation τ l.val)) = 0) ∧
      (∀ i ∈ Finset.univ, MvPolynomial.aeval concreteJet
        (map (Polynomial.evalRingHom 2)
          (taylorAgreementEquationOver (F := ℚ) (Polynomial.C 0) quadraticJetSampleEquation 2
            (Polynomial.C (pointDomain i)) (Polynomial.C 0 + Polynomial.X * Polynomial.C 1)
            (τ := τ))) = 0) ∧
      rationalTaylorPolynomial (0 : ℚ)
        (map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        Polynomial.C 2 := by
  let φ : Polynomial ℚ →ₐ[ℚ] ℚ := challengeHom
  have hφ : φ.toRingHom = Polynomial.evalRingHom (2 : ℚ) := challengeHom_toRingHom
  have hS : MvPolynomial.aeval concreteJet
      (map (Polynomial.evalRingHom 2)
        (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 := by
    simp [quadraticJetSampleEquation, initialJetSeparant, separant, Fin.last]
  have hSφ : MvPolynomial.aeval concreteJet
      (map φ.toRingHom
        (initialJetSeparant (Polynomial.C 0) quadraticJetSampleEquation)) ≠ 0 := by
    simpa only [hφ] using hS
  have hjet : polynomialJet (d := 0) (0 : ℚ) (Polynomial.C 2 : ℚ[X]) = concreteJet := by
    funext j
    fin_cases j
    simp [concreteJet, polynomialJet, Polynomial.hasseJet_apply]
  have hsolution :
    differentialSpecialization (map φ.toRingHom quadraticJetSampleEquation)
        (Polynomial.C 2 : ℚ[X]) = 0 := by
    simp [quadraticJetSampleEquation, φ, differentialSpecialization,
      differentialSpecializationHom, challengeHom]
  have hseparant :
      jetEvaluation (separant (map φ.toRingHom quadraticJetSampleEquation) (Fin.last 0)) 0
        (polynomialJet (d := 0) 0 (Polynomial.C 2 : ℚ[X])) ≠ 0 := by
    rw [hjet]
    norm_num [jetEvaluation, separant, quadraticJetSampleEquation, φ, challengeHom]
  have hpoly :
      rationalTaylorPolynomial 0 (map φ.toRingHom quadraticJetSampleEquation) 2 concreteJet =
      Polynomial.C 2 := by
    rw [← hjet]
    exact rationalTaylorPolynomial_polynomialJet 0
      (map φ.toRingHom quadraticJetSampleEquation) (Polynomial.C 2) hsolution hseparant
      (by norm_num) (by intro i hi hiK; norm_num)
  have hhigh : ∀ l : Fin 2, 1 ≤ l.val → MvPolynomial.aeval concreteJet
      (map (Polynomial.evalRingHom 2)
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
            (map φ.toRingHom quadraticJetSampleEquation) 2 concreteJet)).coeff 1 = 0 := by
      rw [show φ (Polynomial.C (0 : ℚ)) = 0 by simp [φ, challengeHom], hpoly]
      simp
    rw [hcoeff] at hnum
    simp only [mul_zero] at hnum
    rw [← hφ]
    simpa only [Fin.val_one] using hnum
  have hcuts : ∀ i ∈ Finset.univ, MvPolynomial.aeval concreteJet
      (map (Polynomial.evalRingHom 2)
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
        (map (Polynomial.evalRingHom 2)
          (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 1)) = 0 ∧
      map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 1) ≠ 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
          (map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) ∧
      concreteJet = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          2 * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval concreteJet
            (map (Polynomial.evalRingHom 2)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 1 l.val)) =
          MvPolynomial.aeval concreteJet
              (map (Polynomial.evalRingHom 2)
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
        (map (Polynomial.evalRingHom 2)
          (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 1)) = 0 ∧
      map (Polynomial.evalRingHom 2)
        (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 1) ≠ 0 ∧
      rationalTaylorPolynomial (0 : ℚ)
          (map (Polynomial.evalRingHom 2) quadraticJetSampleEquation) 2 concreteJet =
        P₀.map (RingHom.id ℚ) + Polynomial.C 2 * P₁.map (RingHom.id ℚ) ∧
      concreteJet = (fun j ↦
        polynomialJet (d := 0) (0 : ℚ) (P₀.map (RingHom.id ℚ)) j +
          2 * polynomialJet (d := 0) (0 : ℚ) (P₁.map (RingHom.id ℚ)) j) ∧
      ∀ l : Fin 2,
        MvPolynomial.aeval concreteJet
            (map (Polynomial.evalRingHom 2)
              (commonTaylorNumeratorOver ℚ (Polynomial.C 0) quadraticJetSampleEquation 4 l.val)) =
          MvPolynomial.aeval concreteJet
              (map (Polynomial.evalRingHom 2)
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
          (map (Polynomial.evalRingHom (1 : ZMod 2)) frobeniusSampleEquation) 1
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
      (map (Polynomial.evalRingHom (1 : ZMod 2))
        (initialJetSeparant (Polynomial.C (0 : ZMod 2)) frobeniusSampleEquation)) ≠ 0 := by
    simp [frobeniusSampleEquation, initialJetSeparant, separant]
  have hsparse : ∀ l : Fin 1, ¬2 ^ 1 ∣ l.val →
      MvPolynomial.aeval frobeniusSampleJet
        (map (Polynomial.evalRingHom (1 : ZMod 2))
          (commonTaylorNumeratorOver (F := ZMod 2) (Polynomial.C 0)
            frobeniusSampleEquation 2 l.val)) = 0 := by
    intro l hl
    have hl0 : l.val = 0 := by omega
    have hdiv : 2 ^ 1 ∣ l.val := by rw [hl0]; exact dvd_zero _
    exact (hl hdiv).elim
  have hcuts : ∀ i : Fin 1, i ∈ Finset.univ →
      MvPolynomial.aeval frobeniusSampleJet
        (map (Polynomial.evalRingHom (1 : ZMod 2))
          (taylorAgreementEquationOver (F := ZMod 2) (Polynomial.C 0)
            frobeniusSampleEquation 1 (Polynomial.C (1 : ZMod 2))
            (Polynomial.C (1 : ZMod 2) + Polynomial.X ^ (2 ^ 1) *
              Polynomial.C (1 : ZMod 2)) (τ := 2))) = 0 := by
    intro i hi
    have hvalue :
        (rationalTaylorPolynomial (φ (Polynomial.C (0 : ZMod 2)))
          (map φ.toRingHom frobeniusSampleEquation) 1 frobeniusSampleJet).eval
            (φ (Polynomial.C (1 : ZMod 2))) =
          φ (Polynomial.C (1 : ZMod 2) + Polynomial.X ^ (2 ^ 1) *
            Polynomial.C (1 : ZMod 2)) := by
      have hcenter : φ (Polynomial.C (0 : ZMod 2)) = 0 := by simp [φ]
      have hx : φ (Polynomial.C (1 : ZMod 2)) = 1 := by simp [φ]
      have hc : rationalTaylorCoefficient (0 : ZMod 2)
          (map φ.toRingHom frobeniusSampleEquation) frobeniusSampleJet 0 = 0 := by
        simpa [frobeniusSampleJet] using
          rationalTaylorCoefficient_initial (0 : ZMod 2)
            (map φ.toRingHom frobeniusSampleEquation) frobeniusSampleJet (0 : Fin 1)
      have hcEval : rationalTaylorCoefficient (0 : ZMod 2)
          (map (Polynomial.evalRingHom (1 : ZMod 2)) frobeniusSampleEquation)
            frobeniusSampleJet 0 = 0 := by
        simpa only [hφ] using hc
      have hsum : (1 : ZMod 2) + 1 = 0 := by
        exact ZMod.natCast_self' 1
      rw [hcenter, hx, eval_rationalTaylorPolynomial]
      simp [hcEval, hsum, φ]
    have hSφ : MvPolynomial.aeval frobeniusSampleJet
        (map φ.toRingHom
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

end

end ReedSolomon
