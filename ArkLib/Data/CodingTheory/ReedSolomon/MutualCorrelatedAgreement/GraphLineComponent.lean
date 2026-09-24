/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
/-!
# Graph-line recognition on regular Taylor components

The joint Taylor chart keeps the challenge as one polynomial variable and the initial jet as
the remaining variables. A common sample and the high Taylor cuts force every regular point of
the chart onto one graph line over the base field. A positive-dimensional prime component with
these equations is parametrized by that graph line, so every equation in the component ideal
vanishes after restriction to it.

## Main statements

* `exists_graphLine_pair_of_joint_taylor_chart`: reconstruction on a regular joint chart point.
* `exists_graphLine_pair_of_regular_component`: a positive-dimensional prime component lies on
  a graph line determined by the common sample.
* `aeval_jointTaylorAgreementEquation_eq_zero_iff`,
  `commonAgreement_of_jointTaylorAgreementEquation_mem_prime`, and
  `exists_graphLine_pair_of_regular_component_agreements`: agreement extraction from regular
  components.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {E : Type*} [Field E] {r : ℕ}

/-- Evaluating the joint separant specializes its challenge before evaluating the jet. -/
theorem eval_jointInitialJetSeparant (center : E)
    (Q : DifferentialPolynomial E[X] r) (x : Option (Fin (r + 1)) → E) :
    aeval x (jointInitialJetSeparant center Q) =
      aeval (fun j ↦ x (some j))
        (initialJetSeparant center (MvPolynomial.map
          (Polynomial.aeval (x none)).toRingHom Q)) := by
  rw [jointInitialJetSeparant, aeval_optionEquivRight_symm, map_initialJetSeparant]
  simp

/-- Evaluating a joint high cut specializes its challenge before evaluating the jet. -/
theorem eval_jointCommonTaylorNumerator (center : E)
    (Q : DifferentialPolynomial E[X] r) (τ : ℕ) {K : ℕ} (l : Fin K)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointCommonTaylorNumerator center Q τ l) =
      aeval (fun j ↦ x (some j))
        (commonTaylorNumerator center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) τ l.val) := by
  rw [jointCommonTaylorNumerator, aeval_optionEquivRight_symm,
    map_commonTaylorNumeratorOver]
  simp [commonTaylorNumerator, commonTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

/-- Evaluating a joint agreement cut specializes its challenge and received value. -/
theorem eval_jointTaylorAgreementEquation (center : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (x₀ y₀ : E[X])
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointTaylorAgreementEquation center Q K τ x₀ y₀) =
      aeval (fun j ↦ x (some j))
        (taylorAgreementEquation center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) K τ
          (Polynomial.eval (x none) x₀) (Polynomial.eval (x none) y₀)) := by
  rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm,
    map_taylorAgreementEquationOver_eq (τ := τ)]
  simp

variable {F : Type*} [Field F] {n k K : ℕ}

/-- A common sample determines one base-field pair for every regular point of the joint Taylor
chart satisfying the high Taylor cuts and the sample agreement equations. At each such point,
the reconstructed polynomial, initial jet, and cleared Taylor coefficients are those of that
same affine pair. -/
theorem exists_graphLine_pair_of_joint_taylor_chart
    (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) (iota : F →+* E) (center : E)
    (Q : DifferentialPolynomial E[X] r) (hK : r < K) (τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      ∀ x : Option (Fin (r + 1)) → E,
        aeval x (jointInitialJetSeparant center Q) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          aeval x (jointCommonTaylorNumerator center Q τ l) = 0) →
        (∀ i ∈ sample,
          aeval x (jointTaylorAgreementEquation center Q K τ
            (Polynomial.C (iota (domain i)))
            (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))) = 0) →
        rationalTaylorPolynomial center
            (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q) K
            (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota ∧
          (fun j ↦ x (some j)) =
            (fun j ↦ polynomialJet center (P₀.map iota) j +
              x none * polynomialJet center (P₁.map iota) j) ∧
          ∀ l : Fin K,
            aeval x (jointCommonTaylorNumerator center Q τ l) =
              aeval x (jointInitialJetSeparant center Q) ^ τ *
                (Polynomial.taylor center
                  (P₀.map iota + Polynomial.C (x none) * P₁.map iota)).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample_of_exponent domain f g sample hsample iota center Q
      hK τ hτ
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, ?_⟩
  intro x hS hhigh hcuts
  let z := x none
  let jet : Fin (r + 1) → E := fun j ↦ x (some j)
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  let Qz : DifferentialPolynomial E r := MvPolynomial.map φ.toRingHom Q
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hcenterRing : φ.toRingHom (Polynomial.C center) = center := hcenter
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ, Polynomial.evalRingHom]
  have hS_eq : aeval x (jointInitialJetSeparant center Q) =
      aeval jet (initialJetSeparant center Qz) := by
    simpa only [jet, z, Qz, φ] using eval_jointInitialJetSeparant center Q x
  have hS_field : aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [← hS_eq]
    exact hS
  have hS' : aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
      (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
    rw [← hφ, map_initialJetSeparant]
    rw [hcenterRing]
    simpa only [Qz] using hS_field
  have hhigh' : ∀ l : Fin K, k ≤ l.val →
      aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) = 0 := by
    intro l hl
    have hz := hhigh l hl
    have hnum_eq : aeval x (jointCommonTaylorNumerator center Q τ l) =
        aeval jet (commonTaylorNumerator center Qz τ l.val) := by
      simpa only [jet, z, Qz, φ] using
        eval_jointCommonTaylorNumerator center Q τ l x
    rw [hnum_eq] at hz
    rw [← hφ, map_commonTaylorNumeratorOver_eq, hcenter]
    simpa only [Qz] using hz
  have hcuts' : ∀ i ∈ sample,
      aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C (iota (domain i)))
          (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
          (τ := τ))) = 0 := by
    intro i hi
    have hz := hcuts i hi
    have hagree_eq := eval_jointTaylorAgreementEquation center Q K τ
      (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) x
    change aeval x (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))) =
      aeval jet (taylorAgreementEquation center Qz K τ
        (Polynomial.eval z (Polynomial.C (iota (domain i))) )
        (Polynomial.eval z
          (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))))) at hagree_eq
    have hvalx : Polynomial.eval z (Polynomial.C (iota (domain i))) = iota (domain i) := by
      simp [z]
    have hvaly : Polynomial.eval z
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) =
          iota (f i) + z * iota (g i) := by
      simp [z]
      ring
    rw [hvalx, hvaly] at hagree_eq
    rw [hagree_eq] at hz
    have hmap : MvPolynomial.map (Polynomial.evalRingHom z)
        (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C (iota (domain i)))
          (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
          (τ := τ)) =
        taylorAgreementEquation center Qz K τ (iota (domain i))
          (iota (f i) + z * iota (g i)) := by
      rw [← hφ, map_taylorAgreementEquationOver_eq (τ := τ)]
      simp [φ, hcenter, Qz, z]
      congr 1
      ring
    calc
      aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C (iota (domain i)))
          (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
          (τ := τ))) =
          aeval jet (taylorAgreementEquation center Qz K τ
            (iota (domain i)) (iota (f i) + z * iota (g i))) := by rw [hmap]
      _ = 0 := by simpa only [mul_comm] using hz
  obtain ⟨hpoly, hjet, hcoeff⟩ := hrecognize z jet hS' hhigh' hcuts'
  refine ⟨hpoly, ?_, ?_⟩
  · simpa only [jet, z] using hjet
  · intro l
    have hnum := eval_jointCommonTaylorNumerator center Q τ l x
    have hsep := eval_jointInitialJetSeparant center Q x
    have hcoeff' := hcoeff l
    rw [← hφ, map_commonTaylorNumeratorOver_eq, hcenter, map_initialJetSeparant,
      hcenterRing]
      at hcoeff'
    calc
      aeval x (jointCommonTaylorNumerator center Q τ l) =
          aeval jet (commonTaylorNumerator center Qz τ l.val) := hnum
      _ = aeval jet (initialJetSeparant center Qz) ^ τ *
          (Polynomial.taylor center (Polynomial.map iota P₀ +
            Polynomial.C z * Polynomial.map iota P₁)).coeff l.val := by
        simpa only [Qz] using hcoeff'
      _ = aeval x (jointInitialJetSeparant center Q) ^ τ *
          (Polynomial.taylor center (Polynomial.map iota P₀ +
            Polynomial.C z * Polynomial.map iota P₁)).coeff l.val := by
        rw [← hsep]

/-- A positive-dimensional prime component satisfying the initial equation, high Taylor cuts,
and a common sample of agreement cuts is parametrized by the affine pair determined by that
sample. Every polynomial in the component ideal vanishes after this parametrization, and the
initial separant remains nonzero. -/
theorem exists_graphLine_pair_of_regular_component [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) (iota : F →+* E) (center : E)
    (Q : DifferentialPolynomial E[X] r) (hK : r < K) (τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [P.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hd : 0 < (affineHilbertPolynomial P).natDegree)
    (hinit : jointInitialJetEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ P)
    (hcuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      (∀ x ∈ {x | x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        ∃ z : E, x = fun i ↦
          (affinePairCurve center (P₀.map iota) (P₁.map iota) i).eval z) ∧
      (∀ p ∈ P,
        aeval (affinePairCurve center (P₀.map iota) (P₁.map iota)) p = 0) ∧
      aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
        (jointInitialJetEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
          (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
        (jointInitialJetSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
          (jointTaylorReconstructionError center Q τ (P₀.map iota) (P₁.map iota) l) = 0 := by
  classical
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_pair_of_joint_taylor_chart domain f g sample hsample iota center Q hK τ hτ
  let w : Option (Fin (r + 1)) → E[X] :=
    affinePairCurve (r := r) center (P₀.map iota) (P₁.map iota)
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0) :=
    hrecognize x hx.2
      (fun l hl ↦ by
        exact hx.1 _ (hhigh l hl))
      (fun i hi ↦ by
        exact hx.1 _ (hcuts i hi))
  have hgraph : ∀ x, x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      ∃ z : E, x = fun i ↦ (w i).eval z := by
    intro x hx
    refine ⟨x none, ?_⟩
    funext i
    cases i with
    | none => simp [w, affinePairCurve]
    | some j =>
      have hj := congrFun (hpoint x hx).2.1 j
      change x (some j) =
        (Polynomial.C (polynomialJet center (P₀.map iota) j) +
          Polynomial.X * Polynomial.C (polynomialJet center (P₁.map iota) j)).eval (x none)
      rw [Polynomial.eval_add, Polynomial.eval_mul]
      simp only [Polynomial.eval_C, Polynomial.eval_X]
      simpa only [mul_comm] using hj
  have hgraphRange : ∀ x, x ∈ zeroLocus E P →
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
        ∃ z : E, x = fun i ↦ (w i).eval z := by
    intro x hx hsx
    exact hgraph x ⟨hx, hsx⟩
  have hregular : IsLeftRegular (Ideal.Quotient.mk P (jointInitialJetSeparant center Q)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hvanish : ∀ p ∈ P, aeval w p = 0 := by
    intro p hp
    apply MvPolynomial.aeval_eq_zero_of_principalOpen_subset_range hregular hd w hgraphRange
    intro x hx hsx
    exact hx p hp
  have hinfinite :
      {x | x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0}.Infinite := by
    intro hfinite
    have hzero := (MvPolynomial.finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp hfinite
    omega
  have hseparant : aeval w (jointInitialJetSeparant center Q) ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := hinfinite.nonempty
    obtain ⟨z, hxw⟩ := hgraph x hx
    have heval : aeval x (jointInitialJetSeparant center Q) =
        (aeval w (jointInitialJetSeparant center Q)).eval z := by
      rw [MvPolynomial.polynomial_eval_aeval]
      rw [← hxw]
      simp only [MvPolynomial.aeval_eq_eval]
    rw [hzero, Polynomial.eval_zero] at heval
    exact hx.2 heval
  have herror (l : Fin K) :
      aeval w
        (jointTaylorReconstructionError center Q τ (P₀.map iota) (P₁.map iota) l) = 0 := by
    apply MvPolynomial.aeval_eq_zero_of_principalOpen_subset_range hregular hd w hgraphRange
    intro x hx hsx
    have hcoeff := (hpoint x ⟨hx, hsx⟩).2.2 l
    have hlinear : (Polynomial.taylor center
        (P₀.map iota + Polynomial.C (x none) * P₁.map iota)).coeff l.val =
        (Polynomial.taylor center (P₀.map iota)).coeff l.val +
          x none * (Polynomial.taylor center (P₁.map iota)).coeff l.val := by
      rw [← Polynomial.smul_eq_C_mul, map_add, map_smul]
      simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
    simp only [jointTaylorReconstructionError, map_sub, map_mul, map_pow, map_add,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self,
      RingHom.id_apply]
    rw [hcoeff, hlinear, sub_self]
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish,
    hvanish _ hinit, (fun l hl ↦ hvanish _ (hhigh l hl)), hseparant, herror⟩

/-- A regular joint agreement equation vanishes exactly when the reconstructed polynomial takes
the received value at the challenge coordinate. -/
theorem aeval_jointTaylorAgreementEquation_eq_zero_iff
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (x : Option (Fin (r + 1)) → E)
    (hs : aeval x (jointInitialJetSeparant center Q) ≠ 0) (alpha f g : E) :
    aeval x (jointTaylorAgreementEquation center Q K τ (Polynomial.C alpha)
      (Polynomial.C f + Polynomial.X * Polynomial.C g)) = 0 ↔
      (rationalTaylorPolynomial center
        (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q) K
        (fun j ↦ x (some j))).eval alpha = f + x none * g := by
  let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
    ext a <;> simp [φ]
  have hs' : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
    simpa only [jointInitialJetSeparant, aeval_optionEquivRight_symm, φ] using hs
  rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm]
  have hiff := aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hs' (Polynomial.C alpha)
    (Polynomial.C f + Polynomial.X * Polynomial.C g)
  simpa only [hφ, φ, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply] using hiff

/-- An agreement equation in a positive-dimensional regular component forces the corresponding
received coordinate to agree with the pair parametrizing that component. -/
theorem commonAgreement_of_jointTaylorAgreementEquation_mem_prime [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [P.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hd : 0 < (affineHilbertPolynomial P).natDegree) (P₀ P₁ : F[X])
    (hgraph : ∀ x ∈ {x | x ∈ zeroLocus E P ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0},
      ∃ z : E, x = fun j ↦
        (affinePairCurve center (P₀.map iota) (P₁.map iota) j).eval z)
    (hpoly : ∀ x, x ∈ zeroLocus E P → aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota)
    (i : Fin n)
    (hcut : jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) ∈ P) :
    P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i := by
  have hregular : IsLeftRegular (Ideal.Quotient.mk P (jointInitialJetSeparant center Q)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  let regularSet := {x : Option (Fin (r + 1)) → E |
    x ∈ zeroLocus E P ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0}
  have hinfinite : regularSet.Infinite := by
    intro hfinite
    have hzero := (MvPolynomial.finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp hfinite
    omega
  have hcoords (x : Option (Fin (r + 1)) → E) (hx : x ∈ regularSet)
      (j : Fin (r + 1)) :
      x (some j) = polynomialJet center (P₀.map iota) j +
        x none * polynomialJet center (P₁.map iota) j := by
    obtain ⟨z, hz⟩ := hgraph x hx
    have hnone : x none = z := by
      have h := congrFun hz none
      simpa [affinePairCurve] using h
    have hsome := congrFun hz (some j)
    have hsome' : x (some j) = polynomialJet center (P₀.map iota) j +
        z * polynomialJet center (P₁.map iota) j := by
      simpa only [affinePairCurve, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, mul_comm] using hsome
    rw [hnone]
    exact hsome'
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none) regularSet := by
    intro x hx y hy hxy
    change x none = y none at hxy
    funext j
    cases j with
    | none => exact hxy
    | some j => rw [hcoords x hx j, hcoords y hy j, hxy]
  let mismatch : E[X] :=
    Polynomial.C (iota (P₀.eval (domain i)) - iota (f i)) +
      Polynomial.X * Polynomial.C (iota (P₁.eval (domain i)) - iota (g i))
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    have heval := (aeval_jointTaylorAgreementEquation_eq_zero_iff center Q K τ hτ x hx.2
      (iota (domain i)) (iota (f i)) (iota (g i))).mp (hx.1 _ hcut)
    rw [hpoly x hx.1 hx.2] at heval
    have heval' : iota (P₀.eval (domain i)) + x none * iota (P₁.eval (domain i)) =
        iota (f i) + x none * iota (g i) := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply] using heval
    change mismatch.eval (x none) = 0
    simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    linear_combination heval'
  have hconst := congrArg (fun R : E[X] ↦ R.eval 0) hzero
  have hone := congrArg (fun R : E[X] ↦ R.eval 1) hzero
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_zero] at hconst
  simp only [mismatch, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X, one_mul, Polynomial.eval_zero] at hone
  refine ⟨iota.injective (sub_eq_zero.mp hconst), ?_⟩
  rw [hconst, zero_add] at hone
  exact iota.injective (sub_eq_zero.mp hone)

/-- A positive-dimensional regular component supported on any `L` agreement cuts determines a
degree-bounded pair with at least `L` common agreements and all chart restriction identities. -/
theorem exists_graphLine_pair_of_regular_component_agreements [IsAlgClosed E]
    [DecidableEq F] {L : ℕ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [P.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ P)
    (hd : 0 < (affineHilbertPolynomial P).natDegree)
    (hinit : jointInitialJetEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ P)
    (hcuts : ∀ i ∈ indices,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
        (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i))) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      L ≤ (commonPolynomialAgreementSet domain f g P₀ P₁).card ∧
      (∀ x ∈ {x | x ∈ zeroLocus E P ∧
          aeval x (jointInitialJetSeparant center Q) ≠ 0},
        ∃ z : E, x = fun j ↦
          (affinePairCurve center (P₀.map iota) (P₁.map iota) j).eval z) ∧
      (∀ p ∈ P, aeval (affinePairCurve center (P₀.map iota) (P₁.map iota)) p = 0) ∧
      aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
        (jointInitialJetEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
          (jointCommonTaylorNumerator center Q τ l) = 0) ∧
      aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
        (jointInitialJetSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        aeval (affinePairCurve center (P₀.map iota) (P₁.map iota))
          (jointTaylorReconstructionError center Q τ (P₀.map iota) (P₁.map iota) l) = 0 := by
  classical
  obtain ⟨sample, hsub, hsample⟩ := Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hinitPair,
      hhighPair, hregularPair, hreconstruction⟩ :=
    exists_graphLine_pair_of_regular_component domain f g sample hsample iota center Q hK τ hτ
      P hs hd hinit hhigh (fun i hi ↦ hcuts i (hsub hi))
  have hpoly : ∀ x, x ∈ zeroLocus E P →
      aeval x (jointInitialJetSeparant center Q) ≠ 0 →
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = P₀.map iota + Polynomial.C (x none) * P₁.map iota := by
    intro x hx hsep
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ]
    have hS : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
      simpa only [jointInitialJetSeparant, aeval_optionEquivRight_symm, φ] using hsep
    have hdegree := degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
      φ (Polynomial.C center) Q K k τ hτ (fun j ↦ x (some j)) hS
      (fun l hl ↦ by
        have hz := hx _ (hhigh l hl)
        simpa only [jointCommonTaylorNumerator, aeval_optionEquivRight_symm, φ] using hz)
    have hcenter : φ (Polynomial.C center) = center := by simp [φ]
    rw [hcenter, hφ] at hdegree
    have hpairdegree : (P₀.map iota + Polynomial.C (x none) * P₁.map iota).degree < k := by
      apply (Polynomial.degree_add_le _ _).trans_lt
      apply max_lt (Polynomial.degree_map_le.trans_lt hP₀)
      rw [← Polynomial.smul_eq_C_mul]
      exact (Polynomial.degree_smul_le _ _).trans_lt (Polynomial.degree_map_le.trans_lt hP₁)
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
      (domain.trans ⟨iota, iota.injective⟩).injective.injOn
    · simpa only [hsample] using hdegree
    · simpa only [hsample] using hpairdegree
    · intro i hi
      have heval := (aeval_jointTaylorAgreementEquation_eq_zero_iff center Q K τ hτ x hsep
        (iota (domain i)) (iota (f i)) (iota (g i))).mp
        (hx _ (hcuts i (hsub hi)))
      simpa only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_map, Polynomial.eval₂_at_apply,
        (hsamplePair i hi).1, (hsamplePair i hi).2] using heval
  refine ⟨P₀, P₁, hP₀, hP₁, ?_, hgraph, hvanish, hinitPair, hhighPair,
    hregularPair, hreconstruction⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [commonPolynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact commonAgreement_of_jointTaylorAgreementEquation_mem_prime domain f g iota center Q K τ hτ
    P hs hd P₀ P₁ hgraph hpoly i (hcuts i hi)

end

end ReedSolomon
