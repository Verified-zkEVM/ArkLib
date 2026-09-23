/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
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

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {E : Type*} [Field E] {r : ℕ}

/-- The initial equation in joint challenge and initial-jet coordinates. -/
def jointInitialJetEquation (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (PolynomialDifferential.initialJetEquation (Polynomial.C center) Q)

/-- The initial separant in joint challenge and initial-jet coordinates. -/
def jointInitialJetSeparant (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (PolynomialDifferential.initialJetSeparant (Polynomial.C center) Q)

/-- A cleared Taylor coefficient in joint challenge and initial-jet coordinates. -/
def jointCommonTaylorNumerator (center : E) (Q : DifferentialPolynomial E[X] r)
    (τ : ℕ) {K : ℕ} (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (PolynomialDifferential.commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)

/-- The cleared agreement equation in joint challenge and initial-jet coordinates. -/
def jointTaylorAgreementEquation (center : E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (x y : E[X]) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    ((∑ l : Fin K, MvPolynomial.C ((x - Polynomial.C center) ^ l.val) *
      PolynomialDifferential.commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val) -
        MvPolynomial.C y *
          PolynomialDifferential.initialJetSeparant (Polynomial.C center) Q ^ τ)

/-- The cleared equation identifying one Taylor coefficient with an affine pair. -/
def jointTaylorReconstructionError (center : E) (Q : DifferentialPolynomial E[X] r)
    (τ : ℕ) {K : ℕ} (P₀ P₁ : E[X]) (l : Fin K) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  jointCommonTaylorNumerator center Q τ l -
    jointInitialJetSeparant center Q ^ τ *
      (MvPolynomial.C ((Polynomial.taylor center P₀).coeff l.val) +
        MvPolynomial.X none * MvPolynomial.C ((Polynomial.taylor center P₁).coeff l.val))

/-- The polynomial parametrization of the initial jets of an affine pair. -/
def affinePairCurve (center : E) (P₀ P₁ : E[X]) :
    Option (Fin (r + 1)) → E[X] := fun i ↦
  match i with
  | none => Polynomial.X
  | some j => Polynomial.C (polynomialJet center P₀ j) +
      Polynomial.X * Polynomial.C (polynomialJet center P₁ j)

private theorem eval_jointInitialJetSeparant (center : E)
    (Q : DifferentialPolynomial E[X] r) (x : Option (Fin (r + 1)) → E) :
    aeval x (jointInitialJetSeparant center Q) =
      aeval (fun j ↦ x (some j))
        (initialJetSeparant center (MvPolynomial.map
          (Polynomial.aeval (x none)).toRingHom Q)) := by
  rw [jointInitialJetSeparant, aeval_optionEquivRight_symm, map_initialJetSeparant]
  simp

private theorem eval_jointCommonTaylorNumerator (center : E)
    (Q : DifferentialPolynomial E[X] r) (τ : ℕ) {K : ℕ} (l : Fin K)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointCommonTaylorNumerator center Q τ l) =
      aeval (fun j ↦ x (some j))
        (commonTaylorNumerator center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) τ l.val) := by
  rw [jointCommonTaylorNumerator, aeval_optionEquivRight_symm,
    map_commonTaylorNumeratorOver]
  simp [commonTaylorNumerator, commonTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

private theorem map_taylorAgreementExpression (center : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (x y : E[X])
    (φ : E[X] →ₐ[E] E) :
    MvPolynomial.map φ.toRingHom
        ((∑ l : Fin K, MvPolynomial.C ((x - Polynomial.C center) ^ l.val) *
          PolynomialDifferential.commonTaylorNumeratorOver E
            (Polynomial.C center) Q τ l.val) -
            MvPolynomial.C y *
              PolynomialDifferential.initialJetSeparant (Polynomial.C center) Q ^ τ) =
      taylorAgreementEquation (φ (Polynomial.C center))
        (MvPolynomial.map φ.toRingHom Q) K τ (φ x) (φ y) := by
  rw [taylorAgreementEquation, map_sub, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    rw [map_mul, MvPolynomial.map_C, map_commonTaylorNumeratorOver]
    simp [commonTaylorNumerator, commonTaylorNumeratorOver,
      rationalTaylorNumeratorOver_eq]
  · rw [map_mul, MvPolynomial.map_C, map_pow, map_initialJetSeparant]
    simp

private theorem eval_jointTaylorAgreementEquation (center : E)
    (Q : DifferentialPolynomial E[X] r) (K τ : ℕ) (x₀ y₀ : E[X])
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointTaylorAgreementEquation center Q K τ x₀ y₀) =
      aeval (fun j ↦ x (some j))
        (taylorAgreementEquation center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) K τ
          (Polynomial.eval (x none) x₀) (Polynomial.eval (x none) y₀)) := by
  rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm,
    map_taylorAgreementExpression]
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
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, ?_⟩
  intro x hS hhigh hcuts
  let z := x none
  let jet : Fin (r + 1) → E := fun j ↦ x (some j)
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  let Qz : DifferentialPolynomial E r := MvPolynomial.map φ.toRingHom Q
  have hS_eq : aeval x (jointInitialJetSeparant center Q) =
      aeval jet (initialJetSeparant center Qz) := by
    simpa only [jet, z, Qz, φ] using eval_jointInitialJetSeparant center Q x
  have hS' : aeval jet (initialJetSeparant center (MvPolynomial.map φ.toRingHom Q)) ≠ 0 := by
    change aeval jet (initialJetSeparant center Qz) ≠ 0
    rw [hS_eq] at hS
    exact hS
  have hhigh' : ∀ l : ℕ, k ≤ l → l < K →
      aeval jet (commonTaylorNumerator center Qz τ l) = 0 := by
    intro l hl hlK
    let l' : Fin K := ⟨l, hlK⟩
    have hz := hhigh l' (by simpa [l'] using hl)
    have hnum_eq : aeval x (jointCommonTaylorNumerator center Q τ l') =
        aeval jet (commonTaylorNumerator center Qz τ l) := by
      simpa only [jet, z, Qz, φ, l'] using
        eval_jointCommonTaylorNumerator center Q τ l' x
    rw [hnum_eq] at hz
    exact hz
  have hcuts' : ∀ i ∈ sample,
      aeval jet (taylorAgreementEquation center Qz K τ
        (iota (domain i)) (iota (f i) + z * iota (g i))) = 0 := by
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
    simpa only [mul_comm] using hz
  have hdegree :
      (rationalTaylorPolynomial center Qz K jet).degree < k :=
    degree_rationalTaylorPolynomial_lt center Qz hτ k jet hS' hhigh'
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center Qz K jet).eval
        (domain.trans ⟨iota, iota.injective⟩ i) = iota (f i) + z * iota (g i) := by
    intro i hi
    exact (taylorAgreementEquation_eq_zero_iff center Qz hτ jet hS' _ _).mp (hcuts' i hi)
  have hpoly := hrecognize iota z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · have hjetAffine := polynomialJet_affine_combination (d := r) center z
      (P₀.map iota) (P₁.map iota)
    have hjetRec := polynomialJet_rationalTaylorPolynomial center Qz hK jet
    rw [hpoly, hjetAffine] at hjetRec
    exact hjetRec.symm
  · intro l
    have hcoeff := aeval_commonTaylorNumerator center Qz jet (hτ l) hS'
    have hnum_eq : aeval x (jointCommonTaylorNumerator center Q τ l) =
        aeval jet (commonTaylorNumerator center Qz τ l.val) := by
      simpa only [jet, z, Qz, φ] using eval_jointCommonTaylorNumerator center Q τ l x
    have hsep_eq : aeval x (jointInitialJetSeparant center Q) =
        aeval jet (initialJetSeparant center Qz) := by
      simpa only [jet, z, Qz, φ] using eval_jointInitialJetSeparant center Q x
    calc
      aeval x (jointCommonTaylorNumerator center Q τ l) =
          aeval jet (commonTaylorNumerator center Qz τ l.val) := hnum_eq
      _ = aeval jet (initialJetSeparant center Qz) ^ τ *
          (Polynomial.taylor center
            (rationalTaylorPolynomial center Qz K jet)).coeff l.val := by
        rw [hcoeff, coeff_taylor_rationalTaylorPolynomial]
        simp [l.isLt]
      _ = aeval x (jointInitialJetSeparant center Q) ^ τ *
          (Polynomial.taylor center
            (P₀.map iota + Polynomial.C z * P₁.map iota)).coeff l.val := by
        rw [← hsep_eq, ← hpoly, coeff_taylor_rationalTaylorPolynomial]

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

end

end ReedSolomon
