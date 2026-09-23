/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
public import ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Symbolic equations on the rational Taylor chart

The rational Taylor chart can retain a polynomial coefficient parameter while expressing
agreement cuts. Their joint degree is bounded by the jet degree and coefficient height of the
differential polynomial. Vanishing symbolic cuts also force the corresponding coefficients of
the reconstructed polynomial to vanish after coefficient specialization.

## Main statements

* `coeffNatDegreeLE_initialJetEquation` and
  `jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE`: coefficient-height and joint-degree
  bounds for the initial equation.
* `taylorAgreementEquationOver` and
  `jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent`: affine agreement cuts
  over a polynomial parameter and their joint-degree bound.
* `aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent` and
  `sparse_rationalTaylorPolynomial_of_symbolic_cuts`: symbolic numerators evaluate to reconstructed
  Taylor coefficients, and their cuts force sparsity.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {r : ℕ}

/-- The coefficient height of `Q` also bounds that of its initial equation at a constant center.
-/
theorem coeffNatDegreeLE_initialJetEquation (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) {h : ℕ}
    (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (initialJetEquation (Polynomial.C center) Q) h := by
  apply hQ.aeval
  intro i
  cases i with
  | none => exact coeffNatDegreeLE_C (by simp)
  | some i => exact coeffNatDegreeLE_X i

/-- The joint degree of the initial equation is bounded by the jet degree and coefficient height.
-/
theorem jointTotalDegree_initialJetEquation_le (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v)
    (hh : ∀ m ∈ (initialJetEquation (Polynomial.C center) Q).support,
      ((initialJetEquation (Polynomial.C center) Q).coeff m).natDegree ≤ h) :
    jointTotalDegree (initialJetEquation (Polynomial.C center) Q) ≤ v + h := by
  have hd := jointTotalDegree_le_of_natDegree_coeff_le
    (initialJetEquation (Polynomial.C center) Q) h hh
  have hj := (totalDegree_initialJetEquation_le (Polynomial.C center) Q).trans hv
  omega

/-- The source jet degree and coefficient height bound the initial equation's joint degree.
-/
theorem jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v) (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (initialJetEquation (Polynomial.C center) Q) ≤ v + h := by
  apply jointTotalDegree_initialJetEquation_le center Q v h hv
  intro m _
  exact coeffNatDegreeLE_initialJetEquation center Q hQ m

variable {A : Type*} [CommRing A] [Algebra F A]

/-- The agreement equation over a coefficient algebra, with a common separant exponent `τ`.
It is `∑ l, (x - center)^l * N_l - y * S^τ`, where `N_l` is the common Taylor numerator
and `S` is the initial separant. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r)
    (K τ : ℕ) (x y : A) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) * commonTaylorNumeratorOver F center Q τ l.val) -
    C y * initialJetSeparant center Q ^ τ

/-- An affine agreement cut has joint degree at most `1 + τ * B` when its separant and common
numerators have joint degrees at most `B` and `1 + τ * B`, respectively. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (K τ B : ℕ)
    (hS : jointTotalDegree (initialJetSeparant (Polynomial.C center) Q) ≤ B)
    (hN : ∀ l : Fin K,
      jointTotalDegree
        (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l.val) ≤ 1 + τ * B) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K τ
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤ 1 + τ * B := by
  unfold taylorAgreementEquationOver
  apply (jointTotalDegree_sub_le _ _).trans
  apply max_le
  · apply jointTotalDegree_finsetSum_le
    intro l _
    apply (jointTotalDegree_mul_le _ _).trans
    simpa only [← Polynomial.C_sub, ← Polynomial.C_pow, jointTotalDegree_C_C,
      zero_add] using hN l
  · apply (jointTotalDegree_mul_le _ _).trans
    exact Nat.add_le_add (jointTotalDegree_affine_le a b)
      ((jointTotalDegree_pow_le _ _).trans (Nat.mul_le_mul_left _ hS))

/-- The default exponent `2K` gives the corresponding joint-degree bound for affine agreement
cuts. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (K B : ℕ)
    (hS : jointTotalDegree (initialJetSeparant (Polynomial.C center) Q) ≤ B)
    (hN : ∀ l : Fin K,
      jointTotalDegree
        (commonTaylorNumeratorOver F (Polynomial.C center) Q (2 * K) l.val) ≤ 1 + 2 * K * B) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K (2 * K)
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤ 1 + 2 * K * B := by
  exact jointTotalDegree_taylorAgreementEquationOver_le_of_exponent center x a b Q K (2 * K) B
    hS hN

/-- Source jet degree and coefficient height bound an affine agreement cut at any sufficient
common exponent. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hjet : jetTotalDegree Q ≤ v)
    (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K τ
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤
        1 + τ * (v - 1 + h) := by
  apply jointTotalDegree_taylorAgreementEquationOver_le_of_exponent center x a b Q K τ
    (v - 1 + h)
  · exact jointTotalDegree_initialJetSeparant_le (Polynomial.C center) Q v hjet
      (coeffNatDegreeLE_initialJetSeparant Q center hQ)
  · intro l
    exact jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE center Q v h τ
      l.val (hτ l) hjet hQ

/-- The default exponent gives the source-derived affine agreement degree bound. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_source
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K : ℕ)
    (hjet : jetTotalDegree Q ≤ v) (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K (2 * K)
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b)) ≤
        1 + 2 * K * (v - 1 + h) := by
  exact jointTotalDegree_taylorAgreementEquationOver_le_of_source_and_exponent
    center x a b Q v h K (2 * K) (taylorExponentSufficient_two_mul r K) hjet hQ

variable {A E : Type*} [CommRing A] [Field E] [Algebra F A] [Algebra F E]

/-- At a regular specialized jet, a symbolic common numerator evaluates to the corresponding
Taylor coefficient of the reconstructed polynomial, multiplied by the common separant power.
-/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (l : Fin K) :
    aeval jet (MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val)) =
      aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center)
            (MvPolynomial.map φ.toRingHom Q) K jet)).coeff l.val := by
  have hregular : aeval jet
      (initialJetSeparant (φ center) (MvPolynomial.map φ.toRingHom Q)) ≠ 0 := by
    rw [map_initialJetSeparant] at hS
    exact hS
  have hmap : MvPolynomial.map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val) =
    commonTaylorNumerator (φ center) (MvPolynomial.map φ.toRingHom Q) τ l.val := by
    rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver,
      rationalTaylorNumeratorOver_eq, commonTaylorNumerator]
  rw [hmap, map_initialJetSeparant,
    aeval_commonTaylorNumerator (φ center) (MvPolynomial.map φ.toRingHom Q) jet
      (hτ l) hregular]
  simp [coeff_taylor_rationalTaylorPolynomial, l.isLt]

/-- If every symbolic common numerator with index not divisible by `s` vanishes at a regular
specialized jet, the reconstructed polynomial has the same sparsity in its Taylor coefficients.
-/
theorem sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K s τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hcuts : ∀ l : Fin K, ¬s ∣ l.val →
      aeval jet (MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    ∀ i : ℕ, ¬s ∣ i →
      (Polynomial.taylor (φ center)
        (rationalTaylorPolynomial (φ center)
          (MvPolynomial.map φ.toRingHom Q) K jet)).coeff i = 0 := by
  intro i hi
  by_cases hiK : i < K
  · have hnum := hcuts ⟨i, hiK⟩ hi
    have hbridge := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      φ center Q K τ hτ jet hS ⟨i, hiK⟩
    rw [hbridge] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hS)
  · simp [coeff_taylor_rationalTaylorPolynomial, hiK]

end

end PolynomialDifferential
