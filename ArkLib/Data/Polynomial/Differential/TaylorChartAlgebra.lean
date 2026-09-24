/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Symbolic equations on the rational Taylor chart

The initial equation and separant specialize along coefficient maps. Agreement equations can
also be formed over an algebra, then mapped to a field where they describe the reconstructed
polynomial. Vanishing symbolic high cuts bounds the degree of that reconstruction, and each
symbolic common numerator evaluates to its corresponding Taylor coefficient after clearing the
separant denominator.

## Main statements

* `map_initialJetEquation` and `aeval_map_initialJetEquation` describe coefficient maps and
  evaluation of the initial equation.
* `taylorAgreementEquationOver` and its map theorem define symbolic agreement equations over an
  algebra and specialize them to field-valued cuts.
* `jointInitialJetEquation`, `jointInitialJetSeparant`, and `jointCommonTaylorNumerator` define
  flattened challenge and jet coordinates for the Taylor chart.
* `jointTaylorAgreementEquation`, `jointTaylorReconstructionError`, and `affinePairCurve` describe
  the agreement cuts and affine-pair graph in those coordinates.
* `aeval_jointInitialJetSeparant`, `aeval_jointCommonTaylorNumerator`, and
  `aeval_jointTaylorAgreementEquation` specialize joint cuts at a point before evaluating jets.
* `commonTaylorNumeratorOver_eq` and `map_commonTaylorNumeratorOver_eq` bridge algebra-valued
  numerators to their field-valued counterparts.
* `aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent` characterizes regular agreement
  cuts, while `degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent` bounds the
  reconstruction degree.
* `aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent` identifies symbolic common
  numerators with coefficients of the reconstructed polynomial.
* `jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE` and
  `jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent` bound
  symbolic equation degrees from jet degree and coefficient height.
* `sparse_rationalTaylorPolynomial_of_symbolic_cuts` derives coefficient sparsity from symbolic
  cuts at a regular jet.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {r : ℕ}

variable {F : Type*} [Field F] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

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
theorem jointTotalDegree_initialJetEquation_le (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v)
    (hh : ∀ m ∈ (initialJetEquation center Q).support,
      ((initialJetEquation center Q).coeff m).natDegree ≤ h) :
    jointTotalDegree (initialJetEquation center Q) ≤ v + h := by
  have hd := jointTotalDegree_le_of_natDegree_coeff_le
    (initialJetEquation center Q) h hh
  have hj := (totalDegree_initialJetEquation_le center Q).trans hv
  omega

/-- The jet degree and coefficient height bound the initial equation's joint degree.
-/
theorem jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v) (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (initialJetEquation (Polynomial.C center) Q) ≤ v + h := by
  apply jointTotalDegree_initialJetEquation_le (Polynomial.C center) Q v h hv
  intro m _
  exact coeffNatDegreeLE_initialJetEquation center Q hQ m

/-- The agreement equation over an `F`-algebra, with every common numerator using the same
separant exponent. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver F center Q τ l.val) - C y * initialJetSeparant center Q ^ τ

/-- Coefficient specialization maps an algebra-valued agreement equation to the corresponding
agreement equation. -/
theorem map_taylorAgreementEquationOver (φ : A →ₐ[F] B) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A) (τ : ℕ) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquationOver (F := F) (φ center) (map φ.toRingHom Q) K
        (φ x) (φ y) (τ := τ) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver, map_initialJetSeparant]
  rfl

/-- Specializing an algebra-valued agreement equation to a field gives the field-valued cut. -/
theorem map_taylorAgreementEquationOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A)
    (τ : ℕ) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquation (φ center) (map φ.toRingHom Q) K τ (φ x) (φ y) := by
  rw [map_taylorAgreementEquationOver (τ := τ)]
  simp only [taylorAgreementEquationOver, taylorAgreementEquation,
    commonTaylorNumeratorOver_eq]

/-- The initial equation in joint challenge and initial-jet coordinates. -/
def jointInitialJetEquation {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetEquation (Polynomial.C center) Q)

/-- The initial separant in joint challenge and initial-jet coordinates. -/
def jointInitialJetSeparant {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetSeparant (Polynomial.C center) Q)

/-- A cleared Taylor coefficient in joint challenge and initial-jet coordinates. -/
def jointCommonTaylorNumerator {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (τ : ℕ) {K : ℕ} (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)

/-- The cleared agreement equation in joint challenge and initial-jet coordinates. -/
def jointTaylorAgreementEquation {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (K τ : ℕ) (x y : Polynomial E) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K x y (τ := τ))

/-- The cleared equation identifying one Taylor coefficient with an affine pair. -/
def jointTaylorReconstructionError {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (τ : ℕ) {K : ℕ} (P₀ P₁ : Polynomial E) (l : Fin K) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  jointCommonTaylorNumerator center Q τ l -
    jointInitialJetSeparant center Q ^ τ *
      (MvPolynomial.C ((Polynomial.taylor center P₀).coeff l.val) +
        MvPolynomial.X none * MvPolynomial.C ((Polynomial.taylor center P₁).coeff l.val))

/-- The polynomial parametrization of the initial jets of an affine pair. -/
def affinePairCurve {E : Type*} [Semiring E] (center : E) (P₀ P₁ : Polynomial E) :
    Option (Fin (r + 1)) → Polynomial E := fun i ↦
  match i with
  | none => Polynomial.X
  | some j => Polynomial.C (polynomialJet center P₀ j) +
      Polynomial.X * Polynomial.C (polynomialJet center P₁ j)

variable {E : Type*} [Field E]

/-- Evaluating the joint separant specializes its challenge before evaluating the jet. -/
theorem aeval_jointInitialJetSeparant (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (x : Option (Fin (r + 1)) → E) :
    aeval x (jointInitialJetSeparant center Q) =
      aeval (fun j ↦ x (some j))
        (initialJetSeparant center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q)) := by
  rw [jointInitialJetSeparant, aeval_optionEquivRight_symm, map_initialJetSeparant]
  simp

/-- Evaluating a joint high cut specializes its challenge before evaluating the jet. -/
theorem aeval_jointCommonTaylorNumerator (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (τ : ℕ) {K : ℕ} (l : Fin K)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointCommonTaylorNumerator center Q τ l) =
      aeval (fun j ↦ x (some j))
        (commonTaylorNumerator center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) τ l.val) := by
  rw [jointCommonTaylorNumerator, aeval_optionEquivRight_symm,
    map_commonTaylorNumeratorOver]
  simp [commonTaylorNumerator, commonTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

/-- Evaluating a joint agreement cut specializes its challenge and received value. -/
theorem aeval_jointTaylorAgreementEquation (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (K τ : ℕ) (x₀ y₀ : Polynomial E)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointTaylorAgreementEquation center Q K τ x₀ y₀) =
      aeval (fun j ↦ x (some j))
        (taylorAgreementEquation center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) K τ
          (Polynomial.eval (x none) x₀) (Polynomial.eval (x none) y₀)) := by
  rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm,
    map_taylorAgreementEquationOver_eq (τ := τ)]
  simp

/-- An affine agreement cut has joint degree at most `1 + τ * B` when its separant and common
numerators have joint degrees at most `B` and `1 + τ * B`, respectively. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (K τ B : ℕ)
    (hS : jointTotalDegree (initialJetSeparant (Polynomial.C center) Q) ≤ B)
    (hN : ∀ l : Fin K,
      jointTotalDegree
        (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l.val) ≤ 1 + τ * B) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b) (τ := τ)) ≤
        1 + τ * B := by
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

/-- Jet degree and coefficient height bound an affine agreement cut at any sufficient
common exponent. -/
theorem jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent
    (center x a b : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hjet : jetTotalDegree Q ≤ v)
    (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (taylorAgreementEquationOver (F := F) (Polynomial.C center) Q K
      (Polynomial.C x) (Polynomial.C a + Polynomial.X * Polynomial.C b) (τ := τ)) ≤
        1 + τ * (v - 1 + h) := by
  apply jointTotalDegree_taylorAgreementEquationOver_le_of_exponent center x a b Q K τ
    (v - 1 + h)
  · exact jointTotalDegree_initialJetSeparant_le (Polynomial.C center) Q v hjet
      (coeffNatDegreeLE_initialJetSeparant Q center hQ)
  · intro l
    exact jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE center Q v h τ
      l.val (hτ l) hjet hQ

/-- At a regular jet, a sufficiently padded symbolic agreement equation evaluates to the
separant power times the discrepancy of the reconstructed polynomial. -/
theorem aeval_map_taylorAgreementEquationOver_of_exponent {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) =
        aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
          ((rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) -
            φ y) := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  rw [map_taylorAgreementEquationOver_eq (τ := τ)]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    aeval_taylorAgreementEquation (φ center) (map φ.toRingHom Q) hτ jet hS (φ x) (φ y)

/-- A regular symbolic agreement equation vanishes exactly when the reconstructed polynomial
takes the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  rw [aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K τ hτ jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- Vanishing symbolic high cuts with a sufficient exponent bounds the degree of the
reconstructed polynomial. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS
  refine degree_rationalTaylorPolynomial_lt (φ center) (map φ.toRingHom Q) hτ k jet hS ?_
  intro l hkl hlK
  simpa only [map_commonTaylorNumeratorOver_eq] using hhigh ⟨l, hlK⟩ hkl

/-- Every symbolic common numerator evaluates to the cleared Taylor coefficient of the
reconstructed polynomial when its exponent is sufficient. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (l : Fin K) :
    aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff l.val := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hS
  rw [map_commonTaylorNumeratorOver_eq,
    aeval_commonTaylorNumerator (φ center) (map φ.toRingHom Q) jet (hτ l) hS']
  rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  simp [l.isLt]

/-- Vanishing symbolic common numerators outside multiples of `s` force the corresponding
Taylor coefficients of the reconstructed polynomial to vanish at a regular jet. -/
theorem sparse_rationalTaylorPolynomial_of_symbolic_cuts {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K s τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hcuts : ∀ l : Fin K, ¬s ∣ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    ∀ i : ℕ, ¬s ∣ i →
      (Polynomial.taylor (φ center)
        (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff i = 0 := by
  intro i hi
  by_cases hiK : i < K
  · have hnum := hcuts ⟨i, hiK⟩ hi
    have hbridge := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      φ center Q K τ hτ jet hS ⟨i, hiK⟩
    rw [hbridge] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hS)
  · simp [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix, hiK]

end

end PolynomialDifferential
