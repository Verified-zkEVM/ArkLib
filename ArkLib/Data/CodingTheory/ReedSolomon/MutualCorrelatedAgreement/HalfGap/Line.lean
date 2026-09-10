/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
/-!
# Mutual correlated agreement at a half gap

This module proves the characteristic-free half-gap endpoint for mutual correlated agreement on a
line of received words. One finite exceptional set is chosen before the challenge and works for
every close polynomial at every remaining challenge. The conclusion identifies the full agreement
set with the common agreement set of two fixed Reed--Solomon witnesses.

The proof uses a degree-one symbolic Berlekamp--Welch certificate. A polynomial-kernel height bound
controls its challenge degree; ordinary root bounds and Lagrange interpolation then give the exact
agreement-set conclusion.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.4, the half-gap case of Theorem 5.11.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial
open scoped BigOperators

/-- Specialize the coefficient polynomials of a bivariate polynomial at the challenge `z`. -/
private def specializeChallenge {F : Type*} [Field F]
    (Q : Polynomial (Polynomial F)) (z : F) : Polynomial F :=
  Q.map (Polynomial.evalRingHom z)

private lemma eval_specializeChallenge {F : Type*} [Field F]
    (Q : Polynomial (Polynomial F)) (z x : F) :
    (specializeChallenge Q z).eval x = (Q.eval (Polynomial.C x)).eval z := by
  calc
    (specializeChallenge Q z).eval x = Q.eval₂ (Polynomial.evalRingHom z) x := by
      simpa [specializeChallenge] using
        Polynomial.eval_map (p := Q) (Polynomial.evalRingHom z) x
    _ = (Q.eval (Polynomial.C x)).eval z := by
      simpa using
        (Polynomial.eval₂_at_apply (p := Q) (f := Polynomial.evalRingHom z)
          (r := Polynomial.C x))

private lemma natDegree_eval_C_le_of_coeff_natDegree_le {F : Type*} [Field F]
    (Q : Polynomial (Polynomial F)) (height : ℕ)
    (h : ∀ j, (Q.coeff j).natDegree ≤ height) (x : F) :
    (Q.eval (Polynomial.C x)).natDegree ≤ height := by
  rw [Polynomial.eval_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_mul_le.trans <| by simp [h j])

private lemma roots_toFinset_card_le_natDegree {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] (p : R[X]) :
    p.roots.toFinset.card ≤ p.natDegree :=
  (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)

private lemma not_mem_roots_toFinset_iff_eval_ne_zero {F : Type*} [Field F] [DecidableEq F]
    {p : F[X]} (hp : p ≠ 0) (z : F) : z ∉ p.roots.toFinset ↔ p.eval z ≠ 0 := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def, not_iff_not]

/-- The degree-one symbolic Berlekamp--Welch constraint matrix for a received line. -/
private def halfGapConstraintMatrix {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) :
    Matrix (Fin n) (Fin (A + (A - k + 1))) F[X] := fun i ↦
  Fin.addCases
    (fun j : Fin A ↦ Polynomial.C (domain i) ^ (j : ℕ))
    (fun j : Fin (A - k + 1) ↦
      (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) *
        Polynomial.C (domain i) ^ (j : ℕ))

private lemma halfGapConstraintMatrix_entry_natDegree_le_one
    {F : Type*} [Field F] {n k A : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (i : Fin n) (j : Fin (A + (A - k + 1))) :
    (halfGapConstraintMatrix domain f g i j).natDegree ≤ 1 := by
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp [halfGapConstraintMatrix]
  · intro b
    simp only [halfGapConstraintMatrix, Fin.addCases_right]
    exact Polynomial.natDegree_mul_le.trans <| by
      have hleft :
          (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)).natDegree ≤ 1 :=
        (Polynomial.natDegree_add_le _ _).trans <| max_le (by simp) <|
          Polynomial.natDegree_mul_le.trans (by simp)
      have hright : (Polynomial.C (domain i) ^ (b : ℕ)).natDegree = 0 := by simp
      omega

/-- A symbolic linear certificate of bounded challenge degree.

`numerator` has degree `< A` in the evaluation variable and `denominator` has degree at most
`A - k`. Their coefficient polynomials have challenge degree at most `height`, and the displayed
identity holds at every received position before challenge specialization. -/
structure HalfGapCertificate {F : Type*} [Field F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (k A height : ℕ) where
  numerator : Polynomial (Polynomial F)
  denominator : Polynomial (Polynomial F)
  numeratorDegree : numerator.natDegree < A
  denominatorDegree : denominator.natDegree ≤ A - k
  coefficientDegree :
    (∀ j, (numerator.coeff j).natDegree ≤ height) ∧
      ∀ j, (denominator.coeff j).natDegree ≤ height
  denominator_ne_zero : denominator ≠ 0
  identity : ∀ i,
    numerator.eval (Polynomial.C (domain i)) +
        denominator.eval (Polynomial.C (domain i)) *
          (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) = 0

private lemma HalfGapCertificate.specialized_identity
    {F : Type*} [Field F] {n k A height : ℕ}
    {domain : Fin n ↪ F} {f g : Fin n → F}
    (certificate : HalfGapCertificate domain f g k A height) (i : Fin n) (z : F) :
    (specializeChallenge certificate.numerator z).eval (domain i) +
        (specializeChallenge certificate.denominator z).eval (domain i) *
          (f i + z * g i) = 0 := by
  have h := congrArg (Polynomial.eval z) (certificate.identity i)
  simpa [eval_specializeChallenge, mul_add, add_mul, mul_comm (g i) z] using h

private lemma HalfGapCertificate.denominator_eval_ne_zero_of_mem_usable
    {F : Type*} [Field F] [DecidableEq F] {n k A height : ℕ}
    {domain : Fin n ↪ F} {f g : Fin n → F}
    (certificate : HalfGapCertificate domain f g k A height)
    {usable : Finset (Fin n)}
    (husable : usable ⊆ Finset.univ.filter fun i ↦
      certificate.denominator.eval (Polynomial.C (domain i)) ≠ 0)
    {i : Fin n} (hi : i ∈ usable) :
    certificate.denominator.eval (Polynomial.C (domain i)) ≠ 0 :=
  (Finset.mem_filter.mp (husable hi)).2

/-- A bounded symbolic linear certificate implies exact mutual agreement outside at most `2 * n`
challenges. The exceptional set is independent of both the challenge and the close polynomial. -/
theorem exists_exceptionalSet_exactAgreement_of_halfGapCertificate
    {F : Type*} [Field F] [DecidableEq F] {n k A height : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hheight : k * height ≤ n)
    (certificate : HalfGapCertificate domain f g k A height) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * n ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + Polynomial.C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  let usablePositions : Finset (Fin n) :=
    Finset.univ.filter fun i ↦
      certificate.denominator.eval (Polynomial.C (domain i)) ≠ 0
  have hbadCard : n - usablePositions.card ≤ A - k := by
    let badPositions : Finset (Fin n) :=
      Finset.univ.filter fun i ↦
        certificate.denominator.eval (Polynomial.C (domain i)) = 0
    have hpartition : usablePositions.card + badPositions.card = n := by
      simpa [usablePositions, badPositions, Finset.card_filter_add_card_filter_not,
        Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin n)))
          (p := fun i ↦ certificate.denominator.eval (Polynomial.C (domain i)) ≠ 0))
    have hbadDegree : badPositions.card ≤ certificate.denominator.natDegree := by
      let points : Finset (Polynomial F) := badPositions.image fun i ↦ Polynomial.C (domain i)
      have hpointsCard : points.card = badPositions.card := by
        apply Finset.card_image_of_injective
        intro i j hij
        exact domain.injective (Polynomial.C_injective hij)
      have hsubset : points ⊆ certificate.denominator.roots.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots certificate.denominator_ne_zero,
          Polynomial.IsRoot.def]
        exact (Finset.mem_filter.mp hi).2
      rw [← hpointsCard]
      exact (Finset.card_le_card hsubset).trans
        (roots_toFinset_card_le_natDegree certificate.denominator)
    have hbadEq : n - usablePositions.card = badPositions.card := by omega
    rw [hbadEq]
    exact hbadDegree.trans certificate.denominatorDegree
  have hkUsable : k ≤ usablePositions.card := by omega
  obtain ⟨sample, hsampleUsable, hsampleCard⟩ :=
    Finset.exists_subset_card_eq hkUsable
  let F₀ : F[X] := Lagrange.interpolate sample domain f
  let G₀ : F[X] := Lagrange.interpolate sample domain g
  have hsampleInjective : Set.InjOn domain sample := domain.injective.injOn
  have hF₀Degree : F₀.degree < k := by
    simpa [F₀, hsampleCard] using Lagrange.degree_interpolate_lt f hsampleInjective
  have hG₀Degree : G₀.degree < k := by
    simpa [G₀, hsampleCard] using Lagrange.degree_interpolate_lt g hsampleInjective
  have hF₀NatDegree : F₀.natDegree < k := by
    by_cases hzero : F₀ = 0
    · simp [hzero, hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hF₀Degree
  have hG₀NatDegree : G₀.natDegree < k := by
    by_cases hzero : G₀ = 0
    · simp [hzero, hk]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hG₀Degree
  let guardPolynomial : F[X] :=
    ∏ i ∈ sample, certificate.denominator.eval (Polynomial.C (domain i))
  let accidentalFactor : Fin n → F[X] := fun i ↦
    if F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i then 1
    else Polynomial.C (F₀.eval (domain i) - f i) +
      Polynomial.X * Polynomial.C (G₀.eval (domain i) - g i)
  let accidentalPolynomial : F[X] := ∏ i, accidentalFactor i
  have hguardNe : guardPolynomial ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact certificate.denominator_eval_ne_zero_of_mem_usable hsampleUsable hi
  have haccidentalFactorNe : ∀ i, accidentalFactor i ≠ 0 := by
    intro i
    by_cases hi : F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i
    · simp [accidentalFactor, hi]
    · simp only [accidentalFactor, hi, if_false]
      intro hzero
      have hconst := congrArg (Polynomial.eval 0) hzero
      have hlinear := congrArg (Polynomial.eval 1) hzero
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_zero] at hconst
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, one_mul, Polynomial.eval_zero] at hlinear
      apply hi
      constructor
      · exact sub_eq_zero.mp hconst
      · rw [hconst, zero_add] at hlinear
        exact sub_eq_zero.mp hlinear
  have haccidentalNe : accidentalPolynomial ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact haccidentalFactorNe i
  let exceptional := (guardPolynomial * accidentalPolynomial).roots.toFinset
  refine ⟨exceptional, ?_, ?_⟩
  · calc
      exceptional.card ≤ (guardPolynomial * accidentalPolynomial).natDegree :=
        roots_toFinset_card_le_natDegree _
      _ ≤ guardPolynomial.natDegree + accidentalPolynomial.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ sample.card * height + n := by
        apply Nat.add_le_add
        · exact (Polynomial.natDegree_prod_le _ _).trans <| by
            simpa [Finset.sum_const_nat] using Finset.sum_le_sum fun i hi ↦
              natDegree_eval_C_le_of_coeff_natDegree_le certificate.denominator
                height certificate.coefficientDegree.2 (domain i)
        · exact (Polynomial.natDegree_prod_le _ _).trans <| by
            calc
              ∑ i, (accidentalFactor i).natDegree ≤ ∑ _i : Fin n, 1 := by
                apply Finset.sum_le_sum
                intro i _
                simp only [accidentalFactor]
                split_ifs
                · simp
                · exact (Polynomial.natDegree_add_le _ _).trans <| by
                    exact max_le (by simp) <| Polynomial.natDegree_mul_le.trans (by simp)
              _ = n := by simp
      _ ≤ 2 * n := by rw [hsampleCard]; omega
  · intro z hz P hPDegree hPAgreement
    have hPNatDegree : P.natDegree < k := by
      by_cases hzero : P = 0
      · simp [hzero, hk]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hPDegree
    have hproductEval : (guardPolynomial * accidentalPolynomial).eval z ≠ 0 :=
      (not_mem_roots_toFinset_iff_eval_ne_zero (mul_ne_zero hguardNe haccidentalNe) z).mp hz
    have hguardEval : guardPolynomial.eval z ≠ 0 := by
      intro hzero
      exact hproductEval (by simp [hzero])
    have haccidentalEval : accidentalPolynomial.eval z ≠ 0 := by
      intro hzero
      exact hproductEval (by simp [hzero])
    have hsampleDenominator : ∀ i ∈ sample,
        (specializeChallenge certificate.denominator z).eval (domain i) ≠ 0 := by
      intro i hi
      have hfactor :
          (certificate.denominator.eval (Polynomial.C (domain i))).eval z ≠ 0 := by
        intro hzero
        apply hguardEval
        change (∏ j ∈ sample,
          certificate.denominator.eval (Polynomial.C (domain j))).eval z = 0
        rw [Polynomial.eval_prod]
        exact Finset.prod_eq_zero hi hzero
      simpa [eval_specializeChallenge] using hfactor
    let agreement := polynomialAgreementSet domain (fun i ↦ f i + z * g i) P
    let identityPolynomial : F[X] :=
      specializeChallenge certificate.numerator z +
        specializeChallenge certificate.denominator z * P
    have hidentityDegree : identityPolynomial.natDegree < A := by
      have hnum : (specializeChallenge certificate.numerator z).natDegree < A :=
        Polynomial.natDegree_map_le.trans_lt certificate.numeratorDegree
      have hden : (specializeChallenge certificate.denominator z).natDegree ≤ A - k :=
        Polynomial.natDegree_map_le.trans certificate.denominatorDegree
      have hprod :
          (specializeChallenge certificate.denominator z * P).natDegree < A := by
        calc
          _ ≤ (specializeChallenge certificate.denominator z).natDegree + P.natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (A - k) + P.natDegree := Nat.add_le_add_right hden _
          _ < A := by omega
      exact (Polynomial.natDegree_add_le _ _).trans_lt (max_lt hnum hprod)
    have hidentityEval : ∀ i ∈ agreement,
        identityPolynomial.eval (domain i) = 0 := by
      intro i hi
      have hAgree := (Finset.mem_filter.mp hi).2
      have hCert := certificate.specialized_identity i z
      simp only [identityPolynomial, Polynomial.eval_add, Polynomial.eval_mul]
      rw [hAgree]
      exact hCert
    have hidentityZero : identityPolynomial = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        identityPolynomial (agreement.image domain)
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        exact hidentityEval i hi
      · rw [Finset.card_image_of_injective _ domain.injective]
        exact hidentityDegree.trans_le hPAgreement
    have hPOnSample : ∀ i ∈ sample, P.eval (domain i) = f i + z * g i := by
      intro i hi
      have hAt := congrArg (fun p : F[X] ↦ p.eval (domain i)) hidentityZero
      have hCert := certificate.specialized_identity i z
      simp only [identityPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_zero] at hAt
      have hden := hsampleDenominator i hi
      apply (mul_left_cancel₀ hden)
      calc
        (specializeChallenge certificate.denominator z).eval (domain i) *
              P.eval (domain i) =
            -(specializeChallenge certificate.numerator z).eval (domain i) :=
          eq_neg_of_add_eq_zero_right hAt
        _ = (specializeChallenge certificate.denominator z).eval (domain i) *
              (f i + z * g i) :=
          (eq_neg_of_add_eq_zero_right hCert).symm
    have hPFormula : P = F₀ + Polynomial.C z * G₀ := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hsampleInjective
      · simpa [hsampleCard] using hPDegree
      · have hsumNatDegree : (F₀ + Polynomial.C z * G₀).natDegree < k :=
          (Polynomial.natDegree_add_le _ _).trans_lt <| max_lt hF₀NatDegree <|
            (Polynomial.natDegree_C_mul_le z G₀).trans_lt hG₀NatDegree
        by_cases hzero : F₀ + Polynomial.C z * G₀ = 0
        · simp [hzero]
        · simpa [hsampleCard] using
            (Polynomial.natDegree_lt_iff_degree_lt hzero).1 hsumNatDegree
      · intro i hi
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Lagrange.eval_interpolate_at_node f hsampleInjective hi,
          Lagrange.eval_interpolate_at_node g hsampleInjective hi]
        exact hPOnSample i hi
    refine ⟨F₀, G₀, hF₀Degree, hG₀Degree, hPFormula, ?_⟩
    ext i
    simp only [polynomialAgreementSet, commonPolynomialAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hPFormula, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    constructor
    · intro hAgreement
      by_contra hCommon
      have hfactorEval : (accidentalFactor i).eval z = 0 := by
        simp only [accidentalFactor, hCommon, if_false, Polynomial.eval_add,
          Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
        rw [show F₀.eval (domain i) - f i + z * (G₀.eval (domain i) - g i) =
          (F₀.eval (domain i) + z * G₀.eval (domain i)) - (f i + z * g i) by ring]
        exact sub_eq_zero.mpr hAgreement
      apply haccidentalEval
      change (∏ j, accidentalFactor j).eval z = 0
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hfactorEval
    · rintro ⟨hF, hG⟩
      rw [hF, hG]

/-- At agreement at least `k + n / 2`, mutual correlated agreement holds over every field
outside at most `2 * n` challenges. The exceptional set is fixed before quantifying over the
challenge and the close polynomial, and the conclusion identifies the entire agreement set. -/
theorem exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hk : 0 < k) (hAn : A ≤ n) (hhalf : k + n / 2 ≤ A) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * n ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + Polynomial.C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  have hkA : k ≤ A := by omega
  let columnCount := A + (A - k + 1)
  have hColumnCount : n < columnCount := by
    dsimp [columnCount]
    omega
  obtain ⟨coefficients, hcoefficientsNe, hkernel, hcoefficientsDegree⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le
      (halfGapConstraintMatrix domain f g)
      (halfGapConstraintMatrix_entry_natDegree_le_one domain f g) hColumnCount
  let numeratorCoefficients : Fin A → F[X] := fun j ↦
    coefficients (Fin.castAdd (A - k + 1) j)
  let denominatorCoefficients : Fin (A - k + 1) → F[X] := fun j ↦
    coefficients (Fin.natAdd A j)
  let numerator : Polynomial (Polynomial F) :=
    Polynomial.ofFn A numeratorCoefficients
  let denominator : Polynomial (Polynomial F) :=
    Polynomial.ofFn (A - k + 1) denominatorCoefficients
  have hNumeratorDegree : numerator.natDegree < A := by
    apply Polynomial.ofFn_natDegree_lt
    omega
  have hDenominatorDegree : denominator.natDegree ≤ A - k := by
    change (Polynomial.ofFn (A - k + 1) denominatorCoefficients).natDegree ≤ A - k
    have := Polynomial.ofFn_natDegree_lt (R := Polynomial F)
      (by omega : 1 ≤ A - k + 1) denominatorCoefficients
    omega
  have hCoefficientDegree :
      (∀ j, (numerator.coeff j).natDegree ≤ n / (columnCount - n)) ∧
        ∀ j, (denominator.coeff j).natDegree ≤ n / (columnCount - n) := by
    constructor
    · intro j
      by_cases hj : j < A
      · change ((Polynomial.ofFn A numeratorCoefficients).coeff j).natDegree ≤ _
        rw [Polynomial.ofFn_coeff_eq_val_of_lt numeratorCoefficients hj]
        simpa [numeratorCoefficients, columnCount] using
          hcoefficientsDegree (Fin.castAdd (A - k + 1) ⟨j, hj⟩)
      · change ((Polynomial.ofFn A numeratorCoefficients).coeff j).natDegree ≤ _
        rw [Polynomial.ofFn_coeff_eq_zero_of_ge numeratorCoefficients
          (Nat.le_of_not_gt hj)]
        simp
    · intro j
      by_cases hj : j < A - k + 1
      · change
          ((Polynomial.ofFn (A - k + 1) denominatorCoefficients).coeff j).natDegree ≤ _
        rw [Polynomial.ofFn_coeff_eq_val_of_lt denominatorCoefficients hj]
        simpa [denominatorCoefficients, columnCount] using
          hcoefficientsDegree (Fin.natAdd A ⟨j, hj⟩)
      · change
          ((Polynomial.ofFn (A - k + 1) denominatorCoefficients).coeff j).natDegree ≤ _
        rw [Polynomial.ofFn_coeff_eq_zero_of_ge denominatorCoefficients
          (Nat.le_of_not_gt hj)]
        simp
  have hIdentity : ∀ i,
      numerator.eval (Polynomial.C (domain i)) +
          denominator.eval (Polynomial.C (domain i)) *
            (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) = 0 := by
    intro i
    have hi := congrFun hkernel i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    rw [Fin.sum_univ_add] at hi
    simp only [halfGapConstraintMatrix, Fin.addCases_left, Fin.addCases_right] at hi
    change (Polynomial.ofFn A numeratorCoefficients).eval (Polynomial.C (domain i)) +
      (Polynomial.ofFn (A - k + 1) denominatorCoefficients).eval
          (Polynomial.C (domain i)) *
        (Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) = 0
    rw [Polynomial.ofFn_eq_sum_monomial,
      Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial, numeratorCoefficients, denominatorCoefficients]
    rw [Finset.sum_mul]
    simp_rw [mul_add]
    ring_nf at hi ⊢
    exact hi
  have hDenominatorNe : denominator ≠ 0 := by
    intro hDenominatorZero
    have hNumeratorZero : numerator = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        (p := numerator) (f := fun i : Fin n ↦ Polynomial.C (domain i))
      · intro i j hij
        exact domain.injective (Polynomial.C_injective hij)
      · intro i
        have hi := hIdentity i
        simpa [hDenominatorZero] using hi
      · simpa using hNumeratorDegree.trans_le hAn
    have hNumeratorCoefficientsZero : numeratorCoefficients = 0 := by
      apply Polynomial.injective_ofFn A
      simpa [numerator] using hNumeratorZero
    have hDenominatorCoefficientsZero : denominatorCoefficients = 0 := by
      apply Polynomial.injective_ofFn (A - k + 1)
      simpa [denominator] using hDenominatorZero
    apply hcoefficientsNe
    rw [← Fin.append_castAdd_natAdd (f := coefficients)]
    rw [show (fun i ↦ coefficients (Fin.castAdd (A - k + 1) i)) = 0 by
        simpa [numeratorCoefficients] using hNumeratorCoefficientsZero,
      show (fun i ↦ coefficients (Fin.natAdd A i)) = 0 by
        simpa [denominatorCoefficients] using hDenominatorCoefficientsZero]
    exact Fin.append_castAdd_natAdd (f := (0 : Fin columnCount → F[X]))
  let height := n / (columnCount - n)
  have hHeight : k * height ≤ n := by
    have hkDenominator : k ≤ columnCount - n := by
      dsimp [columnCount]
      omega
    calc
      k * height ≤ (columnCount - n) * height :=
        Nat.mul_le_mul_right height hkDenominator
      _ ≤ n := by simpa [height] using Nat.mul_div_le n (columnCount - n)
  let certificate : HalfGapCertificate domain f g k A height := {
    numerator := numerator
    denominator := denominator
    numeratorDegree := hNumeratorDegree
    denominatorDegree := hDenominatorDegree
    coefficientDegree := by simpa [height] using hCoefficientDegree
    denominator_ne_zero := hDenominatorNe
    identity := hIdentity
  }
  exact exists_exceptionalSet_exactAgreement_of_halfGapCertificate
    domain f g hk hkA hAn hHeight certificate

end

end ReedSolomon
