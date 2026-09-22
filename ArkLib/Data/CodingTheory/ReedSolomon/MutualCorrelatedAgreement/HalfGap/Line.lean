/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight
public import ArkLib.ToMathlib.Polynomial.NatDegreeOfSum
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Mutual correlated agreement on a line at a half gap

Fix an evaluation domain `domain : ι ↪ F`, received words `f g : ι → F`, a message-degree bound
`k` and an agreement threshold `A` with `k + Fintype.card ι / 2 ≤ A`. Over every field `F`, one
pair `F₀ G₀` of polynomials of degree below `k` and one finite set of at most
`2 * Fintype.card ι - k` challenges are chosen, such that at every other challenge `z`, every
polynomial `P` of degree below `k` agreeing with `f + z • g` on at least `A` coordinates is
`F₀ + C z * G₀`, and its agreement set is the common agreement set of `F₀` with `f` and `G₀` with
`g`.

The proof uses a symbolic Berlekamp–Welch certificate (`HalfGapCertificate`): polynomials
`N D` in the evaluation variable, with coefficients polynomial in the challenge, such that
`N (x_i) + D (x_i) * (f i + Z * g i) = 0` at every coordinate. The certificate is a nonzero kernel
vector of a polynomial matrix with entries of degree at most `1` in the challenge, and the
polynomial kernel-height theorem bounds the challenge degree of its coefficients. Specializing at
`z`, `N + D * P` has degree below `A` and vanishes on the agreement set of `P`, so it is zero. Then
`P` agrees with `f + z • g` on a sample of `k` coordinates where `D` does not vanish, which
determines `P` by the graph-line recognition of
`ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine`.

## Main statements

* `ReedSolomon.HalfGapCertificate`: the symbolic certificate.
* `ReedSolomon.exists_exactPair_of_halfGapCertificate`: a certificate of challenge height `h`
  gives one pair and at most `k * h + (Fintype.card ι - k)` exceptional challenges.
* `ReedSolomon.exists_halfGapCertificate`: at agreement `k + Fintype.card ι / 2 ≤ A ≤
  Fintype.card ι` with `0 < k`, a certificate exists with `k * h ≤ Fintype.card ι`.
* `ReedSolomon.exists_exactPair_of_messageDim_add_half_blockLength_le`: the half-gap theorem with
  one pair and at most `2 * Fintype.card ι - k` exceptional challenges.
* `ReedSolomon.exists_exceptionalSet_exactAgreement_of_halfGapCertificate` and
  `ReedSolomon.exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le`: the
  forms with the pair chosen after the challenge and at most `2 * Fintype.card ι` exceptional
  challenges.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], the half-gap case of mutual correlated
  agreement
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

/-- **A symbolic Berlekamp–Welch certificate for a line.** Polynomials `numerator` and
`denominator` in the evaluation variable, with coefficients in `F[X]` (the challenge variable),
such that at every coordinate `i`
`numerator (C (domain i)) + denominator (C (domain i)) * (C (f i) + X * C (g i)) = 0`.

The numerator has degree below `A` and the denominator has degree at most `A - k`, so after
specializing the challenge the product of the denominator with a polynomial of degree below `k`
still has degree below `A`, the agreement threshold. Every coefficient has challenge degree at
most `height`; this bounds the number of challenges at which the denominator vanishes on a
sample. The denominator is nonzero, which bounds the number of coordinates where it vanishes. -/
structure HalfGapCertificate {F ι : Type*} [Field F] (domain : ι ↪ F) (f g : ι → F)
    (k A height : ℕ) where
  /-- The numerator, of degree below `A` in the evaluation variable. -/
  numerator : F[X][X]
  /-- The denominator, of degree at most `A - k` in the evaluation variable. -/
  denominator : F[X][X]
  numeratorDegree : numerator.degree < A
  denominatorDegree : denominator.natDegree ≤ A - k
  coefficientDegree :
    (∀ j, (numerator.coeff j).natDegree ≤ height) ∧
      ∀ j, (denominator.coeff j).natDegree ≤ height
  denominator_ne_zero : denominator ≠ 0
  identity : ∀ i,
    numerator.eval (C (domain i)) +
        denominator.eval (C (domain i)) * (C (f i) + X * C (g i)) = 0

/-- Above the block length the threshold cannot be met, so any pair and the empty set of
challenges satisfy the half-gap conclusion. -/
private theorem exists_exactPair_of_card_lt {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {k A : ℕ} (domain : ι ↪ F) (f g : ι → F) (B : ℕ) (hA : Fintype.card ι < A) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      ∃ exceptional : Finset F, exceptional.card ≤ B ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          P = F₀ + C z * G₀ ∧
            polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
              commonPolynomialAgreementSet domain f g F₀ G₀ := by
  refine ⟨0, 0, by simp, by simp, ∅, by simp, fun z _ P _ hP ↦ ?_⟩
  exact absurd (hP.trans (card_le_univ _)) (not_le.mpr hA)

/-- **One pair from a certificate.** Let `certificate` be a `HalfGapCertificate` of challenge
height `height` with `k ≤ A`. There are `F₀ G₀` of degree below `k` and a set of at most
`k * height + (Fintype.card ι - k)` challenges such that, at every other challenge `z`, every `P`
of degree below `k` agreeing with `f + z • g` on at least `A` coordinates is `F₀ + C z * G₀`, and
its agreement set is the common agreement set of `F₀` with `f` and `G₀` with `g`.

The pair and the exceptional set are chosen before `z` and `P`. The first summand counts the
challenges where the specialized denominator vanishes on a sample of `k` coordinates; the second
counts the challenges of `exists_exceptional_graphLine_challenges_of_sample`. The hypothesis
`k ≤ A` is needed: with `f = g = 0`, `numerator = 0`, `denominator = 1`, `A = 0` and `k = 1`, every
constant `P` meets the threshold. -/
theorem exists_exactPair_of_halfGapCertificate
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] {k A height : ℕ}
    {domain : ι ↪ F} {f g : ι → F} (hkA : k ≤ A)
    (certificate : HalfGapCertificate domain f g k A height) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      ∃ exceptional : Finset F, exceptional.card ≤ k * height + (Fintype.card ι - k) ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          P = F₀ + C z * G₀ ∧
            polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
              commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  rcases lt_or_ge (Fintype.card ι) A with hAn | hAn
  · exact exists_exactPair_of_card_lt domain f g _ hAn
  set N := certificate.numerator
  set D := certificate.denominator
  -- The denominator vanishes at no more than `A - k` coordinates.
  have hbad : #{i | D.eval (C (domain i)) = 0} ≤ A - k := by
    refine le_trans ?_ certificate.denominatorDegree
    rw [← card_image_of_injective _ (C_injective.comp domain.injective)]
    refine card_le_degree_of_subset_roots fun x hx ↦ ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact (mem_roots certificate.denominator_ne_zero).mpr (mem_filter.mp hi).2
  have husable : k ≤ #{i | ¬ D.eval (C (domain i)) = 0} := by
    have := card_filter_add_card_filter_not (s := (univ : Finset ι))
      (fun i ↦ D.eval (C (domain i)) = 0)
    rw [card_univ] at this
    omega
  obtain ⟨sample, hsampleUsable, hsampleCard⟩ := exists_subset_card_eq husable
  obtain ⟨F₀, G₀, hF₀, hG₀, hfg, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsampleCard
  obtain ⟨graphExceptional, hgraphCard, hgraph⟩ :=
    exists_exceptional_graphLine_challenges_of_sample domain f g sample hsampleCard F₀ G₀ hfg
      (RingHom.id F)
  let guard : F[X] := ∏ i ∈ sample, D.eval (C (domain i))
  have hguard : guard ≠ 0 :=
    prod_ne_zero_iff.mpr fun i hi ↦ (mem_filter.mp (hsampleUsable hi)).2
  have hguardDegree : guard.natDegree ≤ k * height := by
    refine (natDegree_prod_le _ _).trans ?_
    rw [← hsampleCard, ← smul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun i _ ↦
      natDegree_eval_C_le certificate.coefficientDegree.2 _
  refine ⟨F₀, G₀, hF₀, hG₀, guard.roots.toFinset ∪ graphExceptional, ?_, ?_⟩
  · refine (card_union_le _ _).trans (Nat.add_le_add ?_ hgraphCard)
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hguardDegree)
  intro z hz P hP hA
  have hzGuard : guard.eval z ≠ 0 := fun h ↦
    hz (mem_union_left _ (Multiset.mem_toFinset.mpr ((mem_roots hguard).mpr h)))
  have hzGraph : z ∉ graphExceptional := fun h ↦ hz (mem_union_right _ h)
  have hden : ∀ i ∈ sample, (D.eval (C (domain i))).eval z ≠ 0 := by
    rw [eval_prod, prod_ne_zero_iff] at hzGuard
    exact hzGuard
  -- The certificate identity at the challenge `z`.
  have hspec : ∀ i, (N.eval (C (domain i))).eval z +
      (D.eval (C (domain i))).eval z * (f i + z * g i) = 0 := fun i ↦ by
    simpa [mul_comm (g i) z] using congrArg (eval z) (certificate.identity i)
  -- The specialized identity polynomial vanishes on the agreement set, hence everywhere.
  let identityPolynomial : F[X] := N.map (evalRingHom z) + D.map (evalRingHom z) * P
  have heval : ∀ x, identityPolynomial.eval x =
      (N.eval (C x)).eval z + (D.eval (C x)).eval z * P.eval x := fun x ↦ by
    simp [identityPolynomial, map_evalRingHom_eval]
  have hdegree : identityPolynomial.degree < A := by
    refine (degree_add_le _ _).trans_lt (max_lt (degree_map_le.trans_lt
      certificate.numeratorDegree) ?_)
    by_cases hP0 : P = 0
    · simp [hP0]
    have hPn : P.natDegree < k := (natDegree_lt_iff_degree_lt hP0).mpr hP
    have hDn : (D.map (evalRingHom z)).natDegree ≤ A - k :=
      natDegree_map_le.trans certificate.denominatorDegree
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast natDegree_mul_le.trans_lt (by omega)
  have hzero : identityPolynomial = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).image domain) ?_ ?_
    · rw [card_image_of_injective _ domain.injective]
      exact hdegree.trans_le (by exact_mod_cast hA)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      rw [heval, (mem_polynomialAgreementSet ..).mp hi]
      exact hspec i
  -- On the sample the denominator is nonzero, so `P` agrees with the affine word there.
  have hsample : ∀ i ∈ sample, P.eval (domain i) = f i + z * g i := fun i hi ↦ by
    have h := heval (domain i)
    rw [hzero, eval_zero] at h
    exact mul_left_cancel₀ (hden i hi) (by linear_combination -h - hspec i)
  have hPeq : P = F₀ + C z * G₀ := by
    simpa using hrecognize (RingHom.id F) z P hP fun i hi ↦ by simpa using hsample i hi
  refine ⟨hPeq, ?_⟩
  simpa [hPeq] using hgraph z hzGraph

/-- **Mutual correlated agreement from a certificate, one pair per challenge.** If `k * height ≤
Fintype.card ι`, at most `2 * Fintype.card ι` challenges are exceptional, and at every other
challenge each close `P` has a pair `F₀ G₀` of degree below `k` with `P = F₀ + C z * G₀` and the
same agreement set as the common agreement set of the pair. Here the pair is chosen after the
challenge; `exists_exactPair_of_halfGapCertificate` gives one pair for all challenges. -/
theorem exists_exceptionalSet_exactAgreement_of_halfGapCertificate
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] {k A height : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (hkA : k ≤ A) (hheight : k * height ≤ Fintype.card ι)
    (certificate : HalfGapCertificate domain f g k A height) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * Fintype.card ι ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_halfGapCertificate hkA certificate
  exact ⟨exceptional, by omega, fun z hz P hP hA ↦
    ⟨F₀, G₀, hF₀, hG₀, hpair z hz P hP hA⟩⟩

/-- The degree-one constraint matrix of the symbolic Berlekamp–Welch system. Row `i` has the
powers `domain i ^ j` for `j < A` (numerator columns), followed by
`(C (f i) + X * C (g i)) * domain i ^ j` for `j ≤ A - k` (denominator columns). -/
private noncomputable def halfGapConstraintMatrix {F ι : Type*} [Field F] (k A : ℕ)
    (domain : ι ↪ F) (f g : ι → F) :
    Matrix ι (Fin (A + (A - k + 1))) F[X] := fun i ↦
  Fin.addCases
    (fun j : Fin A ↦ C (domain i) ^ (j : ℕ))
    (fun j : Fin (A - k + 1) ↦ (C (f i) + X * C (g i)) * C (domain i) ^ (j : ℕ))

private lemma halfGapConstraintMatrix_natDegree_le {F ι : Type*} [Field F] (k A : ℕ)
    (domain : ι ↪ F) (f g : ι → F) (i : ι) (j : Fin (A + (A - k + 1))) :
    (halfGapConstraintMatrix k A domain f g i j).natDegree ≤ 1 := by
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) j
  · simp [halfGapConstraintMatrix]
  · simp only [halfGapConstraintMatrix, Fin.addCases_right]
    have hleft : (C (f i) + X * C (g i)).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) (natDegree_mul_le.trans (by simp)))
    have hright : (C (domain i) ^ (b : ℕ)).natDegree = 0 := by simp
    exact natDegree_mul_le.trans (by omega)

/-- **Existence of a half-gap certificate.** If `0 < k`, `A ≤ Fintype.card ι` and
`k + Fintype.card ι / 2 ≤ A`, there is a `HalfGapCertificate` of some challenge height `height`
with `k * height ≤ Fintype.card ι`.

The certificate is a nonzero kernel vector of the `Fintype.card ι × (2 * A - k + 1)` constraint
matrix, whose entries have challenge degree at most `1`; the half-gap hypothesis makes the matrix
wider than tall, and `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` gives
`height = Fintype.card ι / (2 * A - k + 1 - Fintype.card ι)`. The hypothesis `A ≤ Fintype.card ι`
makes the denominator nonzero: a zero denominator forces the numerator, of degree below `A`, to
vanish at every coordinate. The hypothesis `0 < k` is used for the width when
`Fintype.card ι` is odd. -/
theorem exists_halfGapCertificate {F ι : Type*} [Field F] [Fintype ι] {k A : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (hk : 0 < k) (hAn : A ≤ Fintype.card ι)
    (hhalf : k + Fintype.card ι / 2 ≤ A) :
    ∃ height, k * height ≤ Fintype.card ι ∧
      Nonempty (HalfGapCertificate domain f g k A height) := by
  classical
  set n := Fintype.card ι
  let columnCount := A + (A - k + 1)
  have hwide : Fintype.card ι < Fintype.card (Fin columnCount) := by
    simp only [Fintype.card_fin, columnCount]
    omega
  obtain ⟨coefficients, hne, hkernel, hcoefficients⟩ :=
    Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le (halfGapConstraintMatrix k A domain f g)
      (halfGapConstraintMatrix_natDegree_le k A domain f g) hwide
  simp only [Fintype.card_fin, mul_one] at hcoefficients
  let numeratorCoefficients : Fin A → F[X] := fun j ↦ coefficients (Fin.castAdd (A - k + 1) j)
  let denominatorCoefficients : Fin (A - k + 1) → F[X] := fun j ↦
    coefficients (Fin.natAdd A j)
  let numerator : F[X][X] := ofFn A numeratorCoefficients
  let denominator : F[X][X] := ofFn (A - k + 1) denominatorCoefficients
  have hcoeff : ∀ {m : ℕ} (v : Fin m → F[X]),
      (∀ j, (v j).natDegree ≤ n / (columnCount - n)) →
        ∀ j, ((ofFn m v).coeff j).natDegree ≤ n / (columnCount - n) := by
    intro m v hv j
    by_cases hj : j < m
    · rw [ofFn_coeff_eq_val_of_lt v hj]
      exact hv _
    · rw [ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_gt hj)]
      simp
  have hidentity : ∀ i, numerator.eval (C (domain i)) +
      denominator.eval (C (domain i)) * (C (f i) + X * C (g i)) = 0 := by
    intro i
    have hi := congrFun hkernel i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    rw [Fin.sum_univ_add] at hi
    simp only [halfGapConstraintMatrix, Fin.addCases_left, Fin.addCases_right] at hi
    simp only [numerator, denominator, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial,
      numeratorCoefficients, denominatorCoefficients, Finset.sum_mul]
    rw [← hi]
    congr 1 <;> refine Finset.sum_congr rfl fun j _ ↦ ?_ <;> ring
  have hdenominator : denominator ≠ 0 := by
    intro hzero
    have hnumerator : numerator = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero numerator
        (f := fun i : ι ↦ C (domain i)) (C_injective.comp domain.injective)
        (fun i ↦ by simpa [hzero] using hidentity i) ?_
      exact (ofFn_natDegree_lt (by omega) _).trans_le hAn
    have hnum : numeratorCoefficients = 0 := injective_ofFn A (by simpa using hnumerator)
    have hden : denominatorCoefficients = 0 :=
      injective_ofFn (A - k + 1) (by simpa using hzero)
    apply hne
    rw [← Fin.append_castAdd_natAdd (f := coefficients)]
    rw [show (fun i ↦ coefficients (Fin.castAdd (A - k + 1) i)) = 0 from hnum,
      show (fun i ↦ coefficients (Fin.natAdd A i)) = 0 from hden]
    exact Fin.append_castAdd_natAdd (f := (0 : Fin columnCount → F[X]))
  refine ⟨n / (columnCount - n), ?_, ⟨{
    numerator := numerator
    denominator := denominator
    numeratorDegree := ofFn_degree_lt _
    denominatorDegree := Nat.lt_succ_iff.mp (ofFn_natDegree_lt (by omega) _)
    coefficientDegree := ⟨hcoeff _ fun j ↦ hcoefficients _, hcoeff _ fun j ↦ hcoefficients _⟩
    denominator_ne_zero := hdenominator
    identity := hidentity }⟩⟩
  calc
    k * (n / (columnCount - n)) ≤ (columnCount - n) * (n / (columnCount - n)) :=
      Nat.mul_le_mul_right _ (by simp only [columnCount]; omega)
    _ ≤ n := Nat.mul_div_le n _

/-- **Mutual correlated agreement at a half gap, with one pair.** If
`k + Fintype.card ι / 2 ≤ A`, then over every field there are `F₀ G₀` of degree below `k` and a
set of at most `2 * Fintype.card ι - k` challenges such that, at every other challenge `z`, every
`P` of degree below `k` agreeing with `f + z • g` on at least `A` coordinates is `F₀ + C z * G₀`,
and its agreement set is the common agreement set of `F₀` with `f` and `G₀` with `g`.

No hypothesis `0 < k` or `A ≤ Fintype.card ι` is needed. At `k = 0` the only candidate is `0`,
and at most `Fintype.card ι` challenges make `f + z • g` vanish at a coordinate where `f` or `g`
does not; for `A > Fintype.card ι` the threshold cannot be met. -/
theorem exists_exactPair_of_messageDim_add_half_blockLength_le
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] {k A : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (hhalf : k + Fintype.card ι / 2 ≤ A) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      ∃ exceptional : Finset F, exceptional.card ≤ 2 * Fintype.card ι - k ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
          P = F₀ + C z * G₀ ∧
            polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
              commonPolynomialAgreementSet domain f g F₀ G₀ := by
  rcases lt_or_ge (Fintype.card ι) A with hAn | hAn
  · exact exists_exactPair_of_card_lt domain f g _ hAn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨exceptional, hcard, hagree⟩ :=
      exists_exceptional_graphLine_challenges domain f g 0 0 (RingHom.id F)
    refine ⟨0, 0, by simp, by simp, exceptional, hcard.trans (by omega),
      fun z hz P hP _ ↦ ?_⟩
    have hP0 : P = 0 := by simpa using hP
    subst hP0
    simpa using hagree z hz
  obtain ⟨height, hheight, ⟨certificate⟩⟩ := exists_halfGapCertificate domain f g hk hAn hhalf
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_halfGapCertificate (by omega) certificate
  exact ⟨F₀, G₀, hF₀, hG₀, exceptional, by omega, hpair⟩

/-- **Mutual correlated agreement at a half gap, one pair per challenge.** If
`k + Fintype.card ι / 2 ≤ A`, at most `2 * Fintype.card ι` challenges are exceptional, and at
every other challenge each close `P` has a pair `F₀ G₀` of degree below `k` with
`P = F₀ + C z * G₀` and the same agreement set as the common agreement set of the pair.
`exists_exactPair_of_messageDim_add_half_blockLength_le` gives one pair for all challenges. -/
theorem exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] {k A : ℕ}
    (domain : ι ↪ F) (f g : ι → F) (hhalf : k + Fintype.card ι / 2 ≤ A) :
    ∃ exceptional : Finset F, exceptional.card ≤ 2 * Fintype.card ι ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
          P = F₀ + C z * G₀ ∧
          polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, exceptional, hcard, hpair⟩ :=
    exists_exactPair_of_messageDim_add_half_blockLength_le domain f g hhalf
  exact ⟨exceptional, hcard.trans (Nat.sub_le _ _), fun z hz P hP hA ↦
    ⟨F₀, G₀, hF₀, hG₀, hpair z hz P hP hA⟩⟩

end ReedSolomon
