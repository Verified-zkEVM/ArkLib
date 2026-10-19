/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.Uniform
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificates
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.PairwiseJohnson

/-!
# Uniform first-order lists at capacity gap 6/25

At agreement `A ≥ k + (6/25) n` with `n ≥ 2`, the complete list of degree-`< k` polynomials
agreeing with a received word on at least `A` points is represented by an exact finite list with at
most `307 n` members, over an arbitrary field.

The message dimension `k = 1` is handled by agreement incidence, in every characteristic. For
`k ≥ 2` the field characteristic need only be zero or exceed `k - 1`. When it also exceeds the
first-derivative cap `4`, the first-order certificate with multiplicity `12`, derivative cap `4`,
jet cap `22` and height `851` and the squarefree solution count give the bound. Otherwise
primality of the characteristic forces `k ≤ 3`, and the pairwise Johnson bound gives fewer than
`73` members.

## Main statements

* `ReedSolomon.exists_uniformFirstOrder_list`: the exact list with at most `307 n` members.

## References

* [DKTZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

private theorem uniformFirstOrder_stage_le (k : ℕ) (hk : 2 ≤ k) :
    firstOrderCurveFiberStageOne k 22 4 (regularTaylorExponent (k - 1)) ≤ 294 * k - 428 := by
  by_cases hkTwo : k = 2
  · subst k
    norm_num [firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent,
      MvPolynomial.cappedDegreeMixedVolume]
  · simp only [firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, regularTaylorExponent,
      MvPolynomial.cappedDegreeMixedVolume]
    rw [min_eq_right (by omega)]
    omega

private theorem uniformFirstOrder_listRatio_le (n k A : ℕ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    (firstOrderCurveFiberStageOne k 22 4 (regularTaylorExponent (k - 1)) : ℝ) *
          ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) +
        FirstOrder.Squarefree.ordinaryDegreeEnvelope 22 4 ≤ 307 * n := by
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hkn : k ≤ n := hkA.trans hAn
  have hden : (0 : ℝ) < (A - k + 1 : ℕ) := by positivity
  have henvelope : FirstOrder.Squarefree.ordinaryDegreeEnvelope 22 4 = 138 := by
    norm_num [FirstOrder.Squarefree.ordinaryDegreeEnvelope]
  rw [henvelope]
  have hstage :
      (firstOrderCurveFiberStageOne k 22 4 (regularTaylorExponent (k - 1)) : ℝ) ≤
        (294 * k - 428 : ℕ) := by
    exact_mod_cast uniformFirstOrder_stage_le k hk
  have hgap' : (6 : ℝ) * n ≤ 25 * (A - k) := by nlinarith
  have hsquare : 4 * ((k : ℝ) - 1) * (n - (k - 1)) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (k - 1))]
  have hA : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenGap : (6 : ℝ) * n + 25 ≤ 25 * (A - k + 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdenGap
    (show (0 : ℝ) ≤ 307 * n - 4 by nlinarith)
  have hmain : (294 * k - 428 : ℕ) * ((n - k + 1 : ℕ) : ℝ) /
      (A - k + 1 : ℕ) ≤ 307 * n - 138 := by
    apply (div_le_iff₀ hden).2
    rw [Nat.cast_sub (by omega : 428 ≤ 294 * k)]
    push_cast [Nat.cast_sub hkA, Nat.cast_sub hkn]
    have hreduce :
        (294 * (k : ℝ) - 428) * (n - k + 1) + 138 * (A - k + 1) ≤
          294 * (k - 1) * (n - k + 1) + 4 * (A - k + 1) := by
      nlinarith
    nlinarith
  calc
    (firstOrderCurveFiberStageOne k 22 4 (regularTaylorExponent (k - 1)) : ℝ) *
          ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) + 138 ≤
        (294 * k - 428 : ℕ) * ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) + 138 := by
      gcongr
    _ ≤ 307 * n := by
      linarith

/-- If the message degree `k - 1` is below the positive characteristic but the first-derivative
cap `4` is not, primality of the characteristic leaves only the dimensions `2` and `3`. -/
private theorem uniformFirstOrder_messageDim_le_three_of_small_characteristic
    {F : Type*} [Field F] {k : ℕ} (hk : 2 ≤ k)
    (hdegreeChar : k - 1 < ringChar F) (hsupportChar : ¬ 4 < ringChar F) :
    k ≤ 3 := by
  have hpPos : 0 < ringChar F := (Nat.sub_pos_of_lt hk).trans hdegreeChar
  let _ : NeZero (ringChar F) := ⟨hpPos.ne'⟩
  have hpPrime : (ringChar F).Prime := (CharP.char_is_prime_of_pos F (ringChar F)).out
  have hpTwo : 2 ≤ ringChar F := hpPrime.two_le
  have hpNeFour : ringChar F ≠ 4 := by
    intro hp
    rw [hp] at hpPrime
    exact (Nat.not_prime_of_mul_eq (show 2 * 2 = 4 by norm_num) (by norm_num) (by norm_num))
      hpPrime
  omega

/-- In dimensions `2` and `3`, the pairwise Johnson bound at gap `6/25` gives fewer than `73`
members for every length `n ≥ 2`. -/
private theorem exists_uniformFirstOrder_list_of_dimension_le_three
    {F : Type u} [Field F] [decF : DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hkThree : k ≤ 3) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card < 73 := by
  classical
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
    Subsingleton.elim _ _
  cases hdec
  let D := k - 1
  have hDk : D + 1 = k := by omega
  have hDA : D + 1 ≤ A := by
    have : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by positivity))
    rw [hDk]
    exact_mod_cast this
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hDcast : (D : ℝ) = k - 1 := by
    dsimp only [D]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hproduct : (0 : ℝ) ≤ (A - (k + 6 * n / 25)) * (A + (k + 6 * n / 25)) := by
    apply mul_nonneg
    · linarith
    · positivity
  have hkCases : k = 2 ∨ k = 3 := by omega
  have hpositive : n * D < A * A := by
    have hposR : (n : ℝ) * D < A * A := by
      rw [hDcast]
      rcases hkCases with rfl | rfl <;> norm_num at hgap hproduct ⊢ <;>
        nlinarith [sq_nonneg (6 * (n : ℝ) - 25 / 12), sq_nonneg (6 * (n : ℝ) - 175 / 6)]
    exact_mod_cast hposR
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_ncard_le_pairwiseJohnson domain received hDA hpositive
  rw [hDk] at hfinite hcard
  refine ⟨hfinite.toFinset, fun P ↦ hfinite.mem_toFinset, ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfinite]
  apply lt_of_le_of_lt hcard
  unfold Code.pairwiseJohnsonListBound
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < A * A - n * D)).2
  have hboundR : (n : ℝ) * (A - D : ℕ) < 73 * (A * A - n * D : ℕ) := by
    rw [Nat.cast_sub (by omega : D ≤ A), Nat.cast_sub hpositive.le]
    push_cast
    rw [hDcast]
    rcases hkCases with rfl | rfl <;> norm_num at hgap hproduct ⊢ <;>
      nlinarith [sq_nonneg (6 * (n : ℝ) - 25 / 12), sq_nonneg (6 * (n : ℝ) - 175 / 6)]
  exact_mod_cast hboundR

/-- For `k ≥ 2` and a characteristic that is zero or exceeds both `k - 1` and `4`, the
first-order certificate with multiplicity `12`, derivative cap `4`, jet cap `22` and height `851`
bounds the exact list by `307 n`. -/
private theorem exists_uniformFirstOrder_list_of_two_le
    {F : Type u} [Field F] [decF : DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 307 * n := by
  classical
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
    Subsingleton.elim _ _
  cases hdec
  let D := k - 1
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    exact_mod_cast (show (25 : ℝ) * k + 6 * n ≤ 25 * A by nlinarith)
  obtain ⟨hD, hbudget, hkD, hheight⟩ := uniformFirstOrder_parameters n k A hk hgapNat
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hfin := closePolynomialSet_finite domain received hkA
  have hsolutions : ∀ P ∈ hfin.toFinset, P.degree < k ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card := by
    intro P hP
    exact hfin.mem_toFinset.mp hP
  obtain ⟨cert⟩ : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A 12 4 22 k 851 domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := 12) (M := 4) (μ := 22))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain received (fun _ ↦ 0) hheight
  have hcard := FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
    domain received (firstOrderColumns (D := D) (A := A) (m := 12) (M := 4) (μ := 22)) cert
      hk hkA hAn (by norm_num) hchar hfin.toFinset hsolutions
  refine ⟨hfin.toFinset, fun P ↦ hfin.mem_toFinset, ?_⟩
  exact_mod_cast hcard.trans (uniformFirstOrder_listRatio_le n k A hn hk hAn hgap)

/-- **Uniform first-order lists at gap `6/25`.** For `n ≥ 2`, `0 < k` and
`k + (6/25) n ≤ A ≤ n`, the complete list of degree-`< k` polynomials agreeing with the received
word on at least `A` points is an exact finite list with at most `307 n` members. For `k ≥ 2` the
field characteristic must be zero or exceed `k - 1`; the field may be infinite. -/
theorem exists_uniformFirstOrder_list
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ k - 1 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 307 * n := by
  by_cases hkTwo : 2 ≤ k
  · by_cases hsupport : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F
    · exact exists_uniformFirstOrder_list_of_two_le n k A domain received
        hn hkTwo hAn hgap hsupport
    · have hdegreeChar := (hchar hkTwo).resolve_left fun hzero ↦ hsupport (Or.inl hzero)
      have hsupportChar : ¬ 4 < ringChar F := fun hfour ↦
        hsupport (Or.inr (max_lt hdegreeChar hfour))
      obtain ⟨list, hlist, hcard⟩ := exists_uniformFirstOrder_list_of_dimension_le_three
        n k A domain received hn hkTwo
        (uniformFirstOrder_messageDim_le_three_of_small_characteristic
          hkTwo hdegreeChar hsupportChar) hAn hgap
      exact ⟨list, hlist, by omega⟩
  · obtain rfl : k = 1 := by omega
    have hOneA : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
    obtain ⟨list, hlist, hcard⟩ :=
      exists_closePolynomial_finset_one_card_le_div domain received hOneA
    exact ⟨list, hlist, hcard.trans ((Nat.div_le_self n A).trans (by omega))⟩

end ReedSolomon
