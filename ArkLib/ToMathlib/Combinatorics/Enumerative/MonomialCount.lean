/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Counting exponent vectors of bounded degree outside finitely many cones

Let `σ` be a finite type with `n` elements. The exponent vectors `e : σ →₀ ℕ` of total degree
`Finsupp.degree e ≤ N` form a finset `Finsupp.degreeLEFinset σ N` with
`(N + n).choose n` elements. Those lying above a fixed vector `b` are in bijection, by
`e ↦ e - b`, with the vectors of degree at most `N - degree b`.

For a finite set `B` of vectors, inclusion–exclusion over the subsets `T ⊆ B`, whose cones
intersect in the cone above the coordinatewise supremum `T.sup id`, counts the vectors of degree
at most `N` lying above no element of `B`. Replacing each binomial coefficient by Mathlib's
`Polynomial.preHilbertPoly`, this count agrees with the polynomial
`Finsupp.coneAvoidancePoly K n B` for all `N ≥ degree (B.sup id)`, over every field `K` of
characteristic zero. The polynomial has degree at most `n`.

This is the combinatorial half of the eventual polynomiality of affine Hilbert functions: the
standard monomials of a polynomial ideal are the monomials outside finitely many cones.

## Main statements

* `Finsupp.card_degreeLEFinset`, `Finsupp.ncard_setOf_degree_le`: there are
  `(N + n).choose n` vectors of degree at most `N`.
* `Finsupp.card_filter_le_degreeLEFinset`: the count above a fixed vector `b`.
* `Finsupp.card_filter_forall_not_le_degreeLEFinset`: the inclusion–exclusion formula.
* `Finsupp.eval_coneAvoidancePoly`: the polynomial evaluates to the count beyond the threshold
  `degree (B.sup id)`.
* `Finsupp.exists_eval_eq_ncard_forall_not_le`: an instance-free form, with the count written
  as the `Set.ncard` of a set.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/MonomialCounting.lean`, namespace
`MonomialHilbertCounting`: `degreeBall` becomes `Finsupp.degreeLEFinset`, `card_degreeBall` becomes
`Finsupp.card_degreeLEFinset`, `upperConeInBall` and `card_upperConeInBall` become
`Finsupp.card_filter_le_degreeLEFinset`, `standardExponentFinset` and its private
inclusion–exclusion lemma become `Finsupp.card_filter_forall_not_le_degreeLEFinset`,
`countingPolynomial` becomes `Finsupp.coneAvoidancePoly`, `countingPolynomial_eval_eq_card`
becomes `Finsupp.eval_coneAvoidancePoly`, and `exists_eventual_standardExponent_countingPolynomial`
becomes `Finsupp.exists_eval_eq_ncard_forall_not_le`. The source worked over `ℚ` with the
threshold `forbiddenThreshold B`, the largest degree of `T.sup id` over `T ⊆ B`; here the
coefficient field is any field of characteristic zero and the threshold is the single value
`degree (B.sup id)`, which bounds all of those degrees. The source's `forbiddenSup`,
`standardExponentSet` and the finset-level existence statement are not kept as separate
declarations.
-/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace Finsupp

/-- The alternating sum over the subsets `T ⊆ B` of the shifted binomial polynomials
`preHilbertPoly K d (degree (T.sup id))`. For `d = Fintype.card σ` and every `N` beyond
`degree (B.sup id)`, it evaluates at `N` to the number of vectors of degree at most `N` above no
element of `B` (`eval_coneAvoidancePoly`). -/
def coneAvoidancePoly (K : Type*) [Field K] {σ : Type*} (d : ℕ) (B : Finset (σ →₀ ℕ)) : K[X] :=
  ∑ T ∈ B.powerset, ((-1 : K) ^ #T) • preHilbertPoly K d (T.sup id).degree

/-- In characteristic zero the counting polynomial has degree at most `d`. -/
theorem natDegree_coneAvoidancePoly_le (K : Type*) [Field K] [CharZero K] {σ : Type*} (d : ℕ)
    (B : Finset (σ →₀ ℕ)) :
    (coneAvoidancePoly K d B).natDegree ≤ d :=
  natDegree_sum_le_of_forall_le _ _ fun _ _ ↦
    (natDegree_smul_le _ _).trans_eq (natDegree_preHilbertPoly K d _)

section Count

variable (σ : Type*) [Fintype σ] [DecidableEq σ]

/-- The exponent vectors of total degree at most `N`. -/
def degreeLEFinset (N : ℕ) : Finset (σ →₀ ℕ) :=
  (range (N + 1)).biUnion fun t ↦ (univ : Finset σ).finsuppAntidiag t

variable {σ}

@[simp]
theorem mem_degreeLEFinset {N : ℕ} {e : σ →₀ ℕ} :
    e ∈ degreeLEFinset σ N ↔ e.degree ≤ N := by
  simp only [degreeLEFinset, mem_biUnion, mem_range, mem_finsuppAntidiag', subset_univ, and_true]
  change (∃ t < N + 1, e.degree = t) ↔ e.degree ≤ N
  exact ⟨fun ⟨t, ht, he⟩ ↦ by omega, fun he ↦ ⟨e.degree, by omega, rfl⟩⟩

@[simp]
theorem coe_degreeLEFinset (N : ℕ) :
    (degreeLEFinset σ N : Set (σ →₀ ℕ)) = {e | e.degree ≤ N} := by
  ext e
  simp

variable (σ) in
/-- There are `(N + n).choose n` exponent vectors of degree at most `N` in `n` variables. -/
theorem card_degreeLEFinset (N : ℕ) :
    #(degreeLEFinset σ N) = (N + Fintype.card σ).choose (Fintype.card σ) := by
  rw [degreeLEFinset, card_biUnion]
  · simp only [card_finsuppAntidiag_nat_eq_multichoose, card_univ]
    exact Nat.sum_range_multichoose N (Fintype.card σ)
  · intro a _ b _ hab
    rw [Function.onFun, disjoint_left]
    intro e hea heb
    exact hab ((mem_finsuppAntidiag'.mp hea).1.symm.trans (mem_finsuppAntidiag'.mp heb).1)

/-- Among the vectors of degree at most `N`, those above `b` are counted by translating by `b`.
The hypothesis `degree b ≤ N` is needed: otherwise there are no such vectors, while the right side
is `1` because the natural subtraction `N - degree b` truncates to `0`. -/
theorem card_filter_le_degreeLEFinset (b : σ →₀ ℕ) {N : ℕ} (hb : b.degree ≤ N) :
    #{e ∈ degreeLEFinset σ N | b ≤ e} =
      (N - b.degree + Fintype.card σ).choose (Fintype.card σ) := by
  rw [← card_degreeLEFinset σ (N - b.degree)]
  refine card_bij' (fun e _ ↦ e - b) (fun u _ ↦ u + b) ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨heN, hbe⟩ := (mem_filter.mp he)
    rw [mem_degreeLEFinset] at heN ⊢
    have h := congrArg degree (tsub_add_cancel_of_le hbe)
    rw [map_add] at h
    omega
  · intro u hu
    rw [mem_degreeLEFinset] at hu
    refine mem_filter.mpr ⟨?_, le_add_self⟩
    rw [mem_degreeLEFinset, map_add]
    omega
  · intro e he
    exact tsub_add_cancel_of_le (mem_filter.mp he).2
  · intro u _
    exact add_tsub_cancel_right u b

/-- Inclusion–exclusion for the vectors of degree at most `N` lying above no element of `B`:
the cones above the elements of a subset `T ⊆ B` intersect in the cone above `T.sup id`. -/
theorem card_filter_forall_not_le_degreeLEFinset (B : Finset (σ →₀ ℕ)) (N : ℕ) :
    (#{e ∈ degreeLEFinset σ N | ∀ b ∈ B, ¬b ≤ e} : ℤ) =
      ∑ T ∈ B.powerset, (-1 : ℤ) ^ #T * #{e ∈ degreeLEFinset σ N | T.sup id ≤ e} := by
  classical
  let cone : (σ →₀ ℕ) → Finset (degreeLEFinset σ N) := fun b ↦ {e | b ≤ e.1}
  have hinf : ∀ (T : Finset (σ →₀ ℕ)) (e : degreeLEFinset σ N),
      e ∈ T.inf cone ↔ ∀ b ∈ T, b ≤ e.1 := by
    intro T e
    induction T using Finset.induction_on with
    | empty => simp
    | insert b T _ ih =>
      rw [inf_insert, inf_eq_inter, mem_inter, ih]
      simp [cone]
  have hinf_compl : ∀ e : degreeLEFinset σ N,
      e ∈ B.inf (fun b ↦ (cone b)ᶜ) ↔ ∀ b ∈ B, ¬b ≤ e.1 := by
    intro e
    induction B using Finset.induction_on with
    | empty => simp
    | insert b T _ ih =>
      rw [inf_insert, inf_eq_inter, mem_inter, ih, mem_compl]
      simp [cone]
  have hcard : ∀ p : (σ →₀ ℕ) → Prop, ∀ s : Finset (degreeLEFinset σ N), [DecidablePred p] →
      (∀ e, e ∈ s ↔ p e.1) → #s = #{e ∈ degreeLEFinset σ N | p e} := by
    intro p s _ hs
    rw [← card_attach (s := {e ∈ degreeLEFinset σ N | p e})]
    refine card_bij (fun e he ↦ ⟨e.1, mem_filter.mpr ⟨e.2, (hs e).mp he⟩⟩)
      (fun _ _ ↦ mem_attach _ _) (fun a _ b _ h ↦ Subtype.ext
        (congrArg (fun x : {x // x ∈ {e ∈ degreeLEFinset σ N | p e}} ↦ x.1) h)) ?_
    intro e _
    obtain ⟨he, hp⟩ := mem_filter.mp e.2
    exact ⟨⟨e.1, he⟩, (hs _).mpr hp, rfl⟩
  rw [← hcard _ _ hinf_compl, inclusion_exclusion_card_inf_compl]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [hcard _ _ fun e ↦ (hinf T e).trans Finset.sup_le_iff.symm]
  rfl

/-- Beyond the threshold `degree (B.sup id)`, the counting polynomial evaluates to the number of
vectors of degree at most `N` lying above no element of `B`. The threshold is needed because each
binomial `(N - degree (T.sup id) + n).choose n` agrees with its polynomial only when
`degree (T.sup id) ≤ N`, and `degree (T.sup id) ≤ degree (B.sup id)` for `T ⊆ B`. -/
theorem eval_coneAvoidancePoly (K : Type*) [Field K] [CharZero K] (B : Finset (σ →₀ ℕ)) {N : ℕ}
    (hN : (B.sup id).degree ≤ N) :
    (coneAvoidancePoly K (Fintype.card σ) B).eval (N : K) =
      #{e ∈ degreeLEFinset σ N | ∀ b ∈ B, ¬b ≤ e} := by
  have hint := congrArg (Int.cast : ℤ → K) (card_filter_forall_not_le_degreeLEFinset B N)
  push_cast at hint
  rw [hint, coneAvoidancePoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun T hT ↦ ?_
  have hTN : (T.sup id).degree ≤ N :=
    (degree_mono (sup_mono (mem_powerset.mp hT))).trans hN
  rw [eval_smul, smul_eq_mul, preHilbertPoly_eq_choose_add_sub K _ (by omega),
    card_filter_le_degreeLEFinset _ hTN, Nat.sub_add_comm hTN]

end Count

/-- For every finite variable type and finite set `B` of exponent vectors, the number of vectors of
degree at most `N` above no element of `B` agrees, for all `N ≥ degree (B.sup id)`, with a
polynomial over `K` of degree at most `Nat.card σ`. This form needs no `Fintype` or
`DecidableEq` instance on `σ`. -/
theorem exists_eval_eq_ncard_forall_not_le (K : Type*) [Field K] [CharZero K] {σ : Type*}
    [Finite σ] (B : Finset (σ →₀ ℕ)) :
    ∃ P : K[X], P.natDegree ≤ Nat.card σ ∧ ∀ N ≥ (B.sup id).degree,
      P.eval (N : K) = {e : σ →₀ ℕ | e.degree ≤ N ∧ ∀ b ∈ B, ¬b ≤ e}.ncard := by
  classical
  have := Fintype.ofFinite σ
  refine ⟨coneAvoidancePoly K (Fintype.card σ) B, ?_, fun N hN ↦ ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact natDegree_coneAvoidancePoly_le K _ B
  · rw [eval_coneAvoidancePoly K B hN, ← Set.ncard_coe_finset, coe_filter]
    simp

/-- There are `(N + n).choose n` exponent vectors of degree at most `N` in `n = Nat.card σ`
variables. -/
theorem ncard_setOf_degree_le (σ : Type*) [Finite σ] (N : ℕ) :
    {e : σ →₀ ℕ | e.degree ≤ N}.ncard = (N + Nat.card σ).choose (Nat.card σ) := by
  classical
  have := Fintype.ofFinite σ
  rw [← coe_degreeLEFinset, Set.ncard_coe_finset, card_degreeLEFinset, Nat.card_eq_fintype_card]

end Finsupp
