/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Ring

/-!
# Two-point collisions in a finite polynomial family

Two distinct tuples of low-degree polynomials can agree at two sampled points only when both
points are roots of one nonzero coordinate difference.  This module packages that observation
with a union bound over unordered candidate pairs.  The resulting numerator is
`choose candidates.card 2 * degreeBound ^ 2`.

The theorem counts a finite set of bad ordered point pairs.  Restricting the samples to points
outside an evaluation domain, and requiring the two samples to be distinct, can only shrink this
set.  The application layer supplies the corresponding sample-space denominator.
-/

@[expose] public section

namespace ArkLib.TwoPointPolynomialCollision

open Polynomial

noncomputable section

/-- Unordered two-element subsets of a finite candidate family. -/
abbrev CandidatePair {beta : Type*} [DecidableEq beta] (candidates : Finset beta) :=
  {pair : Finset beta // pair ∈ candidates.powersetCard 2}

theorem candidatePair_card {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) : pair.1.card = 2 :=
  (Finset.mem_powersetCard.mp pair.2).2

noncomputable def pairLeft {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) : beta :=
  (Finset.card_eq_two.mp (candidatePair_card pair)).choose

noncomputable def pairRight {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) : beta :=
  (Finset.card_eq_two.mp (candidatePair_card pair)).choose_spec.choose

theorem pairLeft_ne_pairRight {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) :
    pairLeft pair ≠ pairRight pair :=
  (Finset.card_eq_two.mp (candidatePair_card pair)).choose_spec.choose_spec.1

theorem pair_eq_insert {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) :
    pair.1 = {pairLeft pair, pairRight pair} :=
  (Finset.card_eq_two.mp (candidatePair_card pair)).choose_spec.choose_spec.2

theorem pairLeft_mem {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) :
    pairLeft pair ∈ candidates := by
  exact (Finset.mem_powersetCard.mp pair.2).1 <| by simp [pair_eq_insert pair]

theorem pairRight_mem {beta : Type*} [DecidableEq beta]
    {candidates : Finset beta} (pair : CandidatePair candidates) :
    pairRight pair ∈ candidates := by
  exact (Finset.mem_powersetCard.mp pair.2).1 <| by simp [pair_eq_insert pair]

noncomputable def separatingCoordinate {F : Type*} [Field F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    (pair : CandidatePair candidates) : Fin width := by
  classical
  have hne : pairLeft pair ≠ pairRight pair := pairLeft_ne_pairRight pair
  exact Classical.choose <| Function.ne_iff.mp hne

/-- A coordinate difference separating the two members of an unordered candidate pair. -/
noncomputable def separator {F : Type*} [Field F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    (pair : CandidatePair candidates) : F[X] :=
  pairLeft pair (separatingCoordinate pair) - pairRight pair (separatingCoordinate pair)

theorem separator_ne_zero {F : Type*} [Field F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    (pair : CandidatePair candidates) : separator pair ≠ 0 := by
  classical
  apply sub_ne_zero.mpr
  exact Classical.choose_spec <| Function.ne_iff.mp (pairLeft_ne_pairRight pair)

theorem separator_natDegree_le {F : Type*} [Field F]
    {width degreeBound : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    (hdegree : ∀ tuple ∈ candidates, ∀ i, (tuple i).natDegree ≤ degreeBound)
    (pair : CandidatePair candidates) : (separator pair).natDegree ≤ degreeBound := by
  unfold separator
  exact (natDegree_sub_le _ _).trans <| max_le
    (hdegree _ (pairLeft_mem pair) _) (hdegree _ (pairRight_mem pair) _)

/-- Ordered pairs of roots of one polynomial.  Allowing the two roots to coincide only enlarges
the bad set, which is convenient when the application samples distinct anchors. -/
def twoPointRootPairs {F : Type*} [Field F] [DecidableEq F] (p : F[X]) : Finset (F × F) :=
  p.roots.toFinset ×ˢ p.roots.toFinset

theorem card_twoPointRootPairs_le {F : Type*} [Field F] [DecidableEq F]
    {degreeBound : ℕ} (p : F[X]) (hdegree : p.natDegree ≤ degreeBound) :
    (twoPointRootPairs p).card ≤ degreeBound ^ 2 := by
  rw [twoPointRootPairs, Finset.card_product, pow_two]
  exact Nat.mul_le_mul
    ((Multiset.toFinset_card_le p.roots).trans <| (p.card_roots').trans hdegree)
    ((Multiset.toFinset_card_le p.roots).trans <| (p.card_roots').trans hdegree)

/-- Union of the two-root bad sets over every unordered candidate pair. -/
def collisionSet {F : Type*} [Field F] [DecidableEq F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    (candidates : Finset (Fin width → F[X])) : Finset (F × F) := by
  classical
  exact (Finset.univ : Finset (CandidatePair candidates)).biUnion fun pair ↦
    twoPointRootPairs (separator pair)

/-- The two-point collision set has the standard unordered-pair union bound. -/
theorem card_collisionSet_le {F : Type*} [Field F] [DecidableEq F]
    {width degreeBound : ℕ} [DecidableEq (Fin width → F[X])]
    (candidates : Finset (Fin width → F[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ i, (tuple i).natDegree ≤ degreeBound) :
    (collisionSet candidates).card ≤ candidates.card.choose 2 * degreeBound ^ 2 := by
  classical
  unfold collisionSet
  calc
    _ ≤ ∑ pair : CandidatePair candidates,
        (twoPointRootPairs (separator pair)).card := Finset.card_biUnion_le
    _ ≤ ∑ _pair : CandidatePair candidates, degreeBound ^ 2 := by
      apply Finset.sum_le_sum
      intro pair _
      exact card_twoPointRootPairs_le _ (separator_natDegree_le hdegree pair)
    _ = candidates.card.choose 2 * degreeBound ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [CandidatePair]

/-- If two distinct candidate tuples agree coordinatewise at both points, the point pair lies in
`collisionSet`.  Thus the preceding cardinality theorem bounds the actual collision event. -/
theorem mem_collisionSet_of_agree {F : Type*} [Field F] [DecidableEq F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    {left right : Fin width → F[X]} (hleft : left ∈ candidates) (hright : right ∈ candidates)
    (hne : left ≠ right) {x y : F}
    (hagreeX : ∀ i, (left i).eval x = (right i).eval x)
    (hagreeY : ∀ i, (left i).eval y = (right i).eval y) :
    (x, y) ∈ collisionSet candidates := by
  classical
  let pair : CandidatePair candidates := ⟨{left, right}, by
    rw [Finset.mem_powersetCard]
    exact ⟨by simp [Finset.insert_subset_iff, hleft, hright], by simp [hne]⟩⟩
  unfold collisionSet
  apply Finset.mem_biUnion.mpr
  refine ⟨pair, Finset.mem_univ _, ?_⟩
  rw [twoPointRootPairs, Finset.mem_product]
  have hmembers : pair.1 = {pairLeft pair, pairRight pair} := pair_eq_insert pair
  have hleftOr : pairLeft pair = left ∨ pairLeft pair = right := by
    have : pairLeft pair ∈ pair.1 := by rw [pair_eq_insert pair]; simp
    change pairLeft pair ∈ {left, right} at this
    simpa using this
  have hrightOr : pairRight pair = left ∨ pairRight pair = right := by
    have : pairRight pair ∈ pair.1 := by rw [pair_eq_insert pair]; simp
    change pairRight pair ∈ {left, right} at this
    simpa using this
  have heval (z : F) (hagree : ∀ i, (left i).eval z = (right i).eval z) :
      (separator pair).eval z = 0 := by
    unfold separator
    rw [eval_sub]
    rcases hleftOr with hL | hL <;> rcases hrightOr with hR | hR
    · exact (pairLeft_ne_pairRight pair (hL.trans hR.symm)).elim
    · simpa [hL, hR] using sub_eq_zero.mpr (hagree _)
    · simpa [hL, hR] using sub_eq_zero.mpr (hagree _).symm
    · exact (pairLeft_ne_pairRight pair (hL.trans hR.symm)).elim
  constructor <;> rw [Multiset.mem_toFinset, mem_roots (separator_ne_zero pair)]
  · exact heval x hagreeX
  · exact heval y hagreeY

/-- Outside the conservative exceptional set, two candidates agreeing at both anchors are the
same polynomial tuple.  This is the uniqueness form used after the verifier fixes the claimed
anchor values. -/
theorem eq_of_agree_of_not_mem_collisionSet {F : Type*} [Field F] [DecidableEq F]
    {width : ℕ} [DecidableEq (Fin width → F[X])]
    {candidates : Finset (Fin width → F[X])}
    {left right : Fin width → F[X]} (hleft : left ∈ candidates) (hright : right ∈ candidates)
    {x y : F} (hgood : (x, y) ∉ collisionSet candidates)
    (hagreeX : ∀ i, (left i).eval x = (right i).eval x)
    (hagreeY : ∀ i, (left i).eval y = (right i).eval y) :
    left = right := by
  by_contra hne
  exact hgood (mem_collisionSet_of_agree hleft hright hne hagreeX hagreeY)

/-! ## Sampling two distinct points outside a domain -/

/-- Field points outside a fixed evaluation domain. -/
def outsideDomain {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) : Finset F :=
  Finset.univ \ Finset.univ.image domain

theorem card_outsideDomain {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) :
    (outsideDomain domain).card = Fintype.card F - n := by
  rw [outsideDomain, Finset.card_sdiff, Finset.inter_univ]
  rw [Finset.card_univ, Finset.card_image_of_injective _ domain.injective, Finset.card_univ,
    Fintype.card_fin]

/-- Ordered distinct pairs from a finite set, presented as disjoint fibers over the first point. -/
def orderedDistinctPairs {alpha : Type*} [DecidableEq alpha]
    (points : Finset alpha) : Finset (alpha × alpha) :=
  points.biUnion fun x ↦ {x} ×ˢ points.erase x

theorem card_orderedDistinctPairs {alpha : Type*} [DecidableEq alpha]
    (points : Finset alpha) :
    (orderedDistinctPairs points).card = points.card * (points.card - 1) := by
  classical
  unfold orderedDistinctPairs
  rw [Finset.card_biUnion]
  · calc
      ∑ x ∈ points, ({x} ×ˢ points.erase x).card =
          ∑ _x ∈ points, (points.card - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_product, Finset.card_singleton, one_mul,
          Finset.card_erase_of_mem hx]
      _ = points.card * (points.card - 1) := by simp
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro pair hpairX hpairY
    have hx' : pair.1 = x := Finset.mem_singleton.mp (Finset.mem_product.mp hpairX).1
    have hy' : pair.1 = y := Finset.mem_singleton.mp (Finset.mem_product.mp hpairY).1
    exact hxy (hx'.symm.trans hy')

/-- The exact ordered sample-space size for two distinct points outside an `n`-point domain. -/
theorem card_orderedDistinctPairs_outsideDomain
    {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (domain : Fin n ↪ F) :
    (orderedDistinctPairs (outsideDomain domain)).card =
      (Fintype.card F - n) * (Fintype.card F - n - 1) := by
  rw [card_orderedDistinctPairs, card_outsideDomain]

/-- Fraction of distinct outside-domain anchor pairs in the conservative exceptional set.  Every
actual full-tuple collision lies in this set, although the set may also contain pairs where only
the selected separating coordinate agrees. -/
def collisionRate {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n width : ℕ} [DecidableEq (Fin width → F[X])]
    (domain : Fin n ↪ F) (candidates : Finset (Fin width → F[X])) : ℚ :=
  ((collisionSet candidates ∩ orderedDistinctPairs (outsideDomain domain)).card : ℚ) /
    (orderedDistinctPairs (outsideDomain domain)).card

/-- The conservative exceptional-pair fraction containing every two-anchor collision is bounded
by the paper's square-denominator expression.  The only hypotheses are the polynomial degree cap,
a candidate-count cap, and enough field points to sample two distinct anchors outside the domain. -/
theorem collisionRate_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n width degreeBound listBound : ℕ} [DecidableEq (Fin width → F[X])]
    (domain : Fin n ↪ F) (candidates : Finset (Fin width → F[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ i, (tuple i).natDegree ≤ degreeBound)
    (hlist : candidates.card ≤ listBound) (hspace : n + 1 < Fintype.card F) :
    collisionRate domain candidates ≤
      (listBound.choose 2 : ℚ) *
        ((degreeBound : ℚ) / (Fintype.card F - n - 1 : ℕ)) ^ 2 := by
  have hbad :
      (collisionSet candidates ∩ orderedDistinctPairs (outsideDomain domain)).card ≤
        candidates.card.choose 2 * degreeBound ^ 2 :=
    (Finset.card_le_card (Finset.inter_subset_left)).trans
      (card_collisionSet_le candidates hdegree)
  have hchoose : candidates.card.choose 2 ≤ listBound.choose 2 :=
    Nat.choose_le_choose 2 hlist
  rw [collisionRate, card_orderedDistinctPairs_outsideDomain]
  have hden : 0 < Fintype.card F - n - 1 := by omega
  have hfirst : Fintype.card F - n - 1 ≤ Fintype.card F - n := by omega
  calc
    _ ≤ ((candidates.card.choose 2 * degreeBound ^ 2 : ℕ) : ℚ) /
          (((Fintype.card F - n) * (Fintype.card F - n - 1) : ℕ) : ℚ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hbad) (by positivity)
    _ ≤ ((listBound.choose 2 * degreeBound ^ 2 : ℕ) : ℚ) /
          (((Fintype.card F - n - 1) ^ 2 : ℕ) : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
      apply div_le_div₀
      · positivity
      · exact_mod_cast Nat.mul_le_mul_right (degreeBound ^ 2) hchoose
      · positivity
      · exact_mod_cast (by
          simpa [pow_two, Nat.mul_comm] using
            Nat.mul_le_mul_right (Fintype.card F - n - 1) hfirst)
    _ = (listBound.choose 2 : ℚ) *
          ((degreeBound : ℚ) / (Fintype.card F - n - 1 : ℕ)) ^ 2 := by
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [div_pow]
      ring

end

end ArkLib.TwoPointPolynomialCollision
