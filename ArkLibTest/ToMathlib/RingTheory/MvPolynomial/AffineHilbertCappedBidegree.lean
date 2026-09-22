/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree

/-!
# Acceptance tests for affine Hilbert functions of capped bidegree hypersurfaces

The examples compute the natural degree of the kernel of the capped monomial map, bound the
affine Hilbert function of a small pulled-back hypersurface, derive the affine-degree bound in the
form `h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))` for `c < b`, and show that the
bound needs `g ≠ 0` and `c ≤ b`.
-/

open MvPolynomial

namespace AffineHilbertCappedBidegreeTest

/-- The distinguished variable has bounds `(1, 0, 0)`. -/
theorem X_none_mem_restrictCappedBidegree :
    (X none : MvPolynomial (Option (Fin 2)) ℚ) ∈ restrictCappedBidegree (Fin 2) ℚ 1 1 0 0 := by
  rw [mem_restrictCappedBidegree, support_X]
  simp [Finsupp.some_single_none]

/-- The hypersurface `X none = 0` is proper. -/
theorem span_X_none_ne_top : Ideal.span {(X none : MvPolynomial (Option (Fin 2)) ℚ)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro h
  simpa using h.map constantCoeff

/-- For positive bounds, the kernel of the capped monomial map on `Option (Fin 2)` has affine
Hilbert polynomial of natural degree `3`. -/
example {k : Type*} [Field k] {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (affineHilbertPolynomial (RingHom.ker
      (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c)))).natDegree = 3 := by
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective _
    (monomialMap_cappedBidegreeExponents_surjective ha hb hc), Finite.card_option,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Pulled back along the monomial map for bounds `(1, 2, 1)`, the hypersurface `X none = 0` has
affine Hilbert function at `1` at most `2 * 5 - 1 * 5 = 5`. -/
example : affineHilbertFunction ((Ideal.span {(X none : MvPolynomial (Option (Fin 2)) ℚ)}).comap
    (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 2 1))) 1 ≤ 5 := by
  have h := affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le (N := 1)
    (a := 1) (b := 2) (c := 1) (X_ne_zero _) X_none_mem_restrictCappedBidegree
    le_rfl (Nat.zero_le _) (Nat.zero_le _)
  have hT := Finsupp.two_mul_ncard_setOf_degree_le_and_apply_one_le 2 1 (by norm_num)
  norm_num at h
  omega

/-- For `c < b`, the pullback of a hypersurface with bounds `(h, j, r)` has affine degree at most
`h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))`. -/
example {k : Type*} [Field k] {a b c h j r : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcb : c < b) {g : MvPolynomial (Option (Fin 2)) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))) ≤
      (h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c)) : ℕ) := by
  refine (affineDegree_comap_cappedBidegree_span_singleton_le ha hb hc hcb.le hg0 hg).trans_eq ?_
  rw [mul_assoc h, Nat.mul_sub, sq, mul_comm c (2 * b)]

/-- For `c < b`, the minimal primes of the pullback of a hypersurface with bounds `(h, j, r)`
have total affine degree at most `h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))`. -/
example {k : Type*} [Field k] {a b c h j r : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcb : c < b) {g : MvPolynomial (Option (Fin 2)) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    ∑ Q ∈ ((Ideal.span {g}).comap
        (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))).minimalPrimesFinset,
        affineDegree Q ≤
      (h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c)) : ℕ) := by
  refine (sum_affineDegree_minimalPrimes_comap_cappedBidegree_span_singleton_le ha hb hc hcb.le
    hg0 hg).trans_eq ?_
  rw [mul_assoc h, Nat.mul_sub, sq, mul_comm c (2 * b)]

/-- For `c = b`, the bound is `h * b ^ 2 + 2 * j * a * b`, that of the bidegree hypersurface. -/
example {k : Type*} [Field k] {a b h j r : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin 2)) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b b))) ≤
      (h * b ^ 2 + 2 * j * a * b : ℕ) := by
  refine (affineDegree_comap_cappedBidegree_span_singleton_le ha hb hb le_rfl hg0 hg).trans_eq ?_
  rw [show 2 * b - b = b by omega, Nat.sub_self]
  push_cast
  ring

/-- `affineDegree_comap_cappedBidegree_span_singleton_le` needs `g ≠ 0`: `0` has bounds
`(0, 0, 0)`, but the pullback of `span {0}` is the kernel of the monomial map, a proper ideal of
positive affine degree. -/
example : ¬affineDegree ((Ideal.span {(0 : MvPolynomial (Option (Fin 2)) ℚ)}).comap
      (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 1 1))) ≤
    (0 * 1 * (2 * 1 - 1) + 2 * 1 * (0 * 1 + 0 * (1 - 1)) : ℕ) := by
  rw [not_le]
  refine lt_of_eq_of_lt (by simp) (affineDegree_pos fun htop ↦ ?_)
  have h1 : (1 : MvPolynomial (cappedBidegreeExponents (Fin 2) 1 1 1 1) ℚ) ∈
      (Ideal.span {(0 : MvPolynomial (Option (Fin 2)) ℚ)}).comap
        (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 1 1)) :=
    htop ▸ Submodule.mem_top
  simp at h1

/-- `affineDegree_comap_cappedBidegree_span_singleton_le` needs `c ≤ b`: for `b = 1` and
`c = 3`, the hypersurface `X none = 0` has bounds `(1, 0, 0)` and the formula gives `0`, but its
pullback is proper and has positive affine degree. -/
example : ¬affineDegree ((Ideal.span {(X none : MvPolynomial (Option (Fin 2)) ℚ)}).comap
      (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 1 3))) ≤
    (1 * 3 * (2 * 1 - 3) + 2 * 1 * (0 * 3 + 0 * (1 - 3)) : ℕ) := by
  rw [not_le]
  exact lt_of_eq_of_lt (by simp) (affineDegree_pos (Ideal.comap_ne_top _ span_X_none_ne_top))

end AffineHilbertCappedBidegreeTest
