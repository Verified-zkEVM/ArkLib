/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree

/-!
# Acceptance tests for affine Hilbert functions of bidegree hypersurfaces

The examples bound the dimension of a quotient of bounded bidegree by a small hypersurface, state
the affine-degree bound and the bound on the minimal primes of a pulled-back hypersurface with one,
two and `r + 1` further variables, and show that `g ≠ 0` is needed in
`affineDegree_comap_bidegreeMap_span_singleton_le`.
-/

open MvPolynomial

namespace AffineHilbertBidegreeTest

/-- The distinguished variable has bidegree `(1, 0)`. -/
theorem X_none_mem_restrictBidegree : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 1 0 := by
  rw [mem_restrictBidegree, support_X]
  simp

/-- Modulo `X none`, in one further variable, the polynomials of bidegree at most `(1, 1)` span a
space of dimension at most `2 * 2 - 1 * 2 = 2`. -/
example : Module.finrank ℚ (quotientBidegreeLE
    (Ideal.span {(X none : MvPolynomial (Option (Fin 1)) ℚ)}) 1 1) ≤ 2 := by
  have h := finrank_quotientBidegreeLE_span_singleton_le (X_ne_zero _) X_none_mem_restrictBidegree
    le_rfl (Nat.zero_le 1)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- With one further variable, the pullback of a hypersurface of bidegree at most `(h, v)` has
affine degree at most `h * b + v * a`. -/
example {F : Type*} [Field F] {a b h v : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin 1)) F} (hg0 : g ≠ 0) (hg : g ∈ restrictBidegree (Fin 1) F h v) :
    affineDegree ((Ideal.span {g}).comap (bidegreeMap (Fin 1) F a b)) ≤ (h * b + v * a : ℕ) :=
  (affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg).trans_eq (by simp)

/-- With two further variables, the pullback of a hypersurface of bidegree at most `(h, v)` has
affine degree at most `h * b ^ 2 + 2 * v * a * b`. -/
example {F : Type*} [Field F] {a b h v : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin 2)) F} (hg0 : g ≠ 0) (hg : g ∈ restrictBidegree (Fin 2) F h v) :
    affineDegree ((Ideal.span {g}).comap (bidegreeMap (Fin 2) F a b)) ≤
      (h * b ^ 2 + 2 * v * a * b : ℕ) :=
  (affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg).trans_eq (by simp)

/-- With `r + 1` further variables, the pullback of a hypersurface of bidegree at most `(h, v)`
has affine degree at most `h * b ^ (r + 1) + (r + 1) * v * a * b ^ r`. -/
example {F : Type*} [Field F] {r a b h v : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin (r + 1))) F} (hg0 : g ≠ 0)
    (hg : g ∈ restrictBidegree (Fin (r + 1)) F h v) :
    affineDegree ((Ideal.span {g}).comap (bidegreeMap (Fin (r + 1)) F a b)) ≤
      (h * b ^ (r + 1) + (r + 1) * v * a * b ^ r : ℕ) :=
  (affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg).trans_eq (by simp)

/-- With one further variable, the minimal primes of the pullback of a hypersurface of bidegree at
most `(h, v)` have total affine degree at most `h * b + v * a`. -/
example {F : Type*} [Field F] {a b h v : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin 1)) F} (hg0 : g ≠ 0) (hg : g ∈ restrictBidegree (Fin 1) F h v) :
    ∑ Q ∈ ((Ideal.span {g}).comap (bidegreeMap (Fin 1) F a b)).minimalPrimesFinset,
        affineDegree Q ≤ (h * b + v * a : ℕ) :=
  (sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hb g).trans
    ((affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg).trans_eq (by simp))

/-- With two further variables, the minimal primes of the pullback of a hypersurface of bidegree
at most `(h, v)` have total affine degree at most `h * b ^ 2 + 2 * v * a * b`. -/
example {F : Type*} [Field F] {a b h v : ℕ} (ha : 0 < a) (hb : 0 < b)
    {g : MvPolynomial (Option (Fin 2)) F} (hg0 : g ≠ 0) (hg : g ∈ restrictBidegree (Fin 2) F h v) :
    ∑ Q ∈ ((Ideal.span {g}).comap (bidegreeMap (Fin 2) F a b)).minimalPrimesFinset,
        affineDegree Q ≤ (h * b ^ 2 + 2 * v * a * b : ℕ) :=
  (sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hb g).trans
    ((affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg).trans_eq (by simp))

/-- The hypothesis `g ≠ 0` of `affineDegree_comap_bidegreeMap_span_singleton_le` is needed:
`0` has bidegree at most `(0, 0)`, but the pullback of `span {0}` is the kernel of
`bidegreeMap`, a proper ideal of positive affine degree. -/
example : ¬affineDegree ((Ideal.span {(0 : MvPolynomial (Option (Fin 1)) ℚ)}).comap
      (bidegreeMap (Fin 1) ℚ 1 1)) ≤
    (0 * 1 ^ Nat.card (Fin 1) + Nat.card (Fin 1) * 0 * 1 * 1 ^ (Nat.card (Fin 1) - 1) : ℕ) := by
  rw [not_le]
  refine lt_of_eq_of_lt (by simp) (affineDegree_pos fun htop ↦ ?_)
  have h1 : (1 : MvPolynomial (bidegreeExponents (Fin 1) 1 1) ℚ) ∈
      (Ideal.span {(0 : MvPolynomial (Option (Fin 1)) ℚ)}).comap (bidegreeMap (Fin 1) ℚ 1 1) :=
    htop ▸ Submodule.mem_top
  simp at h1

end AffineHilbertBidegreeTest
