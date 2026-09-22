/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree

/-!
# Acceptance tests for affine Hilbert functions of capped degree hypersurfaces

The examples compute the natural degrees of the kernel of the capped monomial map on `Fin 2` and
of a pulled-back hypersurface, write the pullback as a principal cut of the kernel, bound the
affine Hilbert function of a small pulled-back curve, state the dimension count in the quotient,
derive the affine-degree bound in the form `(j - r) * c + r * b` for `r ≤ j`, check the case
`b < c`, and show that the bound needs `g ≠ 0` and `0 < c`.
-/

open MvPolynomial

namespace AffineHilbertCappedDegreeTest

/-- The variable `X 0` has bounds `(1, 0)`. -/
theorem X_zero_mem_restrictCappedDegree :
    (X 0 : MvPolynomial (Fin 2) ℚ) ∈ restrictCappedDegree (Fin 2) ℚ 1 1 0 := by
  rw [mem_restrictCappedDegree, support_X]
  simp

/-- The curve `X 0 = 0` is proper. -/
theorem span_X_zero_ne_top : Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro h
  simpa using h.map constantCoeff

section Kernel

variable {k : Type*} [Field k] {b c : ℕ}

/-- The kernel of the capped monomial map is prime. -/
example : (RingHom.ker (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))).IsPrime :=
  RingHom.ker_isPrime _

/-- For positive bounds, the kernel of the capped monomial map on `Fin 2` has affine Hilbert
polynomial of natural degree `2`. -/
example (hb : 0 < b) (hc : 0 < c) :
    (affineHilbertPolynomial
      (RingHom.ker (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)))).natDegree = 2 := by
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective _
    (monomialMap_cappedDegreeExponents_surjective hb hc), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- For positive bounds, the pullback of `span {g}` has the natural degree of `span {g}`. -/
example (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Fin 2) k) :
    (affineHilbertPolynomial
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)))).natDegree =
      (affineHilbertPolynomial (Ideal.span {g})).natDegree :=
  natDegree_affineHilbertPolynomial_comap_of_surjective _
    (monomialMap_cappedDegreeExponents_surjective hb hc) _

/-- The pullback of `span {g}` is the kernel of the monomial map followed by the quotient
by `g`. -/
example (g : MvPolynomial (Fin 2) k) :
    RingHom.ker ((Ideal.Quotient.mkₐ k (Ideal.span {g})).comp
        (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))) =
      (Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)) := by
  ext P
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- For positive bounds and `g` with bounds `(b, c)`, the pullback of `span {g}` is the principal
cut of the kernel by the linear lift of `g`. -/
example (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Fin 2) k)
    (hg : g ∈ restrictCappedDegree (Fin 2) k 1 b c) :
    (Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)) =
      RingHom.ker (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)) ⊔
        Ideal.span {monomialLift g hg} := by
  conv_lhs => rw [← monomialMap_monomialLift g hg]
  exact Ideal.comap_span_singleton_of_surjective _
    (monomialMap_cappedDegreeExponents_surjective hb hc) _

/-- For positive bounds, the minimal primes of the pullback of `span {g}` have total affine degree
at most its affine degree. -/
example (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Fin 2) k) :
    ∑ Q ∈ ((Ideal.span {g}).comap
        (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))).minimalPrimesFinset,
        affineDegree Q ≤
      affineDegree ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))) :=
  sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective _
    (monomialMap_cappedDegreeExponents_surjective hb hc) g

end Kernel

/-- Let `g ≠ 0` have bounds `(j, r)`. The image of the polynomials with bounds `(B, C)` in the
quotient by `g` has dimension at most the number of capped exponents with bounds `(B, C)` minus
the number with bounds `(B - j, C - r)`. -/
example {k : Type*} [Field k] {g : MvPolynomial (Fin 2) k} {j r B C : ℕ} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) (hj : j ≤ B) (hr : r ≤ C) :
    Module.finrank k ((restrictCappedDegree (Fin 2) k 1 B C).map
        (Ideal.Quotient.mkₐ k (Ideal.span {g})).toLinearMap) +
        (cappedDegreeExponents (Fin 2) 1 (B - j) (C - r)).ncard ≤
      (cappedDegreeExponents (Fin 2) 1 B C).ncard := by
  rw [← finrank_restrictCappedDegree (R := k), ← finrank_restrictCappedDegree (R := k)]
  refine Submodule.finrank_map_mkₐ_span_singleton_add_le hg0 fun p hp ↦ ?_
  have hgp := mul_mem_restrictCappedDegree hg hp
  rwa [Nat.add_sub_cancel' hj, Nat.add_sub_cancel' hr] at hgp

/-- Pulled back along the monomial map for bounds `(2, 1)`, the curve `X 0 = 0` has affine Hilbert
function at `1` at most `5 - 3 = 2`. -/
example : affineHilbertFunction ((Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}).comap
    (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 2 1))) 1 ≤ 2 := by
  have h := affineHilbertFunction_comap_cappedDegree_span_singleton_add_le (N := 1) (b := 2)
    (c := 1) (X_ne_zero _) X_zero_mem_restrictCappedDegree (by norm_num) (Nat.zero_le _)
  have hT := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  have hT' := two_mul_ncard_cappedDegreeExponents_fin_two 1 1 le_rfl
  norm_num at h
  omega

/-- For `r ≤ j` and `c ≤ b`, the pullback of a curve with bounds `(j, r)` has affine degree at
most `(j - r) * c + r * b`. -/
example {k : Type*} [Field k] {b c j r : ℕ} (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b) (hrj : r ≤ j)
    {g : MvPolynomial (Fin 2) k} (hg0 : g ≠ 0) (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    affineDegree ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))) ≤
      ((j - r) * c + r * b : ℕ) := by
  exact (affineDegree_comap_cappedDegree_span_singleton_le hb hc hg0 hg).trans_eq
    (by rw [cappedDegreeMixedVolume_eq hrj hcb])

/-- The minimal primes of the pullback of a curve with bounds `(j, r)` have total affine degree at
most `j * c + r * (b - c)`. -/
example {k : Type*} [Field k] {b c j r : ℕ} (hb : 0 < b) (hc : 0 < c)
    {g : MvPolynomial (Fin 2) k} (hg0 : g ≠ 0) (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    ∑ Q ∈ ((Ideal.span {g}).comap
        (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))).minimalPrimesFinset,
        affineDegree Q ≤ (j * c + r * (b - c) : ℕ) :=
  sum_affineDegree_minimalPrimes_comap_cappedDegree_span_singleton_le hb hc hg0 hg

/-- For `b < c` the bound is `j * c`: for `b = 1` and `c = 3`, the curve `X 0 = 0` has bounds
`(1, 0)`, and its pullback has affine degree at most `3`. -/
example : affineDegree ((Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}).comap
      (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 3))) ≤ 3 := by
  simpa [cappedDegreeMixedVolume] using affineDegree_comap_cappedDegree_span_singleton_le (b := 1)
    (c := 3) (by norm_num) (by norm_num) (X_ne_zero _) X_zero_mem_restrictCappedDegree

/-- `affineDegree_comap_cappedDegree_span_singleton_le` needs `g ≠ 0`: `0` has bounds `(0, 0)`,
but the pullback of `span {0}` is the kernel of the monomial map, a proper ideal of positive affine
degree. -/
example : ¬affineDegree ((Ideal.span {(0 : MvPolynomial (Fin 2) ℚ)}).comap
      (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 1))) ≤
    (cappedDegreeMixedVolume 0 0 1 1 : ℕ) := by
  rw [not_le]
  refine lt_of_eq_of_lt (by simp [cappedDegreeMixedVolume]) (affineDegree_pos fun htop ↦ ?_)
  have h1 : (1 : MvPolynomial (cappedDegreeExponents (Fin 2) 1 1 1) ℚ) ∈
      (Ideal.span {(0 : MvPolynomial (Fin 2) ℚ)}).comap
        (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 1)) :=
    htop ▸ Submodule.mem_top
  simp at h1

/-- `affineDegree_comap_cappedDegree_span_singleton_le` needs `0 < c`: for `c = 0`, the curve
`X 0 = 0` has bounds `(1, 0)` and the formula gives `0`, but its pullback is proper and has
positive affine degree. -/
example : ¬affineDegree ((Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)}).comap
      (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 1 0))) ≤
    (cappedDegreeMixedVolume 1 0 1 0 : ℕ) := by
  rw [not_le]
  exact lt_of_eq_of_lt (by simp [cappedDegreeMixedVolume])
    (affineDegree_pos (Ideal.comap_ne_top _ span_X_zero_ne_top))

end AffineHilbertCappedDegreeTest
