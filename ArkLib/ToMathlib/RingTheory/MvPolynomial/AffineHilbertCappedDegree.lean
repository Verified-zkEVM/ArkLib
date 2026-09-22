/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedDegree

/-!
# Affine Hilbert functions of capped degree hypersurfaces

Let `k` be a field, `σ` a finite type and `i : σ`. The monomial map of the capped exponents
`cappedDegreeExponents σ i b c` sends total degree `N` to the bounds `(b * N, c * N)`. For a
nonzero `g` with bounds `(j, r)`, multiplication by `g` embeds the polynomials with bounds
`(b * N - j, c * N - r)` into the kernel of the projection of the polynomials with bounds
`(b * N, c * N)` onto the quotient by `g`, which bounds the affine Hilbert function of the
pulled-back hypersurface `(span {g}).comap (monomialMap k (cappedDegreeExponents σ i b c))` by a
difference of numbers of capped exponents.

For `σ = Fin 2`, `i = 1` and `C ≤ B`, there are `(C + 1) * (2 * B + 2 - C) / 2` capped exponents
with bounds `(B, C)`. For positive `b` and `c` with `c < b`, the difference of counts is then
eventually a linear polynomial in `N` with leading coefficient
`cappedDegreeMixedVolume j r b c = j * c + r * (b - c)`, while the pulled-back curve has affine
Hilbert polynomial of natural degree `1`. This bounds its affine degree by
`cappedDegreeMixedVolume j r b c`, and the same bound holds for the total affine degree of its
minimal primes. For `b ≤ c` the cap is no condition and the bound is `j * b ≤ j * c`.

## Main statements

* `MvPolynomial.affineHilbertFunction_comap_cappedDegree_span_singleton_add_le`: the count bound
  on the affine Hilbert function of a pulled-back hypersurface.
* `MvPolynomial.affineDegree_comap_cappedDegree_span_singleton_le`: the affine-degree bound for
  `σ = Fin 2`.
* `MvPolynomial.sum_affineDegree_minimalPrimes_comap_cappedDegree_span_singleton_le`: the same
  bound on the total affine degree of the minimal primes.
-/

@[expose] public section

noncomputable section

open Filter Polynomial

namespace MvPolynomial

variable {k σ : Type*} [Field k]

/-- Let `g ≠ 0` have bounds `(j, r)` in the capped degree filtration for `i : σ`, with
`j ≤ b * N` and `r ≤ c * N`. The affine Hilbert function at `N` of the pullback of `span {g}`
along the monomial map of `cappedDegreeExponents σ i b c` plus the number of capped exponents with
bounds `(b * N - j, c * N - r)` is at most the number of capped exponents with bounds
`(b * N, c * N)`. -/
theorem affineHilbertFunction_comap_cappedDegree_span_singleton_add_le [Finite σ] {i : σ}
    {b c j r N : ℕ} {g : MvPolynomial σ k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedDegree σ k i j r) (hj : j ≤ b * N) (hr : r ≤ c * N) :
    affineHilbertFunction
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents σ i b c))) N +
        (cappedDegreeExponents σ i (b * N - j) (c * N - r)).ncard ≤
      (cappedDegreeExponents σ i (b * N) (c * N)).ncard := by
  have hH := affineHilbertFunction_comap_span_singleton_add_finrank_le
    (monomialMap k (cappedDegreeExponents σ i b c)) hg0
    (M := restrictCappedDegree σ k i (b * N) (c * N))
    (M' := restrictCappedDegree σ k i (b * N - j) (c * N - r))
    (fun _ hP ↦ monomialMap_mem_restrictCappedDegree hP) fun p hp ↦ by
      have hgp := mul_mem_restrictCappedDegree hg hp
      rwa [Nat.add_sub_cancel' hj, Nat.add_sub_cancel' hr] at hgp
  rwa [finrank_restrictCappedDegree, finrank_restrictCappedDegree] at hH

/-- For `C ≤ B`, twice the number of capped exponents on `Fin 2` with bounds `(B, C)`, cast to
`ℚ`. -/
private theorem two_mul_ncard_cast (B C : ℕ) (hCB : C ≤ B) :
    (2 : ℚ) * (cappedDegreeExponents (Fin 2) 1 B C).ncard = (C + 1) * (2 * B + 2 - C) := by
  have h := congrArg (Nat.cast : ℕ → ℚ)
    (two_mul_ncard_cappedDegreeExponents_fin_two B C hCB)
  push_cast [Nat.cast_sub (show C ≤ 2 * B + 2 by omega)] at h
  exact h

/-- The affine-degree bound for `c ≤ b`, under the extra condition `c < b ∨ r = j` that makes
`c * N - r ≤ b * N - j` for large `N`. -/
private theorem affineDegree_comap_cappedDegree_span_singleton_le_of_le {b c j r : ℕ}
    (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b) (hcase : c < b ∨ r = j)
    {g : MvPolynomial (Fin 2) k} (hg0 : g ≠ 0) (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))) ≤
      (j * c + r * (b - c) : ℕ) := by
  by_cases hproper : Ideal.span {g} = ⊤
  · rw [hproper, Ideal.comap_top, affineDegree_top]
    exact Nat.cast_nonneg _
  have hdim : (affineHilbertPolynomial
      ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c)))).natDegree
      = 1 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))
      (monomialMap_cappedDegreeExponents_surjective hb hc) hg0 hproper
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  set b' : ℚ := (b : ℚ)
  set c' : ℚ := (c : ℚ)
  set j' : ℚ := (j : ℚ)
  set r' : ℚ := (r : ℚ)
  -- The linear `R` is half the difference of the two counts, expanded in `N`.
  let R : ℚ[X] := Polynomial.C (j' * c' + r' * (b' - c')) * Polynomial.X +
    Polynomial.C (j' + r' / 2 + r' ^ 2 / 2 - j' * r')
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim
    (R := R) natDegree_linear_le ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop (j + r)] with N hN
    have hjN : j ≤ b * N := (show j ≤ N by omega).trans (Nat.le_mul_of_pos_left N hb)
    have hrN : r ≤ c * N := (show r ≤ N by omega).trans (Nat.le_mul_of_pos_left N hc)
    have hshift : c * N - r ≤ b * N - j := by
      rcases hcase with hlt | rfl
      · have hgap : c * N + N ≤ b * N := by
          have := Nat.mul_le_mul_right N hlt
          rwa [Nat.succ_mul] at this
        omega
      · exact Nat.sub_le_sub_right (Nat.mul_le_mul_right N hcb) r
    have hbound := affineHilbertFunction_comap_cappedDegree_span_singleton_add_le (b := b)
      (c := c) hg0 hg hjN hrN
    have hT := two_mul_ncard_cast (b * N) (c * N) (Nat.mul_le_mul_right N hcb)
    have hT' := two_mul_ncard_cast (b * N - j) (c * N - r) hshift
    have hboundq : ((_ : ℕ) : ℚ) ≤ ((_ : ℕ) : ℚ) := Nat.cast_le.mpr hbound
    push_cast [Nat.cast_sub hjN, Nat.cast_sub hrN] at hboundq hT hT'
    have hR : 2 * R.eval (N : ℚ) = (c' * N + 1) * (2 * (b' * N) + 2 - c' * N) -
        (c' * N - r' + 1) * (2 * (b' * N - j') + 2 - (c' * N - r')) := by
      simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      ring
    rw [← hT, ← hT'] at hR
    linarith
  · simp only [R, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_of_ne_zero Nat.one_ne_zero, ↓reduceIte, add_zero, Nat.factorial_one,
      Nat.cast_one, one_mul]
    push_cast [Nat.cast_sub hcb]
    rfl

/-- Let `g ≠ 0` have bounds `(j, r)` in the capped degree filtration on `MvPolynomial (Fin 2) k`
with cap on `1`. For positive `b` and `c`, the pullback of the curve `span {g}` along the monomial
map of `cappedDegreeExponents (Fin 2) 1 b c` has affine degree at most
`cappedDegreeMixedVolume j r b c = j * c + r * (b - c)`.

For `c < b` and `span {g}` proper, the affine Hilbert polynomial of the pullback has natural degree
`1`, and for large `N` its affine Hilbert function is bounded by a linear polynomial in `N` with
leading coefficient `j * c + r * (b - c)`. For `c = b` the bound `j * b` follows from the bounds
`(j, j)` of `g`, and for `b < c` the cap is no condition and the bound `j * b` is at most
`j * c`. -/
theorem affineDegree_comap_cappedDegree_span_singleton_le {b c j r : ℕ} (hb : 0 < b)
    (hc : 0 < c) {g : MvPolynomial (Fin 2) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))) ≤
      (cappedDegreeMixedVolume j r b c : ℕ) := by
  rw [cappedDegreeMixedVolume]
  -- With `c = b`, the bounds `(j, j)` of `g` give the bound `j * b`.
  have hdiag : affineDegree
      ((Ideal.span {g}).comap (monomialMap k (cappedDegreeExponents (Fin 2) 1 b b))) ≤
        (j * b : ℕ) := by
    have hgj : g ∈ restrictCappedDegree (Fin 2) k 1 j j := fun e he ↦
      ⟨(hg he).1, (Finsupp.le_degree 1 e).trans (hg he).1⟩
    simpa using affineDegree_comap_cappedDegree_span_singleton_le_of_le hb hb le_rfl
      (Or.inr rfl) hg0 hgj
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · exact affineDegree_comap_cappedDegree_span_singleton_le_of_le hb hc hcb.le (Or.inl hcb)
      hg0 hg
  · simpa using hdiag
  · -- For `b < c` the capped exponents are those with bounds `(b, b)`.
    have key : ∀ (S : Set (Fin 2 →₀ ℕ)) [Finite S], S = cappedDegreeExponents (Fin 2) 1 b b →
        affineDegree ((Ideal.span {g}).comap (monomialMap k S)) ≤ (j * c + r * (b - c) : ℕ) := by
      rintro S _ rfl
      refine hdiag.trans ?_
      rw [Nat.sub_eq_zero_of_le hbc.le, mul_zero, add_zero, Nat.cast_le]
      exact Nat.mul_le_mul_left j hbc.le
    refine key _ ?_
    rw [cappedDegreeExponents_eq_setOf_degree_le hbc.le,
      cappedDegreeExponents_eq_setOf_degree_le le_rfl]

/-- Let `g ≠ 0` have bounds `(j, r)` in the capped degree filtration on `MvPolynomial (Fin 2) k`
with cap on `1`. For positive `b` and `c`, the affine degrees of the minimal primes of the
pullback of `span {g}` along the monomial map of `cappedDegreeExponents (Fin 2) 1 b c` sum to at
most `cappedDegreeMixedVolume j r b c = j * c + r * (b - c)`. -/
theorem sum_affineDegree_minimalPrimes_comap_cappedDegree_span_singleton_le {b c j r : ℕ}
    (hb : 0 < b) (hc : 0 < c) {g : MvPolynomial (Fin 2) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedDegree (Fin 2) k 1 j r) :
    ∑ Q ∈ ((Ideal.span {g}).comap
        (monomialMap k (cappedDegreeExponents (Fin 2) 1 b c))).minimalPrimesFinset,
        affineDegree Q ≤
      (cappedDegreeMixedVolume j r b c : ℕ) :=
  (sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective _
    (monomialMap_cappedDegreeExponents_surjective hb hc) g).trans
    (affineDegree_comap_cappedDegree_span_singleton_le hb hc hg0 hg)

end MvPolynomial
