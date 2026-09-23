/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree

/-!
# Affine Hilbert functions of capped bidegree hypersurfaces

Let `k` be a field, `σ` a finite type and `i : σ`. The monomial map of the capped exponents
`cappedBidegreeExponents σ i a b c` sends total degree `N` to the bounds `(a * N, b * N, c * N)`.
For a nonzero `g` with bounds `(h, j, r)`, multiplication by `g` embeds the polynomials with bounds
`(a * N - h, b * N - j, c * N - r)` into the kernel of the projection of the polynomials with
bounds `(a * N, b * N, c * N)` onto the quotient by `g`, which bounds the affine Hilbert function of
the pulled-back hypersurface `(span {g}).comap (monomialMap k (cappedBidegreeExponents σ i a b c))`
by a difference of monomial counts.

For `σ = Fin 2`, `i = 1`, positive bounds and `c < b`, there are `(C + 1) * (2 * B + 2 - C) / 2`
capped exponents in `cappedDegreeExponents (Fin 2) 1 B C` for `C ≤ B`. The difference of counts is
then eventually a quadratic polynomial in `N` with leading coefficient
`cappedBidegreeMixedVolume h j r a b c / 2`, where
`cappedBidegreeMixedVolume h j r a b c = h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c))`,
while the pulled-back hypersurface has affine Hilbert polynomial of natural degree `2`. This bounds
its affine degree by `cappedBidegreeMixedVolume h j r a b c`, and the same bound holds for the
total affine degree of its minimal primes. For `c = b` the cap is no condition and the bound is
that of the bidegree hypersurface, and for `b < c` the bound for the cap `b` is at most
`cappedBidegreeMixedVolume h j r a b c`.

## Main statements

* `MvPolynomial.affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le`: the
  count bound on the affine Hilbert function of a pulled-back hypersurface.
* `MvPolynomial.affineDegree_comap_cappedBidegree_span_singleton_le`: the affine-degree bound for
  `σ = Fin 2`.
* `MvPolynomial.sum_affineDegree_minimalPrimes_comap_cappedBidegree_span_singleton_le`: the same
  bound on the total affine degree of the minimal primes.
-/

@[expose] public section

noncomputable section

open Filter Polynomial

namespace MvPolynomial

variable {k σ : Type*} [Field k]

/-- Let `g ≠ 0` have bounds `(h, j, r)` in the capped bidegree filtration for `i : σ`, with
`h ≤ a * N`, `j ≤ b * N` and `r ≤ c * N`. The affine Hilbert function at `N` of the pullback of
`span {g}` along the monomial map of `cappedBidegreeExponents σ i a b c` plus
`(a * N - h + 1)` times the number of capped exponents in
`cappedDegreeExponents σ i (b * N - j) (c * N - r)` is at most `(a * N + 1)` times the number in
`cappedDegreeExponents σ i (b * N) (c * N)`. -/
theorem affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le [Finite σ] {i : σ}
    {a b c h j r N : ℕ} {g : MvPolynomial (Option σ) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree σ k i h j r) (hh : h ≤ a * N) (hj : j ≤ b * N)
    (hr : r ≤ c * N) :
    affineHilbertFunction
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents σ i a b c))) N +
        (a * N - h + 1) * (cappedDegreeExponents σ i (b * N - j) (c * N - r)).ncard ≤
      (a * N + 1) * (cappedDegreeExponents σ i (b * N) (c * N)).ncard := by
  have hH := affineHilbertFunction_comap_span_singleton_add_finrank_le
    (monomialMap k (cappedBidegreeExponents σ i a b c)) hg0
    (M := restrictCappedBidegree σ k i (a * N) (b * N) (c * N))
    (M' := restrictCappedBidegree σ k i (a * N - h) (b * N - j) (c * N - r))
    (fun _ hP ↦ monomialMap_mem_restrictCappedBidegree hP) fun p hp ↦ by
      have hgp := mul_mem_restrictCappedBidegree hg hp
      rwa [Nat.add_sub_cancel' hh, Nat.add_sub_cancel' hj, Nat.add_sub_cancel' hr] at hgp
  rwa [finrank_restrictCappedBidegree, finrank_restrictCappedBidegree] at hH

/-- For `C ≤ B`, twice the number of capped exponents on `Fin 2` with bounds `(B, C)`, cast to
`ℚ`. -/
private theorem two_mul_ncard_cast (B C : ℕ) (hCB : C ≤ B) :
    (2 : ℚ) * (cappedDegreeExponents (Fin 2) 1 B C).ncard = (C + 1) * (2 * B + 2 - C) := by
  have h := congrArg (Nat.cast : ℕ → ℚ) (two_mul_ncard_cappedDegreeExponents_fin_two B C hCB)
  push_cast [Nat.cast_sub (show C ≤ 2 * B + 2 by omega)] at h
  exact h

/-- The affine-degree bound for `c ≤ b`, in the form
`h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c))`. -/
private theorem affineDegree_comap_cappedBidegree_span_singleton_le_of_le {a b c h j r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b) {g : MvPolynomial (Option (Fin 2)) k}
    (hg0 : g ≠ 0) (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))) ≤
      (h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c)) : ℕ) := by
  rcases hcb.lt_or_eq with hcb | rfl
  swap
  · -- For `c = b` the capped exponents are the exponents of bidegree at most `(a, c)`.
    have key : ∀ (S : Set (Option (Fin 2) →₀ ℕ)) [Finite S], S = bidegreeExponents (Fin 2) a c →
        affineDegree ((Ideal.span {g}).comap (monomialMap k S)) ≤
          (h * c * (2 * c - c) + 2 * a * (j * c + r * (c - c)) : ℕ) := by
      rintro S _ rfl
      rw [← bidegreeMap_eq_monomialMap]
      refine (affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0
        (restrictCappedBidegree_le_restrictBidegree hg)).trans_eq ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.sub_self, mul_zero, add_zero,
        show 2 * c - c = c by omega]
      push_cast
      ring
    exact key _ (cappedBidegreeExponents_eq_bidegreeExponents le_rfl)
  by_cases hproper : Ideal.span {g} = ⊤
  · rw [hproper, Ideal.comap_top, affineDegree_top]
    exact Nat.cast_nonneg _
  have hdim : (affineHilbertPolynomial
      ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c)))).natDegree
      = 2 := by
    have h := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
      (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))
      (monomialMap_cappedBidegreeExponents_surjective ha hb hc) hg0 hproper
    rw [Finite.card_option, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  set a' : ℚ := (a : ℚ)
  set b' : ℚ := (b : ℚ)
  set c' : ℚ := (c : ℚ)
  set h' : ℚ := (h : ℚ)
  set j' : ℚ := (j : ℚ)
  set r' : ℚ := (r : ℚ)
  -- The quadratic `R` is half the difference of the two products of counts, expanded in `N`.
  let q₂ : ℚ := (h' * c' * (2 * b' - c') + 2 * a' * (j' * c' + r' * (b' - c'))) / 2
  let q₁ : ℚ := (2 * a' + 2 * c' + (2 * b' - c') - (a' * (1 - r') * (2 - 2 * j' + r') +
    (1 - h') * c' * (2 - 2 * j' + r') + (1 - h') * (1 - r') * (2 * b' - c'))) / 2
  let q₀ : ℚ := (2 - (1 - h') * (1 - r') * (2 - 2 * j' + r')) / 2
  let R : ℚ[X] := Polynomial.C q₂ * Polynomial.X ^ 2 + Polynomial.C q₁ * Polynomial.X +
    Polynomial.C q₀
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le hdim
    (R := R) natDegree_quadratic_le ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop (h + j + r)] with N hN
    have hhN : h ≤ a * N := (show h ≤ N by omega).trans (Nat.le_mul_of_pos_left N ha)
    have hjN : j ≤ b * N := (show j ≤ N by omega).trans (Nat.le_mul_of_pos_left N hb)
    have hrN : r ≤ c * N := (show r ≤ N by omega).trans (Nat.le_mul_of_pos_left N hc)
    have hgap : c * N + N ≤ b * N := by
      have := Nat.mul_le_mul_right N hcb
      rwa [Nat.succ_mul] at this
    have hshift : c * N - r ≤ b * N - j := by omega
    have hbound := affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le hg0 hg
      hhN hjN hrN (a := a) (b := b) (c := c)
    have hT := two_mul_ncard_cast (b * N) (c * N) (by omega)
    have hT' := two_mul_ncard_cast (b * N - j) (c * N - r) hshift
    have hboundq : ((_ : ℕ) : ℚ) ≤ ((_ : ℕ) : ℚ) := Nat.cast_le.mpr hbound
    push_cast [Nat.cast_sub hhN, Nat.cast_sub hjN, Nat.cast_sub hrN] at hboundq hT hT'
    have hR : 2 * R.eval (N : ℚ) = (a' * N + 1) * ((c' * N + 1) * (2 * (b' * N) + 2 - c' * N)) -
        (a' * N - h' + 1) *
          ((c' * N - r' + 1) * (2 * (b' * N - j') + 2 - (c' * N - r'))) := by
      simp only [R, q₂, q₁, q₀, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring
    rw [← hT, ← hT'] at hR
    linarith
  · simp only [R, coeff_add, Polynomial.coeff_C]
    push_cast [Nat.cast_sub (show c ≤ 2 * b by omega), Nat.cast_sub hcb.le]
    norm_num [Nat.factorial, q₂]
    ring

/-- Let `g ≠ 0` have bounds `(h, j, r)` in the capped bidegree filtration on
`MvPolynomial (Option (Fin 2)) k` with cap on `some 1`. For positive `a`, `b` and `c`, the pullback
of the hypersurface `span {g}` along the monomial map of `cappedBidegreeExponents (Fin 2) 1 a b c`
has affine degree at most `cappedBidegreeMixedVolume h j r a b c`, which is
`h * c * (2 * b - c) + 2 * a * (j * c + r * (b - c))` for `c ≤ b`.

For `c < b` and `span {g}` proper, the affine Hilbert polynomial of the pullback has natural degree
`2`, and for large `N` its affine Hilbert function is bounded by a quadratic polynomial in `N` with
leading coefficient `cappedBidegreeMixedVolume h j r a b c / 2`. For `c = b` this is the bound for
the bidegree hypersurface, and for `b < c` the cap is no condition and the bound
`h * b ^ 2 + 2 * a * j * b` is at most `h * b * c + 2 * a * j * c`. -/
theorem affineDegree_comap_cappedBidegree_span_singleton_le {a b c h j r : ℕ} (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) {g : MvPolynomial (Option (Fin 2)) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    affineDegree
        ((Ideal.span {g}).comap (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))) ≤
      (cappedBidegreeMixedVolume h j r a b c : ℕ) := by
  rcases le_or_gt c b with hcb | hbc
  · rw [cappedBidegreeMixedVolume_eq hcb]
    exact affineDegree_comap_cappedBidegree_span_singleton_le_of_le ha hb hc hcb hg0 hg
  -- For `b < c` the capped exponents are those with bounds `(a, b, b)`.
  have key : ∀ (S : Set (Option (Fin 2) →₀ ℕ)) [Finite S],
      S = cappedBidegreeExponents (Fin 2) 1 a b b →
      affineDegree ((Ideal.span {g}).comap (monomialMap k S)) ≤
        (cappedBidegreeMixedVolume h j r a b c : ℕ) := by
    rintro S _ rfl
    refine (affineDegree_comap_cappedBidegree_span_singleton_le_of_le ha hb hb le_rfl hg0
      hg).trans ?_
    rw [Nat.cast_le, cappedBidegreeMixedVolume, cappedDegreeMixedVolume,
      cappedDegreeMixedVolume, Nat.sub_self, Nat.sub_eq_zero_of_le hbc.le, show 2 * b - b = b by
      omega]
    simp only [mul_zero, add_zero]
    have h1 := Nat.mul_le_mul_left (h * b) hbc.le
    have h2 := Nat.mul_le_mul_left (2 * a * j) hbc.le
    nlinarith
  refine key _ ?_
  rw [cappedBidegreeExponents_eq_bidegreeExponents hbc.le,
    cappedBidegreeExponents_eq_bidegreeExponents le_rfl]

/-- Let `g ≠ 0` have bounds `(h, j, r)` in the capped bidegree filtration on
`MvPolynomial (Option (Fin 2)) k` with cap on `some 1`. For positive `a`, `b` and `c`,
the affine degrees of the minimal primes of the pullback of `span {g}` along the monomial map of
`cappedBidegreeExponents (Fin 2) 1 a b c` sum to at most `cappedBidegreeMixedVolume h j r a b c`.
-/
theorem sum_affineDegree_minimalPrimes_comap_cappedBidegree_span_singleton_le {a b c h j r : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {g : MvPolynomial (Option (Fin 2)) k}
    (hg0 : g ≠ 0) (hg : g ∈ restrictCappedBidegree (Fin 2) k 1 h j r) :
    ∑ Q ∈ ((Ideal.span {g}).comap
        (monomialMap k (cappedBidegreeExponents (Fin 2) 1 a b c))).minimalPrimesFinset,
        affineDegree Q ≤
      (cappedBidegreeMixedVolume h j r a b c : ℕ) :=
  (sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective _
    (monomialMap_cappedBidegreeExponents_surjective ha hb hc) g).trans
    (affineDegree_comap_cappedBidegree_span_singleton_le ha hb hc hg0 hg)

end MvPolynomial
