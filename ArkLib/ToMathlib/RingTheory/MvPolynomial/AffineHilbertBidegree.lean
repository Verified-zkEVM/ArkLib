/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.RectangleDifference
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree

/-!
# Affine Hilbert functions of bidegree hypersurfaces

Let `k` be a field and `σ` a finite type with `n = Nat.card σ`. The monomial map
`bidegreeMap σ k a b` from the polynomial ring on the exponents of bidegree at most `(a, b)` to
`MvPolynomial (Option σ) k` pulls an ideal `I` back to `I.comap (bidegreeMap σ k a b)`. It sends
total degree `N` to bidegree `(a * N, b * N)`, so the affine Hilbert function of the pullback at `N`
is at most the dimension of the image `quotientBidegreeLE I (a * N) (b * N)` of the polynomials of
bidegree at most `(a * N, b * N)` in the quotient by `I`. For positive `a` and `b` the map is
surjective, and the pullback has affine Hilbert polynomial of the same natural degree as `I`.

For a nonzero `g` of bidegree at most `(h, v)`, multiplication by `g` embeds the polynomials of
bidegree at most `(A - h, B - v)` into the kernel of the projection of the polynomials of bidegree
at most `(A, B)` onto the quotient by `g`. Counting monomials bounds the affine Hilbert function of
the pulled-back hypersurface at `N` by the rectangle difference

```text
(a N + 1) * (b N + n).choose n - (a N - h + 1) * (b N - v + n).choose n,
```

the value of `Polynomial.rectangleDifference n a b h v` at `N`. That polynomial has natural degree
at most `n` and leading coefficient `(h * b ^ n + n * v * a * b ^ (n - 1)) / n!`, which bounds the
affine degree of the pulled-back hypersurface by `h * b ^ n + n * v * a * b ^ (n - 1)`. The
pullback is the principal cut of the prime `RingHom.ker (bidegreeMap σ k a b)` by a preimage of
`g`, so all its minimal primes have the same dimension and their affine degrees sum to at most the
affine degree of the pullback.

## Main statements

* `MvPolynomial.quotientBidegreeLE`: the image of the polynomials of bounded bidegree in a
  quotient.
* `MvPolynomial.finrank_quotientBidegreeLE_span_singleton_le`: the rectangle-difference bound in
  the quotient by one polynomial.
* `MvPolynomial.affineHilbertFunction_comap_bidegreeMap_le`: the comparison of filtrations.
* `MvPolynomial.natDegree_affineHilbertPolynomial_comap_bidegreeMap`: pulling back preserves the
  natural degree; `MvPolynomial.natDegree_affineHilbertPolynomial_ker_bidegreeMap` and
  `MvPolynomial.natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton` are the cases of
  `⊥` and of a hypersurface.
* `MvPolynomial.comap_bidegreeMap_span_singleton`: the pullback of a hypersurface is a principal
  cut of `RingHom.ker (bidegreeMap σ k a b)`.
* `MvPolynomial.affineDegree_comap_bidegreeMap_span_singleton_le`: the bound
  `h * b ^ n + n * v * a * b ^ (n - 1)` on the affine degree of a pulled-back hypersurface.
* `MvPolynomial.sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le`: the minimal
  primes of a pulled-back hypersurface have total affine degree at most its affine degree.
-/

@[expose] public section

noncomputable section

open Filter

namespace MvPolynomial

variable {k σ : Type*} [Field k]

/-- The image in `MvPolynomial (Option σ) k ⧸ I` of the polynomials of bidegree at most
`(a, b)`. -/
def quotientBidegreeLE (I : Ideal (MvPolynomial (Option σ) k)) (a b : ℕ) :
    Submodule k (MvPolynomial (Option σ) k ⧸ I) :=
  (restrictBidegree σ k a b).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- A class lies in `quotientBidegreeLE I a b` exactly when it has a representative of bidegree
at most `(a, b)`. -/
theorem mem_quotientBidegreeLE {I : Ideal (MvPolynomial (Option σ) k)} {a b : ℕ}
    {x : MvPolynomial (Option σ) k ⧸ I} :
    x ∈ quotientBidegreeLE I a b ↔
      ∃ p ∈ restrictBidegree σ k a b, Ideal.Quotient.mk I p = x :=
  Iff.rfl

/-- With finitely many variables, `quotientBidegreeLE I a b` is finite-dimensional. -/
instance quotientBidegreeLE.moduleFinite [Finite σ] (I : Ideal (MvPolynomial (Option σ) k))
    (a b : ℕ) : Module.Finite k (quotientBidegreeLE I a b) := by
  unfold quotientBidegreeLE
  infer_instance

/-- Let `g ≠ 0` have bidegree at most `(h, v)`, with `h ≤ A` and `v ≤ B`. In the quotient by `g`,
the image of the polynomials of bidegree at most `(A, B)` has dimension at most the number of
exponents of bidegree at most `(A, B)` minus the number of bidegree at most `(A - h, B - v)`:
multiplication by `g` embeds the latter polynomials into the kernel of the projection. -/
theorem finrank_quotientBidegreeLE_span_singleton_add_le [Finite σ]
    {g : MvPolynomial (Option σ) k} {h v A B : ℕ} (hg0 : g ≠ 0)
    (hg : g ∈ restrictBidegree σ k h v) (hhA : h ≤ A) (hvB : v ≤ B) :
    Module.finrank k (quotientBidegreeLE (Ideal.span {g}) A B) +
        Module.finrank k (restrictBidegree σ k (A - h) (B - v)) ≤
      Module.finrank k (restrictBidegree σ k A B) := by
  let π := (Ideal.Quotient.mkₐ k (Ideal.span {g})).toLinearMap.domRestrict
    (restrictBidegree σ k A B)
  let μ : restrictBidegree σ k (A - h) (B - v) →ₗ[k] restrictBidegree σ k A B :=
    ((LinearMap.mulLeft k g).domRestrict _).codRestrict _ fun p ↦ by
      have hp := mul_mem_restrictBidegree hg p.2
      rw [Nat.add_sub_cancel' hhA, Nat.add_sub_cancel' hvB] at hp
      exact hp
  have hμ : Function.Injective μ := fun p q hpq ↦
    Subtype.ext (mul_left_cancel₀ hg0 (congrArg Subtype.val hpq))
  have hμπ : LinearMap.range μ ≤ LinearMap.ker π := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hrank := π.finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hrank
  have hT := (LinearMap.finrank_range_of_inj hμ).symm.trans_le (Submodule.finrank_mono hμπ)
  rw [quotientBidegreeLE, ← hrank]
  omega

/-- Let `g ≠ 0` have bidegree at most `(h, v)`, with `h ≤ A` and `v ≤ B`, and let
`n = Nat.card σ`. In the quotient by `g`, the image of the polynomials of bidegree at most
`(A, B)` has dimension at most
`(A + 1) * (B + n).choose n - (A - h + 1) * (B - v + n).choose n`. -/
theorem finrank_quotientBidegreeLE_span_singleton_le [Finite σ]
    {g : MvPolynomial (Option σ) k} {h v A B : ℕ} (hg0 : g ≠ 0)
    (hg : g ∈ restrictBidegree σ k h v) (hhA : h ≤ A) (hvB : v ≤ B) :
    Module.finrank k (quotientBidegreeLE (Ideal.span {g}) A B) ≤
      (A + 1) * (B + Nat.card σ).choose (Nat.card σ) -
        (A - h + 1) * (B - v + Nat.card σ).choose (Nat.card σ) := by
  have hle := finrank_quotientBidegreeLE_span_singleton_add_le hg0 hg hhA hvB
  rw [finrank_restrictBidegree, finrank_restrictBidegree] at hle
  omega

/-- The affine Hilbert function at `N` of the pullback of `I` along `bidegreeMap σ k a b` is at
most the dimension of `quotientBidegreeLE I (a * N) (b * N)`: the induced map of quotients is
injective and sends total degree `N` to bidegree `(a * N, b * N)`. -/
theorem affineHilbertFunction_comap_bidegreeMap_le [Finite σ]
    (I : Ideal (MvPolynomial (Option σ) k)) (a b N : ℕ) :
    affineHilbertFunction (I.comap (bidegreeMap σ k a b)) N ≤
      Module.finrank k (quotientBidegreeLE I (a * N) (b * N)) := by
  let g := Ideal.quotientMapₐ I (bidegreeMap σ k a b) le_rfl
  let L : quotientDegreeLE (I.comap (bidegreeMap σ k a b)) N →ₗ[k]
      quotientBidegreeLE I (a * N) (b * N) :=
    (g.toLinearMap.domRestrict _).codRestrict _ fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.2
      rw [LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply, ← hpx]
      exact ⟨_, bidegreeMap_mem_restrictBidegree hp, rfl⟩
  exact LinearMap.finrank_le_finrank_of_injective (f := L) fun x y hxy ↦
    Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val hxy))

/-- For positive `a` and `b`, pulling an ideal back along `bidegreeMap σ k a b` preserves the
natural degree of the affine Hilbert polynomial. -/
theorem natDegree_affineHilbertPolynomial_comap_bidegreeMap [Finite σ] {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) (I : Ideal (MvPolynomial (Option σ) k)) :
    (affineHilbertPolynomial (I.comap (bidegreeMap σ k a b))).natDegree =
      (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_comap_of_surjective _ (bidegreeMap_surjective ha hb) I

/-- For positive `a` and `b`, the kernel of `bidegreeMap σ k a b` has affine Hilbert polynomial of
natural degree `Nat.card (Option σ)`. -/
theorem natDegree_affineHilbertPolynomial_ker_bidegreeMap [Finite σ] {a b : ℕ} (ha : 0 < a)
    (hb : 0 < b) :
    (affineHilbertPolynomial (RingHom.ker (bidegreeMap σ k a b))).natDegree =
      Nat.card (Option σ) := by
  rw [RingHom.ker_eq_comap_bot, natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb,
    natDegree_affineHilbertPolynomial_bot]

/-- For positive `a` and `b`, if `bidegreeMap σ k a b` sends `f` to `g`, the pullback of the
hypersurface `span {g}` is the principal cut `RingHom.ker (bidegreeMap σ k a b) ⊔ span {f}`. -/
theorem comap_bidegreeMap_span_singleton {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {f : MvPolynomial (bidegreeExponents σ a b) k} :
    (Ideal.span {bidegreeMap σ k a b f}).comap (bidegreeMap σ k a b) =
      RingHom.ker (bidegreeMap σ k a b) ⊔ Ideal.span {f} := by
  rw [← Set.image_singleton, ← Ideal.map_span (bidegreeMap σ k a b),
    Ideal.comap_map_of_surjective (bidegreeMap σ k a b) (bidegreeMap_surjective ha hb),
    RingHom.ker_eq_comap_bot, sup_comm]

/-- For positive `a` and `b`, the pullback along `bidegreeMap σ k a b` of a proper hypersurface
`span {g}`, `g ≠ 0`, has affine Hilbert polynomial of natural degree `Nat.card σ`. -/
theorem natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton [Finite σ] {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) {g : MvPolynomial (Option σ) k} (hg0 : g ≠ 0)
    (hproper : Ideal.span {g} ≠ ⊤) :
    (affineHilbertPolynomial ((Ideal.span {g}).comap (bidegreeMap σ k a b))).natDegree =
      Nat.card σ := by
  have hs := natDegree_affineHilbertPolynomial_span_singleton_add_one hg0 hproper
  rw [Finite.card_option] at hs
  rw [natDegree_affineHilbertPolynomial_comap_bidegreeMap ha hb]
  omega

/-- Let `g ≠ 0` have bidegree at most `(h, v)` and let `n = Nat.card σ`. For positive `a` and `b`,
the pullback of the hypersurface `span {g}` along `bidegreeMap σ k a b` has affine degree at most
`h * b ^ n + n * v * a * b ^ (n - 1)`.

If `span {g}` is proper, the affine Hilbert polynomial of the pullback has natural degree `n`,
and its affine Hilbert function is bounded by the rectangle difference
`Polynomial.rectangleDifference n a b h v`, whose coefficient in degree `n` is
`(h * b ^ n + n * v * a * b ^ (n - 1)) / n!`. -/
theorem affineDegree_comap_bidegreeMap_span_singleton_le [Finite σ] {a b h v : ℕ} (ha : 0 < a)
    (hb : 0 < b) {g : MvPolynomial (Option σ) k} (hg0 : g ≠ 0)
    (hg : g ∈ restrictBidegree σ k h v) :
    affineDegree ((Ideal.span {g}).comap (bidegreeMap σ k a b)) ≤
      (h * b ^ Nat.card σ + Nat.card σ * v * a * b ^ (Nat.card σ - 1) : ℕ) := by
  set n := Nat.card σ
  by_cases hproper : Ideal.span {g} = ⊤
  · rw [hproper, Ideal.comap_top, affineDegree_top]
    exact Nat.cast_nonneg _
  refine (affineDegree_le_of_eventually_affineHilbertFunction_le
    (natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton ha hb hg0 hproper)
    (Polynomial.natDegree_rectangleDifference_le n (a : ℚ) b h v) ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop (max h v)] with N hN
    have hh : h ≤ a * N := (le_max_left h v).trans hN |>.trans (Nat.le_mul_of_pos_left N ha)
    have hv : v ≤ b * N := (le_max_right h v).trans hN |>.trans (Nat.le_mul_of_pos_left N hb)
    rw [Polynomial.eval_rectangleDifference_natCast n a b h v N hh hv, Nat.cast_le]
    exact (affineHilbertFunction_comap_bidegreeMap_le _ a b N).trans
      (finrank_quotientBidegreeLE_span_singleton_le hg0 hg hh hv)
  · rw [Polynomial.coeff_rectangleDifference_self, mul_div_cancel₀ _ (by positivity)]
    push_cast
    ring

/-- For positive `a` and `b`, the affine degrees of the minimal primes of the pullback of a
hypersurface `span {g}` along `bidegreeMap σ k a b` sum to at most its affine degree.

For `g ≠ 0` with `span {g}` proper, the pullback is the principal cut of the prime
`RingHom.ker (bidegreeMap σ k a b)` by a preimage of `g`, so its minimal primes all have the
dimension of the pullback, and `sum_affineDegree_minimalPrimes_le` applies. For `g = 0` the pullback
is prime, and for `span {g} = ⊤` it has no minimal primes. -/
theorem sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le [Finite σ] {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (g : MvPolynomial (Option σ) k) :
    ∑ Q ∈ ((Ideal.span {g}).comap (bidegreeMap σ k a b)).minimalPrimesFinset, affineDegree Q ≤
      affineDegree ((Ideal.span {g}).comap (bidegreeMap σ k a b)) := by
  obtain ⟨f, rfl⟩ := bidegreeMap_surjective (R := k) ha hb g
  refine sum_affineDegree_minimalPrimes_le fun Q hQ ↦ ?_
  have hQ' := Ideal.mem_minimalPrimesFinset.mp hQ
  by_cases hf : bidegreeMap σ k a b f = 0
  · have : ((Ideal.span {bidegreeMap σ k a b f}).comap (bidegreeMap σ k a b)).IsPrime := by
      rw [hf, Ideal.span_singleton_eq_bot.mpr rfl, ← RingHom.ker_eq_comap_bot]
      exact RingHom.ker_isPrime _
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at hQ'
    rw [Set.mem_singleton_iff.mp hQ']
  by_cases hproper : Ideal.span {bidegreeMap σ k a b f} = ⊤
  · rw [hproper, Ideal.comap_top] at hQ'
    exact absurd (top_le_iff.mp hQ'.1.2) hQ'.1.1.ne_top
  rw [natDegree_affineHilbertPolynomial_comap_bidegreeMap_span_singleton ha hb hf hproper]
  rw [comap_bidegreeMap_span_singleton ha hb] at hQ'
  have := RingHom.ker_isPrime (bidegreeMap σ k a b)
  have hQd := principalCut_natDegree_affineHilbertPolynomial_add_one
    (fun h ↦ hf (RingHom.mem_ker.mp h)) hQ'
  rw [natDegree_affineHilbertPolynomial_ker_bidegreeMap ha hb, Finite.card_option] at hQd
  omega

end MvPolynomial
