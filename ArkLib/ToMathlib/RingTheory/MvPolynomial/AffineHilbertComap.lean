/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity

/-!
# Affine Hilbert functions of pulled-back ideals

Let `k` be a field and `φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k` a map of `k`-algebras. If `φ`
sends every polynomial of total degree at most `N` into a finite-dimensional subspace `M`, the
affine Hilbert function of the pullback `I.comap φ` at `N` is at most the dimension of the image of
`M` in the quotient by `I`, since the induced map of quotients is injective. For a hypersurface
`I = span {g}` with `g ≠ 0`, multiplication by `g` embeds every subspace `M'` with `g * M' ⊆ M`
into the kernel of the projection of `M` onto the quotient, which subtracts `finrank M'` from the
bound.

When `φ` is surjective, the pullback of `span {φ f}` is the principal cut `RingHom.ker φ ⊔ span {f}`
of the prime `RingHom.ker φ`. With `σ` and `τ` finite, the kernel has affine Hilbert polynomial of
natural degree `Nat.card σ`, and the pullback of a nonzero proper hypersurface has natural degree
`Nat.card σ - 1`. Purity of principal cuts then makes the pullback of a hypersurface
equidimensional, so the affine degrees of its minimal primes sum to at most its affine degree.

## Main statements

* `Submodule.finrank_map_mkₐ_span_singleton_add_le`: the dimension count in the quotient by one
  element of a domain.
* `MvPolynomial.affineHilbertFunction_comap_le_finrank_map`: the comparison of filtrations.
* `MvPolynomial.affineHilbertFunction_comap_span_singleton_add_finrank_le`: the bound for a
  pulled-back hypersurface.
* `Ideal.comap_span_singleton_of_surjective`: the pullback of a hypersurface along a surjection is
  a principal cut of the kernel.
* `MvPolynomial.natDegree_affineHilbertPolynomial_ker_of_surjective`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective`: the
  natural degrees of the kernel and of a pulled-back hypersurface.
* `MvPolynomial.sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective`: the minimal
  primes of a pulled-back hypersurface have total affine degree at most its affine degree.
-/

@[expose] public section

noncomputable section

namespace Submodule

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- Let `g ≠ 0` in a domain `A` and let `M`, `M'` be subspaces with `M` finite-dimensional and
`g * p ∈ M` for every `p ∈ M'`. The image of `M` in `A ⧸ span {g}` has dimension at most
`finrank M - finrank M'`: multiplication by `g` embeds `M'` into the kernel of the projection. -/
theorem finrank_map_mkₐ_span_singleton_add_le {g : A} (hg0 : g ≠ 0) {M M' : Submodule k A}
    [Module.Finite k M] (hM' : ∀ p ∈ M', g * p ∈ M) :
    Module.finrank k (M.map (Ideal.Quotient.mkₐ k (Ideal.span {g})).toLinearMap) +
        Module.finrank k M' ≤ Module.finrank k M := by
  let π := (Ideal.Quotient.mkₐ k (Ideal.span {g})).toLinearMap.domRestrict M
  let μ : M' →ₗ[k] M := ((LinearMap.mulLeft k g).domRestrict M').codRestrict M fun p ↦ hM' _ p.2
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
  omega

end Submodule

namespace Ideal

variable {A B : Type*} [CommRing A] [CommRing B]

/-- For a surjective ring map `f`, the pullback of `span {f a}` is `RingHom.ker f ⊔ span {a}`. -/
theorem comap_span_singleton_of_surjective {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Function.Surjective f) (a : A) :
    (Ideal.span {f a}).comap f = RingHom.ker f ⊔ Ideal.span {a} := by
  rw [← Set.image_singleton, ← Ideal.map_span f, Ideal.comap_map_of_surjective f hf,
    RingHom.ker_eq_comap_bot, sup_comm]

end Ideal

namespace MvPolynomial

variable {k σ τ : Type*} [Field k]

/-- If `φ` sends every polynomial of total degree at most `N` into the finite-dimensional subspace
`M`, the affine Hilbert function of `I.comap φ` at `N` is at most the dimension of the image of `M`
in the quotient by `I`: the induced map of quotients is injective and sends the `N`-th piece of the
filtration into that image. -/
theorem affineHilbertFunction_comap_le_finrank_map (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (I : Ideal (MvPolynomial σ k)) {N : ℕ} (M : Submodule k (MvPolynomial σ k))
    [Module.Finite k M] (hM : ∀ P : MvPolynomial τ k, P.totalDegree ≤ N → φ P ∈ M) :
    affineHilbertFunction (I.comap φ) N ≤
      Module.finrank k (M.map (Ideal.Quotient.mkₐ k I).toLinearMap) := by
  let g := Ideal.quotientMapₐ I φ le_rfl
  let L : quotientDegreeLE (I.comap φ) N →ₗ[k] M.map (Ideal.Quotient.mkₐ k I).toLinearMap :=
    (g.toLinearMap.domRestrict _).codRestrict _ fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.2
      rw [LinearMap.domRestrict_apply, AlgHom.toLinearMap_apply, ← hpx]
      exact ⟨_, hM p hp, rfl⟩
  exact LinearMap.finrank_le_finrank_of_injective (f := L) fun x y hxy ↦
    Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val hxy))

/-- Let `g ≠ 0`, let `φ` send every polynomial of total degree at most `N` into the
finite-dimensional subspace `M`, and let `g * p ∈ M` for every `p ∈ M'`. Then the affine Hilbert
function of `(span {g}).comap φ` at `N` is at most `finrank M - finrank M'`. -/
theorem affineHilbertFunction_comap_span_singleton_add_finrank_le
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) {g : MvPolynomial σ k} (hg0 : g ≠ 0) {N : ℕ}
    {M M' : Submodule k (MvPolynomial σ k)} [Module.Finite k M]
    (hM : ∀ P : MvPolynomial τ k, P.totalDegree ≤ N → φ P ∈ M) (hM' : ∀ p ∈ M', g * p ∈ M) :
    affineHilbertFunction ((Ideal.span {g}).comap φ) N + Module.finrank k M' ≤
      Module.finrank k M :=
  (Nat.add_le_add_right (affineHilbertFunction_comap_le_finrank_map φ _ M hM) _).trans
    (Submodule.finrank_map_mkₐ_span_singleton_add_le hg0 hM')

variable [Finite σ] [Finite τ]

/-- The kernel of a surjective `φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k` has affine Hilbert
polynomial of natural degree `Nat.card σ`. -/
theorem natDegree_affineHilbertPolynomial_ker_of_surjective
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (hφ : Function.Surjective φ) :
    (affineHilbertPolynomial (RingHom.ker φ)).natDegree = Nat.card σ := by
  rw [RingHom.ker_eq_comap_bot, natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ,
    natDegree_affineHilbertPolynomial_bot]

/-- For a surjective `φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k`, the pullback of a proper
hypersurface `span {g}`, `g ≠ 0`, has affine Hilbert polynomial of natural degree
`Nat.card σ - 1`, stated as `natDegree + 1 = Nat.card σ`. -/
theorem natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (hφ : Function.Surjective φ)
    {g : MvPolynomial σ k} (hg0 : g ≠ 0) (hproper : Ideal.span {g} ≠ ⊤) :
    (affineHilbertPolynomial ((Ideal.span {g}).comap φ)).natDegree + 1 = Nat.card σ := by
  rw [natDegree_affineHilbertPolynomial_comap_of_surjective φ hφ]
  exact natDegree_affineHilbertPolynomial_span_singleton_add_one hg0 hproper

/-- For a surjective `φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k`, the affine degrees of the
minimal primes of the pullback of a hypersurface `span {g}` sum to at most its affine degree.

For `g ≠ 0` with `span {g}` proper, the pullback is the principal cut of the prime
`RingHom.ker φ` by a preimage of `g`, so its minimal primes all have the dimension of the pullback,
and `sum_affineDegree_minimalPrimes_le` applies. For `g = 0` the pullback is prime, and for
`span {g} = ⊤` it has no minimal primes. -/
theorem sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (hφ : Function.Surjective φ)
    (g : MvPolynomial σ k) :
    ∑ Q ∈ ((Ideal.span {g}).comap φ).minimalPrimesFinset, affineDegree Q ≤
      affineDegree ((Ideal.span {g}).comap φ) := by
  obtain ⟨f, rfl⟩ := hφ g
  refine sum_affineDegree_minimalPrimes_le fun Q hQ ↦ ?_
  have hQ' := Ideal.mem_minimalPrimesFinset.mp hQ
  by_cases hf : φ f = 0
  · have : ((Ideal.span {φ f}).comap φ).IsPrime := by
      rw [hf, Ideal.span_singleton_eq_bot.mpr rfl, ← RingHom.ker_eq_comap_bot]
      exact RingHom.ker_isPrime _
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at hQ'
    rw [Set.mem_singleton_iff.mp hQ']
  by_cases hproper : Ideal.span {φ f} = ⊤
  · rw [hproper, Ideal.comap_top] at hQ'
    exact absurd (top_le_iff.mp hQ'.1.2) hQ'.1.1.ne_top
  have hJ := natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective φ hφ hf
    hproper
  rw [Ideal.comap_span_singleton_of_surjective φ hφ] at hQ' hJ ⊢
  have := RingHom.ker_isPrime φ
  have hQd := principalCut_natDegree_affineHilbertPolynomial_add_one
    (fun h ↦ hf (RingHom.mem_ker.mp h)) hQ'
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective φ hφ] at hQd
  omega

end MvPolynomial
