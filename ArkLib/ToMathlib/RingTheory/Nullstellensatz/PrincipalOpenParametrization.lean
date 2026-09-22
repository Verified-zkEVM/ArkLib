/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen

/-!
# Principal open subsets covered by polynomial parametrizations

Let `k` be a field, `σ` a finite type, `I` an ideal of `MvPolynomial σ k` and `s` a polynomial
whose class is a non-zero-divisor modulo `I`. Write `H(I)` for `affineHilbertPolynomial I` and
`U(I) = {x ∈ V(I) | s(x) ≠ 0}` for the principal open subset of the zero locus cut out by `s`.

Suppose `U(I)` is covered by a polynomial parametrization, that is, every point of `U(I)` has the
form `x = (w i (t))ᵢ` for some parameter `t`, where `w : σ → MvPolynomial τ k`. Then the dimension
`natDegree H(I)` is at most `Nat.card τ`. For a one-parameter family `w : σ → k[X]` the bound is
`1`, and if `I` has positive dimension, then every polynomial vanishing on `U(I)` vanishes
identically after substituting the parametrization.

The dimension bound comes from the kernel `J` of the substitution `aeval w`. Every polynomial in
`J` vanishes on `U(I)`, so by the Nullstellensatz for principal open subsets
(`mem_radical_of_forall_principalOpen`) it lies in `I.radical`. Hence `H(I)` has natural degree at
most that of `H(J)`, and the quotient by `J` embeds into `MvPolynomial τ k`, whose Hilbert
polynomial has natural degree `Nat.card τ`. No image closure is constructed.

The vanishing statement uses only that `U(I)` is infinite when `I` has positive dimension: the
parameters of an infinite set of points form an infinite set of roots of the substituted
polynomial.

## Main statements

* `MvPolynomial.polynomial_eval_aeval`: substituting univariate polynomials and then evaluating
  at `z` is evaluation at the point `(w i (z))ᵢ`.
* `MvPolynomial.aeval_eq_zero_of_infinite`: over a domain, a polynomial vanishing on an infinite
  subset of a one-parameter polynomial curve vanishes after substitution.
* `MvPolynomial.mem_radical_of_forall_principalOpen`: a polynomial vanishing on `U(I)`, with
  points in an algebraically closed extension, lies in `I.radical`.
* `MvPolynomial.ker_aeval_le_radical_of_principalOpen_subset_range` and
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range`: a
  parametrization of `U(I)` by `τ`-tuples bounds the dimension of `I` by `Nat.card τ`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range`: the
  one-parameter case.
* `MvPolynomial.aeval_eq_zero_of_principalOpen_subset_range`: polynomial identities along a
  one-parameter family covering a positive-dimensional `U(I)`.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Incidence/GraphPullback.lean`, namespace `AffineHilbert`.

The source worked on `Option σ`, with the `none` coordinate retained as the parameter, and defined
`polynomialGraphPoint w z` and `polynomialGraphPullback w = aeval (Option.elim · X w)`, and the
affine special case `affineGraphPoint`, `affineGraphPullback`. These definitions are not
introduced: the pullback is `aeval w` for any `w : σ → k[X]` and the point is
`fun i ↦ (w i).eval z`. The source's graphs are the case of `Option σ` with `w none = X`, and its
affine graphs the case `w (some j) = C (a j) + X * C (b j)`; the tests derive both.

* `eval_polynomialGraphPullback` and `eval_affineGraphPullback` are `polynomial_eval_aeval`, over
  any commutative semiring.
* `polynomialGraphPullback_eq_zero_of_infinite` and `affineGraphPullback_eq_zero_of_infinite` are
  `aeval_eq_zero_of_infinite`, over any domain. The retained parameter coordinate is not needed:
  an infinite set of points has an infinite set of parameters whether or not the parameter is
  recorded.
* `polynomialGraphPullback_vanishes_of_principalOpen` and `graphPullback_vanishes_of_principalOpen`
  are `aeval_eq_zero_of_principalOpen_subset_range`, for any polynomial vanishing on `U(I)`
  rather than only members of a prime `P`, with primality of `P` and `s ∉ P` weakened to
  regularity of `s` modulo `I`. Their second conjunct, that the substituted `s` is nonzero, is a
  direct consequence of `polynomial_eval_aeval` at one point of `U(I)`; the tests derive it.
* `hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_polynomialGraph` and
  `hilbertPolynomial_natDegree_le_one_of_principalOpen_subset_affineGraph` are
  `natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range`, a corollary of the
  multi-parameter `natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range`. The
  positive-dimension hypothesis is dropped, primality is weakened to regularity of `s`, the base
  field need not be algebraically closed (the points lie in an algebraically closed extension
  `K`), and the source's proof through an injective map from the quotient by `P` is replaced by
  the kernel comparison above.

`mem_radical_of_forall_principalOpen` and `ker_aeval_le_radical_of_principalOpen_subset_range`
are new.
-/

@[expose] public section

namespace MvPolynomial

/-- Substituting univariate polynomials `w i` into a multivariate polynomial and evaluating the
result at `z` is evaluation at the point `(w i (z))ᵢ`. -/
theorem polynomial_eval_aeval {R σ : Type*} [CommSemiring R] (w : σ → Polynomial R) (z : R)
    (p : MvPolynomial σ R) :
    (aeval w p).eval z = eval (fun i ↦ (w i).eval z) p := by
  have h := comp_aeval_apply (f := w) (Polynomial.aeval z) p
  simp only [Polynomial.coe_aeval_eq_eval] at h
  exact h

/-- Over a domain `R`, let `S` be an infinite set of points of the curve `z ↦ (w i (z))ᵢ`. A
polynomial `p` vanishing on `S` vanishes after substituting `w`: `aeval w p = 0`.

Distinct points of `S` have distinct parameters, so the univariate polynomial `aeval w p` has
infinitely many roots. Infiniteness is needed: for `σ = Unit`, `w = X`, `p = X ()` and `S = {0}`,
`p` vanishes on `S` but `aeval w p = X`. The domain hypothesis is needed for a nonzero
univariate polynomial to have finitely many roots. -/
theorem aeval_eq_zero_of_infinite {R σ : Type*} [CommRing R] [IsDomain R] (w : σ → Polynomial R)
    {S : Set (σ → R)} (hS : S.Infinite) (hcurve : ∀ x ∈ S, ∃ z, x = fun i ↦ (w i).eval z)
    {p : MvPolynomial σ R} (hp : ∀ x ∈ S, eval x p = 0) : aeval w p = 0 := by
  let T : Set R := {z | (fun i ↦ (w i).eval z) ∈ S}
  have hT : T.Infinite := fun hT ↦ hS <| (hT.image fun z i ↦ (w i).eval z).subset fun x hx ↦ by
    obtain ⟨z, rfl⟩ := hcurve x hx
    exact ⟨z, hx, rfl⟩
  refine Polynomial.eq_zero_of_infinite_isRoot _ (hT.mono fun z hz ↦ ?_)
  change (aeval w p).eval z = 0
  rw [polynomial_eval_aeval]
  exact hp _ hz

variable {k K σ τ : Type*} [Field k] [Field K] [Algebra k K]

/-- **Nullstellensatz for principal open subsets.** Let `K` be an algebraically closed extension
of `k` and let the class of `s` be a non-zero-divisor modulo `I`. A polynomial `p` vanishing at
every point `x ∈ V(I)` over `K` with `s(x) ≠ 0` lies in `I.radical`.

The product `s * p` vanishes on all of `V(I)`, so the Nullstellensatz gives `(s * p) ^ n ∈ I`,
and regularity of `s ^ n` modulo `I` gives `p ^ n ∈ I`. Regularity is needed: for `I = (X₀X₁)`
and `s = X₀`, the polynomial `X₁` vanishes wherever `X₀X₁ = 0` and `X₀ ≠ 0`, but `X₁ ∉ I.radical`.
-/
theorem mem_radical_of_forall_principalOpen [IsAlgClosed K] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) {p : MvPolynomial σ k}
    (hp : ∀ x : σ → K, x ∈ zeroLocus K I → aeval x s ≠ 0 → aeval x p = 0) :
    p ∈ I.radical := by
  have hsp : s * p ∈ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
    intro x hx
    by_cases hxs : aeval x s = 0
    · rw [map_mul, hxs, zero_mul]
    · rw [map_mul, hp x hx hxs, mul_zero]
  obtain ⟨n, hn⟩ := hsp
  refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp (hs.pow n ?_)⟩
  change Ideal.Quotient.mk I s ^ n * Ideal.Quotient.mk I (p ^ n) =
    Ideal.Quotient.mk I s ^ n * 0
  rw [mul_zero, ← map_pow, ← map_mul, ← mul_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hn

/-- If every point of `U(I)` over an algebraically closed extension `K` has the form
`(w i (t))ᵢ` for a parameter `t : τ → K`, then the kernel of the substitution
`aeval w : MvPolynomial σ k → MvPolynomial τ k` lies in `I.radical`.

A polynomial in the kernel vanishes at every parametrized point, hence on `U(I)`, and
`mem_radical_of_forall_principalOpen` applies. The regularity of `s` modulo `I` is needed for the
same reason as there. -/
theorem ker_aeval_le_radical_of_principalOpen_subset_range [IsAlgClosed K] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (w : σ → MvPolynomial τ k)
    (hrange : ∀ x : σ → K, x ∈ zeroLocus K I → aeval x s ≠ 0 →
      ∃ t : τ → K, x = fun i ↦ aeval t (w i)) :
    RingHom.ker (aeval w : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) ≤ I.radical := by
  intro p hp
  refine mem_radical_of_forall_principalOpen (K := K) hs fun x hx hxs ↦ ?_
  obtain ⟨t, rfl⟩ := hrange x hx hxs
  rw [← comp_aeval_apply, RingHom.mem_ker.mp hp, map_zero]

/-- **Dimension of a parametrized principal open subset.** Let `K` be an algebraically closed
extension of `k`, let the class of `s` be a non-zero-divisor modulo `I`, and suppose every point
of `U(I)` over `K` has the form `(w i (t))ᵢ` for some `t : τ → K`, where
`w : σ → MvPolynomial τ k`. Then `natDegree H(I) ≤ Nat.card τ`.

With `J` the kernel of `aeval w`, `J ≤ I.radical`
(`ker_aeval_le_radical_of_principalOpen_subset_range`), so `natDegree H(I) = natDegree H(I.radical)
≤ natDegree H(J)`, and `MvPolynomial σ k ⧸ J` embeds into `MvPolynomial τ k`. Regularity of `s`
is needed: for `I = (X₀X₁, X₀X₂)` in three variables and `s = X₀`, the set `U(I)` is the
punctured `X₀`-axis, covered by `t ↦ (t, 0, 0)` with `τ = Unit`, while `I` has the plane `X₀ = 0`
as a component of dimension `2`.
Algebraic closedness of `K` is needed: `span {X₀ ^ 2 + 1}` in `ℚ[X₀, X₁]` has no rational points,
so with `K = ℚ` the hypothesis holds for `τ = Empty`, but its dimension is `1`. -/
theorem natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range [IsAlgClosed K]
    [Finite σ] [Finite τ] {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (w : σ → MvPolynomial τ k)
    (hrange : ∀ x : σ → K, x ∈ zeroLocus K I → aeval x s ≠ 0 →
      ∃ t : τ → K, x = fun i ↦ aeval t (w i)) :
    (affineHilbertPolynomial I).natDegree ≤ Nat.card τ := by
  let g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k ⧸ (⊥ : Ideal (MvPolynomial τ k)) :=
    (Ideal.Quotient.mkₐ k ⊥).comp (aeval w)
  have hJ : RingHom.ker g ≤ I.radical := fun p hp ↦
    ker_aeval_le_radical_of_principalOpen_subset_range hs w hrange <| by
      rw [RingHom.mem_ker] at hp ⊢
      exact (Ideal.mem_bot).mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  calc (affineHilbertPolynomial I).natDegree
      = (affineHilbertPolynomial I.radical).natDegree :=
        (natDegree_affineHilbertPolynomial_radical I).symm
    _ ≤ (affineHilbertPolynomial (RingHom.ker g)).natDegree :=
        natDegree_affineHilbertPolynomial_le_of_le hJ
    _ ≤ (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial τ k))).natDegree :=
        natDegree_affineHilbertPolynomial_le_of_injective _ (Ideal.kerLiftAlg_injective g)
    _ = Nat.card τ := natDegree_affineHilbertPolynomial_bot

/-- **One-parameter families.** If every point of `U(I)` over an algebraically closed extension
`K` has the form `(w i (z))ᵢ` for a scalar `z : K`, where `w : σ → k[X]`, and the class of `s` is
a non-zero-divisor modulo `I`, then `natDegree H(I) ≤ 1`.

This is `natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range` with `τ = Unit`,
through `Polynomial.toMvPolynomial`. -/
theorem natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range [IsAlgClosed K]
    [Finite σ] {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (w : σ → Polynomial k)
    (hrange : ∀ x : σ → K, x ∈ zeroLocus K I → aeval x s ≠ 0 →
      ∃ z : K, x = fun i ↦ Polynomial.aeval z (w i)) :
    (affineHilbertPolynomial I).natDegree ≤ 1 := by
  have := natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range hs
    (fun i ↦ (w i).toMvPolynomial ()) fun x hx hxs ↦ by
      obtain ⟨z, rfl⟩ := hrange x hx hxs
      exact ⟨fun _ ↦ z, by simp⟩
  simpa using this

/-- **Polynomial identities along a one-parameter family.** Over an algebraically closed field
`k`, let the class of `s` be a non-zero-divisor modulo `I`, let `I` have positive dimension, and
suppose every point of `U(I)` has the form `(w i (z))ᵢ` for some `z ∈ k`, where `w : σ → k[X]`.
Then every polynomial `p` vanishing on `U(I)`, in particular every `p ∈ I`, satisfies
`aeval w p = 0`.

Positive dimension and regularity make `U(I)` infinite
(`finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`), and
`aeval_eq_zero_of_infinite` applies. Positive dimension is needed: for `I = (X ())` in one
variable, `s = 1` and `w = X`, the set `U(I) = {0}` is covered, but `p = X ()` gives
`aeval w p = X ≠ 0`. -/
theorem aeval_eq_zero_of_principalOpen_subset_range [IsAlgClosed k] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (w : σ → Polynomial k)
    (hrange : ∀ x : σ → k, x ∈ zeroLocus k I → aeval x s ≠ 0 →
      ∃ z : k, x = fun i ↦ (w i).eval z)
    {p : MvPolynomial σ k} (hp : ∀ x : σ → k, x ∈ zeroLocus k I → aeval x s ≠ 0 → aeval x p = 0) :
    aeval w p = 0 := by
  have hinf : {x : σ → k | x ∈ zeroLocus k I ∧ aeval x s ≠ 0}.Infinite := fun hfin ↦
    hd.ne' ((finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hs).mp hfin)
  exact aeval_eq_zero_of_infinite w hinf (fun x hx ↦ hrange x hx.1 hx.2)
    fun x hx ↦ by simpa using hp x hx.1 hx.2

end MvPolynomial
