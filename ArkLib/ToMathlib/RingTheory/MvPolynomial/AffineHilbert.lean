/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The affine Hilbert function of a polynomial quotient

For an ideal `I` of `MvPolynomial σ k` over a field `k`, the total-degree filtration of the
polynomial ring descends to the coordinate quotient `MvPolynomial σ k ⧸ I`: its `N`-th piece
`MvPolynomial.quotientDegreeLE I N` is the image of the polynomials of total degree at most `N`.
The affine Hilbert function `MvPolynomial.affineHilbertFunction I N` is the `k`-dimension of this
piece. It is the filtered (affine) Hilbert function, not the graded Hilbert function of a
homogeneous ideal; no homogeneity hypothesis on `I` is used.

With finitely many variables every piece is finite-dimensional. The function is monotone in `N`,
antitone in `I`, equal to `1` at `N = 0` for proper ideals and `0` for the unit ideal, and it
stabilizes at `Module.finrank k (MvPolynomial σ k ⧸ I)` when the quotient is finite-dimensional.

The principal-cut inequality compares `I` with `I ⊔ span {f}`: if `f` has total degree at most
`b ≤ N` and multiplication by `f` is injective on the quotient by `I`, then
`H(I ⊔ span {f}, N) + H(I, N - b) ≤ H(I, N)`. Multiplication by `f` embeds the `(N - b)`-th piece
into the kernel of the surjection between the `N`-th pieces.

## Main statements

* `MvPolynomial.quotientDegreeLE`: the image of `restrictTotalDegree σ k N` in the quotient.
* `MvPolynomial.mul_mem_quotientDegreeLE`, `MvPolynomial.algebraMap_mem_quotientDegreeLE`,
  `MvPolynomial.mk_X_mem_quotientDegreeLE`, `MvPolynomial.exists_mem_quotientDegreeLE`: the
  filtration is multiplicative, contains the scalars in degree `0` and the variables in degree
  `1`, and is exhaustive.
* `MvPolynomial.affineHilbertFunction`: the dimension of that image.
* `MvPolynomial.affineHilbertFunction_mono`, `MvPolynomial.affineHilbertFunction_anti`: monotone
  in the degree, antitone in the ideal.
* `MvPolynomial.affineHilbertFunction_zero`, `MvPolynomial.one_le_affineHilbertFunction`: the
  value at degree zero and the resulting lower bound for proper ideals.
* `MvPolynomial.exists_affineHilbertFunction_eq_finrank`: stabilization at the quotient dimension.
* `MvPolynomial.exists_finset_generators_totalDegree_le`: a finite generating set with a uniform
  total-degree bound.
* `MvPolynomial.principalCut_affineHilbertFunction_add_le`: the principal-cut inequality for a
  regular cutting element, and `MvPolynomial.principalCut_affineHilbertFunction_add_le_of_isPrime`
  for a prime ideal and a cutting element outside it.

## References

The definitions and the principal-cut inequality are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Function.lean`: `AffineHilbert.quotientDegreeLE`,
`AffineHilbert.hilbertFunction` (renamed `affineHilbertFunction`),
`AffineHilbert.exists_finset_generators_totalDegree_le` and
`AffineHilbert.principalCut_hilbertFunction_add_le`. The source assumed that `I` is prime and
`f ∉ I`; the general form assumes only that multiplication by the class of `f` is injective on the
quotient, which is what the proof uses, and the source statement is the corollary
`principalCut_affineHilbertFunction_add_le_of_isPrime`. The monotonicity statements,
`quotientDegreeLE_eventually_top` and `one_le_hilbertFunction` of the source files
`Hilbert/Polynomial.lean` and `PrincipalCut/Degree.lean` at the same revision are included here,
since they concern only the Hilbert function. The field is named `k` and the declarations live in
the `MvPolynomial` namespace, as in `ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient`.
The source namespace `AffineHilbert` is not kept: the objects are attached to an ideal of
`MvPolynomial σ k`, and the prefix `affine` in `affineHilbertFunction` separates this function from
Mathlib's graded `Polynomial.hilbertPoly`.

The multiplicativity lemmas for the filtration are used for comparisons along algebra maps in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom`. The Hilbert polynomial of `I` and
the principal-cut statement on its degree are in
`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k σ : Type*} [Field k]

/-- The `N`-th piece of the total-degree filtration on the coordinate quotient
`MvPolynomial σ k ⧸ I`: the image of the polynomials of total degree at most `N`. -/
def quotientDegreeLE (I : Ideal (MvPolynomial σ k)) (N : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k N).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- A class lies in the `N`-th piece exactly when it has a representative of total degree at
most `N`. -/
theorem mem_quotientDegreeLE {I : Ideal (MvPolynomial σ k)} {N : ℕ}
    {x : MvPolynomial σ k ⧸ I} :
    x ∈ quotientDegreeLE I N ↔ ∃ p : MvPolynomial σ k, p.totalDegree ≤ N ∧
      Ideal.Quotient.mk I p = x := by
  simp only [quotientDegreeLE, Submodule.mem_map, mem_restrictTotalDegree]
  rfl

/-- The class of a polynomial of total degree at most `N` lies in the `N`-th piece. -/
theorem mk_mem_quotientDegreeLE {I : Ideal (MvPolynomial σ k)} {N : ℕ}
    {p : MvPolynomial σ k} (hp : p.totalDegree ≤ N) :
    Ideal.Quotient.mk I p ∈ quotientDegreeLE I N :=
  mem_quotientDegreeLE.mpr ⟨p, hp, rfl⟩

/-- With finitely many variables each filtration piece is finite-dimensional, as the image of the
finite-dimensional space `restrictTotalDegree σ k N`. -/
instance quotientDegreeLE.moduleFinite [Finite σ] (I : Ideal (MvPolynomial σ k)) (N : ℕ) :
    Module.Finite k (quotientDegreeLE I N) := by
  unfold quotientDegreeLE
  infer_instance

/-- The filtration is increasing. -/
theorem quotientDegreeLE_mono (I : Ideal (MvPolynomial σ k)) :
    Monotone (quotientDegreeLE I) := by
  intro N M hNM x hx
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hx
  exact mk_mem_quotientDegreeLE (hp.trans hNM)

/-- The filtration is exhaustive: every class has a representative of some finite degree. -/
theorem iSup_quotientDegreeLE (I : Ideal (MvPolynomial σ k)) :
    ⨆ N, quotientDegreeLE I N = ⊤ := by
  refine top_unique fun x _ ↦ ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Submodule.mem_iSup_of_mem p.totalDegree (mk_mem_quotientDegreeLE le_rfl)

/-- Every class lies in some piece of the filtration: the piece indexed by the total degree of any
representative. -/
theorem exists_mem_quotientDegreeLE (I : Ideal (MvPolynomial σ k)) (x : MvPolynomial σ k ⧸ I) :
    ∃ N, x ∈ quotientDegreeLE I N := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨p.totalDegree, mk_mem_quotientDegreeLE le_rfl⟩

/-- Scalars lie in every piece of the filtration. -/
theorem algebraMap_mem_quotientDegreeLE (I : Ideal (MvPolynomial σ k)) (r : k) (N : ℕ) :
    algebraMap k (MvPolynomial σ k ⧸ I) r ∈ quotientDegreeLE I N :=
  mk_mem_quotientDegreeLE ((totalDegree_C r).le.trans (Nat.zero_le N))

/-- The class of `1` lies in every piece of the filtration. -/
theorem one_mem_quotientDegreeLE (I : Ideal (MvPolynomial σ k)) (N : ℕ) :
    (1 : MvPolynomial σ k ⧸ I) ∈ quotientDegreeLE I N := by
  simpa using algebraMap_mem_quotientDegreeLE I 1 N

/-- The class of a variable lies in the piece of degree `1`. -/
theorem mk_X_mem_quotientDegreeLE (I : Ideal (MvPolynomial σ k)) (i : σ) :
    Ideal.Quotient.mk I (X i) ∈ quotientDegreeLE I 1 :=
  mk_mem_quotientDegreeLE (totalDegree_X i).le

/-- The filtration is multiplicative: the product of classes in the pieces of degree `a` and `b`
lies in the piece of degree `a + b`, since the product of representatives has total degree at most
the sum. -/
theorem mul_mem_quotientDegreeLE {I : Ideal (MvPolynomial σ k)} {a b : ℕ}
    {x y : MvPolynomial σ k ⧸ I} (hx : x ∈ quotientDegreeLE I a)
    (hy : y ∈ quotientDegreeLE I b) : x * y ∈ quotientDegreeLE I (a + b) := by
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hx
  obtain ⟨q, hq, rfl⟩ := mem_quotientDegreeLE.mp hy
  rw [← map_mul]
  exact mk_mem_quotientDegreeLE ((totalDegree_mul p q).trans (Nat.add_le_add hp hq))

/-- The degree-zero piece is spanned by the class of `1`: a polynomial of total degree zero is a
constant. -/
theorem quotientDegreeLE_zero (I : Ideal (MvPolynomial σ k)) :
    quotientDegreeLE I 0 = k ∙ (1 : MvPolynomial σ k ⧸ I) := by
  ext x
  rw [mem_quotientDegreeLE, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, p = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)⟩
    exact ⟨c, (Algebra.algebraMap_eq_smul_one (A := MvPolynomial σ k ⧸ I) c).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨C a, (totalDegree_C a).le, Algebra.algebraMap_eq_smul_one (A := MvPolynomial σ k ⧸ I) a⟩

/-- A finite-dimensional quotient is exhausted by a single piece of the filtration, and hence by
every later piece. -/
theorem exists_quotientDegreeLE_eq_top (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, quotientDegreeLE I N = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k) (M := MvPolynomial σ k ⧸ I)
  choose p hp using fun x : MvPolynomial σ k ⧸ I ↦ Ideal.Quotient.mk_surjective x
  refine ⟨s.sup fun x ↦ (p x).totalDegree, fun N hN ↦ top_unique ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  rw [← hp x]
  exact mk_mem_quotientDegreeLE ((Finset.le_sup (f := fun x ↦ (p x).totalDegree) hx).trans hN)

/-- The affine Hilbert function: the `k`-dimension of the image in `MvPolynomial σ k ⧸ I` of the
polynomials of total degree at most `N`.

For infinitely many variables the pieces can be infinite-dimensional, in which case
`Module.finrank` takes the value `0`; the substantive statements below assume `Finite σ`. -/
def affineHilbertFunction (I : Ideal (MvPolynomial σ k)) (N : ℕ) : ℕ :=
  Module.finrank k (quotientDegreeLE I N)

/-- The affine Hilbert function is monotone in the degree. Finiteness of the variable type makes
the pieces finite-dimensional, which the comparison of `finrank`s needs. -/
theorem affineHilbertFunction_mono [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    Monotone (affineHilbertFunction I) :=
  fun _ _ hNM ↦ Submodule.finrank_mono (quotientDegreeLE_mono I hNM)

/-- The natural surjection between the `N`-th pieces for `I ≤ J`. -/
private def quotientDegreeLEFactor {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) (N : ℕ) :
    quotientDegreeLE I N →ₗ[k] quotientDegreeLE J N :=
  ((Ideal.Quotient.factorₐ k hIJ).toLinearMap.domRestrict (quotientDegreeLE I N)).codRestrict
    (quotientDegreeLE J N) fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
      rw [LinearMap.domRestrict_apply, ← hpx]
      exact mk_mem_quotientDegreeLE hp

private theorem quotientDegreeLEFactor_surjective {I J : Ideal (MvPolynomial σ k)}
    (hIJ : I ≤ J) (N : ℕ) : Function.Surjective (quotientDegreeLEFactor hIJ N) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
  exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩

/-- The affine Hilbert function is antitone in the ideal: a larger ideal has a smaller quotient
filtration. -/
theorem affineHilbertFunction_anti [Finite σ] {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J)
    (N : ℕ) : affineHilbertFunction J N ≤ affineHilbertFunction I N :=
  LinearMap.finrank_le_finrank_of_surjective (quotientDegreeLEFactor_surjective hIJ N)

/-- At degree zero the affine Hilbert function is `1` for a proper ideal and `0` for the unit
ideal. No finiteness of the variable type is needed. -/
theorem affineHilbertFunction_zero (I : Ideal (MvPolynomial σ k)) [Decidable (I = ⊤)] :
    affineHilbertFunction I 0 = if I = ⊤ then 0 else 1 := by
  rw [affineHilbertFunction, quotientDegreeLE_zero]
  split_ifs with hI
  · subst hI
    exact Module.finrank_zero_of_subsingleton
  · have := Ideal.Quotient.nontrivial_iff.mpr hI
    exact finrank_span_singleton one_ne_zero

/-- The unit ideal has the zero quotient, so its Hilbert function vanishes identically. -/
@[simp]
theorem affineHilbertFunction_top (N : ℕ) :
    affineHilbertFunction (⊤ : Ideal (MvPolynomial σ k)) N = 0 :=
  Module.finrank_zero_of_subsingleton

/-- A proper ideal has Hilbert function at least `1` in every degree, since the class of `1` is
nonzero. The hypothesis `I ≠ ⊤` is necessary by `affineHilbertFunction_top`. -/
theorem one_le_affineHilbertFunction [Finite σ] {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊤)
    (N : ℕ) : 1 ≤ affineHilbertFunction I N := by
  classical
  have h0 : affineHilbertFunction I 0 = 1 := by simp [affineHilbertFunction_zero, hI]
  exact h0 ▸ affineHilbertFunction_mono I (Nat.zero_le N)

/-- When the quotient is finite-dimensional, every Hilbert-function value is at most its
dimension. -/
theorem affineHilbertFunction_le_finrank (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] (N : ℕ) :
    affineHilbertFunction I N ≤ Module.finrank k (MvPolynomial σ k ⧸ I) :=
  Submodule.finrank_le _

/-- When the quotient is finite-dimensional, the affine Hilbert function is eventually equal to
its dimension. -/
theorem exists_affineHilbertFunction_eq_finrank (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      affineHilbertFunction I N = Module.finrank k (MvPolynomial σ k ⧸ I) := by
  obtain ⟨N₀, hN₀⟩ := exists_quotientDegreeLE_eq_top I
  exact ⟨N₀, fun N hN ↦ by rw [affineHilbertFunction, hN₀ N hN, finrank_top]⟩

/-- Every ideal of a polynomial ring in finitely many variables over a field has a finite
generating set whose members have total degree at most a common bound. Finiteness of `σ` enters
through Hilbert's basis theorem. -/
theorem exists_finset_generators_totalDegree_le [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    ∃ (s : Finset (MvPolynomial σ k)) (b : ℕ),
      Ideal.span (s : Set (MvPolynomial σ k)) = I ∧ ∀ f ∈ s, f.totalDegree ≤ b := by
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff.mp inferInstance).noetherian I
  exact ⟨s, s.sup totalDegree, hs, fun f hf ↦ Finset.le_sup hf⟩

/-- Multiplication by `f`, from the `(N - b)`-th piece to the `N`-th piece. -/
private def quotientDegreeLEMul {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    {b N : ℕ} (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    quotientDegreeLE I (N - b) →ₗ[k] quotientDegreeLE I N :=
  ((LinearMap.mulLeft k (Ideal.Quotient.mk I f)).domRestrict
      (quotientDegreeLE I (N - b))).codRestrict (quotientDegreeLE I N) fun x ↦ by
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp x.property
    rw [LinearMap.domRestrict_apply, LinearMap.mulLeft_apply, ← hpx, ← map_mul]
    exact mk_mem_quotientDegreeLE ((totalDegree_mul f p).trans (by omega))

/-- The principal-cut inequality for a cutting element that is regular on the quotient: if the
class of `f` is a non-zero-divisor on `MvPolynomial σ k ⧸ I`, `f` has total degree at most `b`,
and `b ≤ N`, then `H(I ⊔ span {f}, N) + H(I, N - b) ≤ H(I, N)`.

Multiplication by `f` embeds the `(N - b)`-th piece of `I` into the kernel of the surjection onto
the `N`-th piece of `I ⊔ span {f}`. Regularity is needed for injectivity: for `I = span {X ^ 2}`
in one variable and `f = X`, the inequality fails. The bound `b ≤ N` is needed as well: for
`I = ⊥`, `f = X`, `b = 1` and `N = 0`, the left side is `2` and the right side is `1`. -/
theorem principalCut_affineHilbertFunction_add_le [Finite σ] {I : Ideal (MvPolynomial σ k)}
    {f : MvPolynomial σ k} (hf : IsLeftRegular (Ideal.Quotient.mk I f)) {b N : ℕ}
    (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    affineHilbertFunction (I ⊔ Ideal.span {f}) N + affineHilbertFunction I (N - b) ≤
      affineHilbertFunction I N := by
  have hIJ : I ≤ I ⊔ Ideal.span {f} := le_sup_left
  let cut := quotientDegreeLEFactor hIJ N
  let mul := quotientDegreeLEMul (I := I) hfdeg hbN
  have hmul : ∀ x, mul x ∈ LinearMap.ker cut := fun x ↦ by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change Ideal.Quotient.factor hIJ (Ideal.Quotient.mk I f * x) = 0
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)), zero_mul]
  have hmul_inj : Function.Injective (mul.codRestrict (LinearMap.ker cut) hmul) := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg (fun z ↦ (z.val : MvPolynomial σ k ⧸ I)) hxy))
  have hker := LinearMap.finrank_le_finrank_of_injective hmul_inj
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientDegreeLEFactor_surjective hIJ N), finrank_top] at hrank
  unfold affineHilbertFunction
  omega

/-- The principal-cut inequality for a prime ideal `I` and a cutting element `f ∉ I`, in which
case the class of `f` is a non-zero-divisor on the domain `MvPolynomial σ k ⧸ I`. This is the
source statement. -/
theorem principalCut_affineHilbertFunction_add_le_of_isPrime [Finite σ]
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsPrime) {f : MvPolynomial σ k} (hfI : f ∉ I)
    {b N : ℕ} (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    affineHilbertFunction (I ⊔ Ideal.span {f}) N + affineHilbertFunction I (N - b) ≤
      affineHilbertFunction I N :=
  have := hI
  principalCut_affineHilbertFunction_add_le
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hfI)) hfdeg hbN

end MvPolynomial
