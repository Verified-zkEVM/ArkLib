/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Projection

/-!
# Additional finite-dimensional linear-algebra lemmas

## Main statements

* `LinearMap.finrank_eq_of_map_eq` — a linear map injective on `B` and mapping `B` onto `A`
  makes the two submodules equidimensional.
* `Submodule.exists_adapted_basis` — a finite-dimensional space has a basis whose initial
  segment is a basis of a prescribed subspace.
* `LinearMap.finrank_range_le_sub_of_injective_ker` — rank–nullity when only part of the kernel
  is exhibited, as the image of an injective map.
* `LinearMap.finrank_range_comp_le_left` — the `finrank` form of `LinearMap.rank_comp_le_left`.
* `LinearMap.rangeCoordinates`, `LinearMap.rangeCoordinates_eq_zero_iff`,
  `LinearMap.ker_rangeCoordinates`, `LinearMap.rangeCoordinates_surjective` — a linear map
  followed by coordinates on its finite-dimensional range: a map onto `K^(rank f)` with the kernel
  of `f`.
* `LinearMap.finrank_range_pi_le_sum` — the rank of a finite family of linear maps, taken
  jointly, is at most the sum of their ranks.
* `LinearMap.exists_ne_zero_of_sum_finrank_range_lt` — if the source dimension exceeds the sum of
  the ranks of a finite family of linear maps, some nonzero vector lies in all their kernels.

The last two are the linear-algebra part of `finrank_range_le_sub_finrank_of_injective_to_ker`
and `finrank_range_comp_le_outer` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Rank.lean` at ArkLib
revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source assumed a field, a
finite-dimensional exhibited space, and a finite-dimensional middle space; here the scalars form
a division ring, the exhibited space is arbitrary, and only the range of the outer map must be
finite-dimensional.

`LinearMap.rangeCoordinates` generalizes `gradedImageCoordinateEquiv` and
`gradedImageCoordinateMap`, and `LinearMap.rangeCoordinates_eq_zero_iff` generalizes
`gradedImageCoordinateMap_eq_zero_iff`, in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/GradedRank.lean` at the
same revision, from a field to a division ring.

`LinearMap.finrank_range_pi_le_sum` and `LinearMap.exists_ne_zero_of_sum_finrank_range_lt` are
the source's lemmas of the same names in `ArkLib/ToMathlib/LinearAlgebra/FiniteDimensional.lean`
at the same revision, generalized from a field to a division ring. The second no longer assumes
that the source is finite-dimensional: a strict surplus makes its dimension positive, which
forces finite-dimensionality.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

@[expose] public section

/-- If a linear map is injective on `B` and maps `B` onto `A`, then `B` and `A`
have the same dimension. -/
lemma LinearMap.finrank_eq_of_map_eq {F M N : Type*} [Field F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (B : Submodule F M) (A : Submodule F N)
    (hinj : ∀ p ∈ B, f p = 0 → p = 0) (hmap : B.map f = A) :
    Module.finrank F B = Module.finrank F A := by
  have hg : Function.Injective (f.domRestrict B) := by
    rw [← LinearMap.ker_eq_bot]
    ext p
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext (hinj p.1 p.2 h), fun h => by rw [h]; simp⟩
  rw [← LinearMap.finrank_range_of_inj hg, LinearMap.range_domRestrict, hmap]

/-- A finite-dimensional space of dimension `n` has a basis indexed by `Fin n` whose first
`finrank F N` vectors lie in a prescribed subspace `N`. -/
lemma Submodule.exists_adapted_basis {F M : Type*} [Field F] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (N : Submodule F M) {n : ℕ}
    (hn : Module.finrank F M = n) :
    ∃ b : Module.Basis (Fin n) F M,
      ∀ j : Fin n, (j : ℕ) < Module.finrank F N → b j ∈ N := by
  classical
  obtain ⟨K, hK⟩ := N.exists_isCompl
  set t := Module.finrank F N with ht
  set u := Module.finrank F K with hu
  have htu : t + u = n := by rw [ht, hu, Submodule.finrank_add_eq_of_isCompl hK, hn]
  set b₀ : Module.Basis (Fin t ⊕ Fin u) F M :=
    ((Module.finBasis F N).prod (Module.finBasis F K)).map (N.prodEquivOfIsCompl K hK)
      with hb₀
  set e : Fin t ⊕ Fin u ≃ Fin n := finSumFinEquiv.trans (finCongr htu) with he
  refine ⟨b₀.reindex e, fun j hj => ?_⟩
  have hsymm : e.symm j = Sum.inl ⟨(j : ℕ), hj⟩ := by
    rw [Equiv.symm_apply_eq]
    rw [he]
    simp [finSumFinEquiv_apply_left]
  rw [Module.Basis.reindex_apply, hsymm, hb₀]
  simp only [Module.Basis.map_apply]
  rw [Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_snd]
  simp only [ZeroMemClass.coe_zero, add_zero]
  rw [Module.Basis.prod_apply_inl_fst]
  exact ((Module.finBasis F N) ⟨(j : ℕ), hj⟩).2

/-- Rank–nullity with an exhibited part of the kernel. If `K` maps injectively into `ker f`, then
`f` loses at least `finrank K` dimensions. The injection need not span the kernel, so the result
is an upper bound on the rank of `f`, not an equality. Finite-dimensionality of `V` is needed:
otherwise `finrank` of the range may be positive while `finrank V = 0`. -/
theorem LinearMap.finrank_range_le_sub_of_injective_ker {K V V₂ W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] V₂) (g : W →ₗ[K] LinearMap.ker f)
    (hg : Function.Injective g) :
    Module.finrank K (LinearMap.range f) ≤ Module.finrank K V - Module.finrank K W := by
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hrankNullity := f.finrank_range_add_finrank_ker
  omega

/-- Precomposition cannot enlarge the range: `finrank (range (g ∘ f)) ≤ finrank (range g)`.
The range of `g` must be finite-dimensional, since `finrank` of an infinite-dimensional space is
zero. -/
theorem LinearMap.finrank_range_comp_le_left {K V V₂ V₃ : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃] (g : V₂ →ₗ[K] V₃) (f : V →ₗ[K] V₂)
    [FiniteDimensional K (LinearMap.range g)] :
    Module.finrank K (LinearMap.range (g ∘ₗ f)) ≤ Module.finrank K (LinearMap.range g) :=
  Submodule.finrank_mono (LinearMap.range_comp_le_range f g)

/-! ### Coordinates on the range -/

/-- Coordinates of a linear map on its own finite-dimensional range: `f` followed by the
coordinates of a chosen basis of `range f`, indexed by `Fin (finrank (range f))`. The target has
exactly the rank of `f`, and `f v = 0` exactly when these coordinates vanish
(`LinearMap.rangeCoordinates_eq_zero_iff`). The basis is chosen noncanonically. -/
noncomputable def LinearMap.rangeCoordinates {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    [Module.Finite K (LinearMap.range f)] :
    V →ₗ[K] (Fin (Module.finrank K (LinearMap.range f)) → K) :=
  ((Module.finBasis K (LinearMap.range f)).equivFun.toLinearMap).comp f.rangeRestrict

/-- Passing to coordinates on the range loses no equation: `rangeCoordinates f v = 0` if and
only if `f v = 0`. -/
theorem LinearMap.rangeCoordinates_eq_zero_iff {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    [Module.Finite K (LinearMap.range f)] (v : V) :
    f.rangeCoordinates v = 0 ↔ f v = 0 := by
  rw [rangeCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff, ← Subtype.coe_inj]
  rfl

/-- The coordinate map has the kernel of `f`. -/
theorem LinearMap.ker_rangeCoordinates {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    [Module.Finite K (LinearMap.range f)] :
    LinearMap.ker f.rangeCoordinates = LinearMap.ker f := by
  ext v
  exact f.rangeCoordinates_eq_zero_iff v

/-- The coordinate map is onto `K^(finrank (range f))`, so no coordinate is redundant. -/
theorem LinearMap.rangeCoordinates_surjective {K V W : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    [Module.Finite K (LinearMap.range f)] :
    Function.Surjective f.rangeCoordinates := by
  rw [rangeCoordinates, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp f.surjective_rangeRestrict

/-! ### Joint kernels of finite families -/

/-- The rank of a finite family of linear maps, taken jointly as `LinearMap.pi φ`, is at most the
sum of their ranks. Only the source must be finite-dimensional; the targets are arbitrary. The
inequality can be strict, for instance when two maps of the family coincide. -/
theorem LinearMap.finrank_range_pi_le_sum {K V ι : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype ι]
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (φ : ∀ i, V →ₗ[K] W i) :
    Module.finrank K (LinearMap.range (LinearMap.pi φ)) ≤
      ∑ i, Module.finrank K (LinearMap.range (φ i)) := by
  let includeRange : LinearMap.range (LinearMap.pi φ) →ₗ[K] (∀ i, LinearMap.range (φ i)) :=
    { toFun y i := ⟨y.1 i, by
        obtain ⟨v, hv⟩ := y.2
        exact ⟨v, congrFun hv i⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hinj : Function.Injective includeRange := fun x y hxy =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun hxy i))
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans_eq
    (Module.finrank_pi_fintype K)

/-- If the dimension of `V` exceeds the sum of the ranks of a finite family of linear maps on `V`,
then some nonzero vector lies in the kernel of every map of the family. This is rank–nullity for
the joint map `LinearMap.pi φ`, whose rank is at most the sum
(`LinearMap.finrank_range_pi_le_sum`). No finiteness assumption on `V` is needed: the surplus
makes `finrank K V` positive, hence `V` finite-dimensional. The inequality must be strict: the
identity map of `K` has rank `1 = finrank K K` and trivial kernel. -/
theorem LinearMap.exists_ne_zero_of_sum_finrank_range_lt {K V ι : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fintype ι]
    {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (φ : ∀ i, V →ₗ[K] W i)
    (hsurplus : ∑ i, Module.finrank K (LinearMap.range (φ i)) < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, φ i v = 0 := by
  have : Module.Finite K V := Module.finite_of_finrank_pos (Nat.zero_lt_of_lt hsurplus)
  have hrank := (LinearMap.finrank_range_pi_le_sum φ).trans_lt hsurplus
  have hnull := (LinearMap.pi φ).finrank_range_add_finrank_ker
  have hker : LinearMap.ker (LinearMap.pi φ) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hnull
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, fun i => congrFun (LinearMap.mem_ker.mp hv) i⟩
