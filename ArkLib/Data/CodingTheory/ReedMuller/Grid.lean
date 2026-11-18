/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import ArkLib.ToMathlib.LinearAlgebra.PiFinsetHyperplane
public import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel
public import Mathlib.Combinatorics.Nullstellensatz

/-!
# Grid points on hyperplanes

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, viewed through `algebraMap`.
The grid `K₀ᵏ` sits inside `Fᵏ` and has `n = q₀ᵏ` points.

A hyperplane `a ⬝ᵥ x = b` of `Fᵏ` with `a ≠ 0` holds at most `n / q₀ = q₀ᵏ⁻¹` grid points.
This is (7.1) in Section 7 of [CWYZ26].
The paper reads it off a coset of a proper `K₀`-subspace.
The proof here uses the general bound for a grid `Sᵏ` over any finite set `S`.

A set of more than `q₀ᵏ⁻¹` grid points therefore lies in no hyperplane.
It has `k + 1` points where only the zero affine form `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` vanishes.
This is the form used in Lemma A.1 of [CWYZ26].

The module also counts the grid zeros of a nonzero polynomial over `F`.
This is the Schwartz–Zippel lemma on the grid.

Exponents `k - 1` use subtraction in `ℕ`.
At `k = 0` no hyperplane exists, and the other statements hold trivially.

The [paper page](../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.gridPoint`: the grid point `z ∈ K₀ᵏ` as a point of `Fᵏ`.
* `ReedMuller.gridValues`: the image of `K₀` in `F`.

## Main statements

* `ReedMuller.gridPoint_apply` and `ReedMuller.gridPoint_injective`: the embedding.
* `ReedMuller.eval_gridPoint_map`: evaluation at grid points commutes with base change.
* `ReedMuller.card_gridValues` and `ReedMuller.card_filter_gridPoint`: transport to `F`.
* `ReedMuller.card_grid_inter_hyperplane_le`: a hyperplane holds at most `q₀ᵏ⁻¹` grid points.
* `ReedMuller.eq_zero_of_forall_mem_add_dotProduct_eq_zero`: an affine form vanishing on more
  than `q₀ᵏ⁻¹` grid points is zero.
* `ReedMuller.exists_subset_card_eq_forall_add_dotProduct_eq_zero`: such a set has `k + 1`
  points on which only the zero affine form vanishes.
* `ReedMuller.card_grid_eval_eq_zero_le`: a nonzero polynomial of total degree `D` has at most
  `D q₀ᵏ⁻¹` grid zeros.
* `ReedMuller.eq_zero_of_forall_eval_gridPoint_eq_zero`: a polynomial of degree below `q₀` in
  each variable that vanishes on the grid is zero.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open Finset

variable {K₀ : Type*} (F : Type*) [Field K₀] [Field F] [Algebra K₀ F] {k : ℕ}

/-- The grid point `z ∈ K₀ᵏ` as a point of `Fᵏ`. -/
def gridPoint (z : Fin k → K₀) : Fin k → F := fun i ↦ algebraMap K₀ F (z i)

/-- The coordinates of a grid point are the images of its `K₀` coordinates. -/
@[simp]
theorem gridPoint_apply (z : Fin k → K₀) (i : Fin k) : gridPoint F z i = algebraMap K₀ F (z i) :=
  rfl

/-- Distinct grid points of `K₀ᵏ` stay distinct in `Fᵏ`. -/
theorem gridPoint_injective : Function.Injective (gridPoint F : (Fin k → K₀) → Fin k → F) :=
  fun _ _ h ↦ funext fun i ↦ (algebraMap K₀ F).injective (congrFun h i)

/-- Let `K₀ ⊆ F ⊆ F'` be a tower of fields, and `P` a polynomial over `F` in `k` variables.
Mapping `P` into `F'` and evaluating at a grid point gives the image of the value over `F`. -/
theorem eval_gridPoint_map {F' : Type*} [Field F'] [Algebra F F'] [Algebra K₀ F']
    [IsScalarTower K₀ F F'] (z : Fin k → K₀) (P : MvPolynomial (Fin k) F) :
    MvPolynomial.eval (gridPoint F' z) (P.map (algebraMap F F')) =
      algebraMap F F' (MvPolynomial.eval (gridPoint F z) P) := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  simp [IsScalarTower.algebraMap_apply K₀ F F']

variable {F} [Fintype K₀] [DecidableEq F]

variable (K₀ F) in
/-- The values of `K₀` inside `F`, the side of the grid `K₀ᵏ` inside `Fᵏ`. -/
def gridValues : Finset F := univ.image (algebraMap K₀ F)

/-- The side of the grid has `q₀ = |K₀|` elements. -/
@[simp]
theorem card_gridValues : #(gridValues K₀ F) = Fintype.card K₀ :=
  card_image_of_injective _ (algebraMap K₀ F).injective

/-- Grid points of `K₀ᵏ` with a property of their image in `Fᵏ` are counted in `Fᵏ`.

There they are the points of the grid over the image of `K₀` with that property. -/
theorem card_filter_gridPoint (p : (Fin k → F) → Prop) [DecidablePred p] :
    #{z : Fin k → K₀ | p (gridPoint F z)} =
      #{x ∈ Fintype.piFinset fun _ : Fin k ↦ gridValues K₀ F | p x} := by
  classical
  rw [← card_image_of_injective _ (gridPoint_injective F)]
  congr 1
  ext x
  simp only [mem_image, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, gridValues]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fun i ↦ ⟨z i, rfl⟩, hz⟩
  · rintro ⟨hx, hz⟩
    choose z hz' using hx
    refine ⟨z, ?_, funext hz'⟩
    convert hz
    exact funext hz'


/-- A hyperplane `a ⬝ᵥ x = b` of `Fᵏ` with `a ≠ 0` contains at most `q₀ᵏ⁻¹` grid points.

Here `q₀ = |K₀|`, and the grid `K₀ᵏ` embeds in `Fᵏ` through `algebraMap`. -/
theorem card_grid_inter_hyperplane_le (a : Fin k → F) (ha : a ≠ 0) (b : F) :
    #{z : Fin k → K₀ | a ⬝ᵥ gridPoint F z = b} ≤ Fintype.card K₀ ^ (k - 1) := by
  cases k with
  | zero => exact absurd (Subsingleton.elim a 0) ha
  | succ k =>
    rw [card_filter_gridPoint (fun x ↦ a ⬝ᵥ x = b), ← card_gridValues (F := F)]
    exact Fintype.card_filter_piFinset_dotProduct_eq_le _ ha b

omit [DecidableEq F] in
/-- Let `T` be a set of more than `q₀ᵏ⁻¹` points of the grid `K₀ᵏ`, where `q₀ = |K₀|`.

If the affine form `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` over `F` vanishes on `T`, then `σ = 0`. -/
theorem eq_zero_of_forall_mem_add_dotProduct_eq_zero (T : Finset (Fin k → K₀))
    (hT : Fintype.card K₀ ^ (k - 1) < #T) (σ : Fin (k + 1) → F)
    (h : ∀ z ∈ T, σ 0 + Fin.tail σ ⬝ᵥ gridPoint F z = 0) : σ = 0 := by
  classical
  cases k with
  | zero =>
    have := card_le_univ T
    simp at this hT
    omega
  | succ k =>
    refine Fintype.eq_zero_of_forall_mem_add_dotProduct_eq_zero (gridValues K₀ F)
      (T := T.image (gridPoint F)) (fun x hx ↦ ?_) ?_ σ ?_
    · obtain ⟨z, -, rfl⟩ := mem_image.mp hx
      exact Fintype.mem_piFinset.mpr fun i ↦ mem_image.mpr ⟨z i, mem_univ _, rfl⟩
    · rwa [card_image_of_injective _ (gridPoint_injective F), card_gridValues]
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact h z hz

omit [DecidableEq F] in
/-- Let `T` be a set of more than `q₀ᵏ⁻¹` points of the grid `K₀ᵏ`, where `q₀ = |K₀|`.

Then `T` has a subset `t` of `k + 1` points with the following property.

If the affine form `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` over `F` vanishes on `t`, then `σ = 0`. -/
theorem exists_subset_card_eq_forall_add_dotProduct_eq_zero (T : Finset (Fin k → K₀))
    (hT : Fintype.card K₀ ^ (k - 1) < #T) :
    ∃ t ⊆ T, #t = k + 1 ∧ ∀ σ : Fin (k + 1) → F,
      (∀ z ∈ t, σ 0 + Fin.tail σ ⬝ᵥ gridPoint F z = 0) → σ = 0 := by
  classical
  set v : (Fin k → K₀) → Fin (k + 1) → F := fun z ↦ Fin.cons 1 (gridPoint F z)
  have hv : ∀ σ z, σ ⬝ᵥ v z = σ 0 + Fin.tail σ ⬝ᵥ gridPoint F z := by
    intro σ z
    simp [v, dotProduct, Fin.sum_univ_succ, Fin.tail]
  have hvinj : Function.Injective v := by
    intro z z' h
    funext i
    exact (algebraMap K₀ F).injective (by simpa [v] using congrFun h i.succ)
  have hspan : Submodule.span F (v '' T) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf, hle⟩ :=
      (Submodule.span F (v '' T)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    have hfun : ∀ w, f w = (fun j ↦ f (Pi.single j 1)) ⬝ᵥ w := by
      intro w
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      simp only [dotProduct, mul_comm]
      congr 1
      ext x
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have hσ := eq_zero_of_forall_mem_add_dotProduct_eq_zero T hT (fun j ↦ f (Pi.single j 1))
      fun z hz ↦ by
        refine (hv (fun j ↦ f (Pi.single j 1)) z).symm.trans ?_
        rw [← hfun]
        exact hle (Submodule.subset_span ⟨z, hz, rfl⟩)
    exact hf (LinearMap.ext fun w ↦ by rw [hfun, hσ, zero_dotProduct, LinearMap.zero_apply])
  obtain ⟨b, hbT, hbspan, hbind⟩ := exists_linearIndependent F (v '' T)
  set t := T.filter fun z ↦ v z ∈ b
  have himage : ((t.image v : Finset _) : Set (Fin (k + 1) → F)) = b := by
    ext w
    simp only [coe_image, coe_filter, Set.mem_image, Set.mem_ofPred_eq, t]
    constructor
    · rintro ⟨z, ⟨-, hz⟩, rfl⟩
      exact hz
    · intro hw
      obtain ⟨z, hz, rfl⟩ := hbT hw
      exact ⟨z, ⟨hz, hw⟩, rfl⟩
  refine ⟨t, filter_subset _ _, ?_, fun σ hσ ↦ ?_⟩
  · have h := finrank_span_finset_eq_card (R := F) (s := t.image v) (by rw [himage]; exact hbind)
    rw [himage, hbspan, hspan, finrank_top, Module.finrank_fin_fun,
      card_image_of_injective t hvinj] at h
    exact h.symm
  · have hzero : ∀ w ∈ Submodule.span F b, σ ⬝ᵥ w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨z, hz, rfl⟩ := hbT hw
        rw [hv]
        exact hσ z (mem_filter.mpr ⟨hz, hw⟩)
      | zero => exact dotProduct_zero σ
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
    funext j
    have := hzero (Pi.single j 1) (by rw [hbspan, hspan]; trivial)
    simpa using this

/-- A nonzero polynomial `p` over `F` in `k` variables has few zeros on the grid `K₀ᵏ`.

There are at most `deg p · q₀ᵏ⁻¹` of them, where `deg` is the total degree and `q₀ = |K₀|`. -/
theorem card_grid_eval_eq_zero_le {p : MvPolynomial (Fin k) F} (hp : p ≠ 0) :
    #{z : Fin k → K₀ | MvPolynomial.eval (gridPoint F z) p = 0} ≤
      p.totalDegree * Fintype.card K₀ ^ (k - 1) := by
  classical
  cases k with
  | zero =>
    rw [MvPolynomial.eq_C_of_isEmpty p] at hp ⊢
    have hc : p.coeff 0 ≠ 0 := fun h ↦ hp (by simp [h])
    simp [hc]
  | succ k =>
    rw [card_filter_gridPoint (fun x ↦ MvPolynomial.eval x p = 0), ← card_gridValues (F := F)]
    exact MvPolynomial.card_filter_eval_eq_zero_le hp _

omit [DecidableEq F] in
/-- Let `P` be a polynomial over `F` in `k` variables of degree below `q₀ = |K₀|` in each variable.
If `P` vanishes at every point of the grid `K₀ᵏ`, then `P = 0`. -/
theorem eq_zero_of_forall_eval_gridPoint_eq_zero {P : MvPolynomial (Fin k) F}
    (hP : ∀ i, P.degreeOf i < Fintype.card K₀)
    (h : ∀ z : Fin k → K₀, MvPolynomial.eval (gridPoint F z) P = 0) : P = 0 := by
  classical
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset P (fun _ ↦ gridValues K₀ F)
    (by simpa using hP) fun y hy ↦ ?_
  simp only [gridValues, mem_image, mem_univ, true_and] at hy
  choose z hz using hy
  convert h z
  funext i
  simp [hz i]

end ReedMuller
