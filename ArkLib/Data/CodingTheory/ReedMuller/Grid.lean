/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.LinearCombination
public import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel

/-!
# Grid points on hyperplanes

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, viewed through `algebraMap`.
The grid `K₀ᵏ` sits inside `Fᵏ` and has `n = q₀ᵏ` points.

A hyperplane `a · x = b` of `Fᵏ` with `a ≠ 0` contains at most `n / q₀ = q₀ᵏ⁻¹` grid points.
This is (7.1) in Section 7 of [CWYZ26].
The paper reads it off a coset of a proper `K₀`-subspace.
The proof here fixes a coordinate `i` with `aᵢ ≠ 0`: the other coordinates determine `zᵢ`.

Consequently, a set of more than `q₀ᵏ⁻¹` grid points is not contained in any hyperplane.
It then has `k + 1` points at which the affine forms `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` are independent.
Their values at those points determine `σ`, which is the form used in Lemma A.1 of [CWYZ26].

The module also counts the grid zeros of a nonzero polynomial over `F`.
This is the Schwartz–Zippel lemma on the grid.

Exponents `k - 1` use subtraction in `ℕ`.
At `k = 0` no hyperplane exists, and the other statements hold trivially.

The [paper page](../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedMuller.gridPoint`: the grid point `z ∈ K₀ᵏ` as a point of `Fᵏ`.

## Main statements

* `ReedMuller.card_grid_inter_hyperplane_le`: a hyperplane holds at most `q₀ᵏ⁻¹` grid points.
* `ReedMuller.eq_zero_of_forall_mem_add_sum_eq_zero`: an affine form vanishing on more than
  `q₀ᵏ⁻¹` grid points is zero.
* `ReedMuller.exists_subset_card_eq_forall_add_sum_eq_zero`: such a set has `k + 1` points
  on which only the zero affine form vanishes.
* `ReedMuller.card_grid_eval_eq_zero_le`: a nonzero polynomial of total degree `D` has at most
  `D q₀ᵏ⁻¹` grid zeros.

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

@[simp]
theorem gridPoint_apply (z : Fin k → K₀) (i : Fin k) : gridPoint F z i = algebraMap K₀ F (z i) :=
  rfl

/-- Distinct grid points of `K₀ᵏ` stay distinct in `Fᵏ`. -/
theorem gridPoint_injective : Function.Injective (gridPoint F : (Fin k → K₀) → Fin k → F) :=
  fun _ _ h ↦ funext fun i ↦ (algebraMap K₀ F).injective (congrFun h i)

variable {F} [Fintype K₀] [DecidableEq F]

/-- A hyperplane `a · x = b` of `Fᵏ` with `a ≠ 0` contains at most `q₀ᵏ⁻¹` points of the grid
`K₀ᵏ`, where `q₀ = |K₀|` and `K₀` embeds in `F` through `algebraMap`. -/
theorem card_grid_inter_hyperplane_le (a : Fin k → F) (ha : a ≠ 0) (b : F) :
    #{z : Fin k → K₀ | ∑ i, a i * algebraMap K₀ F (z i) = b} ≤ Fintype.card K₀ ^ (k - 1) := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  calc #{z : Fin k → K₀ | ∑ i, a i * algebraMap K₀ F (z i) = b}
      ≤ #(univ : Finset ({j // j ≠ i} → K₀)) := by
        refine card_le_card_of_injOn (fun z j ↦ z j) (fun _ _ ↦ mem_coe.mpr (mem_univ _)) ?_
        intro z hz z' hz' h
        simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hz hz'
        have hoff : ∀ j, j ≠ i → z j = z' j := fun j hj ↦ congrFun h ⟨j, hj⟩
        have hsum : ∑ j, a j * (algebraMap K₀ F (z j) - algebraMap K₀ F (z' j)) = 0 := by
          simp only [mul_sub, sum_sub_distrib, hz, hz', sub_self]
        rw [sum_eq_single i (fun j _ hj ↦ by simp [hoff j hj]) (by simp)] at hsum
        funext j
        by_cases hj : j = i
        · subst hj
          exact (algebraMap K₀ F).injective
            (sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hi))
        · exact hoff j hj
    _ = Fintype.card K₀ ^ (k - 1) := by simp

omit [DecidableEq F] in
/-- Let `T` be a set of more than `q₀ᵏ⁻¹` points of the grid `K₀ᵏ`, where `q₀ = |K₀|`.
If the affine form `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` over `F` vanishes on `T`, then `σ = 0`. -/
theorem eq_zero_of_forall_mem_add_sum_eq_zero (T : Finset (Fin k → K₀))
    (hT : Fintype.card K₀ ^ (k - 1) < #T) (σ : Fin (k + 1) → F)
    (h : ∀ z ∈ T, σ 0 + ∑ i, σ i.succ * algebraMap K₀ F (z i) = 0) : σ = 0 := by
  classical
  by_contra hσ
  by_cases ht : (fun i : Fin k ↦ σ i.succ) = 0
  · have h0 : σ 0 ≠ 0 := fun h0 ↦ hσ (funext fun j ↦ Fin.cases h0 (fun i ↦ congrFun ht i) j)
    obtain ⟨z, hz⟩ : T.Nonempty := card_pos.mp (by omega)
    have := h z hz
    have hi : ∀ i : Fin k, σ i.succ = 0 := fun i ↦ by simpa using congrFun ht i
    simp only [hi, zero_mul, sum_const_zero, add_zero] at this
    exact h0 this
  · have hsub : T ⊆ ({z : Fin k → K₀ | ∑ i, σ i.succ * algebraMap K₀ F (z i) = -σ 0} :
        Finset _) :=
      fun z hz ↦ mem_filter.mpr ⟨mem_univ _, by linear_combination h z hz⟩
    have := (card_le_card hsub).trans (card_grid_inter_hyperplane_le _ ht _)
    omega

omit [DecidableEq F] in
/-- Let `T` be a set of more than `q₀ᵏ⁻¹` points of the grid `K₀ᵏ`, where `q₀ = |K₀|`.
Then `T` has a subset `t` of `k + 1` points with the following property.
If the affine form `σ₀ + σ₁ x₁ + ⋯ + σₖ xₖ` over `F` vanishes on `t`, then `σ = 0`. -/
theorem exists_subset_card_eq_forall_add_sum_eq_zero (T : Finset (Fin k → K₀))
    (hT : Fintype.card K₀ ^ (k - 1) < #T) :
    ∃ t ⊆ T, #t = k + 1 ∧ ∀ σ : Fin (k + 1) → F,
      (∀ z ∈ t, σ 0 + ∑ i, σ i.succ * algebraMap K₀ F (z i) = 0) → σ = 0 := by
  classical
  set v : (Fin k → K₀) → Fin (k + 1) → F := fun z ↦ Fin.cons 1 (fun i ↦ algebraMap K₀ F (z i))
  have hv : ∀ σ z, σ ⬝ᵥ v z = σ 0 + ∑ i, σ i.succ * algebraMap K₀ F (z i) := by
    intro σ z
    simp [v, dotProduct, Fin.sum_univ_succ]
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
    have hσ := eq_zero_of_forall_mem_add_sum_eq_zero T hT (fun j ↦ f (Pi.single j 1))
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

/-- A nonzero polynomial `p` over `F` in `k` variables has at most `deg p · q₀ᵏ⁻¹` zeros on the
grid `K₀ᵏ`, where `deg` is the total degree and `q₀ = |K₀|`. -/
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
    set S : Finset F := univ.image (algebraMap K₀ F)
    have hS : #S = Fintype.card K₀ := card_image_of_injective _ (algebraMap K₀ F).injective
    have himage : (({z : Fin (k + 1) → K₀ | MvPolynomial.eval (gridPoint F z) p = 0} :
        Finset _).image (gridPoint F)) =
        {x ∈ Fintype.piFinset (fun _ : Fin (k + 1) ↦ S) | MvPolynomial.eval x p = 0} := by
      ext x
      simp only [mem_image, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, S]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨fun i ↦ ⟨z i, rfl⟩, hz⟩
      · rintro ⟨hx, hz⟩
        choose z hz' using hx
        refine ⟨z, ?_, funext hz'⟩
        convert hz
        exact funext hz'
    rw [← card_image_of_injective _ (gridPoint_injective F), himage, ← hS]
    exact MvPolynomial.card_filter_eval_eq_zero_le hp S

end ReedMuller
