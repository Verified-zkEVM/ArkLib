/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Avoidance
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum

/-!
# Deterministic avoidance for Rojas projection parameters

This file bounds the bad moment-curve parameters for the simultaneous linear
projections in Rojas Steps 0--3.  The result is geometric and does not enumerate
roots: any explicit list longer than the stated bound contains a good value.
The Mathlib collision polynomials and root finsets below are proof-only;
runtime selection remains the executable candidate scan.
-/

@[expose] public section

namespace ArkLib.Rojas

open Polynomial



section ProjectionCollisions

variable {K : Type*} [Field K]
variable {s : ℕ}

/-- The moment-curve projection `θ(ε) = -∑ ε^(i+1) ζᵢ` of one point. -/
noncomputable def projectionPolynomial (point : Fin s → K) : K[X] :=
  ∑ i, C (-point i) * X ^ (i.val + 1)

@[simp]
theorem coeff_projectionPolynomial (point : Fin s → K) (i : Fin s) :
    (projectionPolynomial point).coeff (i.val + 1) = -point i := by
  simp [projectionPolynomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Fin.val_inj]

theorem eval_projectionPolynomial (point : Fin s → K) (ε : K) :
    (projectionPolynomial point).eval ε =
      -∑ i, ε ^ (i.val + 1) * point i := by
  rw [projectionPolynomial]
  change Polynomial.evalRingHom ε (∑ i, C (-point i) * X ^ (i.val + 1)) = _
  rw [map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- The base projection, the `s` Step-2 projections, and the `s` Step-3
projections. -/
abbrev ProjectionKind (s : ℕ) := Unit ⊕ (Fin s ⊕ Fin s)

/-- Constant offset added to the base projection by one Step-1--3 family. -/
def projectionOffset (α : K) : ProjectionKind s → (Fin s → K) → K
  | .inl _, _ => 0
  | .inr (.inl i), point => point i
  | .inr (.inr i), point => -α * point i

/-- One of the `2s+1` projection polynomials attached to a point. -/
noncomputable def shiftedProjectionPolynomial
    (α : K) (kind : ProjectionKind s) (point : Fin s → K) : K[X] :=
  projectionPolynomial point + C (projectionOffset α kind point)

@[simp]
theorem eval_shiftedProjectionPolynomial_base (α ε : K) (point : Fin s → K) :
    (shiftedProjectionPolynomial α (.inl ()) point).eval ε =
      -∑ i, ε ^ (i.val + 1) * point i := by
  simp [shiftedProjectionPolynomial, projectionOffset, eval_projectionPolynomial]

@[simp]
theorem eval_shiftedProjectionPolynomial_plus
    (α ε : K) (point : Fin s → K) (i : Fin s) :
    (shiftedProjectionPolynomial α (.inr (.inl i)) point).eval ε =
      -∑ j, ε ^ (j.val + 1) * point j + point i := by
  simp [shiftedProjectionPolynomial, projectionOffset, eval_projectionPolynomial]

@[simp]
theorem eval_shiftedProjectionPolynomial_minus
    (α ε : K) (point : Fin s → K) (i : Fin s) :
    (shiftedProjectionPolynomial α (.inr (.inr i)) point).eval ε =
      -∑ j, ε ^ (j.val + 1) * point j - α * point i := by
  simp [shiftedProjectionPolynomial, projectionOffset, eval_projectionPolynomial,
    sub_eq_add_neg]

/-- The collision polynomial for two points in one projection family. -/
noncomputable def collisionPolynomial
    (α : K) (kind : ProjectionKind s) (left right : Fin s → K) : K[X] :=
  shiftedProjectionPolynomial α kind left -
    shiftedProjectionPolynomial α kind right

theorem natDegree_projectionPolynomial_le (point : Fin s → K) :
    (projectionPolynomial point).natDegree ≤ s := by
  refine (Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    (fun i ↦ C (-point i) * X ^ (i.val + 1)) ?_)
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem natDegree_shiftedProjectionPolynomial_le
    (α : K) (kind : ProjectionKind s) (point : Fin s → K) :
    (shiftedProjectionPolynomial α kind point).natDegree ≤ s := by
  exact (Polynomial.natDegree_add_le _ _).trans <| max_le
    (natDegree_projectionPolynomial_le point) (by simp)

theorem natDegree_collisionPolynomial_le
    (α : K) (kind : ProjectionKind s) (left right : Fin s → K) :
    (collisionPolynomial α kind left right).natDegree ≤ s := by
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    (natDegree_shiftedProjectionPolynomial_le α kind left)
    (natDegree_shiftedProjectionPolynomial_le α kind right)

/-- Distinct affine points give a nonzero collision polynomial in every one
of the `2s+1` shifted projection families.  Its positive-degree coefficients
already encode the coordinate differences, independently of the offset. -/
theorem collisionPolynomial_ne_zero
    (α : K) (kind : ProjectionKind s) {left right : Fin s → K}
    (hdistinct : left ≠ right) : collisionPolynomial α kind left right ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, left i ≠ right i := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hdistinct (funext h)
  intro hzero
  have hcoeff := congrArg (fun polynomial : K[X] ↦ polynomial.coeff (i.val + 1)) hzero
  simp only [collisionPolynomial, shiftedProjectionPolynomial, coeff_sub,
    coeff_add, coeff_projectionPolynomial, coeff_C_succ, add_zero,
    sub_neg_eq_add, coeff_zero] at hcoeff
  exact hi (neg_add_eq_zero.mp hcoeff)

/-- Unordered pairs of distinct point indices, represented in increasing
order. -/
def pointPairs (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ.product Finset.univ).filter fun pair ↦ pair.1 < pair.2

@[simp]
theorem card_pointPairs (M : ℕ) : (pointPairs M).card = M.choose 2 := by
  simpa [pointPairs] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin M))))

/-- All collision polynomials for `2s+1` families and all unordered point
pairs. -/
noncomputable def collisionPolynomials {M : ℕ} (α : K)
    (points : Fin M → Fin s → K) : Finset K[X] := by
  classical
  exact ((Finset.univ : Finset (ProjectionKind s)).product (pointPairs M)).image
    fun index ↦ collisionPolynomial α index.1
      (points index.2.1) (points index.2.2)

theorem card_collisionPolynomials_le {M : ℕ} (α : K)
    (points : Fin M → Fin s → K) :
    (collisionPolynomials α points).card ≤ (2 * s + 1) * M.choose 2 := by
  classical
  rw [collisionPolynomials]
  refine (Finset.card_image_le).trans_eq ?_
  simp [ProjectionKind, card_pointPairs]
  omega

theorem collisionPolynomials_nonzero {M : ℕ} (α : K)
    {points : Fin M → Fin s → K} (hpoints : Function.Injective points) :
    ∀ polynomial ∈ collisionPolynomials α points, polynomial ≠ 0 := by
  classical
  intro polynomial hpolynomial
  rw [collisionPolynomials] at hpolynomial
  obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hpolynomial
  apply collisionPolynomial_ne_zero
  apply hpoints.ne
  have hpair := (Finset.mem_product.mp hindex).2
  exact ne_of_lt (Finset.mem_filter.mp hpair).2

theorem collisionPolynomials_degree_le {M : ℕ} (α : K)
    (points : Fin M → Fin s → K) :
    ∀ polynomial ∈ collisionPolynomials α points, polynomial.natDegree ≤ s := by
  classical
  intro polynomial hpolynomial
  rw [collisionPolynomials] at hpolynomial
  obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hpolynomial
  exact natDegree_collisionPolynomial_le _ _ _ _

/-- Union of roots of the collision polynomials.  When the input points are
distinct, these are exactly the parameters causing a collision in some family;
for repeated points the corresponding zero collision polynomial has no stored
root multiset. -/
noncomputable def badProjectionParameters {M : ℕ} (α : K)
    (points : Fin M → Fin s → K) : Finset K := by
  classical
  exact (collisionPolynomials α points).biUnion
    fun polynomial ↦ polynomial.roots.toFinset

/-- The exact union-bound budget used by deterministic specialization. -/
theorem card_badProjectionParameters_le {M : ℕ} (α : K)
    (points : Fin M → Fin s → K) :
    (badProjectionParameters α points).card ≤
      s * (2 * s + 1) * M.choose 2 := by
  classical
  rw [badProjectionParameters]
  calc
    ((collisionPolynomials α points).biUnion
        fun polynomial ↦ polynomial.roots.toFinset).card ≤
        (collisionPolynomials α points).card * s := by
      apply Finset.card_biUnion_le_card_mul
      intro polynomial hpolynomial
      exact (Multiset.toFinset_card_le polynomial.roots).trans
        ((Polynomial.card_roots' polynomial).trans
          (collisionPolynomials_degree_le α points polynomial hpolynomial))
    _ ≤ ((2 * s + 1) * M.choose 2) * s :=
      Nat.mul_le_mul_right s (card_collisionPolynomials_le α points)
    _ = s * (2 * s + 1) * M.choose 2 := by ring

/-- An explicit candidate list longer than
`s * (2s+1) * choose(M,2)` contains a parameter for which the base, all
Step-2, and all Step-3 projections are simultaneously injective on `M`
distinct geometric points. -/
theorem exists_parameter_with_injective_projections
    {F : Type*} [Field F] (ι : F →+* K) {M : ℕ} (α : K)
    {points : Fin M → Fin s → K} (hpoints : Function.Injective points)
    (candidates : List F) (hnodup : candidates.Nodup)
    (hlength : s * (2 * s + 1) * M.choose 2 < candidates.length) :
    ∃ ε ∈ candidates, ∀ kind : ProjectionKind s,
      Function.Injective fun j ↦
        (shiftedProjectionPolynomial α kind (points j)).eval (ι ε) := by
  classical
  let polynomials := collisionPolynomials α points
  have hcard : polynomials.card * s ≤ s * (2 * s + 1) * M.choose 2 := by
    calc
      polynomials.card * s ≤ ((2 * s + 1) * M.choose 2) * s :=
        Nat.mul_le_mul_right s (card_collisionPolynomials_le α points)
      _ = s * (2 * s + 1) * M.choose 2 := by ring
  obtain ⟨ε, hε, havoid⟩ := exists_avoiding_finite_polynomials ι polynomials s
    (collisionPolynomials_nonzero α hpoints)
    (collisionPolynomials_degree_le α points) candidates hnodup
    (hcard.trans_lt hlength)
  refine ⟨ε, hε, ?_⟩
  intro kind left right hequal
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmember : collisionPolynomial α kind (points left) (points right) ∈
        polynomials := by
      apply Finset.mem_image.mpr
      exact ⟨(kind, (left, right)), by simp [pointPairs, hlt], rfl⟩
    apply havoid _ hmember
    simpa only [collisionPolynomial, Polynomial.eval_sub, sub_eq_zero] using hequal
  · have hmember : collisionPolynomial α kind (points right) (points left) ∈
        polynomials := by
      apply Finset.mem_image.mpr
      exact ⟨(kind, (right, left)), by simp [pointPairs, hgt], rfl⟩
    apply havoid _ hmember
    simpa only [collisionPolynomial, Polynomial.eval_sub, sub_eq_zero] using hequal.symm

end ProjectionCollisions

end ArkLib.Rojas
