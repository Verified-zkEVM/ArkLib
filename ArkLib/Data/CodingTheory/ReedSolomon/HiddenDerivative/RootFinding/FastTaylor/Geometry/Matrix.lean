/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Explicit projection matrices from a certified direction

A supplied nonzero pivot completes a direction to a basis with that direction last.
Both matrices execute directly; selection of a suitable direction remains upstream.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Geometry.ProjectionMatrix

variable {E : Type*} [Field E] {r : ℕ}

/-- Standard coordinate columns away from the pivot, followed by the supplied direction. -/
def forward (v : Fin (r + 1) → E) (pivot : Fin (r + 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun i =>
  Fin.lastCases (v i) (fun j => if i = pivot.succAbove j then 1 else 0)

/-- Explicit inverse-coordinate rows; only the certified pivot coefficient is divided out. -/
def backward (v : Fin (r + 1) → E) (pivot : Fin (r + 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Fin.lastCases (fun i => if i = pivot then (v pivot)⁻¹ else 0)
    (fun j i => (if i = pivot.succAbove j then 1 else 0) -
      v (pivot.succAbove j) * (if i = pivot then (v pivot)⁻¹ else 0))

/-- Return the concrete coordinate matrix and its candidate inverse without witness extraction. -/
def matrices (v : Fin (r + 1) → E) (pivot : Fin (r + 1)) :=
  (forward v pivot, backward v pivot)

@[simp] theorem last_column (v : Fin (r + 1) → E) (pivot : Fin (r + 1)) (i : Fin (r + 1)) :
    forward v pivot i (Fin.last r) = v i := by simp [forward]

@[simp] theorem forward_pivot (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (x : Fin (r + 1) → E) :
    (forward v pivot).mulVec x pivot = v pivot * x (Fin.last r) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, forward]

@[simp] theorem forward_other (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (x : Fin (r + 1) → E) (j : Fin r) :
    (forward v pivot).mulVec x (pivot.succAbove j) =
      x j.castSucc + v (pivot.succAbove j) * x (Fin.last r) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, forward]

@[simp] theorem backward_last (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (u : Fin (r + 1) → E) :
    (backward v pivot).mulVec u (Fin.last r) = (v pivot)⁻¹ * u pivot := by
  simp [Matrix.mulVec, dotProduct, backward]

@[simp] theorem backward_other (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (u : Fin (r + 1) → E) (j : Fin r) :
    (backward v pivot).mulVec u j.castSucc =
      u (pivot.succAbove j) - v (pivot.succAbove j) * ((v pivot)⁻¹ * u pivot) := by
  simp [Matrix.mulVec, dotProduct, backward, sub_mul, Finset.sum_sub_distrib,
    mul_assoc]

/-- The supplied pivot certificate makes the explicit matrices right inverses. -/
theorem forward_mul_backward (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (hp : v pivot ≠ 0) : forward v pivot * backward v pivot = 1 := by
  apply Matrix.mulVec_injective
  funext u i
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  cases i using Fin.succAboveCases pivot with
  | x => simp [hp]
  | p j => simp

/-- The supplied pivot certificate also makes the matrices left inverses. -/
theorem backward_mul_forward (v : Fin (r + 1) → E) (pivot : Fin (r + 1))
    (hp : v pivot ≠ 0) : backward v pivot * forward v pivot = 1 := by
  apply Matrix.mulVec_injective
  funext u i
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  cases i using Fin.lastCases with
  | last => simp [hp]
  | cast j => simp [hp]

variable [BEq E] [LawfulBEq E]

/-- Inspect only the finitely many coordinates, stopping at the first nonzero coefficient. -/
def selectPivot (v : Fin (r + 1) → E) : Option (Fin (r + 1)) :=
  (List.finRange (r + 1)).find? fun i => v i != 0

/-- A selected pivot has the required nonzero coefficient. -/
theorem selectPivot_sound {v : Fin (r + 1) → E} {pivot : Fin (r + 1)}
    (h : selectPivot v = some pivot) : v pivot ≠ 0 := by
  simpa using (List.find?_eq_some_iff_append.mp h).1

/-- Pivot search succeeds for every nonzero direction, without enumerating the field. -/
theorem selectPivot_exists (v : Fin (r + 1) → E) (hv : v ≠ 0) :
    ∃ pivot, selectPivot v = some pivot := by
  cases hs : selectPivot v with
  | some pivot => exact ⟨pivot, rfl⟩
  | none =>
    have hzero := List.find?_eq_none.mp hs
    apply False.elim
    apply hv
    funext i
    simpa using hzero i (List.mem_finRange i)

/-- Construct the two explicit matrices after deterministic coordinate pivot selection. -/
def construct? (v : Fin (r + 1) → E) :
    Option (Matrix (Fin (r + 1)) (Fin (r + 1)) E ×
      Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  (selectPivot v).map (matrices v)

/-- Successful construction returns inverse matrices whose last column is the input direction. -/
theorem construct?_sound (v : Fin (r + 1) → E)
    (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : construct? v = some (M, N)) :
    M * N = 1 ∧ N * M = 1 ∧ ∀ i, M i (Fin.last r) = v i := by
  obtain ⟨pivot, hp, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨forward_mul_backward v pivot (selectPivot_sound hp),
    backward_mul_forward v pivot (selectPivot_sound hp), last_column v pivot⟩

/-- Every nonzero supplied direction admits the executable matrix construction. -/
theorem construct?_exists (v : Fin (r + 1) → E) (hv : v ≠ 0) :
    ∃ M N, construct? v = some (M, N) := by
  obtain ⟨pivot, hp⟩ := selectPivot_exists v hv
  exact ⟨forward v pivot, backward v pivot, by simp [construct?, hp, matrices]⟩

end ReedSolomon.HiddenDerivative.FastTaylor.Geometry.ProjectionMatrix
