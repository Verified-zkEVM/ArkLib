/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Acceptance client for shifted and column-budget polynomial kernels

The first examples use concrete matrices over `ℚ[X]`. A two-by-three matrix with a forced-zero
entry gets per-coordinate budgets from the shifted theorem that are smaller than the uniform
budget, and the bridge lemma shows that the forced zero cannot be replaced by a nonzero constant.
A one-by-three matrix `[1, X, X ^ 2]` with column weights `0, 1, 2` and height `1` shows that the
column of weight above the height receives the zero coordinate.

The remaining examples derive the forms used by Reed–Solomon interpolation: the column rank form
with a rank bound over `RatFunc F`, and the shifted primitive form with `Fin` indices and the
split hypotheses `hdegree`/`hzero`, including the specialization clause recovered from
`Ideal.comp_ne_zero_of_span_range_eq_top`.
-/

open Polynomial

namespace Matrix

/-- A two-by-three matrix with row weights `0, 1` and column weights `0, 1, 1`. Its entry in
row `1` and column `0` has negative weight difference and is zero. -/
private noncomputable def shiftedCanary : Matrix (Fin 2) (Fin 3) ℚ[X] :=
  !![1, X, 0; 0, 1, 1]

private theorem shiftedCanary_entry (i : Fin 2) (j : Fin 3) :
    shiftedCanary i j ∈ degreeLT ℚ (![0, 1, 1] j + 1 - ![0, 1] i) := by
  rw [mem_degreeLT_add_one_sub_iff]
  fin_cases i <;> fin_cases j <;> simp [shiftedCanary]

/-- At height `1` the shifted surplus is `2 + 1 < 2 + 1 + 1`. The shifted theorem gives a kernel
vector with a coordinate of degree at most one and two constant coordinates; the uniform theorem
with entry bound `1` would allow degree up to `2 * 1 / (3 - 2) = 2` in every coordinate. -/
example :
    ∃ v : Fin 3 → ℚ[X], v ≠ 0 ∧ shiftedCanary *ᵥ v = 0 ∧
      v 0 ∈ degreeLT ℚ 2 ∧ v 1 ∈ degreeLT ℚ 1 ∧ v 2 ∈ degreeLT ℚ 1 := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_shifted_degreeLT shiftedCanary ![0, 1] ![0, 1, 1] 1
      (fun i j _ ↦ shiftedCanary_entry i j) (by decide)
  exact ⟨v, hv, hMv, by simpa using hvdegree 0, by simpa using hvdegree 1,
    by simpa using hvdegree 2⟩

/-- The split entry conditions `hdegree`/`hzero` do not hold if the forced-zero entry is replaced
by the constant `1`: its natural degree is `0`, but the budget `degreeLT ℚ (0 + 1 - 1)` is `⊥`. -/
example : (1 : ℚ[X]) ∉ degreeLT ℚ (0 + 1 - 1) := by
  rw [mem_degreeLT_add_one_sub_iff]
  simp

/-- The bridge lemma on a matrix: the hypotheses `hdegree` and `hzero` together are
equivalent to the single `degreeLT` entry hypothesis. -/
example {F : Type*} [Field F] {rows cols : Type*} (M : Matrix rows cols F[X])
    (rowWeight : rows → ℕ) (columnWeight : cols → ℕ) :
    ((∀ i j, rowWeight i ≤ columnWeight j → (M i j).natDegree ≤ columnWeight j - rowWeight i) ∧
        ∀ i j, columnWeight j < rowWeight i → M i j = 0) ↔
      ∀ i j, M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i) := by
  simp only [mem_degreeLT_add_one_sub_iff]
  exact ⟨fun h i j ↦ ⟨h.1 i j, h.2 i j⟩, fun h ↦ ⟨fun i j ↦ (h i j).1, fun i j ↦ (h i j).2⟩⟩

/-- The row `[1, X, X ^ 2]` with column weights `0, 1, 2` at height `1`. -/
private noncomputable def columnCanary : Matrix Unit (Fin 3) ℚ[X] :=
  fun _ j ↦ X ^ (j : ℕ)

/-- The column surplus is `1 * 2 < 2 + 1 + 0`. The column of weight `2` exceeds the height, so the
kernel vector has zero third coordinate and constant second coordinate. The uniform theorem with
entry bound `2` allows degree up to `1 * 2 / (3 - 1) = 1` in every coordinate. -/
example :
    ∃ v : Fin 3 → ℚ[X], v ≠ 0 ∧ columnCanary *ᵥ v = 0 ∧
      v 0 ∈ degreeLT ℚ 2 ∧ v 1 ∈ degreeLT ℚ 1 ∧ v 2 = 0 := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_column_degreeLT columnCanary (fun j ↦ (j : ℕ)) 1
      (fun _ j ↦ by simp [columnCanary]) (by decide)
  refine ⟨v, hv, hMv, by simpa using hvdegree 0, by simpa using hvdegree 1, ?_⟩
  simpa [degreeLT_zero] using hvdegree 2

/-- With no rows, one column of weight at most the height suffices, and the budgets are still
respected. -/
example {F : Type*} [Field F] (M : Matrix Empty (Fin 2) F[X]) :
    ∃ v : Fin 2 → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      v 0 ∈ degreeLT F 1 ∧ v 1 = 0 := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_shifted_degreeLT M (fun _ ↦ 0) ![0, 1] 0
      (fun i ↦ Empty.elim i) (by decide)
  exact ⟨v, hv, hMv, by simpa using hvdegree 0, by simpa [degreeLT_zero] using hvdegree 1⟩

/-- The column consumer shape: a rank bound `n * r` over `RatFunc F` and the surplus
`n * r * (h + 1) < ∑ j, (h + 1 - weight j)` give a primitive kernel vector with
`natDegree ≤ h` and the specialization clause. -/
example {F : Type*} [Field F] {m N n r h : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (weight : Fin N → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ weight j)
    (hrank : (M.map (algebraMap F[X] (RatFunc F))).rank ≤ n * r)
    (hheight : n * r * (h + 1) < ∑ j, (h + 1 - weight j)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧ (∀ j, (v j).natDegree ≤ h) ∧
      Ideal.span (Set.range v) = ⊤ ∧
        ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hvdegree, hspan⟩ :=
    exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le M weight h hdeg _
      (IsFractionRing.injective F[X] (RatFunc F)) hrank hheight
  refine ⟨v, hv, hMv, fun j ↦ ?_, hspan, fun ι z ↦ ?_⟩
  · exact natDegree_le_of_mem_degreeLT_succ
      (degreeLT_mono (Nat.sub_le (h + 1) (weight j)) (hvdegree j))
  · exact Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)

/-- The exact-rank column form over `RatFunc F`, whose surplus is stated with the rank itself, is
the case `s := rank`. -/
example {F : Type*} [Field F] {m N h : ℕ} (M : Matrix (Fin m) (Fin N) F[X])
    (weight : Fin N → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ weight j)
    (hsurplus : (M.map (algebraMap F[X] (RatFunc F))).rank * (h + 1) <
      ∑ j, (h + 1 - weight j)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧ ∀ j, v j ∈ degreeLT F (h + 1 - weight j) :=
  exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le M weight h hdeg _
    (IsFractionRing.injective F[X] (RatFunc F)) le_rfl hsurplus

/-- The shifted primitive form with `Fin` indices, the hypotheses `hdegree`/`hzero`, and the
specialization clause, recovered from the unit-ideal conclusion. -/
example {F : Type*} [Field F] {rows N h : ℕ} (M : Matrix (Fin rows) (Fin N) F[X])
    (rowWeight : Fin rows → ℕ) (columnWeight : Fin N → ℕ)
    (hdegree : ∀ i j, rowWeight i ≤ columnWeight j →
      (M i j).natDegree ≤ columnWeight j - rowWeight i)
    (hzero : ∀ i j, columnWeight j < rowWeight i → M i j = 0)
    (hsurplus : Finset.univ.sum (fun i : Fin rows ↦ h + 1 - rowWeight i) <
      Finset.univ.sum (fun j : Fin N ↦ h + 1 - columnWeight j)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, v j ∈ degreeLT F (h + 1 - columnWeight j)) ∧ Ideal.span (Set.range v) = ⊤ ∧
        ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0 := by
  obtain ⟨v, hv, hMv, hvdegree, hspan⟩ :=
    exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le M rowWeight
      columnWeight h hdegree hzero hsurplus
  exact ⟨v, hv, hMv, hvdegree, hspan, fun ι z ↦
    Ideal.comp_ne_zero_of_span_range_eq_top hspan (eval₂RingHom ι z)⟩

end Matrix

/--
info: 'Polynomial.mem_degreeLT_add_one_sub_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.mem_degreeLT_add_one_sub_iff

/--
info: 'Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT

/--
info: 'Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le' depends
 on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le

/--
info: 'Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le' depends on
 axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le
