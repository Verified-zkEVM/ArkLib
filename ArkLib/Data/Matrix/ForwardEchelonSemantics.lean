/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.AugmentedColumnMachine

/-!
# Materialized forward-echelon output invariants

Completed rows retain their logical pivot indices. Residual rows retain their RHS values even
when every coefficient is zero; deciding consistency and back substitution are separate stages.
-/

@[expose] public section

namespace Matrix.ForwardEchelonMachine

abbrev Row (F : Type*) := PivotSelectionMachine.Row F
abbrev Pivot (F : Type*) := ℕ × Row F

variable {F : Type*} [Field F]

/-- All coefficient lists have the declared width. -/
def Rectangular (n : ℕ) (rows : List (Row F)) : Prop := ∀ r ∈ rows, r.1.length = n
/-- Every coefficient before a logical column is zero. -/
def ZeroBefore (j : ℕ) (rows : List (Row F)) : Prop :=
  ∀ i < j, ∀ r ∈ rows, r.1.getD i 0 = 0
/-- One materialized completed pivot row, with a valid nonzero pivot and preceding zeros. -/
def PivotValid (n lower : ℕ) (p : Pivot F) : Prop :=
  lower ≤ p.1 ∧ p.1 < n ∧ p.2.1.length = n ∧ p.2.1.getD p.1 0 ≠ 0 ∧
    ∀ i < p.1, p.2.1.getD i 0 = 0
/-- Useful echelon output: ordered pivots and residual rows with all coefficients zero. -/
def Echelon (n lower : ℕ) (pivots : List (Pivot F)) (rest : List (Row F)) : Prop :=
  pivots.Pairwise (fun p q => p.1 < q.1) ∧
    (∀ p ∈ pivots, PivotValid n lower p) ∧ Rectangular n rest ∧ ZeroBefore n rest

/-- The equation set represented by materialized pivots followed by residual rows. -/
def Solutions (pivots : List (Pivot F)) (rest : List (Row F)) (x : ℕ → F) : Prop :=
  PivotSelectionMachine.Satisfies (pivots.map Prod.snd ++ rest) x

omit [Field F] in
/-- Permuting complete augmented rows preserves rectangularity. -/
theorem Rectangular.perm {n : ℕ} {rows out : List (Row F)}
    (h : Rectangular n rows) (hp : rows.Perm out) : Rectangular n out := by
  intro r hr
  exact h r (hp.mem_iff.mpr hr)

/-- Permuting complete augmented rows preserves previously zero columns. -/
theorem ZeroBefore.perm {j : ℕ} {rows out : List (Row F)}
    (h : ZeroBefore j rows) (hp : rows.Perm out) : ZeroBefore j out := by
  intro i hi r hr
  exact h i hi r (hp.mem_iff.mpr hr)

/-- An all-zero selected column extends the zero prefix by one. -/
theorem ZeroBefore.next {j : ℕ} {rows : List (Row F)} (h : ZeroBefore j rows)
    (hz : ∀ r ∈ rows, r.1[j]? = some 0) : ZeroBefore (j + 1) rows := by
  intro i hi r hr
  by_cases heq : i = j
  · subst i
    simp [List.getD, hz r hr]
  · exact h i (by omega) r hr

/-- Augmented elimination leaves its active tail rectangular with one additional zero column. -/
theorem augmented_tail {n j : ℕ} (p : Row F) (rows : List (Row F))
    (hrect : Rectangular n (p :: rows)) (hz : ZeroBefore j (p :: rows))
    (hj : j < n) (hp : p.1.getD j 0 ≠ 0) :
    Rectangular n (rows.map (AugmentedColumnMachine.transformRow p j)) ∧
      ZeroBefore (j + 1) (rows.map (AugmentedColumnMachine.transformRow p j)) := by
  have hplen := hrect p (by simp)
  have hlen : ∀ r ∈ rows, r.1.length = p.1.length := fun r hr =>
    (hrect r (by simp [hr])).trans hplen.symm
  have hjp : j < p.1.length := by omega
  refine ⟨?_, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact (AugmentedColumnMachine.transformRow_length p s j (hlen s hs)).trans hplen
  · intro i hi r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    by_cases heq : i = j
    · subst i
      apply AugmentedColumnMachine.transformRow_selected_zero p s j (hlen s hs) hjp
      simpa only [List.getD_eq_getElem _ _ hjp] using hp
    · exact AugmentedColumnMachine.transformRow_preserves_zero p s j i (hlen s hs)
        (by omega) (hz i (by omega) p (by simp)) (hz i (by omega) s (by simp [hs]))

/-- Advancing past a zero column only weakens the lower bound on future pivot indices. -/
theorem Echelon.weaken {n j : ℕ} {ps : List (Pivot F)} {rest : List (Row F)}
    (h : Echelon n (j + 1) ps rest) : Echelon n j ps rest := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro p hp
  obtain ⟨hlo, hs⟩ := h.2.1 p hp
  exact ⟨by omega, hs⟩

/-- Prepending the completed current pivot preserves strict order of all pivot indices. -/
theorem Echelon.cons {n j : ℕ} (p : Row F) {ps : List (Pivot F)} {rest : List (Row F)}
    (h : Echelon n (j + 1) ps rest) (hj : j < n) (hlen : p.1.length = n)
    (hp : p.1.getD j 0 ≠ 0) (hz : ∀ i < j, p.1.getD i 0 = 0) :
    Echelon n j ((j, p) :: ps) rest := by
  refine ⟨List.pairwise_cons.mpr ⟨?_, h.1⟩, ?_, h.2.2⟩
  · intro q hq
    have hq' := (h.2.1 q hq).1
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hq'
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨le_rfl, hj, hlen, hp, hz⟩
    · exact (h.weaken).2.1 q hq

/-- Adding the same retained head equation preserves equivalence of the active equation sets. -/
theorem solutions_cons {ps : List (Pivot F)} {rest rows : List (Row F)}
    (p : Row F) (j : ℕ)
    (h : ∀ x, Solutions ps rest x ↔ PivotSelectionMachine.Satisfies rows x) :
    ∀ x, Solutions ((j, p) :: ps) rest x ↔ PivotSelectionMachine.Satisfies (p :: rows) x := by
  intro x
  simpa only [Solutions, List.map_cons, List.cons_append,
    PivotSelectionMachine.Satisfies, List.forall_mem_cons] using and_congr_right
      (fun _ => h x)

end Matrix.ForwardEchelonMachine
