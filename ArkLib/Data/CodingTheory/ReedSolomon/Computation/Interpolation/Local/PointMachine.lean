/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Support.Machine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.RewriteMachine
public import ArkLib.Data.Matrix.PivotSelectionMachine
/-!
# Materialized interpolation rows for one received point

The program enumerates actual support columns, executes each translated/reduced column, collects
all emitted exponent vectors as a redundant row frame, and allocates homogeneous augmented rows
by duplicate-aware coefficient lookup. There is no matrix-entry callback. Collecting the actual
vectors avoids a separate exponent-box coverage assumption. Duplicate rows and zero terms remain.

Every recursive clause charges 32 primitive units for control, pointer/register operations,
natural tests, scalar constants, and allocations, plus every executed callee charge. Exponent
vectors are shared immutable tails; copying an outer list cell is charged. Bit costs, garbage
collection and host fuel administration are outside this unit-operation model.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine

namespace Rewrite
export LocalColumnRewriteMachine
  (DenseTerm appendCells appendCells_correct lookup column lookup_cost)
end Rewrite

abbrev DenseColumn (F : Type*) := List (Rewrite.DenseTerm F)
abbrev Row (F : Type*) := Matrix.PivotSelectionMachine.Row F

variable {F : Type*} [CommRing F]

/-- Decode an actual support vector and run the complete scalar-input column program. -/
def makeColumn (d m : ℕ) (a y : F) : List ℕ → Option (DenseColumn F) × ℕ
  | x :: b :: higher =>
      let r := Rewrite.column d m higher a y x b
      (r.1, 32 + r.2)
  | _ => (none, 32)

/-- Every column is computed once, in the enumerated support order. -/
def columns (d m : ℕ) (a y : F) : List (List ℕ) → Option (List (DenseColumn F)) × ℕ
  | [] => (some [], 32)
  | v :: vs =>
      let c := makeColumn d m a y v
      match c.1 with
      | none => (none, 32 + c.2)
      | some col =>
          let rest := columns d m a y vs
          match rest.1 with
          | none => (none, 32 + c.2 + rest.2)
          | some cols => (some (col :: cols), 32 + c.2 + rest.2)

/-- Allocate row-frame cells, sharing the already materialized exponent vectors. -/
def vectors : DenseColumn F → List (List ℕ) × ℕ
  | [] => ([], 32)
  | t :: ts =>
      let rest := vectors ts
      (t.2 :: rest.1, 32 + rest.2)

/-- Collect every emitted vector, with duplicates; every concatenated cell is charged. -/
def frame : List (DenseColumn F) → List (List ℕ) × ℕ
  | [] => ([], 32)
  | c :: cs =>
      let head := vectors c
      let tail := frame cs
      let joined := Rewrite.appendCells head.1 tail.1
      (joined.1, 32 + head.2 + tail.2 + joined.2)

/-- Allocate every scalar entry from the actual dense coefficient lookup. -/
def coefficients (q : List ℕ) : List (DenseColumn F) → List F × ℕ
  | [] => ([], 32)
  | c :: cs =>
      let entry := Rewrite.lookup q c
      let tail := coefficients q cs
      (entry.1 :: tail.1, 32 + entry.2 + tail.2)

/-- Allocate coefficient lists, explicit zero augmentation, and matrix outer cells. -/
def rows (cols : List (DenseColumn F)) : List (List ℕ) → List (Row F) × ℕ
  | [] => ([], 32)
  | q :: qs =>
      let r := coefficients q cols
      let tail := rows cols qs
      ((r.1, 0) :: tail.1, 32 + r.2 + tail.2)

/-- Build a full homogeneous point block from materialized dense columns. -/
def block (cols : List (DenseColumn F)) : List (Row F) × ℕ :=
  let grid := frame cols
  let result := rows cols grid.1
  (result.1, 32 + grid.2 + result.2)

/-- Actual support enumeration with an explicit strict jet budget, column execution, row frame,
and homogeneous row allocation. -/
def assembleWithBudget (D d m J A : ℕ) (a y : F) : Option (List (Row F)) × ℕ :=
  let support := InterpolationSupportMachine.enumerateWithBudget D d m J A
  match support.1 with
  | .done vs =>
      let computed := columns d m a y vs
      match computed.1 with
      | none => (none, 32 + support.2 + computed.2)
      | some cols =>
          let out := block cols
          (some out.1, 32 + support.2 + computed.2 + out.2)
  | _ => (none, 32 + support.2)

/-- Legacy point-block assembly specializes the strict jet budget to `2 * m`. -/
def assemble (D d m A : ℕ) (a y : F) : Option (List (Row F)) × ℕ :=
  assembleWithBudget D d m (2 * m) A a y

omit [CommRing F] in
theorem vectors_correct (c : DenseColumn F) :
    vectors c = (c.map Prod.snd, 32 * (c.length + 1)) := by
  induction c with
  | nil => rfl
  | cons t ts ih => simp [vectors, ih]; omega

omit [CommRing F] in
theorem frame_result (cs : List (DenseColumn F)) :
    (frame cs).1 = cs.flatMap (fun c => c.map Prod.snd) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [frame, vectors_correct, Rewrite.appendCells_correct, ih]

omit [CommRing F] in
theorem frame_bounds (K : ℕ) (cs : List (DenseColumn F))
    (h : ∀ c ∈ cs, c.length ≤ K) :
    (frame cs).1.length ≤ K * cs.length ∧
    (frame cs).2 ≤ 128 * (K + 1) * (cs.length + 1) := by
  induction cs with
  | nil => simp [frame]; omega
  | cons c cs ih =>
    obtain ⟨hl, hc⟩ := ih (fun c hm => h c (by simp [hm]))
    have hh := h c (by simp)
    simp only [frame, vectors_correct, Rewrite.appendCells_correct, List.length_map,
      List.length_append, List.length_cons]
    constructor <;> nlinarith

theorem coefficients_result (q : List ℕ) (cs : List (DenseColumn F)) :
    (coefficients q cs).1 = cs.map (fun c => LocalColumnRewriteMachine.coordinate q c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [coefficients, LocalColumnRewriteMachine.lookup_result, ih]

theorem coefficients_cost (K : ℕ) (q : List ℕ) (cs : List (DenseColumn F))
    (h : ∀ c ∈ cs, c.length ≤ K) :
    (coefficients q cs).2 ≤ 128 * (q.length + 2) * (K + 1) * (cs.length + 1) := by
  induction cs with
  | nil => simp [coefficients]; nlinarith
  | cons c cs ih =>
    have hh := Rewrite.lookup_cost q c
    have hl := h c (by simp)
    have ht := ih (fun c hm => h c (by simp [hm]))
    have hh' := hh.trans (Nat.mul_le_mul_left (64 * (q.length + 2))
      (Nat.add_le_add_right hl 1))
    simp only [coefficients, List.length_cons]
    nlinarith

theorem rows_result (cs : List (DenseColumn F)) (qs : List (List ℕ)) :
    (rows cs qs).1 = qs.map
      (fun q => (cs.map (fun c => LocalColumnRewriteMachine.coordinate q c), 0)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [rows, coefficients_result, ih]

theorem rows_cost (K w : ℕ) (cs : List (DenseColumn F)) (qs : List (List ℕ))
    (hc : ∀ c ∈ cs, c.length ≤ K) (hq : ∀ q ∈ qs, q.length ≤ w) :
    (rows cs qs).2 ≤ 256 * (w + 2) * (K + 1) * (cs.length + 1) * (qs.length + 1) := by
  have hp : 1 ≤ (w + 2) * (K + 1) * (cs.length + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  induction qs with
  | nil => simp [rows]; nlinarith
  | cons q qs ih =>
    have hr := coefficients_cost K q cs hc
    have hw := hq q (by simp)
    have hr' := hr.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 128 (Nat.add_le_add_right hw 2))))
    have ht := ih (fun q hm => hq q (by simp [hm]))
    simp only [rows, List.length_cons]
    nlinarith

/-- The adaptive grid introduces only quadratic column-count work at fixed gap parameters. -/
theorem block_bounds (K w : ℕ) (cs : List (DenseColumn F))
    (hc : ∀ c ∈ cs, c.length ≤ K) (hw : ∀ c ∈ cs, ∀ t ∈ c, t.2.length ≤ w) :
    (block cs).1.length ≤ K * cs.length ∧
    (block cs).2 ≤ 512 * (w + 2) * (K + 1) ^ 2 * (cs.length + 1) ^ 2 := by
  obtain ⟨hl, hf⟩ := frame_bounds K cs hc
  have hq : ∀ q ∈ (frame cs).1, q.length ≤ w := by
    rw [frame_result]
    intro q hq
    obtain ⟨c, hc', ht⟩ := List.mem_flatMap.mp hq
    obtain ⟨t, hs, rfl⟩ := List.mem_map.mp ht
    exact hw c hc' t hs
  have hr := rows_cost K w cs (frame cs).1 hc hq
  simp only [block, rows_result, List.length_map]
  refine ⟨hl, ?_⟩
  have hr' := hr.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hl 1))
  nlinarith [Nat.zero_le (w * K * cs.length)]

/-- Generic successful column traversal; the uniform bound includes every output outer cell. -/
theorem columns_correct (d m B : ℕ) (a y : F) (vs : List (List ℕ))
    (spec : List ℕ → DenseColumn F)
    (h : ∀ v ∈ vs, ∃ c, makeColumn d m a y v = (some (spec v), c) ∧ c ≤ B) :
    ∃ c, columns d m a y vs = (some (vs.map spec), c) ∧
      c ≤ (B + 64) * (vs.length + 1) := by
  induction vs with
  | nil => exact ⟨32, rfl, by simp⟩
  | cons v vs ih =>
    obtain ⟨c, hc, hb⟩ := h v (by simp)
    obtain ⟨k, hk, hb'⟩ := ih (fun v hm => h v (by simp [hm]))
    refine ⟨32 + c + k, ?_, ?_⟩
    · simp [columns, hc, hk]
    · simp only [List.length_cons]; nlinarith

end ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine
