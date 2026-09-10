/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.RewriteBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Matrix.Semantics
/-!
# Polynomial matrix-block assembly cost at derivative order zero

The actual support enumeration and column program are unchanged. The order-zero column size
is at most m², so the materialized row count and assembly charge remain polynomial even when
m grows with the input. Exact kernel semantics are inherited from the same point-block program.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine

noncomputable section

variable {F : Type*} [CommRing F]

/-- Uniform observed column charge at order zero, polynomial in multiplicity and threshold. -/
def zeroColumnBudget (m A : ℕ) : ℕ :=
  288 * (m * A + 2 * m + m + 2) * (m + 1) +
    (224 * m + 224) * (m * m) + 160

/-- Every order-zero support column has at most m² terms and the tighter observed charge. -/
theorem support_column_zero_bounds (D m A : ℕ) (a y : F) (v : List ℕ)
    (hv : v ∈ InterpolationSupportMachine.supportSpec
      (InterpolationSupportMachine.parameters D 0 m A)) :
    ∃ c, makeColumn 0 m a y v = (some (columnValue 0 m a y v), c) ∧
      (columnValue 0 m a y v).length ≤ m * m ∧ c ≤ zeroColumnBudget m A := by
  have hw := InterpolationSupportMachine.supportSpec_width _ hv
  simp only [InterpolationSupportMachine.parameters] at hw
  obtain ⟨x, b, rfl⟩ : ∃ x b, v = [x, b] := by
    cases v with
    | nil => simp at hw
    | cons x vs =>
      cases vs with
      | nil => simp at hw
      | cons b xs =>
        have hx : xs = [] := by simpa using hw
        exact ⟨x, b, by rw [hx]⟩
  obtain ⟨ts, c, hc, _, _, hl, hb⟩ :=
    LocalColumnRewriteMachine.column_zero_refines a y x b m
  have hv' : columnValue 0 m a y [x, b] = ts := by
    simp [columnValue, makeColumn, hc]
  obtain ⟨_, hsum, hweight⟩ :=
    (InterpolationSupportMachine.mem_supportSpec_iff _ x [b]).mp hv
  simp only [InterpolationSupportMachine.parameters, List.sum_cons, List.sum_nil] at hsum hweight
  refine ⟨32 + c, by simp [makeColumn, hc, hv'], by simpa [hv'] using hl, ?_⟩
  have hh : x + b + m + 2 ≤ m * A + 2 * m + m + 2 := by omega
  have hm := Nat.mul_le_mul_right (m + 1) (Nat.mul_le_mul_left 288 hh)
  unfold zeroColumnBudget
  omega

/-- Observed assembly budget with no exponential dependence on multiplicity. -/
def zeroAssemblyBudget (m A L : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor 1 (2 * m) * (m * A + 1) +
    (zeroColumnBudget m A + 64) * (L + 1) +
    2048 * (m * m + 1) ^ 2 * (L + 1) ^ 2 + 32

/-- The same actual one-point assembly admits polynomial row-count and work bounds at d=0. -/
theorem assemble_zero_bounds (D m A : ℕ) (a y : F) :
    ∃ rs c, assemble D 0 m A a y = (some rs, c) ∧
      rs.length ≤ m * m * (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D 0 m A)).length ∧
      c ≤ zeroAssemblyBudget m A (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D 0 m A)).length := by
  let vs := InterpolationSupportMachine.supportSpec
    (InterpolationSupportMachine.parameters D 0 m A)
  let cs := vs.map (columnValue 0 m a y)
  have h (v : List ℕ) (hv : v ∈ vs) := support_column_zero_bounds D m A a y v hv
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D 0 m A
  simp only [Nat.zero_add] at hsc
  have hs' : InterpolationSupportMachine.enumerateWithBudget D 0 m (2 * m) A =
      (.done (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D 0 m (2 * m) A)), sc) := by
    simpa [InterpolationSupportMachine.enumerate, InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using hs
  obtain ⟨cc, hc, hcc⟩ := columns_correct 0 m (zeroColumnBudget m A) a y vs
    (columnValue 0 m a y) (by
      intro v hv
      obtain ⟨c, hc, _, hb⟩ := h v hv
      exact ⟨c, hc, hb⟩)
  have hl : ∀ col ∈ cs, col.length ≤ m * m := by
    intro col hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact (h v hv).choose_spec.2.1
  have hw : ∀ col ∈ cs, ∀ t ∈ col, t.2.length ≤ 2 := by
    intro col hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    intro t ht
    exact ((support_column_refines D m A a y v hv).choose_spec.2.2.1 t ht).le
  obtain ⟨hbl, hbc⟩ := block_bounds (m * m) 2 cs hl hw
  refine ⟨(block cs).1, 32 + sc + cc + (block cs).2, ?_, ?_, ?_⟩
  · simp only [assemble, assembleWithBudget, hs']
    have hvs : InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D 0 m (2 * m) A) = vs := by
      simp [vs, InterpolationSupportMachine.parameters,
        InterpolationSupportMachine.parametersWithBudget]
    rw [hvs, hc]
  · simpa only [cs, List.length_map] using hbl
  · have hlen : cs.length = vs.length := List.length_map _
    rw [hlen] at hbc
    change 32 + sc + cc + (block cs).2 ≤ zeroAssemblyBudget m A vs.length
    unfold zeroAssemblyBudget
    change (block cs).2 ≤ 2048 * (m * m + 1) ^ 2 * (vs.length + 1) ^ 2 at hbc
    omega

end
end ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine

namespace ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine

noncomputable section

variable {F : Type*} [CommRing F]

/-- Full received-matrix charge at order zero, polynomial also in growing multiplicity. -/
def zeroMatrixBudget (m A L n : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor 1 (2 * m) * (m * A + 1) +
    32 * (L + 1) +
    (InterpolationPointBlockMachine.zeroAssemblyBudget m A L +
      64 * (m * m * L + 1) + 64) * (n + 1) + 32

/-- The actual received matrix has at most n*m²*supportLength rows at order zero. Its observed
charge is polynomial in n,m,A and support length. Kernel semantics use the unchanged run. -/
theorem run_zero_bounds (D m A : ℕ) (received : List (F × F)) :
    ∃ out c, run D 0 m A received = (some out, c) ∧
      out.columns = (support D 0 m A).length ∧ out.points = received.length ∧
      out.rowCount = out.rows.length ∧
      out.rowCount ≤ m * m * (support D 0 m A).length * received.length ∧
      c ≤ zeroMatrixBudget m A (support D 0 m A).length received.length := by
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerate_correct D 0 m A
  simp only [Nat.zero_add] at hsc
  have hs' : InterpolationSupportMachine.enumerateWithBudget D 0 m (2 * m) A =
      (.done (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D 0 m (2 * m) A)), sc) := by
    simpa [InterpolationSupportMachine.enumerate, InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using hs
  obtain ⟨tc, ht, hrows, hcost⟩ := traverse_correct D 0 m A (support D 0 m A).length
    (InterpolationPointBlockMachine.zeroAssemblyBudget m A (support D 0 m A).length)
    (m * m * (support D 0 m A).length) received (pointRows D 0 m A) (by
      intro p _
      obtain ⟨rs, c, hc, hl, hb⟩ :=
        InterpolationPointBlockMachine.assemble_zero_bounds D m A p.1 p.2
      have hc' : InterpolationPointBlockMachine.assembleWithBudget D 0 m (2 * m) A
          p.1 p.2 = (some rs, c) := by
        simpa [InterpolationPointBlockMachine.assemble] using hc
      have hr : pointRows D 0 m A p = rs := by
        simp [pointRows, pointRowsWithBudget, hc']
      exact ⟨c, by simpa only [hr] using hc,
        by simpa only [hr, support, supportWithBudget,
          InterpolationSupportMachine.parameters, InterpolationSupportMachine.parametersWithBudget]
          using hl,
        hb⟩)
  have ht' : traverseWithBudget D 0 m (2 * m) A (support D 0 m A).length received =
      (some ⟨(support D 0 m A).length, received.length,
        (received.flatMap (pointRows D 0 m A)).length,
        received.flatMap (pointRows D 0 m A)⟩, tc) := by
    simpa [traverse] using ht
  refine ⟨⟨(support D 0 m A).length, received.length,
    (received.flatMap (pointRows D 0 m A)).length, received.flatMap (pointRows D 0 m A)⟩,
    32 + sc + 32 * ((support D 0 m A).length + 1) + tc,
    ?_, rfl, rfl, rfl, hrows, ?_⟩
  · simp only [run, runWithBudget, hs', countCells_correct]
    simpa only [support, supportWithBudget, InterpolationSupportMachine.parameters,
      InterpolationSupportMachine.parametersWithBudget] using congrArg
      (fun r => (r.1, 32 + sc + 32 * ((support D 0 m A).length + 1) + r.2)) ht'
  · unfold zeroMatrixBudget
    omega

end
end ReedSolomon.HiddenDerivative.ReceivedInterpolationMatrixMachine
