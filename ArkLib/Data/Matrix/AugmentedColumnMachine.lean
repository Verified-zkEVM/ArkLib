/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ColumnEliminationMachine
public import ArkLib.Data.Matrix.PivotSelectionMachine
public import Mathlib.Tactic.Linarith

/-!
# Closed augmented-column elimination

Each coefficient/RHS pair is packed as `rhs :: coefficients`. The actual column machine uses
physical column `j+1`, so the RHS receives the same row operation without becoming a pivot.
Packing, unpacking, both outer reversals, pair/cell allocation and output are explicit steps.
Delegation retains every inner charge and adds a wrapper dispatch plus two state-root accesses.
Input materialization, reclamation, literals, interpreter bookkeeping and scalar bit costs are
outside the abstract model. Tail lists are shared. This is one supplied-pivot column operation,
not a solver, pivot selector, consistency checker or forward-echelon recursion.
-/

@[expose] public section

namespace Matrix.AugmentedColumnMachine

abbrev Row (F : Type*) := PivotSelectionMachine.Row F
abbrev Cost := PivotEliminationMachine.Cost

/-- Read row cell, both pair fields and accumulator; allocate two cells and write both cursors. -/
def packCost : Cost := ⟨⟨0, 0, 1, 8, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted cursor and initialize reversal output. -/
def endCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read cell/output pointer, allocate a cell and update both pointers. -/
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read empty cursor/output; write callee and physical-index registers, computing successor. -/
def enterCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 1⟩
/-- Read inner output and initialize unpack cursor/accumulator. -/
def returnCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩
/-- Read outer cell, packed head/tail and accumulator; allocate pair/cell and write cursors. -/
def unpackCost : Cost := ⟨⟨0, 0, 1, 7, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted output cursor and augmented matrix handle; emit the handle. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩
/-- Read failed/malformed input handle and emit rejection. -/
def rejectCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
/-- One outer dispatch and read/write of the suspended callee root per delegated step. -/
def wrapperCost (t : ℕ) : Cost := ⟨⟨0, 0, t, 2 * t, 0⟩, 0, 0, 0, 0⟩

/-- A single scalar cons packs an augmented row; used in specifications, not as a bulk loop. -/
def packRow {F : Type*} (r : Row F) : List F := r.2 :: r.1

/-- Serialization phases and the actual suspended column-machine state. -/
inductive Configuration (F : Type*) where
  | pack (remaining : List (Row F)) (reversed : List (List F))
  | reversePacked (remaining output : List (List F))
  | column (physical : ℕ) (inner : ColumnEliminationMachine.Configuration F)
  | unpack (remaining : List (List F)) (reversed : List (Row F))
  | reverseRows (remaining output : List (Row F))
  | done (rows : List (Row F))
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent small-step rules; delegation invokes one actual inner transition. -/
inductive Step (j : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | pack {cs b rs rev} : Step j (.pack ((cs, b) :: rs) rev) packCost
      (.pack rs ((b :: cs) :: rev))
  | packEnd {rev} : Step j (.pack [] rev) endCost (.reversePacked rev [])
  | reversePacked {r rs out} : Step j (.reversePacked (r :: rs) out) reverseCost
      (.reversePacked rs (r :: out))
  | enter {out} : Step j (.reversePacked [] out) enterCost (.column (j + 1) (.begin out))
  | column {i s c t} (h : ColumnEliminationMachine.Step i s c t) :
      Step j (.column i s) (c + wrapperCost 1) (.column i t)
  | returned {i out} : Step j (.column i (.done out)) returnCost (.unpack out [])
  | failed {i} : Step j (.column i .rejected) rejectCost .rejected
  | unpack {b cs rs rev} : Step j (.unpack ((b :: cs) :: rs) rev) unpackCost
      (.unpack rs ((cs, b) :: rev))
  | malformed {rs rev} : Step j (.unpack ([] :: rs) rev) rejectCost .rejected
  | unpackEnd {rev} : Step j (.unpack [] rev) endCost (.reverseRows rev [])
  | reverseRows {r rs out} : Step j (.reverseRows (r :: rs) out) reverseCost
      (.reverseRows rs (r :: out))
  | emit {out} : Step j (.reverseRows [] out) emitCost (.done out)

/-- Literal dispatch preserves sharing and never calls a bulk serialization or evaluation. -/
def step (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .pack ((cs, b) :: rs) rev => some (.pack rs ((b :: cs) :: rev), packCost)
  | .pack [] rev => some (.reversePacked rev [], endCost)
  | .reversePacked (r :: rs) out => some (.reversePacked rs (r :: out), reverseCost)
  | .reversePacked [] out => some (.column (j + 1) (.begin out), enterCost)
  | .column i s => match ColumnEliminationMachine.step i s with
      | some (t, c) => some (.column i t, c + wrapperCost 1)
      | none => match s with
          | .done out => some (.unpack out [], returnCost)
          | .rejected => some (.rejected, rejectCost)
          | _ => none
  | .unpack ((b :: cs) :: rs) rev => some (.unpack rs ((cs, b) :: rev), unpackCost)
  | .unpack ([] :: _) _ => some (.rejected, rejectCost)
  | .unpack [] rev => some (.reverseRows rev [], endCost)
  | .reverseRows (r :: rs) out => some (.reverseRows rs (r :: out), reverseCost)
  | .reverseRows [] out => some (.done out, emitCost)
  | .done _ | .rejected => none

/-- Rules fix executable successor and all primitive charges. -/
theorem Step.step_eq {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step j s c t) : step j s = some (t, c) := by
  cases h with
  | column h => simp only [step, h.step_eq]
  | _ => rfl

/-- Every executable transition is justified by an independent rule. -/
theorem step_sound {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step j s = some (t, c)) : Step j s c t := by
  cases s with
  | pack rs rev => cases rs <;> cases h <;> constructor
  | reversePacked rs out => cases rs <;> cases h <;> constructor
  | unpack rs rev =>
      cases rs with
      | nil => cases h; exact Step.unpackEnd
      | cons r rs => cases r <;> cases h <;> constructor
  | reverseRows rs out => cases rs <;> cases h <;> constructor
  | done out => simp [step] at h
  | rejected => simp [step] at h
  | column i s =>
      cases hs : ColumnEliminationMachine.step i s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.column (ColumnEliminationMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases h; exact Step.returned
          | rejected => cases h; exact Step.failed
          | _ => simp [step, hs] at h

/-- Finite traces accumulate actual serialization and delegated charges. -/
inductive Trace (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace j 0 s 0 s
  | cons {n s u t c d} (head : Step j s c u) (tail : Trace j n u d t) :
      Trace j (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Trace composition preserves all charges. -/
theorem Trace.trans {j n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace j n s c u) (h' : Trace j m u d t) : Trace j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Interpreter fuel exposes partial states on exhaustion. -/
def runFuel (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step j s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel j n t; (result.1, c + result.2)

/-- Actual interpreter results have traces with identical costs. -/
theorem runFuel_refines (j fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace j n s (runFuel j fuel s).2 (runFuel j fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step j s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (j := j) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel realizes its result and charge. -/
theorem Trace.runFuel_eq {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace j n s c t) : runFuel j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

omit [DecidableEq F] in
/-- Delegate every inner step, with explicit wrapper overhead. -/
theorem lift_column_trace {j i n : ℕ} {s t : ColumnEliminationMachine.Configuration F}
    {c : Cost} (h : ColumnEliminationMachine.Trace i n s c t) :
    Trace j n (.column i s) (c + wrapperCost n) (.column i t) := by
  induction h with
  | nil s => simpa [wrapperCost] using Trace.nil (j := j) (.column i s)
  | @cons n s u t c d head tail ih =>
      have hc : (c + wrapperCost 1) + (d + wrapperCost n) = (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost] <;> omega
      rw [← hc]
      exact Trace.cons (Step.column head) ih

/-- Exact complete packing charge for `m` rows. -/
def packingCost (m : ℕ) : Cost := ⟨⟨0, 0, 2 * m + 2, 13 * m + 6, 0⟩, 0, 0, 0, 1⟩
/-- Exact complete unpacking charge for `m` rows. -/
def unpackingCost (m : ℕ) : Cost := ⟨⟨0, 0, 2 * m + 2, 12 * m + 4, 1⟩, 0, 0, 0, 0⟩

omit [DecidableEq F] in
private theorem reversePacked_trace (j : ℕ) (rs out : List (List F)) :
    Trace j (rs.length + 1) (.reversePacked rs out)
      ⟨⟨0, 0, rs.length + 1, 5 * rs.length + 4, 0⟩, 0, 0, 0, 1⟩
      (.column (j + 1) (.begin (rs.reverse ++ out))) := by
  induction rs generalizing out with
  | nil => simpa [enterCost] using Trace.cons (Step.enter (j := j) (out := out)) (Trace.nil _)
  | cons r rs ih =>
      simpa [reverseCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reversePacked (ih (r :: out))

omit [DecidableEq F] in
private theorem pack_loop (j : ℕ) (rs : List (Row F)) (rev : List (List F)) :
    Trace j (rs.length + 1) (.pack rs rev)
      ⟨⟨0, 0, rs.length + 1, 8 * rs.length + 2, 0⟩, 0, 0, 0, 0⟩
      (.reversePacked ((rs.map packRow).reverse ++ rev) []) := by
  induction rs generalizing rev with
  | nil => simpa [endCost] using Trace.cons (Step.packEnd (j := j) (rev := rev)) (Trace.nil _)
  | cons r rs ih =>
      rcases r with ⟨cs, b⟩
      simpa [packRow, packCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.pack (ih ((b :: cs) :: rev))

omit [DecidableEq F] in
/-- The complete packing loop constructs the exact materialized matrix passed to the callee. -/
theorem packing_trace (j : ℕ) (rs : List (Row F)) :
    Trace j (2 * rs.length + 2) (.pack rs []) (packingCost rs.length)
      (.column (j + 1) (.begin (rs.map packRow))) := by
  have hp := pack_loop j rs []
  simp only [List.append_nil] at hp
  have h := hp.trans (reversePacked_trace j (rs.map packRow).reverse [])
  convert h using 1 <;>
    simp [packingCost, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, two_mul]; omega

omit [DecidableEq F] in
private theorem reverseRows_trace (j : ℕ) (rs out : List (Row F)) :
    Trace j (rs.length + 1) (.reverseRows rs out)
      ⟨⟨0, 0, rs.length + 1, 5 * rs.length + 2, 1⟩, 0, 0, 0, 0⟩
      (.done (rs.reverse ++ out)) := by
  induction rs generalizing out with
  | nil => simpa [emitCost] using Trace.cons (Step.emit (j := j) (out := out)) (Trace.nil _)
  | cons r rs ih =>
      simpa [reverseCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverseRows (ih (r :: out))

omit [DecidableEq F] in
private theorem unpack_loop (j : ℕ) (rs rev : List (Row F)) :
    Trace j (rs.length + 1) (.unpack (rs.map packRow) rev)
      ⟨⟨0, 0, rs.length + 1, 7 * rs.length + 2, 0⟩, 0, 0, 0, 0⟩
      (.reverseRows (rs.reverse ++ rev) []) := by
  induction rs generalizing rev with
  | nil => simpa [endCost] using Trace.cons (Step.unpackEnd (j := j) (rev := rev)) (Trace.nil _)
  | cons r rs ih =>
      rcases r with ⟨cs, b⟩
      simpa [packRow, unpackCost, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.unpack (ih ((cs, b) :: rev))

omit [DecidableEq F] in
/-- Unpacking allocates every augmented pair and returns the original row representation. -/
theorem unpacking_trace (j : ℕ) (rs : List (Row F)) :
    Trace j (2 * rs.length + 2) (.unpack (rs.map packRow) []) (unpackingCost rs.length)
      (.done rs) := by
  have hu := unpack_loop j rs []
  simp only [List.append_nil] at hu
  have h := hu.trans (reverseRows_trace j rs.reverse [])
  convert h using 1 <;>
    simp [unpackingCost, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, two_mul]; omega

/-- The scalar used for a target's coefficient and RHS updates. -/
def factor (p : Row F) (j : ℕ) (r : Row F) : F :=
  PivotEliminationMachine.eliminationFactor (r.1.getD j 0) (p.1.getD j 0)

/-- Semantic augmented row operation; executable work is delegated after packing. -/
def transformRow (p : Row F) (j : ℕ) (r : Row F) : Row F :=
  (List.zipWith (fun t s => t + factor p j r * s) r.1 p.1, r.2 + factor p j r * p.2)

omit [DecidableEq F] in
/-- Physical column `j+1` updates the prepended RHS and every coefficient together. -/
theorem packed_target (p : Row F) (j : ℕ) (r : Row F) :
    ColumnEliminationMachine.targetRow (packRow p) (j + 1) (packRow r) =
      packRow (transformRow p j r) := by
  simp [ColumnEliminationMachine.targetRow, packRow, transformRow, factor]

/-- Actual delegated column fuel on `k+1` rows of coefficient width `n`. -/
def columnFuel (n k j : ℕ) : ℕ := k * (4 * (n + 1) + (j + 1) + 11) + (j + 1) + 6
/-- Full exact fuel includes both serialization loops and the callee return. -/
def fuel (n k j : ℕ) : ℕ := 4 * (k + 1) + 5 + columnFuel n k j
/-- Exact composed charge. -/
def cost (n k j : ℕ) : Cost := packingCost (k + 1) +
  ((ColumnEliminationMachine.columnCost (n + 1) k (j + 1) + wrapperCost (columnFuel n k j)) +
    (returnCost + unpackingCost (k + 1)))

omit [DecidableEq F] in
private theorem column_control {j n : ℕ} {s t : ColumnEliminationMachine.Configuration F}
    {c : Cost} (h : ColumnEliminationMachine.Trace j n s c t) : c.row.control = n := by
  induction h with
  | nil s => rfl
  | cons head tail ih =>
      have hs : ∀ {a b : ColumnEliminationMachine.Configuration F} {d : Cost},
          ColumnEliminationMachine.Step j a d b → d.row.control = 1 := by
        intro a b d h
        cases h with
        | delegate h =>
            cases h with
            | row h => cases h <;> rfl
            | _ => rfl
        | _ => rfl
      change _ + _ = _
      rw [hs head, ih]
      omega

/-- Actual packed execution returns the semantic augmented update with exact composed cost. -/
theorem evaluation_runFuel (j : ℕ) (p : Row F) (rows : List (Row F))
    (hj : j < p.1.length) (hp : p.1[j] ≠ 0)
    (hlen : ∀ r ∈ rows, r.1.length = p.1.length) :
    runFuel j (fuel p.1.length rows.length j) (.pack (p :: rows) []) =
      (.done (p :: rows.map (transformRow p j)), cost p.1.length rows.length j) := by
  have hrun := ColumnEliminationMachine.column_runFuel (j + 1) (packRow p)
    (rows.map packRow) (by simpa [packRow] using hj) (by simpa [packRow] using hp)
    (by
      intro row hr
      obtain ⟨r, hmem, heq⟩ := List.mem_map.mp hr
      rw [← heq]
      simpa [packRow] using hlen r hmem)
  simp only [List.map_map, Function.comp_def, packed_target] at hrun
  obtain ⟨n, hn, ht⟩ := ColumnEliminationMachine.runFuel_refines (j + 1)
    (rows.length * (4 * (packRow p).length + (j + 1) + 11) + (j + 1) + 6)
    (.begin (packRow p :: rows.map packRow))
  simp only [List.length_map] at hrun
  rw [hrun] at ht
  have hcontrol := column_control ht
  change rows.length * (4 * (packRow p).length + (j + 1) + 11) + (j + 1) + 6 = n at hcontrol
  have hn : n = columnFuel p.1.length rows.length j := by
    simpa only [columnFuel, packRow, List.length_cons] using hcontrol.symm
  have hpack := packing_trace j (p :: rows)
  have hunpack := unpacking_trace j (p :: rows.map (transformRow p j))
  simp only [List.map_cons, List.map_map, Function.comp_def] at hunpack
  have hinner := lift_column_trace (j := j) ht
  rw [hn] at hinner
  have h := hpack.trans (hinner.trans (Trace.cons Step.returned hunpack))
  have heq := h.runFuel_eq
  simp only [List.length_map, List.length_cons] at heq
  have hfuel : (2 * (rows.length + 1) + 2) +
      (columnFuel p.1.length rows.length j + (2 * (rows.length + 1) + 2 + 1)) =
        fuel p.1.length rows.length j := by unfold fuel; omega
  rw [hfuel] at heq
  exact heq

omit [DecidableEq F] in
/-- Every target retains the coefficient width of the supplied pivot. -/
theorem transformRow_length (p r : Row F) (j : ℕ) (hlen : r.1.length = p.1.length) :
    (transformRow p j r).1.length = p.1.length := by simp [transformRow, hlen]

omit [DecidableEq F] in
/-- Entrywise coefficient semantics under an actual valid index. -/
theorem transformRow_getD (p r : Row F) (j i : ℕ) (hlen : r.1.length = p.1.length)
    (hi : i < p.1.length) :
    (transformRow p j r).1.getD i 0 = r.1.getD i 0 + factor p j r * p.1.getD i 0 := by
  have hr : i < r.1.length := by omega
  have ho : i < (transformRow p j r).1.length := by rw [transformRow_length p r j hlen]; exact hi
  rw [List.getD_eq_getElem _ _ ho, List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ hi]
  simp [transformRow]

omit [DecidableEq F] in
/-- The selected coefficient is zero after the augmented update. -/
theorem transformRow_selected_zero (p r : Row F) (j : ℕ) (hlen : r.1.length = p.1.length)
    (hj : j < p.1.length) (hp : p.1[j] ≠ 0) : (transformRow p j r).1.getD j 0 = 0 := by
  rw [transformRow_getD p r j j hlen hj]
  apply PivotEliminationMachine.eliminated_entry
  rw [List.getD_eq_getElem _ _ hj]
  exact hp

omit [DecidableEq F] in
/-- A coefficient already zero in both source and target remains zero, including earlier columns. -/
theorem transformRow_preserves_zero (p r : Row F) (j i : ℕ)
    (hlen : r.1.length = p.1.length) (hi : i < p.1.length)
    (hp : p.1.getD i 0 = 0) (hr : r.1.getD i 0 = 0) :
    (transformRow p j r).1.getD i 0 = 0 := by
  rw [transformRow_getD p r j i hlen hi, hp, hr, mul_zero, add_zero]

/-- The coefficient-side value of an augmented row. -/
def rowValue (cs : List F) (x : ℕ → F) : F := ∑ i ∈ Finset.range cs.length, cs.getD i 0 * x i

omit [DecidableEq F] in
private theorem transformRow_value (p r : Row F) (j : ℕ) (hlen : r.1.length = p.1.length)
    (x : ℕ → F) :
    rowValue (transformRow p j r).1 x = rowValue r.1 x + factor p j r * rowValue p.1 x := by
  simp only [rowValue, transformRow_length p r j hlen, hlen]
  calc
    _ = ∑ i ∈ Finset.range p.1.length, (r.1.getD i 0 + factor p j r * p.1.getD i 0) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [transformRow_getD p r j i hlen (Finset.mem_range.mp hi)]
    _ = _ := by simp [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

omit [DecidableEq F] in
/-- With the unchanged head equation, each target transformation preserves its full RHS equation. -/
theorem transformRow_equation_iff (p r : Row F) (j : ℕ) (hlen : r.1.length = p.1.length)
    (x : ℕ → F) (hp : rowValue p.1 x = p.2) :
    rowValue (transformRow p j r).1 x = (transformRow p j r).2 ↔ rowValue r.1 x = r.2 := by
  rw [transformRow_value p r j hlen x, hp]
  exact add_right_cancel_iff

omit [DecidableEq F] in
/-- The entire decoded augmented system preserves every nonhomogeneous solution. -/
theorem solution_iff (p : Row F) (rows : List (Row F)) (j : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = p.1.length) (x : ℕ → F) :
    PivotSelectionMachine.Satisfies (p :: rows.map (transformRow p j)) x ↔
      PivotSelectionMachine.Satisfies (p :: rows) x := by
  change (∀ r ∈ p :: rows.map (transformRow p j), rowValue r.1 x = r.2) ↔
    (∀ r ∈ p :: rows, rowValue r.1 x = r.2)
  simp only [List.forall_mem_cons, List.forall_mem_map]
  constructor
  · rintro ⟨hp, ht⟩
    exact ⟨hp, fun r hr => (transformRow_equation_iff p r j (hlen r hr) x hp).mp (ht r hr)⟩
  · rintro ⟨hp, ht⟩
    exact ⟨hp, fun r hr => (transformRow_equation_iff p r j (hlen r hr) x hp).mpr (ht r hr)⟩

/-- All counted primitive operations are polynomial in the rectangular matrix dimensions. -/
theorem cost_total_le (n k j : ℕ) (hj : j < n) :
    PivotSelectionMachine.totalCost (cost n k j) ≤ 200 * (k + 1) * (n + 1) := by
  simp only [PivotSelectionMachine.totalCost, cost, packingCost, unpackingCost,
    ColumnEliminationMachine.columnCost, wrapperCost, columnFuel, returnCost,
    PivotEliminationMachine.cost_add, RowReductionMachine.cost_add]
  nlinarith [Nat.mul_le_mul_left k (Nat.le_of_lt hj)]

omit [DecidableEq F] in
/-- Head and row count are preserved in the exact decoded output. -/
theorem output_shape (p : Row F) (rows : List (Row F)) (j : ℕ) :
    (p :: rows.map (transformRow p j)).head? = some p ∧
      (p :: rows.map (transformRow p j)).length = (p :: rows).length := by simp

omit [DecidableEq F] in
/-- Every decoded row has the original coefficient width. -/
theorem output_rectangular (p : Row F) (rows : List (Row F)) (j : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = p.1.length) :
    ∀ r ∈ p :: rows.map (transformRow p j), r.1.length = p.1.length := by
  simp only [List.forall_mem_cons, List.forall_mem_map]
  exact ⟨trivial, fun r hr => transformRow_length p r j (hlen r hr)⟩

omit [DecidableEq F] in
/-- All-zero earlier columns survive the complete decoded column operation. -/
theorem output_preserves_earlier (p : Row F) (rows : List (Row F)) (j : ℕ)
    (hj : j < p.1.length) (hlen : ∀ r ∈ rows, r.1.length = p.1.length)
    (hz : ∀ i < j, ∀ r ∈ p :: rows, r.1.getD i 0 = 0) :
    ∀ i < j, ∀ r ∈ p :: rows.map (transformRow p j), r.1.getD i 0 = 0 := by
  intro i hi
  have hp := hz i hi p (by simp)
  simp only [List.forall_mem_cons, List.forall_mem_map]
  exact ⟨hp, fun r hr => transformRow_preserves_zero p r j i (hlen r hr) (by omega)
    hp (hz i hi r (by simp [hr]))⟩

omit [DecidableEq F] in
/-- Inner rejection propagates without returning a partially decoded matrix. -/
theorem rejection_trace {j i n : ℕ} {s : ColumnEliminationMachine.Configuration F} {c : Cost}
    (h : ColumnEliminationMachine.Trace i n s c .rejected) :
    Trace j (n + 1) (.column i s) ((c + wrapperCost n) + rejectCost) .rejected := by
  simpa using (lift_column_trace (j := j) h).trans (Trace.cons Step.failed (Trace.nil _))

end Matrix.AugmentedColumnMachine
