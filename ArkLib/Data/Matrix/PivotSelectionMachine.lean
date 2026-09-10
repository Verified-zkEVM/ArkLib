/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotEliminationMachine
public import Mathlib.Tactic.Ring

/-!
# Charged pivot selection on augmented rows

Rows pair a materialized coefficient list with its right-hand side. A selected-column scan
retains zero rows in reverse order until the first nonzero entry. Explicit reversal restores
that prefix onto the untouched tail, and a charged construction moves the pivot to the head.
If every entry is zero, the same reversal restores the input. Missing entries reject when read;
an unscanned tail is not validated here. Rectangular validation belongs to the consumer.

Costs count abstract scalar equality, natural tests/decrements, dispatch, register/cell accesses,
cell allocation and tagged output. Row handles and untouched tails are shared. A cell read
returns head and tail together; constants, input materialization, reclamation, interpreter
bookkeeping and scalar bit costs are outside this model. No bulk list operation is dispatched.
-/

@[expose] public section

namespace Matrix.PivotSelectionMachine

abbrev Row (F : Type*) := List F × F
abbrev Cost := PivotEliminationMachine.Cost

/-- Read row cell, coefficient pointer and column; write candidate, tail, cursor and index. -/
def takeCost : Cost := ⟨⟨0, 0, 1, 7, 0⟩, 0, 0, 0, 0⟩
/-- Read/write cursor and index; test and decrement the index. -/
def seekCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 2⟩
/-- Read cell/index, test index zero, and write the selected scalar. -/
def hitCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 1⟩
/-- Read/test entry and read row/prefix handles; allocate a cell and update the prefix. -/
def zeroCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 1, 0⟩
/-- Read/test entry, prefix and tail pointers; initialize reversal destination. -/
def foundCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 1, 0⟩
/-- Read exhausted row cursor and initialize empty reversal destination. -/
def exhaustedCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read prefix cell/destination; allocate a cell and update both pointers. -/
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read empty cursor and restored row pointer. -/
def finishCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted cursor, pivot and tail; allocate a head cell and write the output pointer. -/
def assembleCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read and emit a tagged row-list handle. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
/-- Read exhausted lookup cursor and emit rejection. -/
def rejectCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩

/-- Fixed selection, indexed lookup, materialization and output phases. -/
inductive Configuration (F : Type*) where
  | scan (rows saved : List (Row F))
  | lookup (row : Row F) (rows saved : List (Row F)) (cursor : List F) (index : ℕ)
  | check (row : Row F) (rows saved : List (Row F)) (entry : F)
  | restore (pivot : Option (Row F)) (saved output : List (Row F))
  | emit (found : Bool) (rows : List (Row F))
  | done (found : Bool) (rows : List (Row F))
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Independent transition rules expose the actual scan and list-cell operations. -/
inductive Step (j : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | take {r rs rev} : Step j (.scan (r :: rs) rev) takeCost (.lookup r rs rev r.1 j)
  | exhausted {rev} : Step j (.scan [] rev) exhaustedCost (.restore none rev [])
  | seek {r rs rev x xs i} : Step j (.lookup r rs rev (x :: xs) (i + 1)) seekCost
      (.lookup r rs rev xs i)
  | hit {r rs rev x xs} : Step j (.lookup r rs rev (x :: xs) 0) hitCost (.check r rs rev x)
  | missing {r rs rev i} : Step j (.lookup r rs rev [] i) rejectCost .rejected
  | zero {r rs rev} : Step j (.check r rs rev 0) zeroCost (.scan rs (r :: rev))
  | found {r rs rev x} (hx : x ≠ 0) : Step j (.check r rs rev x) foundCost
      (.restore (some r) rev rs)
  | reverse {p r rs out} : Step j (.restore p (r :: rs) out) reverseCost
      (.restore p rs (r :: out))
  | finish {out} : Step j (.restore none [] out) finishCost (.emit false out)
  | assemble {p out} : Step j (.restore (some p) [] out) assembleCost (.emit true (p :: out))
  | emit {b out} : Step j (.emit b out) emitCost (.done b out)

/-- Literal executable dispatch; there is no find, filter, reverse or permutation primitive. -/
def step (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .scan (r :: rs) rev => some (.lookup r rs rev r.1 j, takeCost)
  | .scan [] rev => some (.restore none rev [], exhaustedCost)
  | .lookup r rs rev (_ :: xs) (i + 1) => some (.lookup r rs rev xs i, seekCost)
  | .lookup r rs rev (x :: _) 0 => some (.check r rs rev x, hitCost)
  | .lookup _ _ _ [] _ => some (.rejected, rejectCost)
  | .check r rs rev x => if x = 0 then some (.scan rs (r :: rev), zeroCost)
      else some (.restore (some r) rev rs, foundCost)
  | .restore p (r :: rs) out => some (.restore p rs (r :: out), reverseCost)
  | .restore none [] out => some (.emit false out, finishCost)
  | .restore (some p) [] out => some (.emit true (p :: out), assembleCost)
  | .emit b out => some (.done b out, emitCost)
  | .done _ _ | .rejected => none

/-- Rules fix both executable successor and charge. -/
theorem Step.step_eq {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step j s c t) : step j s = some (t, c) := by
  cases h with
  | zero => simp [step]
  | found hx => simp [step, hx]
  | _ => rfl

/-- All executable steps have an independent operational rule. -/
theorem step_sound {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step j s = some (t, c)) : Step j s c t := by
  cases s with
  | scan rows rev => cases rows <;> cases h <;> constructor
  | lookup r rs rev xs i => cases xs <;> cases i <;> cases h <;> constructor
  | check r rs rev x =>
      by_cases hx : x = 0
      · subst x
        simp only [step] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.zero
      · simp only [step, if_neg hx, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.found hx
  | restore p rev out => cases rev <;> cases p <;> cases h <;> constructor
  | emit b out => cases h; exact Step.emit
  | done b out => simp [step] at h
  | rejected => simp [step] at h

/-- Finite traces accumulate every primitive charge. -/
inductive Trace (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace j 0 s 0 s
  | cons {n s u t c d} (head : Step j s c u) (tail : Trace j n u d t) :
      Trace j (n + 1) s (c + d) t

private theorem cost_add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Trace composition preserves all charges. -/
theorem Trace.trans {j n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace j n s c u) (h' : Trace j m u d t) : Trace j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel exhaustion exposes the reached phase. -/
def runFuel (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step j s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel j n t; (result.1, c + result.2)

/-- Every executable result has an identical-cost trace. -/
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

/-- Exact trace fuel realizes its output and cost. -/
theorem Trace.runFuel_eq {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace j n s c t) : runFuel j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Exact indexed-lookup cost. -/
def lookupCost (j : ℕ) : Cost := ⟨⟨0, 0, j + 1, 4 * j + 3, 0⟩, 0, 0, 0, 2 * j + 1⟩
/-- Exact prefix reversal cost before assembly. -/
def reversalCost (m : ℕ) : Cost := ⟨⟨0, 0, m, 5 * m, 0⟩, 0, 0, 0, 0⟩
/-- Exact charge when the first nonzero pivot follows `i` zero rows. -/
def foundCostTotal (j i : ℕ) : Cost :=
  ⟨⟨0, 0, i * (j + 4) + j + 5, (i + 1) * (4 * j + 20), 1⟩,
    0, 0, i + 1, (i + 1) * (2 * j + 1)⟩
/-- Exact charge when all `m` rows have a valid zero entry. -/
def allZeroCost (j m : ℕ) : Cost :=
  ⟨⟨0, 0, m * (j + 4) + 3, m * (4 * j + 20) + 5, 1⟩,
    0, 0, m, m * (2 * j + 1)⟩

omit [DecidableEq F] in
/-- A valid selected entry is reached by actual indexed-list steps. -/
theorem lookup_trace (j : ℕ) (r : Row F) (rs rev : List (Row F)) (xs : List F)
    (i : ℕ) (x : F) (hx : xs[i]? = some x) :
    Trace j (i + 1) (.lookup r rs rev xs i) (lookupCost i) (.check r rs rev x) := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst a
          simpa [lookupCost, hitCost] using
            Trace.cons (Step.hit (j := j) (r := r) (rs := rs) (rev := rev) (xs := xs)) (Trace.nil _)
  | succ i ih =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
          simp only [List.getElem?_cons_succ] at hx
          simpa [lookupCost, seekCost, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using Trace.cons (Step.seek (x := a)) (ih xs hx)

omit [DecidableEq F] in
/-- Prefix restoration allocates one actual outer cell per moved row. -/
theorem restore_trace (j : ℕ) (p : Option (Row F)) (rev out : List (Row F)) :
    Trace j rev.length (.restore p rev out) (reversalCost rev.length)
      (.restore p [] (rev.reverse ++ out)) := by
  induction rev generalizing out with
  | nil => simpa [reversalCost] using Trace.nil (j := j) (.restore p [] out)
  | cons r rev ih =>
      simpa [reversalCost, reverseCost, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (r :: out))

omit [DecidableEq F] in
/-- Each valid zero row is scanned and stored before continuing. -/
theorem zeros_trace (j : ℕ) (zs rows rev : List (Row F))
    (hz : ∀ r ∈ zs, r.1[j]? = some 0) :
    Trace j (zs.length * (j + 3)) (.scan (zs ++ rows) rev)
      ⟨⟨0, 0, zs.length * (j + 3), zs.length * (4 * j + 15), 0⟩,
        0, 0, zs.length, zs.length * (2 * j + 1)⟩
      (.scan rows (zs.reverse ++ rev)) := by
  induction zs generalizing rev with
  | nil => simpa using Trace.nil (j := j) (.scan rows rev)
  | cons r zs ih =>
      have hl := lookup_trace j r (zs ++ rows) rev r.1 j 0 (hz r (by simp))
      have ht := ih (r :: rev) (fun r hr => hz r (by simp [hr]))
      have h := Trace.cons Step.take (hl.trans (Trace.cons Step.zero ht))
      convert h using 1 <;>
        simp only [List.length_cons, List.cons_append, PivotEliminationMachine.cost_add,
        RowReductionMachine.cost_add,
        PivotEliminationMachine.Cost.mk.injEq, RowReductionMachine.Cost.mk.injEq,
        and_true, true_and, Nat.zero_add, Nat.add_zero, Nat.one_mul, takeCost, lookupCost,
        zeroCost, List.reverse_cons, List.append_assoc,
          Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals first | omega | congr 1

/-- The first nonzero pivot is moved to the head, preserving the order of all other rows. -/
theorem found_runFuel (j : ℕ) (zs : List (Row F)) (p : Row F) (tail : List (Row F))
    (a : F) (hz : ∀ r ∈ zs, r.1[j]? = some 0) (hp : p.1[j]? = some a) (ha : a ≠ 0) :
    runFuel j (zs.length * (j + 4) + j + 5) (.scan (zs ++ p :: tail) []) =
      (.done true (p :: (zs ++ tail)), foundCostTotal j zs.length) := by
  have hz' := zeros_trace j zs (p :: tail) [] hz
  simp only [List.append_nil] at hz'
  have hl := lookup_trace j p tail zs.reverse p.1 j a hp
  have hr := restore_trace j (some p) zs.reverse tail
  simp only [List.reverse_reverse] at hr
  have h := hz'.trans (Trace.cons Step.take (hl.trans (Trace.cons (Step.found ha)
    (hr.trans (Trace.cons Step.assemble (Trace.cons Step.emit (Trace.nil _)))))))
  have heq := h.runFuel_eq
  convert heq using 1 <;>
    simp only [List.length_reverse, PivotEliminationMachine.cost_zero,
        RowReductionMachine.cost_zero,
        PivotEliminationMachine.cost_add, RowReductionMachine.cost_add,
        PivotEliminationMachine.Cost.mk.injEq, RowReductionMachine.Cost.mk.injEq,
        Prod.mk.injEq, and_true, true_and, Nat.zero_add, Nat.add_zero, Nat.one_mul, Nat.reduceAdd,
        foundCostTotal, takeCost, lookupCost, foundCost, reversalCost, assembleCost, emitCost,
      Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals first | omega | (congr 1; omega)

/-- Exhausting a valid all-zero column restores the complete original augmented matrix. -/
theorem allZero_runFuel (j : ℕ) (rows : List (Row F))
    (hz : ∀ r ∈ rows, r.1[j]? = some 0) :
    runFuel j (rows.length * (j + 4) + 3) (.scan rows []) =
      (.done false rows, allZeroCost j rows.length) := by
  have hz' := zeros_trace j rows [] [] hz
  simp only [List.append_nil] at hz'
  have hr := restore_trace j none rows.reverse []
  simp only [List.reverse_reverse, List.append_nil] at hr
  have h := hz'.trans (Trace.cons Step.exhausted
    (hr.trans (Trace.cons Step.finish (Trace.cons Step.emit (Trace.nil _)))))
  have heq := h.runFuel_eq
  convert heq using 1 <;>
    simp only [List.length_reverse, PivotEliminationMachine.cost_zero,
        RowReductionMachine.cost_zero,
        PivotEliminationMachine.cost_add, RowReductionMachine.cost_add,
        PivotEliminationMachine.Cost.mk.injEq, RowReductionMachine.Cost.mk.injEq,
        Prod.mk.injEq, and_true, true_and, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, allZeroCost,
        exhaustedCost, reversalCost, finishCost, emitCost,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals first | omega | (congr 1; omega)

/-- Total primitive cost in the inherited scalar/register categories. -/
def totalCost (c : Cost) : ℕ := c.row.additions + c.row.multiplications + c.row.control +
  c.row.data + c.row.output + c.inversions + c.negations + c.equalities + c.natural

/-- Uniform fuel for either outcome of a valid column scan. -/
def selectionFuel (j m : ℕ) : ℕ := m * (j + 4) + 3

omit [DecidableEq F] in
private theorem first_nonzero (j : ℕ) (rows : List (Row F))
    (hv : ∀ r ∈ rows, ∃ a, r.1[j]? = some a) :
    (∀ r ∈ rows, r.1[j]? = some 0) ∨
      ∃ zs p tail a, rows = zs ++ p :: tail ∧
        (∀ r ∈ zs, r.1[j]? = some 0) ∧ p.1[j]? = some a ∧ a ≠ 0 := by
  classical
  induction rows with
  | nil => exact Or.inl (by simp)
  | cons r rs ih =>
      obtain ⟨a, ha⟩ := hv r (by simp)
      by_cases hzero : a = 0
      · subst a
        rcases ih (fun r hr => hv r (by simp [hr])) with hz | ⟨zs, p, tail, a, heq, hz, hp, hn⟩
        · exact Or.inl (by simpa [ha] using hz)
        · exact Or.inr ⟨r :: zs, p, tail, a, by simp [heq], by simpa [ha] using hz, hp, hn⟩
      · exact Or.inr ⟨[], r, rs, a, rfl, by simp, ha, hzero⟩

/-- Trace execution can consume any additional fuel. -/
theorem Trace.runFuel_add {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace j n s c t) (extra : ℕ) :
    runFuel j (n + extra) s = ((runFuel j extra t).1, c + (runFuel j extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_add_assoc]

private theorem extend_done {j fuel bound : ℕ} {s : Configuration F} {b : Bool}
    {out : List (Row F)} {c : Cost}
    (h : runFuel j fuel s = (.done b out, c)) (hb : fuel ≤ bound) :
    runFuel j bound s = (.done b out, c) := by
  obtain ⟨n, hn, ht⟩ := runFuel_refines j fuel s
  rw [h] at ht
  have heq : n + (bound - n) = bound := by omega
  have hext := ht.runFuel_add (bound - n)
  rw [heq] at hext
  have hd : runFuel j (bound - n) (.done b out) = (.done b out, (0 : Cost)) := by
    cases bound - n <;> rfl
  simpa [hd] using hext

omit [CommSemiring F] [DecidableEq F] in
/-- The pivot move is a permutation of complete augmented rows, including their RHS entries. -/
theorem pivotMove_perm (zs : List (Row F)) (p : Row F) (tail : List (Row F)) :
    (zs ++ p :: tail).Perm (p :: (zs ++ tail)) := by
  induction zs with
  | nil => exact List.Perm.refl _
  | cons r zs ih =>
      exact (ih.cons r).trans (List.Perm.swap p r (zs ++ tail))

/-- A valid column returns either a nonzero head or a certificate that every entry is zero. -/
def ResultCorrect (j : ℕ) (input : List (Row F)) (found : Bool) (out : List (Row F)) : Prop :=
  input.Perm out ∧ if found then
    ∃ p tail a, out = p :: tail ∧ p.1[j]? = some a ∧ a ≠ 0
  else ∀ r ∈ out, r.1[j]? = some 0

/-- Uniform bounded execution has a correct result and a polynomial primitive cost. -/
theorem selection_runFuel (j : ℕ) (rows : List (Row F))
    (hv : ∀ r ∈ rows, ∃ a, r.1[j]? = some a) :
    ∃ b out c, runFuel j (selectionFuel j rows.length) (.scan rows []) = (.done b out, c) ∧
      ResultCorrect j rows b out ∧ totalCost c ≤ rows.length * (7 * j + 26) + 9 := by
  rcases first_nonzero j rows hv with hz | ⟨zs, p, tail, a, rfl, hz, hp, ha⟩
  · refine ⟨false, rows, allZeroCost j rows.length, allZero_runFuel j rows hz, ?_, ?_⟩
    · exact ⟨List.Perm.refl _, hz⟩
    · simp only [totalCost, allZeroCost]
      ring_nf
      exact le_rfl
  · have hbound : zs.length * (j + 4) + j + 5 ≤
        selectionFuel j (zs ++ p :: tail).length := by
      simp only [selectionFuel, List.length_append, List.length_cons]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    refine ⟨true, p :: (zs ++ tail), foundCostTotal j zs.length,
      extend_done (found_runFuel j zs p tail a hz hp ha) hbound, ?_, ?_⟩
    · exact ⟨pivotMove_perm zs p tail, p, zs ++ tail, a, rfl, hp, ha⟩
    · simp only [totalCost, foundCostTotal, List.length_append, List.length_cons]
      ring_nf
      omega

/-- Augmented rows express equations without requiring a separate RHS permutation. -/
def Satisfies (rows : List (Row F)) (x : ℕ → F) : Prop :=
  ∀ r ∈ rows, (∑ i ∈ Finset.range r.1.length, r.1.getD i 0 * x i) = r.2

omit [DecidableEq F] in
/-- Any permutation of augmented rows preserves the full nonhomogeneous solution set. -/
theorem satisfies_perm {rows out : List (Row F)} (h : rows.Perm out) (x : ℕ → F) :
    Satisfies out x ↔ Satisfies rows x := by
  simp only [Satisfies, h.mem_iff]

omit [DecidableEq F] in
/-- Both certified outcomes preserve every augmented-system solution. -/
theorem ResultCorrect.solution_iff {j : ℕ} {rows out : List (Row F)} {b : Bool}
    (h : ResultCorrect j rows b out) (x : ℕ → F) : Satisfies out x ↔ Satisfies rows x :=
  satisfies_perm h.1 x

omit [DecidableEq F] in
/-- The augmented-list equations agree with ordinary finite-matrix multiplication. -/
theorem satisfies_ofFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (b : Fin m → F)
    (x : ℕ → F) :
    Satisfies (List.ofFn (fun i => (List.ofFn (A i), b i))) x ↔
      A *ᵥ (fun i => x i.val) = b := by
  simp only [Satisfies, List.forall_mem_ofFn_iff, Matrix.mulVec, dotProduct, funext_iff]
  apply forall_congr'
  intro r
  change (∑ i ∈ Finset.range (List.ofFn (A r)).length,
    (List.ofFn (A r)).getD i 0 * x i) = b r ↔ _
  rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  simp [List.getD]

/-- Rectangular materialized input supplies the selected-entry validity required by selection. -/
theorem selection_runFuel_rectangular (j n : ℕ) (rows : List (Row F))
    (hj : j < n) (hlen : ∀ r ∈ rows, r.1.length = n) :
    ∃ b out c, runFuel j (selectionFuel j rows.length) (.scan rows []) = (.done b out, c) ∧
      ResultCorrect j rows b out ∧ totalCost c ≤ rows.length * (7 * j + 26) + 9 := by
  apply selection_runFuel
  intro r hr
  have h : j < r.1.length := by rw [hlen r hr]; exact hj
  exact ⟨r.1[j], by simp⟩

end Matrix.PivotSelectionMachine
