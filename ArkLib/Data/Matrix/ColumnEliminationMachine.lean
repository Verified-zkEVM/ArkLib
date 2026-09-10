/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.PivotEliminationMachine
public import Mathlib.Data.List.GetD

/-!
# Closed column elimination with a supplied head pivot

The nonempty input matrix is a materialized list of rows; its head is already selected as pivot.
The driver validates the head entry even when there are no target rows. Every tail row is processed
by actual `PivotEliminationMachine.Step` transitions. Successful rows are consed into a reversed
outer list, including the unchanged head, then explicitly reversed before emission. Empty input,
Invalid pivot indices, zero pivots and delegated row failures reject without partial output.

The cost units are those of the pivot machine. Call/store transitions charge row handles and frame
initialization; delegation retains all inner costs and dispatches. Outer reversal charges every
allocated row-list cell. An output event is a tagged matrix handle, not a hidden traversal. Input
materialization and memory reclamation are outside the model. Pivot selection/permutation, matrix
extraction/writeback, echelon recursion and back substitution remain separate stages.
-/

@[expose] public section

namespace Matrix.ColumnEliminationMachine

abbrev Cost := PivotEliminationMachine.Cost

/-- Read the head cell and column parameter; initialize pivot, tail, cursor and index registers. -/
def beginCost : Cost := ⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 0⟩
/-- Read cursor/index, test and decrement index, and write both registers. -/
def seekCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 2⟩
/-- Read selected cell/index, test zero index, and write pivot-entry register. -/
def hitCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 1⟩
/-- Read and test pivot; allocate singleton head output cell and initialize accumulator pointer. -/
def validCost : Cost := ⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 1, 0⟩
/-- Read and test a zero pivot, then emit rejection. -/
def zeroCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 1, 0⟩
/-- Read an empty input/cursor or failed result handle, then emit rejection. -/
def rejectCost : Cost := ⟨⟨0, 0, 1, 1, 1⟩, 0, 0, 0, 0⟩
/-- Read target cell, pivot pointer and column; write tail and five inner lookup registers. -/
def callCost : Cost := ⟨⟨0, 0, 1, 9, 0⟩, 0, 0, 0, 0⟩
/-- Read inner output and outer accumulator pointers; allocate cell and update accumulator. -/
def storeCost : Cost := ⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted target cursor and initialize reversal output pointer. -/
def beginReverseCost : Cost := ⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩
/-- Read outer-list cell/output pointer, allocate a cell, and update both pointers. -/
def reverseCost : Cost := ⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩
/-- Read exhausted reversal cursor and matrix handle; emit that tagged handle. -/
def emitCost : Cost := ⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩

/-- Fixed outer control phases, including explicit row-list reversal. -/
inductive Configuration (F : Type*) where
  | begin (rows : List (List F))
  | validate (pivot : List F) (rows : List (List F)) (cursor : List F) (index : ℕ)
  | check (pivot : List F) (rows : List (List F)) (entry : F)
  | scan (pivot : List F) (rows reversed : List (List F))
  | row (pivot : List F) (rows reversed : List (List F))
      (inner : PivotEliminationMachine.Configuration F)
  | reverse (remaining output : List (List F))
  | done (rows : List (List F))
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules; delegation lifts exactly one actual pivot-machine transition. -/
inductive Step (j : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | empty : Step j (.begin []) rejectCost .rejected
  | begin {p rows} : Step j (.begin (p :: rows)) beginCost (.validate p rows p j)
  | missing {p rows i} : Step j (.validate p rows [] i) rejectCost .rejected
  | seek {p rows x xs i} : Step j (.validate p rows (x :: xs) (i + 1)) seekCost
      (.validate p rows xs i)
  | hit {p rows x xs} : Step j (.validate p rows (x :: xs) 0) hitCost (.check p rows x)
  | zero {p rows} : Step j (.check p rows 0) zeroCost .rejected
  | valid {p rows x} (hx : x ≠ 0) : Step j (.check p rows x) validCost (.scan p rows [p])
  | call {p t ts rev} : Step j (.scan p (t :: ts) rev) callCost
      (.row p ts rev (.lookup p t p t j))
  | delegate {p rows rev s c t} (h : PivotEliminationMachine.Step s c t) :
      Step j (.row p rows rev s) c (.row p rows rev t)
  | store {p rows rev out} : Step j (.row p rows rev (.done out)) storeCost
      (.scan p rows (out :: rev))
  | failed {p rows rev} : Step j (.row p rows rev .rejected) rejectCost .rejected
  | beginReverse {p rev} : Step j (.scan p [] rev) beginReverseCost (.reverse rev [])
  | reverse {x xs out} : Step j (.reverse (x :: xs) out) reverseCost (.reverse xs (x :: out))
  | emit {out} : Step j (.reverse [] out) emitCost (.done out)

/-- Dispatch executes no whole-row or whole-matrix transformation. -/
def step (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .done _ | .rejected => none
  | .begin [] => some (.rejected, rejectCost)
  | .begin (p :: rows) => some (.validate p rows p j, beginCost)
  | .validate _ _ [] _ => some (.rejected, rejectCost)
  | .validate p rows (_ :: xs) (i + 1) => some (.validate p rows xs i, seekCost)
  | .validate p rows (x :: _) 0 => some (.check p rows x, hitCost)
  | .check p rows x => if x = 0 then some (.rejected, zeroCost)
      else some (.scan p rows [p], validCost)
  | .scan p (t :: ts) rev => some (.row p ts rev (.lookup p t p t j), callCost)
  | .scan _ [] rev => some (.reverse rev [], beginReverseCost)
  | .row p rows rev inner =>
      match PivotEliminationMachine.step inner with
      | some (next, cost) => some (.row p rows rev next, cost)
      | none => match inner with
        | .done out => some (.scan p rows (out :: rev), storeCost)
        | .rejected => some (.rejected, rejectCost)
        | _ => none
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), reverseCost)
  | .reverse [] out => some (.done out, emitCost)

/-- Independent transitions fix both executable successor and cost. -/
theorem Step.step_eq {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step j s c t) : step j s = some (t, c) := by
  cases h with
  | delegate h => simp only [step, h.step_eq]
  | valid hx => simp [step, hx]
  | zero => simp [step]
  | _ => rfl

/-- Successful executable steps are covered by independent rules. -/
theorem step_sound {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step j s = some (t, c)) : Step j s c t := by
  cases s with
  | done rows => simp [step] at h
  | rejected => simp [step] at h
  | begin rows =>
      cases rows with
      | nil => cases h; exact Step.empty
      | cons p rows => cases h; exact Step.begin
  | validate p rows xs i =>
      cases xs with
      | nil => cases h; exact Step.missing
      | cons x xs =>
          cases i with
          | zero => cases h; exact Step.hit
          | succ i => cases h; exact Step.seek
  | check p rows x =>
      by_cases hx : x = 0
      · subst x
        simp only [step] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.zero
      · simp only [step, if_neg hx, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; exact Step.valid hx
  | scan p rows rev =>
      cases rows with
      | nil => cases h; exact Step.beginReverse
      | cons t rows => cases h; exact Step.call
  | reverse xs out =>
      cases xs with
      | nil => cases h; exact Step.emit
      | cons x xs => cases h; exact Step.reverse
  | row p rows rev inner =>
      cases hs : PivotEliminationMachine.step inner with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.delegate (PivotEliminationMachine.step_sound hs)
      | none =>
          cases inner with
          | done out => cases h; exact Step.store
          | rejected => cases h; exact Step.failed
          | _ => simp [step, hs] at h

omit [DecidableEq F] in
/-- Next state and charge are uniquely determined. -/
theorem Step.deterministic {j : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Step j s c t) (h' : Step j s d u) : t = u ∧ c = d := by
  classical
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- Actual composed traces with accumulated primitive charges. -/
inductive Trace (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace j 0 s 0 s
  | cons {n s u t c d} (head : Step j s c u) (tail : Trace j n u d t) :
      Trace j (n + 1) s (c + d) t

private theorem cost_add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Trace composition preserves every inner charge. -/
theorem Trace.trans {j n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace j n s c u) (h' : Trace j m u d t) : Trace j (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

omit [DecidableEq F] in
/-- Lift every actual pivot transition; no opaque per-row evaluation rule is introduced. -/
theorem Trace.delegate {j n : ℕ} (pivot : List F) (rows rev : List (List F))
    {s t : PivotEliminationMachine.Configuration F} {c : Cost}
    (h : PivotEliminationMachine.Trace n s c t) :
    Trace j n (.row pivot rows rev s) c (.row pivot rows rev t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih => exact Trace.cons (Step.delegate head) ih

/-- Fuel execution exposes partial phases on exhaustion. -/
def runFuel (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step j s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel j n t
          (result.1, c + result.2)

/-- Every executable result is justified by an independent trace with identical cost. -/
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

/-- Exact trace fuel reproduces its state and charge. -/
theorem Trace.runFuel_eq {j n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace j n s c t) : runFuel j n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

omit [DecidableEq F] in
private theorem pivot_step_control {s t : PivotEliminationMachine.Configuration F} {c : Cost}
    (h : PivotEliminationMachine.Step s c t) : c.row.control = 1 := by
  cases h with
  | row h => cases h <;> rfl
  | _ => rfl

omit [DecidableEq F] in
private theorem pivot_trace_control {n : ℕ} {s t : PivotEliminationMachine.Configuration F}
    {c : Cost} (h : PivotEliminationMachine.Trace n s c t) : c.row.control = n := by
  induction h with
  | nil s => rfl
  | cons head tail ih =>
      change _ + _ = _
      rw [pivot_step_control head, ih]
      omega

omit [DecidableEq F] in
private theorem pivot_trace (p t : List F) (j : ℕ) (x y : F)
    (hx : p[j]? = some x) (hy : t[j]? = some y) (hx0 : x ≠ 0) (hlen : t.length = p.length) :
    PivotEliminationMachine.Trace (4 * t.length + j + 8) (.lookup p t p t j)
      (PivotEliminationMachine.eliminationCost t.length j)
      (.done (List.zipWith
        (fun a b => a + PivotEliminationMachine.eliminationFactor y x * b) t p)) := by
  classical
  obtain ⟨n, _, h⟩ := PivotEliminationMachine.runFuel_refines
    (4 * t.length + j + 8) (.lookup p t p t j)
  rw [PivotEliminationMachine.elimination_runFuel p t j x y hx hy hx0 hlen] at h
  have hn := pivot_trace_control h
  change 4 * t.length + j + 8 = n at hn
  simpa only [← hn] using h

/-- Semantic target-row transformation, used only under the explicit valid-column hypotheses. -/
def targetRow (pivot : List F) (j : ℕ) (target : List F) : List F :=
  List.zipWith (fun t s => t +
    PivotEliminationMachine.eliminationFactor (target.getD j 0) (pivot.getD j 0) * s) target pivot

/-- Exact reversal cost for an outer list of `m` row handles. -/
def reversalCost (m : ℕ) : Cost := ⟨⟨0, 0, m + 1, 5 * m + 2, 1⟩, 0, 0, 0, 0⟩

/-- Exact scan cost with `k` target rows and `m` previously stored output rows. -/
def scanCost (n k j m : ℕ) : Cost :=
  ⟨⟨k * n, k * (n + 1), k * (4 * n + j + 11) + m + 2,
    k * (19 * n + 6 * j + 40) + 5 * m + 4, 2 * k + 1⟩,
    k, k, k, k * (2 * j + 1)⟩

/-- Exact head validation traversal cost. -/
def validationCost (j : ℕ) : Cost := ⟨⟨0, 0, j + 1, 4 * j + 3, 0⟩, 0, 0, 0, 2 * j + 1⟩

/-- Exact full-column modeled cost, polynomial in row count, column count and selected index. -/
def columnCost (n k j : ℕ) : Cost :=
  ⟨⟨k * n, k * (n + 1), k * (4 * n + j + 11) + j + 6,
    k * (19 * n + 6 * j + 40) + 4 * j + 21, 2 * k + 1⟩,
    k, k, k + 1, (k + 1) * (2 * j + 1)⟩

omit [DecidableEq F] in
/-- Outer reversal is a real sequence of allocated row-list cells. -/
theorem reverse_trace (j : ℕ) (xs out : List (List F)) :
    Trace j (xs.length + 1) (.reverse xs out) (reversalCost xs.length)
      (.done (xs.reverse ++ out)) := by
  induction xs generalizing out with
  | nil => simpa [reversalCost, emitCost] using
      Trace.cons (Step.emit (j := j) (out := out)) (Trace.nil _)
  | cons x xs ih =>
      simpa [reversalCost, reverseCost, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (x :: out))

omit [DecidableEq F] in
/-- Head lookup validates an actual index, without a default value. -/
theorem validation_trace (j : ℕ) (pivot : List F) (rows : List (List F)) (xs : List F)
    (i : ℕ) (x : F) (hx : xs[i]? = some x) :
    Trace j (i + 1) (.validate pivot rows xs i) (validationCost i) (.check pivot rows x) := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst a
          simpa [validationCost, hitCost] using
            Trace.cons
              (Step.hit (j := j) (p := pivot) (rows := rows) (x := x) (xs := xs)) (Trace.nil _)
  | succ i ih =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
          simp only [List.getElem?_cons_succ] at hx
          simpa [validationCost, seekCost, Nat.mul_add, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using
              Trace.cons (Step.seek (x := a)) (ih xs hx)

omit [DecidableEq F] in
/-- Target pivot traces are followed by explicit outer-list reversal. -/
theorem scan_trace (j : ℕ) (pivot : List F) (rows rev : List (List F))
    (hj : j < pivot.length) (hp : pivot[j] ≠ 0)
    (hlen : ∀ row ∈ rows, row.length = pivot.length) :
    Trace j (rows.length * (4 * pivot.length + j + 11) + rev.length + 2)
      (.scan pivot rows rev) (scanCost pivot.length rows.length j rev.length)
      (.done (rev.reverse ++ rows.map (targetRow pivot j))) := by
  induction rows generalizing rev with
  | nil =>
      have h := Trace.cons (Step.beginReverse (p := pivot)) (reverse_trace j rev [])
      convert h using 1 <;>
        simp [scanCost, reversalCost, beginReverseCost]; omega
  | cons t ts ih =>
      have ht := hlen t (by simp)
      have hjt : j < t.length := by omega
      have hcall := pivot_trace pivot t j pivot[j] t[j]
        (by simp) (by simp) hp ht
      have hrow := Trace.delegate (j := j) pivot ts rev hcall
      have htail := ih (targetRow pivot j t :: rev) (fun r hr => hlen r (by simp [hr]))
      have hvalue : targetRow pivot j t =
          List.zipWith (fun a b => a + PivotEliminationMachine.eliminationFactor t[j] pivot[j] * b)
            t pivot := by simp [targetRow, hj, hjt]
      rw [hvalue] at htail
      have h := Trace.cons Step.call (hrow.trans (Trace.cons Step.store htail))
      convert h using 1 <;>
        simp [scanCost, callCost, storeCost, PivotEliminationMachine.eliminationCost,
          List.reverse_cons, List.append_assoc, ht, ← hvalue, Nat.mul_add, Nat.add_mul,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Full-column success preserves the head, transforms the tail and has exact modeled cost. -/
theorem column_runFuel (j : ℕ) (pivot : List F) (rows : List (List F))
    (hj : j < pivot.length) (hp : pivot[j] ≠ 0)
    (hlen : ∀ row ∈ rows, row.length = pivot.length) :
    runFuel j (rows.length * (4 * pivot.length + j + 11) + j + 6) (.begin (pivot :: rows)) =
      (.done (pivot :: rows.map (targetRow pivot j)), columnCost pivot.length rows.length j) := by
  have h := Trace.cons Step.begin
    ((validation_trace j pivot rows pivot j pivot[j] (by simp)).trans
      (Trace.cons (Step.valid hp) (scan_trace j pivot rows [pivot] hj hp hlen)))
  have hsteps : (j + 1 + (rows.length * (4 * pivot.length + j + 11) + [pivot].length + 2 + 1)) + 1 =
      rows.length * (4 * pivot.length + j + 11) + j + 6 := by simp; omega
  have hc : beginCost + (validationCost j + (validCost +
      scanCost pivot.length rows.length j 1)) = columnCost pivot.length rows.length j := by
    ext <;> simp [beginCost, validationCost, validCost, scanCost, columnCost, Nat.add_mul] <;> omega
  have hr := h.runFuel_eq
  rw [hsteps] at hr
  simpa only [List.length_singleton, hc, List.reverse_singleton, List.singleton_append] using hr

omit [DecidableEq F] in
/-- Every output target has zero in the selected column; the head is retained separately. -/
theorem targetRow_entry_zero (j : ℕ) (pivot target : List F) (hj : j < pivot.length)
    (hp : pivot[j] ≠ 0) (hlen : target.length = pivot.length) :
    (targetRow pivot j target)[j]'(by simp [targetRow, List.length_zipWith, hlen]; omega) = 0 := by
  have hjt : j < target.length := by omega
  simpa only [targetRow, List.getD_eq_getElem _ _ hjt, List.getD_eq_getElem _ _ hj] using
    PivotEliminationMachine.output_entry_zero pivot target j hj hjt hp

omit [DecidableEq F] in
/-- A failed delegated row aborts the outer driver without exposing its partial output list. -/
theorem rejection_propagates {j n : ℕ} (pivot : List F) (rows rev : List (List F))
    {inner : PivotEliminationMachine.Configuration F} {c : Cost}
    (h : PivotEliminationMachine.Trace n inner c .rejected) :
    Trace j (n + 1) (.row pivot rows rev inner) (c + rejectCost) .rejected := by
  simpa using (Trace.delegate pivot rows rev h).trans (Trace.cons Step.failed (Trace.nil _))

/-- Empty matrix input rejects before pivot search or arithmetic. -/
theorem empty_runFuel (j : ℕ) : runFuel (F := F) j 1 (.begin []) = (.rejected, rejectCost) := rfl

/-- A zero selected head entry rejects before any target row is processed. -/
theorem zeroPivot_runFuel (j : ℕ) (pivot : List F) (rows : List (List F))
    (hp : pivot[j]? = some 0) :
    runFuel j (j + 3) (.begin (pivot :: rows)) =
      (.rejected, beginCost + (validationCost j + zeroCost)) := by
  have h := Trace.cons Step.begin
    ((validation_trace j pivot rows pivot j 0 hp).trans
      (Trace.cons Step.zero (Trace.nil _)))
  simpa [Nat.add_assoc] using h.runFuel_eq

/-- Canonical column operation: keep row zero and eliminate each successor row. -/
def eliminateColumn {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F) (j : Fin n) :
    Matrix (Fin (k + 1)) (Fin n) F :=
  Fin.cases (A 0) (fun i => PivotEliminationMachine.eliminateMatrix A i.succ 0 j i.succ)

omit [DecidableEq F] in
/-- The supplied head pivot is preserved verbatim. -/
theorem eliminateColumn_head {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) : eliminateColumn A j 0 = A 0 := rfl

omit [DecidableEq F] in
/-- Every tail row has zero in the selected column. -/
theorem eliminateColumn_entry {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (hp : A 0 j ≠ 0) (i : Fin k) : eliminateColumn A j i.succ j = 0 :=
  PivotEliminationMachine.eliminateMatrix_entry A i.succ 0 j hp

omit [DecidableEq F] in
/-- List-level row output agrees with the canonical matrix operation. -/
theorem targetRow_ofFn {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (i : Fin k) :
    targetRow (List.ofFn (A 0)) j.val (List.ofFn (A i.succ)) =
      List.ofFn (eliminateColumn A j i.succ) := by
  apply List.ext_getElem
  · simp [targetRow]
  · intro c hc hc'
    simp [targetRow, j.isLt, eliminateColumn,
      PivotEliminationMachine.eliminateMatrix, RowReductionMachine.addMultiple]

/-- Executing the materialized matrix produces the canonical column operation at exact cost. -/
theorem column_runFuel_matrix {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (hp : A 0 j ≠ 0) :
    runFuel j.val (k * (4 * n + j.val + 11) + j.val + 6)
      (.begin (List.ofFn (fun i => List.ofFn (A i)))) =
      (.done (List.ofFn (fun i => List.ofFn (eliminateColumn A j i))),
        columnCost n k j.val) := by
  have h := column_runFuel j.val (List.ofFn (A 0))
    (List.ofFn (fun i : Fin k => List.ofFn (A i.succ))) (by simp)
    (by simpa using hp) (by simp)
  simpa [List.ofFn_succ, List.map_ofFn, Function.comp_def, targetRow_ofFn,
    eliminateColumn_head] using h

omit [DecidableEq F] in
/-- The same column operation on equation results or right-hand sides. -/
def transformRhs {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F) (j : Fin n)
    (b : Fin (k + 1) → F) : Fin (k + 1) → F :=
  Fin.cases (b 0) (fun i => b i.succ +
    PivotEliminationMachine.eliminationFactor (A i.succ j) (A 0 j) * b 0)

omit [DecidableEq F] in
/-- Matrix multiplication transforms by exactly the corresponding right-hand-side operation. -/
theorem eliminateColumn_mulVec {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (x : Fin n → F) :
    eliminateColumn A j *ᵥ x = transformRhs A j (A *ᵥ x) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · change (PivotEliminationMachine.eliminateMatrix A i.succ 0 j *ᵥ x) i.succ = _
    simp [PivotEliminationMachine.eliminateMatrix,
      RowReductionMachine.addMultiple_mulVec, transformRhs]

omit [DecidableEq F] in
/-- The unchanged head makes the right-hand-side transformation injective. -/
theorem transformRhs_injective {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) : Function.Injective (transformRhs A j) := by
  intro b c h
  have hzero : b 0 = c 0 := congrFun h 0
  funext i
  refine Fin.cases hzero (fun i => ?_) i
  have hi := congrFun h i.succ
  change b i.succ + _ * b 0 = c i.succ + _ * c 0 at hi
  rw [hzero] at hi
  exact add_right_cancel hi

omit [DecidableEq F] in
/-- Augmented-system semantics preserve every solution under the matching RHS operation. -/
theorem eliminateColumn_solution_iff {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (b : Fin (k + 1) → F) (x : Fin n → F) :
    eliminateColumn A j *ᵥ x = transformRhs A j b ↔ A *ᵥ x = b := by
  rw [eliminateColumn_mulVec, (transformRhs_injective A j).eq_iff]

omit [DecidableEq F] in
/-- In particular, the whole homogeneous-system kernel is unchanged. -/
theorem eliminateColumn_kernel_iff {k n : ℕ} (A : Matrix (Fin (k + 1)) (Fin n) F)
    (j : Fin n) (x : Fin n → F) : eliminateColumn A j *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  have hz : transformRhs A j 0 = 0 := by
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    simp [transformRhs]
  simpa only [hz] using eliminateColumn_solution_iff A j 0 x

end Matrix.ColumnEliminationMachine
