/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.Range

/-!
# Closed enumeration machine for `ZMod`

A counter starts at `q` and a scalar starts at zero. Each iteration saves one scalar in an
explicit list cell and increments it by one. Explicit reversal transitions restore order.
The specification uses `List.range` and `map`; executable dispatch uses neither, nor `reverse`.

Costs count scalar additions/equalities, natural-number tests/decrements, materialized constants,
control transitions, register/cell accesses, and output events. A cell read includes head and tail;
allocation is one write. Unchanged registers are retained. Constants count scalar zero/one and
empty-list initialization; phase tags are included in control. Constructor tests on lists are
included in control, whereas natural zero tests and predecessor operations are charged separately.
Input materialization, host fuel bookkeeping, memory reclamation, and integer/field bit costs
are excluded.
Completeness needs `q > 0`; no primality is needed for enumeration of the residue ring itself.
-/

@[expose] public section

namespace ZMod.EnumerationMachine

/-- Primitive charges; equality is explicit even though this machine needs no scalar equality. -/
@[ext] structure Cost where
  additions : ℕ
  equalities : ℕ
  natOperations : ℕ
  constants : ℕ
  control : ℕ
  data : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦
  ⟨a.additions + b.additions, a.equalities + b.equalities,
    a.natOperations + b.natOperations, a.constants + b.constants,
    a.control + b.control, a.data + b.data, a.output + b.output⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.equalities + b.equalities,
      a.natOperations + b.natOperations, a.constants + b.constants,
      a.control + b.control, a.data + b.data, a.output + b.output⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; rfl

/-- Read modulus; initialize counter, zero scalar and empty accumulator. -/
def startCost : Cost := ⟨0, 0, 0, 2, 1, 4, 0⟩
/-- Read/test a nonzero counter and write its predecessor. -/
def takeCost : Cost := ⟨0, 0, 2, 0, 1, 2, 0⟩
/-- Read scalar/accumulator; allocate a cell and update the accumulator pointer. -/
def saveCost : Cost := ⟨0, 0, 0, 0, 1, 4, 0⟩
/-- Materialize one; read scalar, add, and write its successor. -/
def incrementCost : Cost := ⟨1, 0, 0, 1, 1, 2, 0⟩
/-- Read/test exhausted counter and initialize the empty output pointer. -/
def beginReverseCost : Cost := ⟨0, 0, 1, 1, 1, 2, 0⟩
/-- Read cell/output pointer; allocate a cell and update both pointers. -/
def reverseCost : Cost := ⟨0, 0, 0, 0, 1, 5, 0⟩
/-- Read exhausted cursor/output pointer and emit the completed list handle. -/
def emitCost : Cost := ⟨0, 0, 0, 0, 1, 2, 1⟩

/-- Fixed phases store only counters, scalars and materialized lists. -/
inductive Configuration (q : ℕ) where
  | start
  | scan (remaining : ℕ) (current : ZMod q) (reversed : List (ZMod q))
  | save (remaining : ℕ) (current : ZMod q) (reversed : List (ZMod q))
  | increment (remaining : ℕ) (current : ZMod q) (reversed : List (ZMod q))
  | reverse (remaining output : List (ZMod q))
  | done (values : List (ZMod q))
  deriving DecidableEq, Repr

variable {q : ℕ}

/-- Independent transition rules specify scalar updates and their primitive costs. -/
inductive Step : Configuration q → Cost → Configuration q → Prop where
  | start : Step .start startCost (.scan q 0 [])
  | take {n x rev} : Step (.scan (n + 1) x rev) takeCost (.save n x rev)
  | save {n x rev} : Step (.save n x rev) saveCost (.increment n x (x :: rev))
  | increment {n x rev} : Step (.increment n x rev) incrementCost (.scan n (x + 1) rev)
  | beginReverse {x rev} : Step (.scan 0 x rev) beginReverseCost (.reverse rev [])
  | reverse {x xs out} : Step (.reverse (x :: xs) out) reverseCost (.reverse xs (x :: out))
  | emit {out} : Step (.reverse [] out) emitCost (.done out)

/-- Closed executable dispatch; list construction and scalar arithmetic are individual phases. -/
def step : Configuration q → Option (Configuration q × Cost)
  | .start => some (.scan q 0 [], startCost)
  | .scan 0 _ rev => some (.reverse rev [], beginReverseCost)
  | .scan (n + 1) x rev => some (.save n x rev, takeCost)
  | .save n x rev => some (.increment n x (x :: rev), saveCost)
  | .increment n x rev => some (.scan n (x + 1) rev, incrementCost)
  | .reverse [] out => some (.done out, emitCost)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), reverseCost)
  | .done _ => none

/-- Every specified transition is implemented with the exact charge. -/
theorem Step.step_eq {s t : Configuration q} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Every executable transition is one of the independent rules. -/
theorem step_sound {s t : Configuration q} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | start => cases h; exact Step.start
  | scan n x rev =>
      cases n with
      | zero => cases h; exact Step.beginReverse
      | succ n => cases h; exact Step.take
  | save n x rev => cases h; exact Step.save
  | increment n x rev => cases h; exact Step.increment
  | reverse xs out =>
      cases xs with
      | nil => cases h; exact Step.emit
      | cons x xs => cases h; exact Step.reverse
  | done xs => simp [step] at h

/-- Exact operational equivalence, including cost. -/
theorem step_iff {s t : Configuration q} {c : Cost} : step s = some (t, c) ↔ Step s c t :=
  ⟨step_sound, Step.step_eq⟩

/-- Finite traces accumulate every transition charge. -/
inductive Trace : ℕ → Configuration q → Cost → Configuration q → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

/-- Fuel exhaustion returns the actual current phase; it never fabricates a completed list. -/
def runFuel : ℕ → Configuration q → Configuration q × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel n t
          (result.1, c + result.2)

/-- Execution refines the independent trace semantics with identical accumulated cost. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration q) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel reproduces its final configuration and cost. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration q} {c : Cost}
    (h : Trace n s c t) : runFuel n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Reversal materializes one output cell per input cell, then emits a handle. -/
def reversalCost (n : ℕ) : Cost := ⟨0, 0, 0, 0, n + 1, 5 * n + 2, 1⟩

/-- Cost from a scan with `n` entries remaining and `m` entries already accumulated. -/
def scanCost (n m : ℕ) : Cost :=
  ⟨n, 0, 2 * n + 1, n + 1, 4 * n + m + 2, 13 * n + 5 * m + 4, 1⟩

/-- Exact linear primitive cost of enumeration, including initialization and reversal. -/
def enumerationCost (q : ℕ) : Cost :=
  ⟨q, 0, 2 * q + 1, q + 3, 4 * q + 3, 13 * q + 8, 1⟩

/-- Every reversal cell is backed by an actual charged transition. -/
theorem reverse_trace (xs out : List (ZMod q)) :
    Trace (xs.length + 1) (.reverse xs out) (reversalCost xs.length)
      (.done (xs.reverse ++ out)) := by
  induction xs generalizing out with
  | nil => simpa [reversalCost, emitCost] using
      Trace.cons (Step.emit (q := q) (out := out)) (Trace.nil _)
  | cons x xs ih =>
      simpa [reversalCost, reverseCost, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (x :: out))

/-- A scan emits the consecutive residue values in increasing counter order. -/
theorem scan_trace (n : ℕ) (x : ZMod q) (rev : List (ZMod q)) :
    Trace (4 * n + rev.length + 2) (.scan n x rev) (scanCost n rev.length)
      (.done (rev.reverse ++ (List.range n).map (fun i : ℕ ↦ x + (i : ZMod q)))) := by
  induction n generalizing x rev with
  | zero =>
      have h := Trace.cons (Step.beginReverse (x := x)) (reverse_trace rev [])
      convert h using 1 <;> simp [scanCost, beginReverseCost, reversalCost]; omega
  | succ n ih =>
      have hseq : (List.range (n + 1)).map (fun i : ℕ ↦ x + (i : ZMod q)) =
          x :: (List.range n).map (fun i : ℕ ↦ (x + 1) + (i : ZMod q)) := by
        rw [List.range_succ_eq_map]
        simp only [List.map_cons, List.map_map, Nat.cast_zero, add_zero]
        congr 1
        apply List.map_congr_left
        intro i hi
        simp [Nat.cast_add, add_comm, add_left_comm]
      have h := Trace.cons Step.take (Trace.cons Step.save
        (Trace.cons Step.increment (ih (x + 1) (x :: rev))))
      convert h using 1 <;>
        simp [scanCost, takeCost, saveCost, incrementCost, hseq,
          List.reverse_cons, List.append_assoc, add_assoc, add_comm, add_left_comm, Nat.mul_add] <;>
          omega

/-- Closed execution enumerates the range casts; these bulk operations occur only in the theorem. -/
theorem enumeration_runFuel (q : ℕ) :
    runFuel (4 * q + 3) (.start : Configuration q) =
      (.done ((List.range q).map (fun i : ℕ ↦ (i : ZMod q))), enumerationCost q) := by
  have h := Trace.cons Step.start (scan_trace q (0 : ZMod q) [])
  have hrun := h.runFuel_eq
  convert hrun using 1 <;> simp [scanCost, startCost, enumerationCost]; omega

/-- Range casts are distinct because their canonical representatives are below the modulus. -/
theorem enumeration_spec_nodup (q : ℕ) :
    ((List.range q).map (fun i : ℕ ↦ (i : ZMod q))).Nodup := by
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi j hj hij
  have h := congrArg ZMod.val hij
  simpa only [ZMod.val_natCast_of_lt (List.mem_range.mp hi),
    ZMod.val_natCast_of_lt (List.mem_range.mp hj)] using h

/-- A positive modulus makes every residue's representative occur in the range. -/
theorem enumeration_spec_complete (q : ℕ) (hq : 0 < q) (x : ZMod q) :
    x ∈ (List.range q).map (fun i : ℕ ↦ (i : ZMod q)) := by
  let : NeZero q := ⟨hq.ne'⟩
  exact List.mem_map.mpr ⟨x.val, List.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

/-- The actual machine output contains every residue exactly once, with exact length and cost.
For `q=0` the machine returns an empty list; completeness does not apply. -/
theorem enumeration_correct (q : ℕ) (hq : 0 < q) :
    ∃ values : List (ZMod q),
      runFuel (4 * q + 3) (.start : Configuration q) = (.done values, enumerationCost q) ∧
        values.length = q ∧ values.Nodup ∧ ∀ x : ZMod q, x ∈ values := by
  refine ⟨(List.range q).map (fun i : ℕ ↦ (i : ZMod q)), enumeration_runFuel q,
    by simp, enumeration_spec_nodup q, ?_⟩
  exact enumeration_spec_complete q hq

/-- Five residues distinguish order, zero inclusion, and the modulus-exclusive endpoint. -/
example : runFuel 23 (.start : Configuration 5) =
    (.done [0, 1, 2, 3, 4], ⟨5, 0, 11, 8, 23, 73, 1⟩) := by decide

/-- One transition before completion, the ordered cells exist but no output has been emitted. -/
example : runFuel 22 (.start : Configuration 5) =
    (.reverse [] [0, 1, 2, 3, 4], ⟨5, 0, 11, 8, 22, 71, 0⟩) := by decide

/-- Successive field addition wraps at the modulus even on the final increment. -/
example : runFuel 1 (.increment 0 4 [4] : Configuration 5) =
    (.scan 0 0 [4], ⟨1, 0, 0, 1, 1, 2, 0⟩) := by decide

/-- Modulus one has exactly one residue; initialization and reversal are still charged. -/
example : runFuel 7 (.start : Configuration 1) =
    (.done [0], ⟨1, 0, 3, 4, 7, 21, 1⟩) := by decide

/-- Zero modulus terminates with no residues enumerated and does not certify completeness. -/
example : runFuel 3 (.start : Configuration 0) =
    (.done [], ⟨0, 0, 1, 3, 3, 8, 1⟩) := by decide

end ZMod.EnumerationMachine
