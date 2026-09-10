/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Closed row-add-multiple machine

The input is a scalar and two materialized rows. The machine starts with an empty reversed output,
scans both rows in lockstep, and separately multiplies and adds each pair. It then reverses the
result by explicit list-cell transitions. Unequal lengths reject without returning a partial row.
There is no map, zip, reverse, or matrix-operation primitive in executable dispatch.

Costs distinguish scalar additions/multiplications, control dispatches, data accesses, and output
events. A cell read includes its head and tail; allocation writes a cell. Unchanged registers are
retained, not copied. Dispatch includes list-constructor tests. Output emits one tagged result
handle (or rejection); all returned cells have already been constructed and charged. Initial input
materialization, host fuel bookkeeping, memory reclamation, and field bit costs are separate.
The matrix bridge is mathematical; this subroutine does not implement row extraction or a solver.
-/

@[expose] public section

namespace Matrix.RowReductionMachine

/-- Charges for the abstract scalar and list primitives. -/
@[ext] structure Cost where
  additions : ℕ
  multiplications : ℕ
  control : ℕ
  data : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b =>
  ⟨a.additions + b.additions, a.multiplications + b.multiplications,
    a.control + b.control, a.data + b.data, a.output + b.output⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.multiplications + b.multiplications,
      a.control + b.control, a.data + b.data, a.output + b.output⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; rfl

/-- Read two row cells; write two row cursors and two scalar registers. -/
def takeCost : Cost := ⟨0, 0, 1, 6, 0⟩
/-- Read the multiplier and source scalar; multiply and write the product register. -/
def multiplyCost : Cost := ⟨0, 1, 1, 3, 0⟩
/-- Read target scalar, product and accumulator pointer; add, allocate and update the pointer. -/
def addCost : Cost := ⟨1, 0, 1, 5, 0⟩
/-- Read both empty row cursors; initialize the output pointer for reversal. -/
def beginReverseCost : Cost := ⟨0, 0, 1, 3, 0⟩
/-- Read reversal cell and output pointer; allocate output cell and update both pointers. -/
def reverseCost : Cost := ⟨0, 0, 1, 5, 0⟩
/-- Read exhausted reversal cursor and output pointer; emit one tagged row handle. -/
def emitCost : Cost := ⟨0, 0, 1, 2, 1⟩
/-- Read the mismatching row cursors and emit rejection. -/
def rejectCost : Cost := ⟨0, 0, 1, 2, 1⟩

/-- Fixed phases; the reversal accumulator is materialized one cell at a time. -/
inductive Configuration (F : Type*) where
  | scan (target source reversed : List F)
  | multiply (target source reversed : List F) (t s : F)
  | add (target source reversed : List F) (t product : F)
  | reverse (remaining output : List F)
  | done (row : List F)
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Semiring F]

/-- Independent rules specify the exact updates and primitive charges. -/
inductive Step (a : F) : Configuration F → Cost → Configuration F → Prop where
  | take {t s ts ss rev} : Step a (.scan (t :: ts) (s :: ss) rev) takeCost
      (.multiply ts ss rev t s)
  | multiply {ts ss rev t s} : Step a (.multiply ts ss rev t s) multiplyCost
      (.add ts ss rev t (a * s))
  | add {ts ss rev t p} : Step a (.add ts ss rev t p) addCost (.scan ts ss ((t + p) :: rev))
  | beginReverse {rev} : Step a (.scan [] [] rev) beginReverseCost (.reverse rev [])
  | reverse {x xs out} : Step a (.reverse (x :: xs) out) reverseCost (.reverse xs (x :: out))
  | emit {out} : Step a (.reverse [] out) emitCost (.done out)
  | shortTarget {s ss rev} : Step a (.scan [] (s :: ss) rev) rejectCost .rejected
  | shortSource {t ts rev} : Step a (.scan (t :: ts) [] rev) rejectCost .rejected

/-- Executable dispatch has no bulk list or row-arithmetic instruction. -/
def step (a : F) : Configuration F → Option (Configuration F × Cost)
  | .done _ | .rejected => none
  | .scan [] [] rev => some (.reverse rev [], beginReverseCost)
  | .scan [] (_ :: _) _ | .scan (_ :: _) [] _ => some (.rejected, rejectCost)
  | .scan (t :: ts) (s :: ss) rev => some (.multiply ts ss rev t s, takeCost)
  | .multiply ts ss rev t s => some (.add ts ss rev t (a * s), multiplyCost)
  | .add ts ss rev t p => some (.scan ts ss ((t + p) :: rev), addCost)
  | .reverse [] out => some (.done out, emitCost)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), reverseCost)

/-- Each independent rule is implemented with its prescribed cost. -/
theorem Step.step_eq {a : F} {s t : Configuration F} {c : Cost}
    (h : Step a s c t) : step a s = some (t, c) := by
  cases h <;> rfl

/-- Every successful executable dispatch satisfies an independent rule. -/
theorem step_sound {a : F} {s t : Configuration F} {c : Cost}
    (h : step a s = some (t, c)) : Step a s c t := by
  cases s with
  | done out => simp [step] at h
  | rejected => simp [step] at h
  | multiply ts ss rev x y => cases h; exact Step.multiply
  | add ts ss rev x p => cases h; exact Step.add
  | reverse xs out =>
      cases xs with
      | nil => cases h; exact Step.emit
      | cons x xs => cases h; exact Step.reverse
  | scan ts ss rev =>
      cases ts <;> cases ss <;> cases h
      · exact Step.beginReverse
      · exact Step.shortTarget
      · exact Step.shortSource
      · exact Step.take

/-- Successor and charge are deterministic. -/
theorem Step.deterministic {a : F} {s t u : Configuration F} {c d : Cost}
    (h : Step a s c t) (h' : Step a s d u) : t = u ∧ c = d := by
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- Actual transition traces with accumulated costs. -/
inductive Trace (a : F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s u t c d} (head : Step a s c u) (tail : Trace a n u d t) :
      Trace a (n + 1) s (c + d) t

/-- Fuel exhaustion returns a phase, not a spurious successful row. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step a s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel a n t
          (result.1, c + result.2)

/-- Executable refinement includes the accumulated primitive charges. -/
theorem runFuel_refines (a : F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace a n s (runFuel a fuel s).2 (runFuel a fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step a s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (a := a) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel recovers the same terminal state and charge. -/
theorem Trace.runFuel_eq {a : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace a n s c t) : runFuel a n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Reversal cost includes each newly allocated output cell and final emission. -/
def reversalCost (n : ℕ) : Cost := ⟨0, 0, n + 1, 5 * n + 2, 1⟩

/-- Cost from a scan header, with `n` remaining pairs and `m` previously constructed entries. -/
def scanCost (n m : ℕ) : Cost := ⟨n, n, 4 * n + m + 2, 19 * n + 5 * m + 5, 1⟩

/-- Exact cost of a successful row operation on `n` entries. -/
def rowCost (n : ℕ) : Cost := ⟨n, n, 4 * n + 2, 19 * n + 5, 1⟩

/-- Rejection cost after processing `n` matching pairs, without reversing partial results. -/
def rejectionCost (n : ℕ) : Cost := ⟨n, n, 3 * n + 1, 14 * n + 2, 1⟩

/-- Every output cell in the reversal is produced by a charged transition. -/
theorem reverse_trace (a : F) (xs out : List F) :
    Trace a (xs.length + 1) (.reverse xs out) (reversalCost xs.length)
      (.done (xs.reverse ++ out)) := by
  induction xs generalizing out with
  | nil => simpa [reversalCost, emitCost] using
      Trace.cons (Step.emit (a := a) (out := out)) (Trace.nil _)
  | cons x xs ih =>
      simpa [reversalCost, reverseCost, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (x :: out))

/-- Successful lockstep scanning computes the pointwise row formula, in its original order. -/
theorem scan_trace (a : F) (target source rev : List F) (hlen : target.length = source.length) :
    Trace a (4 * target.length + rev.length + 2) (.scan target source rev)
      (scanCost target.length rev.length)
      (.done (rev.reverse ++ List.zipWith (fun t s => t + a * s) target source)) := by
  induction target generalizing source rev with
  | nil =>
      have hs : source = [] := List.length_eq_zero_iff.mp hlen.symm
      subst source
      have h := Trace.cons Step.beginReverse (reverse_trace a rev [])
      convert h using 1 <;>
        simp [scanCost, beginReverseCost, reversalCost, Nat.add_comm,
          Nat.add_left_comm]
      omega
  | cons t ts ih =>
      cases source with
      | nil => simp at hlen
      | cons s ss =>
          have h := Trace.cons Step.take (Trace.cons Step.multiply
            (Trace.cons Step.add (ih ss ((t + a * s) :: rev) (by simpa using hlen))))
          convert h using 1 <;>
            simp [scanCost, takeCost, multiplyCost, addCost, List.reverse_cons,
              List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
              omega

/-- Exact terminating row result, with all reversal costs included. -/
theorem row_runFuel (a : F) (target source : List F) (hlen : target.length = source.length) :
    runFuel a (4 * target.length + 2) (.scan target source []) =
      (.done (List.zipWith (fun t s => t + a * s) target source), rowCost target.length) := by
  simpa [scanCost, rowCost] using (scan_trace a target source [] hlen).runFuel_eq

/-- Unequal row lengths cause explicit rejection after exactly the matching prefix. -/
theorem rejection_trace (a : F) (target source rev : List F)
    (hlen : target.length ≠ source.length) :
    Trace a (3 * min target.length source.length + 1) (.scan target source rev)
      (rejectionCost (min target.length source.length)) .rejected := by
  induction target generalizing source rev with
  | nil =>
      cases source with
      | nil => exact (hlen rfl).elim
      | cons s ss =>
          simpa [rejectionCost, rejectCost] using
            Trace.cons (Step.shortTarget (a := a) (s := s) (ss := ss) (rev := rev)) (Trace.nil _)
  | cons t ts ih =>
      cases source with
      | nil =>
          simpa [rejectionCost, rejectCost] using
            Trace.cons (Step.shortSource (a := a) (t := t) (ts := ts) (rev := rev)) (Trace.nil _)
      | cons s ss =>
          have h := Trace.cons Step.take (Trace.cons Step.multiply
            (Trace.cons Step.add (ih ss ((t + a * s) :: rev) (by simpa using hlen))))
          convert h using 1 <;>
            simp [rejectionCost, takeCost, multiplyCost, addCost,
              Nat.mul_add, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- The executable machine does not silently truncate unequal rows. -/
theorem rejection_runFuel (a : F) (target source : List F)
    (hlen : target.length ≠ source.length) :
    runFuel a (3 * min target.length source.length + 1) (.scan target source []) =
      (.rejected, rejectionCost (min target.length source.length)) :=
  (rejection_trace a target source [] hlen).runFuel_eq

/-! ## Canonical elementary row operation -/

/-- Add `a` times source row `s` to target row `t`, using Mathlib's row update. -/
def addMultiple {m n : Type*} [DecidableEq m] (A : Matrix m n F) (t s : m) (a : F) :
    Matrix m n F := A.updateRow t (fun j => A t j + a * A s j)

/-- Concrete rows materialized from a matrix produce exactly its updated target row. -/
theorem row_runFuel_matrix {m : Type*} {n : ℕ} [DecidableEq m]
    (A : Matrix m (Fin n) F) (t s : m) (a : F) :
    runFuel a (4 * n + 2) (.scan (List.ofFn (A t)) (List.ofFn (A s)) []) =
      (.done (List.ofFn (addMultiple A t s a t)), rowCost n) := by
  have h := row_runFuel a (List.ofFn (A t)) (List.ofFn (A s)) (by simp)
  have hrows : List.zipWith (fun x y => x + a * y) (List.ofFn (A t)) (List.ofFn (A s)) =
      List.ofFn (fun j => A t j + a * A s j) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi
      simp
  simpa [addMultiple, hrows] using h

/-- Matrix-vector multiplication performs the same elementary operation on its result vector. -/
theorem addMultiple_mulVec {m n : Type*} [DecidableEq m] [Fintype n]
    (A : Matrix m n F) (t s : m) (a : F) (x : n → F) :
    addMultiple A t s a *ᵥ x =
      Function.update (A *ᵥ x) t ((A *ᵥ x) t + a * (A *ᵥ x) s) := by
  rw [addMultiple, Matrix.updateRow_mulVec]
  congr 1
  simp [Matrix.mulVec, dotProduct, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

section Ring
variable {R : Type*} [Ring R]

/-- Updating a different source/target pair is invertible on the equation-result vector. -/
theorem update_add_multiple_eq_iff {m : Type*} [DecidableEq m]
    (v b : m → R) (t s : m) (a : R) (hts : t ≠ s) :
    Function.update v t (v t + a * v s) =
      Function.update b t (b t + a * b s) ↔ v = b := by
  constructor
  · intro h
    have hs : v s = b s := by
      simpa [Function.update_of_ne hts.symm] using congrFun h s
    have ht : v t = b t := by
      have h' := congrFun h t
      simp only [Function.update_self] at h'
      rw [hs] at h'
      exact add_right_cancel h'
    funext i
    by_cases hi : i = t
    · simpa [hi] using ht
    · simpa [Function.update_of_ne hi] using congrFun h i
  · rintro rfl
    rfl

/-- Inhomogeneous solutions are preserved when the right-hand side receives the same operation. -/
theorem addMultiple_solution_iff {m n : Type*} [DecidableEq m] [Fintype n]
    (A : Matrix m n R) (b : m → R) (t s : m) (a : R) (hts : t ≠ s) (x : n → R) :
    addMultiple A t s a *ᵥ x = Function.update b t (b t + a * b s) ↔ A *ᵥ x = b := by
  rw [addMultiple_mulVec]
  exact update_add_multiple_eq_iff _ _ t s a hts

/-- Distinct source and target indices preserve the homogeneous solution set (matrix kernel). -/
theorem addMultiple_kernel_iff {m n : Type*} [DecidableEq m] [Fintype n]
    (A : Matrix m n R) (t s : m) (a : R) (hts : t ≠ s) (x : n → R) :
    addMultiple A t s a *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  simpa using addMultiple_solution_iff A 0 t s a hts x

end Ring
/-- Over a commutative ring, the row update is precisely left multiplication by Mathlib's
canonical transvection matrix. Matrix multiplication appears only in the specification. -/
theorem addMultiple_eq_transvection_mul {K m n : Type*} [CommRing K]
    [DecidableEq m] [Fintype m] (A : Matrix m n K) (t s : m) (a : K) :
    addMultiple A t s a = Matrix.transvection t s a * A := by
  ext i j
  by_cases hi : i = t
  · subst i
    simp [addMultiple]
  · simp [addMultiple, Matrix.updateRow_apply, hi]

end Matrix.RowReductionMachine
