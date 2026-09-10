/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.Semantics
public import ArkLib.Data.Polynomial.CoefficientUpdateMachine
/-!
# Closed direct coefficient computation

Two actual residual coefficient recoveries surround an actual increment of one candidate cell.
Both requested coefficients are read by charged list traversal. Scalar instructions then negate
the intercept, add to form the slope, test zero, invert and multiply. All callee costs survive
embedding, including seed constants and outputs. Shared input roots and materialized samples
are supplied; host fuel and scalar bit costs are outside the primitive model.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.DirectCoefficientMachine

open Polynomial Matrix

abbrev Input := ResidualCoefficientMachine.Input
abbrev Cost := ResidualCoefficientMachine.Cost
abbrev totalCost := ResidualCoefficientMachine.totalCost

/-- Update only the immutable coefficient-list register; other input roots are shared. -/
def withCoefficients {F : Type*} (input : Input F) (cs : List F) : Input F :=
  ⟨cs, input.terms, input.center, input.order⟩

/-- Embed all indexed-update cost fields into the inherited matrix/constant ledger. -/
def updateCost (c : CoefficientUpdateMachine.Cost) : Cost :=
  ⟨⟨⟨c.additions, c.multiplications, c.control, c.data, c.output⟩, 0, 0, 0, c.natural⟩, 0⟩
/-- Callee state-root dispatch. -/
def wrapperCost (n : ℕ) : Cost := ResidualCoefficientMachine.wrapperCost n
/-- Read input/sample roots and initialize the first recovery. -/
def startCost : Cost := ⟨⟨⟨0, 0, 1, 5, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read returned vector and requested index, initializing its cursor. -/
def lookupCost : Cost := ⟨⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Read a cell, test/decrement the index and advance the cursor. -/
def advanceCost : Cost := ⟨⟨⟨0, 0, 1, 4, 0⟩, 0, 0, 0, 2⟩, 0⟩
/-- Read beta and input registers, form `w-1-(k+r)`, and initialize increment one. -/
def selectZeroCost : Cost := ⟨⟨⟨0, 0, 1, 8, 0⟩, 0, 0, 0, 4⟩, 1⟩
/-- Read the second selected scalar and the retained intercept. -/
def selectOneCost : Cost := ⟨⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 0, 1⟩, 0⟩
/-- Retain updated coefficients and initialize the second recovery from the shared samples. -/
def updateReturnCost : Cost := ⟨⟨⟨0, 0, 1, 6, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- One scalar negation, with operand/result register accesses. -/
def negateCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 1, 0, 0⟩, 0⟩
/-- Add the second residual coefficient to the negated intercept. -/
def slopeCost : Cost := ⟨⟨⟨1, 0, 1, 3, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Compare the slope with zero and retain the selected continuation. -/
def testCost : Cost := ⟨⟨⟨0, 0, 1, 3, 0⟩, 0, 0, 1, 0⟩, 0⟩
/-- Invert a tested nonzero slope. -/
def invertCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 1, 0, 0, 0⟩, 0⟩
/-- Multiply the retained negative intercept by the inverse slope. -/
def multiplyCost : Cost := ⟨⟨⟨0, 1, 1, 3, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Retain a failure tag after a rejected callee or exhausted lookup. -/
def rejectCost : Cost := ⟨⟨⟨0, 0, 1, 2, 0⟩, 0, 0, 0, 0⟩, 0⟩
/-- Emit the tagged scalar result. -/
def emitCost : Cost := ⟨⟨⟨0, 0, 1, 2, 1⟩, 0, 0, 0, 0⟩, 0⟩

/-- The recovery mode retains the intercept only on the second pass. -/
inductive Configuration (F : Type*) where
  | start (samples : List F)
  | recover (beta : Option F) (cs samples : List F)
      (state : ResidualCoefficientMachine.Configuration F)
  | lookup (beta : Option F) (samples : List F) (index : ℕ) (values : List F)
  | update (beta : F) (samples : List F) (state : CoefficientUpdateMachine.Configuration F)
  | negate (beta one : F)
  | slope (negativeBeta one : F)
  | test (negativeBeta slope : F)
  | invert (negativeBeta slope : F)
  | multiply (negativeBeta inverse : F)
  | emit (result : Option F)
  | done (result : Option F)
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent rules expose each call, cursor and scalar operation. -/
inductive Step (input : Input F) (w L k : ℕ) :
    Configuration F → Cost → Configuration F → Prop where
  | start {xs} : Step input w L k (.start xs) startCost
      (.recover none input.coefficients xs (.start xs))
  | recover {b cs xs s t c}
      (h : ResidualCoefficientMachine.Step (withCoefficients input cs) L s c t) :
      Step input w L k (.recover b cs xs s) (c + wrapperCost 1) (.recover b cs xs t)
  | recoverReturn {b cs xs out} :
      Step input w L k (.recover b cs xs (.done (some out))) lookupCost (.lookup b xs k out)
  | recoverReject {b cs xs} :
      Step input w L k (.recover b cs xs (.done none)) rejectCost (.emit none)
  | advance {b xs j a tail} : Step input w L k (.lookup b xs (j + 1) (a :: tail))
      advanceCost (.lookup b xs j tail)
  | empty {b xs j} : Step input w L k (.lookup b xs j []) rejectCost (.emit none)
  | selectZero {xs a tail} : Step input w L k (.lookup none xs 0 (a :: tail)) selectZeroCost
      (.update a xs (.start input.coefficients (w - 1 - (k + input.order))))
  | selectOne {b xs a tail} : Step input w L k (.lookup (some b) xs 0 (a :: tail))
      selectOneCost (.negate b a)
  | update {b xs s t c} (h : CoefficientUpdateMachine.Step (1 : F) s c t) :
      Step input w L k (.update b xs s) (updateCost c + wrapperCost 1) (.update b xs t)
  | updateReturn {b xs cs} :
      Step input w L k (.update b xs (.done (some cs))) updateReturnCost
        (.recover (some b) cs xs (.start xs))
  | updateReject {b xs} :
      Step input w L k (.update b xs (.done none)) rejectCost (.emit none)
  | negate {b a} : Step input w L k (.negate b a) negateCost (.slope (-b) a)
  | slope {b a} : Step input w L k (.slope b a) slopeCost (.test b (a + b))
  | zero {b s} (h : s = 0) : Step input w L k (.test b s) testCost (.emit none)
  | nonzero {b s} (h : s ≠ 0) : Step input w L k (.test b s) testCost (.invert b s)
  | invert {b s} : Step input w L k (.invert b s) invertCost (.multiply b s⁻¹)
  | multiply {b v} : Step input w L k (.multiply b v) multiplyCost (.emit (some (b * v)))
  | emit {out} : Step input w L k (.emit out) emitCost (.done out)

/-- Dispatch invokes only one callee step or one explicitly charged local instruction. -/
def step (input : Input F) (w L k : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start xs => some (.recover none input.coefficients xs (.start xs), startCost)
  | .recover b cs xs s => match ResidualCoefficientMachine.step (withCoefficients input cs) L s with
      | some (t, c) => some (.recover b cs xs t, c + wrapperCost 1)
      | none => match s with
          | .done (some out) => some (.lookup b xs k out, lookupCost)
          | .done none => some (.emit none, rejectCost)
          | _ => none
  | .lookup _ _ _ [] => some (.emit none, rejectCost)
  | .lookup b xs (j + 1) (_ :: tail) => some (.lookup b xs j tail, advanceCost)
  | .lookup none xs 0 (a :: _) => some
      (.update a xs (.start input.coefficients (w - 1 - (k + input.order))), selectZeroCost)
  | .lookup (some b) _ 0 (a :: _) => some (.negate b a, selectOneCost)
  | .update b xs s => match CoefficientUpdateMachine.step (1 : F) s with
      | some (t, c) => some (.update b xs t, updateCost c + wrapperCost 1)
      | none => match s with
          | .done (some cs) => some (.recover (some b) cs xs (.start xs), updateReturnCost)
          | .done none => some (.emit none, rejectCost)
          | _ => none
  | .negate b a => some (.slope (-b) a, negateCost)
  | .slope b a => some (.test b (a + b), slopeCost)
  | .test b s => if s = 0 then some (.emit none, testCost) else some (.invert b s, testCost)
  | .invert b s => some (.multiply b s⁻¹, invertCost)
  | .multiply b v => some (.emit (some (b * v)), multiplyCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Each operational rule agrees with executable dispatch and its exact charge. -/
theorem Step.step_eq {input : Input F} {w L k : ℕ} {s t : Configuration F} {c : Cost}
    (h : Step input w L k s c t) : step input w L k s = some (t, c) := by
  cases h with
  | recover h => simp [step, h.step_eq]
  | update h => simp [step, h.step_eq]
  | zero h => simp [step, h]
  | nonzero h => simp [step, h]
  | _ => rfl

/-- Every actual branch has a rule, including callee failures and lookup exhaustion. -/
theorem step_sound {input : Input F} {w L k : ℕ} {s t : Configuration F} {c : Cost}
    (h : step input w L k s = some (t, c)) : Step input w L k s c t := by
  cases s with
  | recover b cs xs s =>
      cases hs : ResidualCoefficientMachine.step (withCoefficients input cs) L s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.recover (ResidualCoefficientMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | update b xs s =>
      cases hs : CoefficientUpdateMachine.step (1 : F) s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.update (CoefficientUpdateMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, reduceCtorEq] at h
          rename_i out
          cases out <;> cases h <;> constructor
  | lookup b xs j values =>
      cases values <;> cases j <;> cases b <;> cases h <;> constructor
  | test b a =>
      by_cases ha : a = 0
      · simp only [step, ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.zero ha
      · simp only [step, ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Step.nonzero ha
  | done out => simp [step] at h
  | _ => cases h; constructor

/-- Actual traces retain every local and nested charge. -/
inductive Trace (input : Input F) (w L k : ℕ) :
    ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input w L k 0 s 0 s
  | cons {n s u t c d} (head : Step input w L k s c u)
      (tail : Trace input w L k n u d t) : Trace input w L k (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [ResidualCoefficientMachine.cost_add, PivotEliminationMachine.cost_add,
    RowReductionMachine.cost_add, Nat.add_assoc]

omit [DecidableEq F] in
/-- Concatenate actual trace segments. -/
theorem Trace.trans {input : Input F} {w L k n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input w L k n s c t) (h' : Trace input w L k m t d u) :
    Trace input w L k (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- The interpreter suspends at fuel exhaustion and never calls a whole-program oracle. -/
def runFuel (input : Input F) (w L k : ℕ) :
    ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input w L k s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input w L k n t; (result.1, c + result.2)

/-- Interpreter output is an actual trace prefix with identical charge. -/
theorem runFuel_refines (input : Input F) (w L k fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input w L k n s (runFuel input w L k fuel s).2
      (runFuel input w L k fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input w L k s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed executions do no additional work with surplus host fuel. -/
theorem Trace.runFuel_done {input : Input F} {w L k n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option F} (h : Trace input w L k n s c (.done out)) (extra : ℕ) :
    runFuel input w L k (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

omit [DecidableEq F] in
/-- Lift either recovery without dropping nested cost fields. -/
theorem lift_recover (input : Input F) (w L k : ℕ) (b : Option F) (cs xs : List F)
    {n : ℕ} {s t : ResidualCoefficientMachine.Configuration F} {c : Cost}
    (h : ResidualCoefficientMachine.Trace (withCoefficients input cs) L n s c t) :
    Trace input w L k n (.recover b cs xs s) (c + wrapperCost n) (.recover b cs xs t) := by
  induction h with
  | nil s => simpa [wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (w := w) (L := L) (k := k) (.recover b cs xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (c + wrapperCost 1) + (d + wrapperCost n) =
          (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.recover head) ih

omit [DecidableEq F] in
/-- Lift the actual candidate update and retain all prefix-copying and arithmetic costs. -/
theorem lift_update (input : Input F) (w L k : ℕ) (b : F) (xs : List F)
    {n : ℕ} {s t : CoefficientUpdateMachine.Configuration F} {c : CoefficientUpdateMachine.Cost}
    (h : CoefficientUpdateMachine.Trace (1 : F) n s c t) :
    Trace input w L k n (.update b xs s) (updateCost c + wrapperCost n) (.update b xs t) := by
  induction h with
  | nil s => simpa [updateCost, wrapperCost, ResidualCoefficientMachine.wrapperCost] using
      Trace.nil (input := input) (w := w) (L := L) (k := k) (.update b xs s)
  | @cons n s u t c d head tail ih =>
      have heq : (updateCost c + wrapperCost 1) + (updateCost d + wrapperCost n) =
          updateCost (c + d) + wrapperCost (n + 1) := by
        ext <;> simp [updateCost, wrapperCost, ResidualCoefficientMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.update head) ih

/-- Exact cost of advancing across `n` cells, before the selected cell is read. -/
def traversalCost (n : ℕ) : Cost := ⟨⟨⟨0, 0, n, 4 * n, 0⟩, 0, 0, 0, 2 * n⟩, 0⟩

omit [DecidableEq F] in
/-- In-range lookup is implemented by one charged cursor transition per preceding cell. -/
theorem lookup_trace (input : Input F) (w L k : ℕ) (b : Option F) (xs values : List F)
    (j : ℕ) (hj : j < values.length) :
    ∃ tail, Trace input w L k j (.lookup b xs j values) (traversalCost j)
      (.lookup b xs 0 (values.getD j 0 :: tail)) := by
  induction values generalizing j with
  | nil => simp at hj
  | cons a values ih =>
      cases j with
      | zero =>
          refine ⟨values, ?_⟩
          simpa [traversalCost] using
            Trace.nil (input := input) (w := w) (L := L) (k := k) (.lookup b xs 0 (a :: values))
      | succ j =>
          obtain ⟨tail, ht⟩ := ih j (by simpa using hj)
          refine ⟨tail, ?_⟩
          convert Trace.cons Step.advance ht using 1
          · ext <;> simp [traversalCost, advanceCost] <;> omega
          · simp

/-- Mathematical scalar result; executable instructions implement it below. -/
def result (beta one : F) : Option F :=
  if one - beta = 0 then none else some (-beta / (one - beta))

/-- Negation, slope, branch and quotient terminate with their own primitive charges. -/
theorem arithmetic_trace (input : Input F) (w L k : ℕ) (beta one : F) :
    ∃ n c, Trace input w L k n (.negate beta one) c (.done (result beta one)) ∧
      n ≤ 6 ∧ totalCost c ≤ 27 := by
  by_cases hz : one + -beta = 0
  · refine ⟨4, negateCost + (slopeCost + (testCost + (emitCost + 0))), ?_, by omega, ?_⟩
    · simpa [result, sub_eq_add_neg, hz] using
        Trace.cons (Step.negate (input := input) (w := w) (L := L) (k := k))
          (Trace.cons Step.slope (Trace.cons (Step.zero hz) (Trace.cons Step.emit (Trace.nil _))))
    · decide
  · refine ⟨6, negateCost + (slopeCost + (testCost +
      (invertCost + (multiplyCost + (emitCost + 0))))), ?_, by omega, ?_⟩
    · simpa [result, sub_eq_add_neg, div_eq_mul_inv, hz] using
        Trace.cons (Step.negate (input := input) (w := w) (L := L) (k := k))
          (Trace.cons Step.slope (Trace.cons (Step.nonzero hz) (Trace.cons Step.invert
            (Trace.cons Step.multiply (Trace.cons Step.emit (Trace.nil _))))))
    · decide

end ReedSolomon.HiddenDerivative.DirectCoefficientMachine
