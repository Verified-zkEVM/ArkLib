/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.CoefficientList
/-!
# Closed initial-jet preparation

A supplied ascending jet is reversed into a descending coefficient list while consuming the
explicit capacity `D+1`. A second loop prepends zeros to fill that capacity. Overlong inputs
are rejected, and success and failure are separately emitted. No list length, reversal, padding,
or polynomial primitive is executed. Leading zeros and an empty initial jet are supported.

The cost extends the jet machine's categories by counting scalar constants. Each padding zero,
list allocation, cursor access, capacity test/decrement, and the initial successor is charged.
Cell reads retrieve head and tail together; retained registers are shared. Input materialization,
host fuel bookkeeping and scalar bit costs remain outside the model.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.JetPreparationMachine

open Polynomial

/-- Preserve all jet-machine categories and separately count materialized scalar constants. -/
@[ext] structure Cost where
  machine : Polynomial.JetHornerMachine.Cost
  constants : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦ ⟨a.machine + b.machine, a.constants + b.constants⟩⟩

@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.machine + b.machine, a.constants + b.constants⟩ := rfl
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0⟩ := rfl

/-- This machine performs no scalar additions or multiplications. -/
def charge (control data natural output constants : ℕ) : Cost :=
  ⟨⟨0, 0, control, data, natural, output⟩, constants⟩

/-- Sum of all primitive categories, including scalar zero constants. -/
def Cost.total (c : Cost) : ℕ := c.machine.total + c.constants

/-- Read inputs, initialize cursor/capacity/buffer, and compute the successor of `D`. -/
def startCost : Cost := charge 1 5 1 0 0
/-- Copy a cell to the reversed buffer, update cursors, and test/decrement capacity. -/
def takeCost : Cost := charge 1 8 2 0 0
/-- Read exhausted input cursor and enter padding with the retained capacity. -/
def padStartCost : Cost := charge 1 2 0 0 0
/-- Test/decrement capacity, materialize zero, allocate a cell and update the buffer root. -/
def padCost : Cost := charge 1 5 2 0 1
/-- Test exhausted padding capacity and retain the success payload. -/
def padDoneCost : Cost := charge 1 2 1 0 0
/-- Test exhausted capacity while reading a remaining input cell, and retain failure. -/
def rejectCost : Cost := charge 1 2 1 0 0
/-- Read and emit the tagged result handle. -/
def emitCost : Cost := charge 1 2 0 1 0

/-- Fixed phases expose reversal, padding, rejection, and emission. -/
inductive Configuration (F : Type*) where
  | start (degree : ℕ) (jet : List F)
  | scan (capacity : ℕ) (remaining reversed : List F)
  | pad (capacity : ℕ) (result : List F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent rules fix every phase change and charge. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | start {D bs} : Step (.start D bs) startCost (.scan (D + 1) bs [])
  | take {n b bs rev} : Step (.scan (n + 1) (b :: bs) rev) takeCost (.scan n bs (b :: rev))
  | padStart {n rev} : Step (.scan n [] rev) padStartCost (.pad n rev)
  | reject {b bs rev} : Step (.scan 0 (b :: bs) rev) rejectCost (.emit none)
  | pad {n out} : Step (.pad (n + 1) out) padCost (.pad n (0 :: out))
  | padDone {out} : Step (.pad 0 out) padDoneCost (.emit (some out))
  | emit {out} : Step (.emit out) emitCost (.done out)

/-- Literal dispatch has no bulk reversal, padding, or hidden capacity computation. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .start D bs => some (.scan (D + 1) bs [], startCost)
  | .scan n [] rev => some (.pad n rev, padStartCost)
  | .scan 0 (_ :: _) _ => some (.emit none, rejectCost)
  | .scan (n + 1) (b :: bs) rev => some (.scan n bs (b :: rev), takeCost)
  | .pad (n + 1) out => some (.pad n (0 :: out), padCost)
  | .pad 0 out => some (.emit (some out), padDoneCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Every independent rule agrees with executable dispatch and its charge. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Every executable branch has an independent operational rule. -/
theorem step_sound {s t : Configuration F} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | start D bs => cases h; constructor
  | scan n bs rev => cases bs <;> cases n <;> cases h <;> constructor
  | pad n out => cases n <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

/-- Finite traces accumulate actual primitive charges. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

/-- Insufficient fuel exposes the current phase rather than fabricating output. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel n t; (result.1, c + result.2)

/-- Every run refines an actual trace with the same accumulated cost. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration F) :
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

/-- Completed traces retain their endpoint and cost under surplus host fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F} {c : Cost} {out : Option (List F)}
    (h : Trace n s c (.done out)) (extra : ℕ) : runFuel (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

private theorem pad_trace (n : ℕ) (out : List F) :
    Trace (n + 2) (.pad n out) (charge (n + 2) (5 * n + 4) (2 * n + 1) 1 n)
      (.done (some (List.replicate n 0 ++ out))) := by
  induction n generalizing out with
  | zero =>
      convert Trace.cons Step.padDone
        (Trace.cons Step.emit (Trace.nil (.done (some out)))) using 1 <;>
        simp [charge, padDoneCost, emitCost]
  | succ n ih =>
      convert Trace.cons Step.pad (ih (0 :: out)) using 1
      · ext <;> simp [charge, padCost] <;> omega
      · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

private theorem scan_trace (n : ℕ) (bs rev : List F) (h : bs.length ≤ n) :
    Trace (n + 3) (.scan n bs rev)
      (charge (n + 3) (8 * bs.length + 5 * (n - bs.length) + 6) (2 * n + 1) 1 (n - bs.length))
      (.done (some (List.replicate (n - bs.length) 0 ++ (bs.reverse ++ rev)))) := by
  induction bs generalizing n rev with
  | nil =>
      convert Trace.cons Step.padStart (pad_trace n rev) using 1 <;>
        simp only [List.length_nil, mul_zero, tsub_zero, zero_add, cost_add,
          JetHornerMachine.cost_add, List.reverse_nil, List.nil_append]
      ext <;> simp [charge, padStartCost] <;> omega
  | cons b bs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          have hb : bs.length ≤ n := by simpa using h
          convert Trace.cons Step.take (ih n (b :: rev) hb) using 1 <;>
            simp only [List.length_cons, Nat.reduceSubDiff, cost_add, JetHornerMachine.cost_add,
              List.reverse_cons, List.append_assoc, List.singleton_append]
          ext <;> simp [charge, takeCost] <;> omega

private theorem reject_trace (n : ℕ) (bs rev : List F) (h : n < bs.length) :
    Trace (n + 2) (.scan n bs rev) (charge (n + 2) (8 * n + 4) (2 * n + 1) 1 0) (.done none) := by
  induction n generalizing bs rev with
  | zero =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          convert Trace.cons Step.reject (Trace.cons Step.emit (Trace.nil (.done none))) using 1
          simp [charge, rejectCost, emitCost]
  | succ n ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          convert Trace.cons Step.take (ih bs (b :: rev) (by simpa using h)) using 1
          ext <;> simp [charge, takeCost] <;> omega

/-- Mathematical output specification with physical width determined by `D`. -/
def prepared (D : ℕ) (bs : List F) : List F := List.replicate (D + 1 - bs.length) 0 ++ bs.reverse

/-- Exact successful charges, including every zero constant written by padding. -/
def successCost (D n : ℕ) : Cost :=
  charge (D + 5) (8 * n + 5 * (D + 1 - n) + 11) (2 * (D + 1) + 2) 1 (D + 1 - n)
/-- Exact rejection charges after consuming the available capacity. -/
def failureCost (D : ℕ) : Cost := charge (D + 4) (8 * (D + 1) + 9) (2 * (D + 1) + 2) 1 0

/-- Full preparation trace, available for later callers to lift one transition at a time. -/
theorem preparation_trace (D : ℕ) (bs : List F) (h : bs.length ≤ D + 1) :
    Trace (D + 5) (.start D bs) (successCost D bs.length) (.done (some (prepared D bs))) := by
  have ht := Trace.cons Step.start (scan_trace (D + 1) bs [] h)
  convert ht using 1
  · ext <;> simp [charge, successCost, startCost] <;> omega
  · simp [prepared]

/-- Actual execution reverses and pads the input, with its exact primitive cost. -/
theorem preparation_runFuel (D : ℕ) (bs : List F) (h : bs.length ≤ D + 1) :
    runFuel (D + 5) (.start D bs) = (.done (some (prepared D bs)), successCost D bs.length) := by
  simpa only [Nat.add_zero] using (preparation_trace D bs h).runFuel_done 0

/-- Overlong jets reject; the machine never silently truncates the input. -/
theorem rejection_runFuel (D : ℕ) (bs : List F) (h : D + 1 < bs.length) :
    runFuel (D + 5) (.start D bs) = (.done none, failureCost D) := by
  have ht := Trace.cons Step.start (reject_trace (D + 1) bs [] h)
  have hr := ht.runFuel_done 1
  convert hr using 1
  ext <;> simp [charge, failureCost, startCost] <;> omega

/-- Successful output has the requested physical width, including leading zeros. -/
theorem prepared_length (D : ℕ) (bs : List F) (h : bs.length ≤ D + 1) :
    (prepared D bs).length = D + 1 := by simp [prepared]; omega

/-- Padding adds only higher zero coefficients and preserves the exact initial-jet polynomial. -/
theorem prepared_polynomial (D : ℕ) (bs : List F) :
    Polynomial.JetHornerMachine.coefficientPolynomial (prepared D bs) =
      Polynomial.CoefficientList.ascendingPolynomial bs :=
  Polynomial.CoefficientList.padReverse_polynomial (D + 1) bs

/-- Every coefficient of the actual prepared output equals the supplied ascending jet entry. -/
theorem prepared_coeff (D : ℕ) (bs : List F) (j : ℕ) :
    (Polynomial.JetHornerMachine.coefficientPolynomial (prepared D bs)).coeff j = bs.getD j 0 := by
  rw [prepared_polynomial, Polynomial.CoefficientList.ascendingPolynomial_coeff]

/-- All coefficients above the supplied jet are zero, including padding positions. -/
theorem prepared_coeff_eq_zero (D : ℕ) (bs : List F) (j : ℕ) (h : bs.length ≤ j) :
    (Polynomial.JetHornerMachine.coefficientPolynomial (prepared D bs)).coeff j = 0 := by
  rw [prepared_coeff]
  simp [List.getD, h]

/-- Exact polynomial representation and width are tied to the actual successful execution. -/
theorem preparation_correct (D : ℕ) (bs : List F) (h : bs.length ≤ D + 1) :
    ∃ cs, runFuel (D + 5) (.start D bs) = (.done (some cs), successCost D bs.length) ∧
      cs.length = D + 1 ∧
      Polynomial.JetHornerMachine.coefficientPolynomial cs =
        Polynomial.CoefficientList.ascendingPolynomial bs ∧
      ∀ j, (Polynomial.JetHornerMachine.coefficientPolynomial cs).coeff j = bs.getD j 0 :=
  ⟨prepared D bs, preparation_runFuel D bs h, prepared_length D bs h,
    prepared_polynomial D bs, prepared_coeff D bs⟩

/-- Successful preparation has linear total primitive cost in degree and input length. -/
theorem successCost_total_le (D n : ℕ) (h : n ≤ D + 1) :
    (successCost D n).total ≤ 40 * (D + n + 1) := by
  simp [Cost.total, successCost, charge, Polynomial.JetHornerMachine.Cost.total]
  omega

/-- Rejection is linear in capacity even when the remaining input is arbitrarily long. -/
theorem failureCost_total_le (D : ℕ) : (failureCost D).total ≤ 40 * (D + 1) := by
  simp [Cost.total, failureCost, charge, Polynomial.JetHornerMachine.Cost.total]
  omega

/-- Both success and rejection give a linear bound on the actual executed cost. -/
theorem preparation_cost_le (D : ℕ) (bs : List F) :
    (runFuel (D + 5) (.start D bs)).2.total ≤ 40 * (D + bs.length + 1) := by
  by_cases h : bs.length ≤ D + 1
  · rw [preparation_runFuel D bs h]
    exact successCost_total_le D bs.length h
  · rw [rejection_runFuel D bs (by omega)]
    have hc := failureCost_total_le D
    dsimp only at hc ⊢
    omega

end ReedSolomon.HiddenDerivative.JetPreparationMachine
