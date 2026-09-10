/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.JetHornerMachine

/-!
# Checked truncation of descending coefficient vectors

To restrict a width-`w` polynomial to degree less than `k`, inspect its first `w-k` coefficient
cells and reject if any is nonzero. On success the remaining list is shared, not copied.
Leading zeros are therefore removed only after being checked. The supplied width is a physical
representation parameter; its equality to input length is explicit in the polynomial theorem.

The closed machine charges every scalar equality, natural operation, cursor access, dispatch,
and output handle. It does not charge input materialization, host fuel, or scalar bit costs.
The intended consumer is the final degree filter of a polynomial list decoder.
-/

@[expose] public section

namespace Polynomial.DegreeTruncationMachine

/-- Primitive charges; zero is a literal and retained list roots are shared. -/
@[ext] structure Cost where
  control : ℕ
  data : ℕ
  natural : ℕ
  equalities : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦ ⟨a.control + b.control, a.data + b.data,
  a.natural + b.natural, a.equalities + b.equalities, a.output + b.output⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.control + b.control, a.data + b.data, a.natural + b.natural,
      a.equalities + b.equalities, a.output + b.output⟩ := rfl

/-- Sum of the actual primitive categories, not a bit-operation count. -/
def Cost.total (c : Cost) : ℕ := c.control + c.data + c.natural + c.equalities + c.output
/-- Read width, cutoff and list root; subtract the cutoff from the supplied width. -/
def startCost : Cost := ⟨1, 3, 1, 0, 0⟩
/-- Test the counter, read a cell, compare with zero, and advance the cursor/counter. -/
def checkCost : Cost := ⟨1, 4, 2, 1, 0⟩
/-- Test the exhausted counter and retain the successful tail for emission. -/
def finishCost : Cost := ⟨1, 2, 1, 0, 0⟩
/-- An exhausted list with a positive pending count is malformed. -/
def rejectCost : Cost := ⟨1, 2, 1, 0, 0⟩
/-- Read the tagged result and emit its handle. -/
def emitCost : Cost := ⟨1, 1, 0, 0, 1⟩

/-- The scan retains only its pending count and the shared coefficient-list suffix. -/
inductive Configuration (F : Type*) where
  | start (coefficients : List F)
  | scan (remaining : ℕ) (coefficients : List F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [Zero F] [DecidableEq F]

/-- Rules specify the zero test and reject rather than discard nonzero high coefficients. -/
inductive Step (w k : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | start {cs} : Step w k (.start cs) startCost (.scan (w - k) cs)
  | zero {n c cs} (h : c = 0) : Step w k (.scan (n + 1) (c :: cs)) checkCost (.scan n cs)
  | nonzero {n c cs} (h : c ≠ 0) :
      Step w k (.scan (n + 1) (c :: cs)) checkCost (.emit none)
  | empty {n} : Step w k (.scan (n + 1) []) rejectCost (.emit none)
  | finish {cs} : Step w k (.scan 0 cs) finishCost (.emit (some cs))
  | emit {out} : Step w k (.emit out) emitCost (.done out)

/-- One charged cursor transition, with no bulk take, drop, length or polynomial operation. -/
def step (w k : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .start cs => some (.scan (w - k) cs, startCost)
  | .scan 0 cs => some (.emit (some cs), finishCost)
  | .scan (_ + 1) [] => some (.emit none, rejectCost)
  | .scan (n + 1) (c :: cs) =>
      if c = 0 then some (.scan n cs, checkCost) else some (.emit none, checkCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Each operational rule has its exact executable successor and cost. -/
theorem Step.step_eq {w k : ℕ} {s t : Configuration F} {c : Cost} (h : Step w k s c t) :
    step w k s = some (t, c) := by
  cases h with
  | zero h => simp [step, h]
  | nonzero h => simp [step, h]
  | _ => rfl

/-- No executable branch escapes the independently stated rules. -/
theorem step_sound {w k : ℕ} {s t : Configuration F} {c : Cost}
    (h : step w k s = some (t, c)) : Step w k s c t := by
  cases s with
  | start cs => cases h; constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h
  | scan n cs =>
      cases n with
      | zero => cases h; constructor
      | succ n =>
          cases cs with
          | nil => cases h; constructor
          | cons a cs =>
              by_cases ha : a = 0
              · simp only [step, ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                exact Step.zero ha
              · simp only [step, ha, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                exact Step.nonzero ha

/-- Traces sum only the charges of actual transitions. -/
inductive Trace (w k : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace w k 0 s 0 s
  | cons {n s t u c d} (head : Step w k s c t) (tail : Trace w k n t d u) :
      Trace w k (n + 1) s (c + d) u

/-- Fuel is host bookkeeping, not an uncharged whole-program evaluation primitive. -/
def runFuel (w k : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step w k s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel w k n t; (result.1, c + result.2)

/-- Every interpreter result is an actual cost-preserving trace prefix. -/
theorem runFuel_refines (w k fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace w k n s (runFuel w k fuel s).2 (runFuel w k fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step w k s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (w := w) (k := k) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- A completed trace is unchanged by extra host fuel. -/
theorem Trace.runFuel_done {w k n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option (List F)} (h : Trace w k n s c (.done out)) (extra : ℕ) :
    runFuel w k (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

/-- Proof-only recursive specification of checked prefix removal. -/
def result : ℕ → List F → Option (List F)
  | 0, cs => some cs
  | _ + 1, [] => none
  | n + 1, c :: cs => if c = 0 then result n cs else none

/-- Every prefix scan terminates, including nonzero and malformed-input rejection. -/
theorem scan_trace (w k n : ℕ) (cs : List F) :
    ∃ steps c, steps ≤ n + 2 ∧ Trace w k steps (.scan n cs) c (.done (result n cs)) := by
  induction n generalizing cs with
  | zero => exact ⟨2, _, le_rfl, Trace.cons Step.finish (Trace.cons Step.emit (Trace.nil _))⟩
  | succ n ih =>
      cases cs with
      | nil => exact ⟨2, _, by omega, Trace.cons Step.empty (Trace.cons Step.emit (Trace.nil _))⟩
      | cons a cs =>
          by_cases ha : a = 0
          · obtain ⟨steps, c, hb, ht⟩ := ih cs
            exact ⟨steps + 1, checkCost + c, by omega,
              by simpa [result, ha] using Trace.cons (Step.zero ha) ht⟩
          · refine ⟨2, checkCost + (emitCost + 0), by omega, ?_⟩
            simpa [result, ha] using
              (Trace.cons (Step.nonzero (w := w) (k := k) (n := n) (cs := cs) ha)
                (Trace.cons Step.emit (Trace.nil _)))

omit [DecidableEq F] in
/-- Every transition costs at most eight primitive operations. -/
theorem Step.total_le {w k : ℕ} {s t : Configuration F} {c : Cost} (h : Step w k s c t) :
    c.total ≤ 8 := by cases h <;> decide

omit [DecidableEq F] in
/-- The trace's work bound counts each visited instruction. -/
theorem Trace.total_le {w k n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace w k n s c t) : c.total ≤ 8 * n := by
  induction h with
  | nil s => decide
  | cons head tail ih =>
      have hh := head.total_le
      simp only [Cost.total, cost_add] at *
      omega

/-- Actual output and linear work bound for the same supplied-fuel computation. -/
theorem truncation_runFuel (w k : ℕ) (cs : List F) :
    ∃ c, runFuel w k (w - k + 3) (.start cs) = (.done (result (w - k) cs), c) ∧
      c.total ≤ 8 * (w - k + 3) := by
  obtain ⟨n, c, hn, ht⟩ := scan_trace w k (w - k) cs
  have h := Trace.cons Step.start ht
  have hr := h.runFuel_done (w - k + 3 - (n + 1))
  rw [Nat.add_sub_of_le (by omega : n + 1 ≤ w - k + 3)] at hr
  exact ⟨startCost + c, hr, h.total_le.trans (by omega)⟩

/-- Successful removal returns exactly a suffix and discards only zero coefficients. -/
theorem result_eq_some_iff (n : ℕ) (cs out : List F) :
    result n cs = some out ↔ cs = List.replicate n 0 ++ out := by
  induction n generalizing cs with
  | zero => simp [result]
  | succ n ih =>
      cases cs with
      | nil => simp [result, List.replicate_succ]
      | cons a cs =>
          by_cases ha : a = 0 <;> simp [result, ha, ih, List.replicate_succ]

end Polynomial.DegreeTruncationMachine
