/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Matrix.ForwardEchelonMachine
public import ArkLib.Data.Matrix.BackSubstitutionMachine

/-!
# Closed nonzero homogeneous kernel extraction

The input consists of a width and materialized augmented rows. Preflight checks every RHS and
coefficient-list width. The driver executes forward elimination, scans ordered pivots for the
first free column, builds a unit seed one cell at a time, and executes back substitution.
All delegated work consists of single callee steps. There is no whole-run or solver callback.

Costs use shared immutable list handles. Each driver dispatch pays one control operation;
`charge` records data accesses/register writes, natural operations, field equalities and outputs.
Callee delegation adds one dispatch and two data operations to every callee step. Input
materialization, memory reclamation, fuel administration and field bit costs are separate.
-/

@[expose] public section

namespace Matrix.NonzeroKernelMachine

open ForwardEchelonMachine
abbrev Cost := PivotEliminationMachine.Cost

/-- One driver dispatch with explicit primitive charges. -/
def charge (data natural equalities output : ℕ) : Cost :=
  ⟨⟨0, 0, 1, data, output⟩, 0, 0, equalities, natural⟩
/-- The suspended callee root is read and rewritten on every inner transition. -/
abbrev wrapperCost := BackSubstitutionMachine.wrapperCost

/-- Materialized cursors and suspended executable callees. -/
inductive Configuration (F : Type*) where
  | check (original pending : List (Row F))
  | width (original pending : List (Row F)) (coefficients : List F) (remaining : ℕ)
  | forward (inner : ForwardEchelonMachine.Configuration F)
  | free (pivots : List (Pivot F)) (rest : List (Row F)) (cursor : List (Pivot F)) (column : ℕ)
  | seed (pivots : List (Pivot F)) (rest : List (Row F)) (chosen remaining : ℕ) (out : List F)
  | back (chosen : ℕ) (inner : BackSubstitutionMachine.Configuration F)
  | done (chosen : ℕ) (values : List F)
  | noFree
  | rejected
  deriving DecidableEq, Repr

variable {F : Type*} [Field F] [DecidableEq F]

/-- Independent primitive transitions. Free-column probes conservatively charge both natural
comparisons even on an empty pivot cursor; all seed cells are allocated explicitly. -/
inductive Step (n : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | check {orig cs rs} : Step n (.check orig ((cs, 0) :: rs)) (charge 6 0 1 0)
      (.width orig rs cs n)
  | rhs {orig r rs} (h : r.2 ≠ 0) :
      Step n (.check orig (r :: rs)) (charge 2 0 1 1) .rejected
  | launch {orig} : Step n (.check orig []) (charge 5 0 0 0) (.forward (.loop 0 n orig []))
  | width {orig rs x xs k} : Step n (.width orig rs (x :: xs) (k + 1)) (charge 3 2 0 0)
      (.width orig rs xs k)
  | widthEnd {orig rs} : Step n (.width orig rs [] 0) (charge 3 1 0 0) (.check orig rs)
  | short {orig rs k} : Step n (.width orig rs [] (k + 1)) (charge 1 1 0 1) .rejected
  | long {orig rs x xs} : Step n (.width orig rs (x :: xs) 0) (charge 1 1 0 1) .rejected
  | forward {s c t} (h : ForwardEchelonMachine.Step s c t) :
      Step n (.forward s) (c + wrapperCost 1) (.forward t)
  | forwardDone {ps rs} : Step n (.forward (.done ps rs)) (charge 6 0 0 0) (.free ps rs ps 0)
  | forwardFailed : Step n (.forward .rejected) (charge 1 0 0 1) .rejected
  | noFree {ps rs cur j} (h : n ≤ j) :
      Step n (.free ps rs cur j) (charge 6 2 0 1) .noFree
  | freeNil {ps rs j} (h : j < n) : Step n (.free ps rs [] j) (charge 6 2 0 0)
      (.seed ps rs j n [])
  | freeHit {ps rs p cur j} (h : j < n) (hp : p.1 = j) :
      Step n (.free ps rs (p :: cur) j) (charge 6 3 0 0) (.free ps rs cur (j + 1))
  | freeGap {ps rs p cur j} (h : j < n) (hp : p.1 ≠ j) :
      Step n (.free ps rs (p :: cur) j) (charge 6 2 0 0) (.seed ps rs j n [])
  | seed {ps rs j k out} : Step n (.seed ps rs j (k + 1) out) (charge 5 3 0 0)
      (.seed ps rs j k ((if k = j then 1 else 0) :: out))
  | backStart {ps rs j out} : Step n (.seed ps rs j 0 out) (charge 6 1 0 0)
      (.back j (.check rs ps out))
  | back {j s c t} (h : BackSubstitutionMachine.Step s c t) :
      Step n (.back j s) (c + wrapperCost 1) (.back j t)
  | emit {j out} : Step n (.back j (.done out)) (charge 3 0 0 1) (.done j out)
  | backFailed {j} : Step n (.back j .rejected) (charge 1 0 0 1) .rejected
  | inconsistent {j} : Step n (.back j .inconsistent) (charge 1 0 0 1) .rejected

/-- Closed dispatch: each delegated branch advances exactly one actual callee step. -/
def step (n : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .check orig [] => some (.forward (.loop 0 n orig []), charge 5 0 0 0)
  | .check orig (r :: rs) => if r.2 = 0 then some (.width orig rs r.1 n, charge 6 0 1 0)
      else some (.rejected, charge 2 0 1 1)
  | .width orig rs [] 0 => some (.check orig rs, charge 3 1 0 0)
  | .width orig rs (_ :: xs) (k + 1) => some (.width orig rs xs k, charge 3 2 0 0)
  | .width _ _ [] (_ + 1) | .width _ _ (_ :: _) 0 => some (.rejected, charge 1 1 0 1)
  | .forward s => match ForwardEchelonMachine.step s with
      | some (t, c) => some (.forward t, c + wrapperCost 1)
      | none => match s with
          | .done ps rs => some (.free ps rs ps 0, charge 6 0 0 0)
          | .rejected => some (.rejected, charge 1 0 0 1)
          | _ => none
  | .free ps rs cur j => if j < n then match cur with
      | [] => some (.seed ps rs j n [], charge 6 2 0 0)
      | p :: tail => if p.1 = j then some (.free ps rs tail (j + 1), charge 6 3 0 0)
          else some (.seed ps rs j n [], charge 6 2 0 0)
      else some (.noFree, charge 6 2 0 1)
  | .seed ps rs j (k + 1) out =>
      some (.seed ps rs j k ((if k = j then 1 else 0) :: out), charge 5 3 0 0)
  | .seed ps rs j 0 out => some (.back j (.check rs ps out), charge 6 1 0 0)
  | .back j s => match BackSubstitutionMachine.step s with
      | some (t, c) => some (.back j t, c + wrapperCost 1)
      | none => match s with
          | .done out => some (.done j out, charge 3 0 0 1)
          | .rejected | .inconsistent => some (.rejected, charge 1 0 0 1)
          | _ => none
  | .done _ _ | .noFree | .rejected => none

/-- Every independent transition has the specified executable state and exact cost. -/
theorem Step.step_eq {n : ℕ} {s t : Configuration F} {c : Cost} (h : Step n s c t) :
    step n s = some (t, c) := by
  cases h with
  | check => simp [step]
  | rhs h => simp [step, h]
  | forward h => simp only [step, h.step_eq]
  | back h => simp only [step, h.step_eq]
  | noFree h => simp [step, Nat.not_lt.mpr h]
  | freeNil h => simp [step, h]
  | freeHit h hp => simp [step, h, hp]
  | freeGap h hp => simp [step, h, hp]
  | _ => rfl

/-- Every successful dispatch refines the independent primitive rules. -/
theorem step_sound {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : step n s = some (t, c)) : Step n s c t := by
  cases s with
  | check orig rs =>
      cases rs with
      | nil => cases h; exact Step.launch
      | cons r rs =>
          by_cases hz : r.2 = 0
          · rcases r with ⟨cs, b⟩
            simp only at hz
            subst b
            simp only [step] at h
            rcases h with ⟨rfl, rfl⟩; exact Step.check
          · simp only [step, if_neg hz, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; exact Step.rhs hz
  | width orig rs cs k => cases cs <;> cases k <;> cases h <;> constructor
  | free ps rs cur j =>
      by_cases hj : j < n
      · cases cur with
        | nil => simp only [step, if_pos hj] at h; cases h; exact Step.freeNil hj
        | cons p tail =>
            by_cases hp : p.1 = j
            · simp only [step, if_pos hj, if_pos hp] at h
              cases h; exact Step.freeHit hj hp
            · simp only [step, if_pos hj, if_neg hp] at h
              cases h; exact Step.freeGap hj hp
      · simp only [step, if_neg hj] at h
        cases h; exact Step.noFree (Nat.le_of_not_gt hj)
  | seed ps rs j k out => cases k <;> cases h <;> constructor
  | forward s =>
      cases hs : ForwardEchelonMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.forward (ForwardEchelonMachine.step_sound hs)
      | none =>
          cases s with
          | done ps rs => cases h; exact Step.forwardDone
          | rejected => cases h; exact Step.forwardFailed
          | _ => simp [step, hs] at h
  | back j s =>
      cases hs : BackSubstitutionMachine.step s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.back (BackSubstitutionMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases h; exact Step.emit
          | rejected => cases h; exact Step.backFailed
          | inconsistent => cases h; exact Step.inconsistent
          | _ => simp [step, hs] at h
  | done j out => simp [step] at h
  | noFree => simp [step] at h
  | rejected => simp [step] at h

/-- Finite execution with accumulated primitive cost. -/
inductive Trace (n : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace n 0 s 0 s
  | cons {k s u t c e} (head : Step n s c u) (tail : Trace n k u e t) :
      Trace n (k + 1) s (c + e) t

/-- Associativity of componentwise primitive charges. -/
theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

omit [DecidableEq F] in
/-- Compose traces without hiding driver work. -/
theorem Trace.trans {n k m : ℕ} {s u t : Configuration F} {c e : Cost}
    (h : Trace n k s c u) (h' : Trace n m u e t) : Trace n (k + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Fuel limits interpretation; insufficient fuel exposes partial state. -/
def runFuel (n : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | k + 1, s => match step n s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel n k t; (z.1, c + z.2)

/-- All executable runs refine independent traces, including partial runs. -/
theorem runFuel_refines (n fuel : ℕ) (s : Configuration F) :
    ∃ k ≤ fuel, Trace n k s (runFuel n fuel s).2 (runFuel n fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step n s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨k, hk, ht⟩ := ih pair.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Executing beyond a certified trace continues from its endpoint. -/
theorem Trace.runFuel_add {n k : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n k s c t) (extra : ℕ) :
    runFuel n (k + extra) s = ((runFuel n extra t).1, c + (runFuel n extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_assoc]

/-- Terminal traces determine every sufficiently fueled executable result. -/
theorem terminal_run {n k B : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace n k s c t) (ht : step n t = none) (hk : k ≤ B) :
    runFuel n B s = (t, c) := by
  have hx : runFuel n (B - k) t = (t, (0 : Cost)) := by
    cases B - k <;> simp [runFuel, ht]
  have heq := h.runFuel_add (B - k)
  rw [show k + (B - k) = B by omega, hx] at heq
  simpa using heq

end Matrix.NonzeroKernelMachine
