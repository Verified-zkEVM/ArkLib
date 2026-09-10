/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.PartialDerivativeMachine

/-!
# Charged aggregation of sparse terms with explicit keys

The machine inserts each materialized input term into an aggregate list. Keys are compared one
variable/exponent pair at a time. Equal keys have their coefficients added; zero coefficients
and zero sums are dropped. Every traversed prefix is explicitly restored. There is no whole-list
equality, coefficient lookup, support computation or normalization primitive in dispatch.

Costs retain the sparse derivative's work/equality fields. Natural equality tests count separately
from scalar equality; a pair comparison is conservatively charged two natural tests.
List-constructor tests are dispatches; unchanged immutable handles are
retained. Input construction, reclamation, host fuel and bit costs are separate obligations.
-/

@[expose] public section

namespace MvPolynomial.DenseNormalizeMachine

abbrev Term := EvaluationMachine.Term
abbrev Cost := PartialDerivativeMachine.Cost
abbrev charge := PartialDerivativeMachine.charge

/-- Materialized insertion and key-comparison cursors. -/
inductive Configuration (F : Type*) where
  | terms (pending aggregate : List (Term F))
  | search (coefficient : F) (key : List (ℕ × ℕ))
      (remaining saved pending : List (Term F))
  | compare (coefficient : F) (key : List (ℕ × ℕ)) (candidate : Term F)
      (left right : List (ℕ × ℕ)) (remaining saved pending : List (Term F))
  | sum (coefficient : F) (key : List (ℕ × ℕ)) (remaining saved pending : List (Term F))
  | restore (saved aggregate pending : List (Term F))
  | done (aggregate : List (Term F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Independent primitive rules expose key scans, scalar cancellation and list restoration. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | skipZero {fs ts out} : Step (.terms ((0, fs) :: ts) out) (charge 0 2 0 1 0) (.terms ts out)
  | term {c fs ts out} (h : c ≠ 0) : Step (.terms ((c, fs) :: ts) out) (charge 0 6 0 1 0)
      (.search c fs out [] ts)
  | emit {out} : Step (.terms [] out) (charge 0 2 0 0 1) (.done out)
  | newKey {c fs pre ts} : Step (.search c fs [] pre ts) (charge 0 4 0 0 0)
      (.restore pre [(c, fs)] ts)
  | candidate {c fs d gs rest pre ts} : Step (.search c fs ((d, gs) :: rest) pre ts)
      (charge 0 8 0 0 0) (.compare c fs (d, gs) fs gs rest pre ts)
  | equal {c fs d gs rest pre ts} : Step (.compare c fs (d, gs) [] [] rest pre ts)
      (charge 1 4 0 0 0) (.sum (c + d) fs rest pre ts)
  | pair {c fs t i e is js rest pre ts} :
      Step (.compare c fs t ((i, e) :: is) ((i, e) :: js) rest pre ts) (charge 0 4 2 0 0)
        (.compare c fs t is js rest pre ts)
  | different {c fs t i e k f is js rest pre ts} (h : i ≠ k ∨ e ≠ f) :
      Step (.compare c fs t ((i, e) :: is) ((k, f) :: js) rest pre ts) (charge 0 6 2 0 0)
        (.search c fs rest (t :: pre) ts)
  | short {c fs t k f js rest pre ts} :
      Step (.compare c fs t [] ((k, f) :: js) rest pre ts) (charge 0 5 0 0 0)
        (.search c fs rest (t :: pre) ts)
  | long {c fs t i e is rest pre ts} :
      Step (.compare c fs t ((i, e) :: is) [] rest pre ts) (charge 0 5 0 0 0)
        (.search c fs rest (t :: pre) ts)
  | zeroSum {fs rest pre ts} : Step (.sum 0 fs rest pre ts) (charge 0 3 0 1 0)
      (.restore pre rest ts)
  | nonzeroSum {c fs rest pre ts} (h : c ≠ 0) : Step (.sum c fs rest pre ts) (charge 0 5 0 1 0)
      (.restore pre ((c, fs) :: rest) ts)
  | restore {t pre out ts} : Step (.restore (t :: pre) out ts) (charge 0 5 0 0 0)
      (.restore pre (t :: out) ts)
  | restored {out ts} : Step (.restore [] out ts) (charge 0 3 0 0 0) (.terms ts out)

/-- One actual local transition; key equality uses only natural comparisons of one pair. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .terms [] out => some (.done out, charge 0 2 0 0 1)
  | .terms ((c, fs) :: ts) out => if c = 0 then some (.terms ts out, charge 0 2 0 1 0)
      else some (.search c fs out [] ts, charge 0 6 0 1 0)
  | .search c fs [] pre ts => some (.restore pre [(c, fs)] ts, charge 0 4 0 0 0)
  | .search c fs ((d, gs) :: rest) pre ts =>
      some (.compare c fs (d, gs) fs gs rest pre ts, charge 0 8 0 0 0)
  | .compare c fs (d, _) [] [] rest pre ts => some (.sum (c + d) fs rest pre ts, charge 1 4 0 0 0)
  | .compare c fs t ((i, e) :: is) ((k, f) :: js) rest pre ts =>
      if i = k ∧ e = f then some (.compare c fs t is js rest pre ts, charge 0 4 2 0 0)
      else some (.search c fs rest (t :: pre) ts, charge 0 6 2 0 0)
  | .compare c fs t [] (_ :: _) rest pre ts | .compare c fs t (_ :: _) [] rest pre ts =>
      some (.search c fs rest (t :: pre) ts, charge 0 5 0 0 0)
  | .sum c fs rest pre ts => if c = 0 then some (.restore pre rest ts, charge 0 3 0 1 0)
      else some (.restore pre ((c, fs) :: rest) ts, charge 0 5 0 1 0)
  | .restore (t :: pre) out ts => some (.restore pre (t :: out) ts, charge 0 5 0 0 0)
  | .restore [] out ts => some (.terms ts out, charge 0 3 0 0 0)
  | .done _ => none

/-- Independent transitions determine executable state and exact charges. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | skipZero => simp [step]
  | term h => simp [step, h]
  | pair => simp [step]
  | different h => simp [step, not_and_or.mpr h]
  | zeroSum => simp [step]
  | nonzeroSum h => simp [step, h]
  | _ => rfl

/-- Every dispatch has an independent primitive derivation. -/
theorem step_sound {s t : Configuration F} {c : Cost} (h : step s = some (t, c)) : Step s c t := by
  cases s with
  | terms ts out => cases ts with
    | nil => cases h; exact Step.emit
    | cons t ts =>
        rcases t with ⟨a, fs⟩
        by_cases ha : a = 0
        · subst a; simp only [step] at h; cases h; exact Step.skipZero
        · simp only [step, if_neg ha] at h; cases h; exact Step.term ha
  | search c fs rest pre ts => cases rest with
    | nil => cases h; exact Step.newKey
    | cons t rest => cases t; cases h; exact Step.candidate
  | compare c fs t left right rest pre ts =>
      cases left with
      | nil => cases right with
        | nil => cases t; cases h; exact Step.equal
        | cons p right => cases p; cases h; exact Step.short
      | cons p left => cases right with
        | nil => cases p; cases h; exact Step.long
        | cons q right =>
            rcases p with ⟨i, e⟩
            rcases q with ⟨k, f⟩
            by_cases hp : i = k ∧ e = f
            · rcases hp with ⟨rfl, rfl⟩
              simp only [step] at h; cases h; exact Step.pair
            · simp only [step, if_neg hp] at h
              cases h; exact Step.different (not_and_or.mp hp)
  | sum c fs rest pre ts =>
      by_cases hc : c = 0
      · subst c; simp only [step] at h; cases h; exact Step.zeroSum
      · simp only [step, if_neg hc] at h; cases h; exact Step.nonzeroSum hc
  | restore pre out ts => cases pre <;> cases h <;> constructor
  | done out => simp [step] at h

/-- Finite traces retain all primitive charges. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : Step s c u) (tail : Trace n u e t) : Trace (n + 1) s (c + e) t

omit [DecidableEq F] in
/-- Compose actual traces without uncharged work. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c e : Cost}
    (h : Trace n s c u) (h' : Trace m u e t) : Trace (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [PartialDerivativeMachine.cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Trace.cons head (ih h')

/-- Insufficient fuel leaves the partial configuration observable. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | k + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel k t; (z.1, c + z.2)

/-- Every executable run refines an independent trace. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration F) :
    ∃ k ≤ fuel, Trace k s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨k, hk, ht⟩ := ih pair.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Continue from the endpoint of a certified trace. -/
theorem Trace.runFuel_add {k : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace k s c t) (extra : ℕ) :
    runFuel (k + extra) s = ((runFuel extra t).1, c + (runFuel extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [PartialDerivativeMachine.cost_assoc]

/-- A completed trace determines every sufficiently fueled execution. -/
theorem Trace.runFuel_done {k : ℕ} {s : Configuration F} {out : List (Term F)} {c : Cost}
    (h : Trace k s c (.done out)) (extra : ℕ) : runFuel (k + extra) s = (.done out, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel extra (.done out) = (.done out, (0 : Cost)) := by
    cases extra <;> simp [runFuel, step]
  simpa only [ht, PartialDerivativeMachine.cost_add_zero] using he

end MvPolynomial.DenseNormalizeMachine
