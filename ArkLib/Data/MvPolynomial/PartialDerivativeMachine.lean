/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.EvaluationMachine

/-!
# Closed sparse partial differentiation

Terms use `EvaluationMachine.Term`: a coefficient and a materialized list of variable/exponent
pairs. The semantic theorem requires distinct variable indices within each term; term order,
variable order, duplicate terms, zero exponents and zero coefficients remain unrestricted.
Each coefficient is scaled by repeated addition, with no natural-to-field cast in dispatch.
Zero scaled coefficients are dropped, including characteristic-induced cancellation.

Every dispatch costs one control operation. Data counts include list reads, saved-prefix/output
allocations and register writes. Natural comparisons and predecessors, scalar additions/equality
tests, and outputs are separate. Literal zero/one and retained immutable handles are free.
Input preparation, reclamation, interpreter fuel and bit costs are separate obligations.
-/

@[expose] public section

namespace MvPolynomial.PartialDerivativeMachine

abbrev Term := EvaluationMachine.Term

/-- Evaluator-compatible work counts plus scalar equality tests. -/
@[ext] structure Cost where
  work : EvaluationMachine.Cost
  equalities : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0⟩⟩
instance : Add Cost := ⟨fun a b => ⟨a.work + b.work, a.equalities + b.equalities⟩⟩
@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) :
    a + b = ⟨a.work + b.work, a.equalities + b.equalities⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; simp
/-- Associativity of componentwise primitive charges. -/
theorem cost_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- One dispatch with additions, data operations, natural operations, equalities and outputs. -/
def charge (a data natural eq out : ℕ) : Cost := ⟨⟨a, 0, 1, data, natural, out⟩, eq⟩

/-- Actual suspended traversal and scalar-scaling phases. -/
inductive Configuration (F : Type*) where
  | terms (pending output : List (Term F))
  | scan (coefficient : F) (pending saved : List (ℕ × ℕ)) (terms output : List (Term F))
  | scale (coefficient : F) (remaining : ℕ) (accumulator : F)
      (factors saved : List (ℕ × ℕ)) (terms output : List (Term F))
  | test (coefficient : F) (factors saved : List (ℕ × ℕ)) (terms output : List (Term F))
  | restore (coefficient : F) (saved factors : List (ℕ × ℕ)) (terms output : List (Term F))
  | reverse (pending output : List (Term F))
  | done (terms : List (Term F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Independent transitions expose all arithmetic, zero checks, list scans and restoration. -/
inductive Step (j : ℕ) : Configuration F → Cost → Configuration F → Prop where
  | term {c fs ts out} : Step j (.terms ((c, fs) :: ts) out) (charge 0 4 0 0 0)
      (.scan c fs [] ts out)
  | finish {out} : Step j (.terms [] out) (charge 0 3 0 0 0) (.reverse out [])
  | absent {c pre ts out} : Step j (.scan c [] pre ts out) (charge 0 1 0 0 0) (.terms ts out)
  | skip {c i e fs pre ts out} (h : i ≠ j) :
      Step j (.scan c ((i, e) :: fs) pre ts out) (charge 0 6 1 0 0)
        (.scan c fs ((i, e) :: pre) ts out)
  | zeroExponent {c fs pre ts out} :
      Step j (.scan c ((j, 0) :: fs) pre ts out) (charge 0 2 2 0 0) (.terms ts out)
  | hit {c e fs pre ts out} :
      Step j (.scan c ((j, e + 1) :: fs) pre ts out) (charge 0 7 3 0 0)
        (.scale c (e + 1) 0 ((j, e) :: fs) pre ts out)
  | add {c k a fs pre ts out} :
      Step j (.scale c (k + 1) a fs pre ts out) (charge 1 5 2 0 0)
        (.scale c k (a + c) fs pre ts out)
  | scaled {c a fs pre ts out} : Step j (.scale c 0 a fs pre ts out) (charge 0 1 1 0 0)
      (.test a fs pre ts out)
  | zeroCoefficient {fs pre ts out} : Step j (.test 0 fs pre ts out) (charge 0 2 0 1 0)
      (.terms ts out)
  | nonzero {c fs pre ts out} (h : c ≠ 0) :
      Step j (.test c fs pre ts out) (charge 0 2 0 1 0) (.restore c pre fs ts out)
  | restore {c x xs fs ts out} :
      Step j (.restore c (x :: xs) fs ts out) (charge 0 5 0 0 0)
        (.restore c xs (x :: fs) ts out)
  | store {c fs ts out} : Step j (.restore c [] fs ts out) (charge 0 5 0 0 1)
      (.terms ts ((c, fs) :: out))
  | reverse {t ts out} : Step j (.reverse (t :: ts) out) (charge 0 5 0 0 0)
      (.reverse ts (t :: out))
  | emit {out} : Step j (.reverse [] out) (charge 0 2 0 0 1) (.done out)

/-- Closed executable dispatch, including individually charged repeated additions. -/
def step (j : ℕ) : Configuration F → Option (Configuration F × Cost)
  | .terms ((c, fs) :: ts) out => some (.scan c fs [] ts out, charge 0 4 0 0 0)
  | .terms [] out => some (.reverse out [], charge 0 3 0 0 0)
  | .scan _ [] _ ts out => some (.terms ts out, charge 0 1 0 0 0)
  | .scan c ((i, e) :: fs) pre ts out => if i = j then match e with
      | 0 => some (.terms ts out, charge 0 2 2 0 0)
      | k + 1 => some (.scale c (k + 1) 0 ((i, k) :: fs) pre ts out, charge 0 7 3 0 0)
      else some (.scan c fs ((i, e) :: pre) ts out, charge 0 6 1 0 0)
  | .scale c (k + 1) a fs pre ts out => some (.scale c k (a + c) fs pre ts out, charge 1 5 2 0 0)
  | .scale _ 0 a fs pre ts out => some (.test a fs pre ts out, charge 0 1 1 0 0)
  | .test c fs pre ts out => if c = 0 then some (.terms ts out, charge 0 2 0 1 0)
      else some (.restore c pre fs ts out, charge 0 2 0 1 0)
  | .restore c (x :: xs) fs ts out => some (.restore c xs (x :: fs) ts out, charge 0 5 0 0 0)
  | .restore c [] fs ts out => some (.terms ts ((c, fs) :: out), charge 0 5 0 0 1)
  | .reverse (t :: ts) out => some (.reverse ts (t :: out), charge 0 5 0 0 0)
  | .reverse [] out => some (.done out, charge 0 2 0 0 1)
  | .done _ => none

/-- Independent transitions determine both executable state and cost. -/
theorem Step.step_eq {j : ℕ} {s t : Configuration F} {c : Cost} (h : Step j s c t) :
    step j s = some (t, c) := by
  cases h with
  | skip h => simp [step, h]
  | zeroExponent => simp [step]
  | hit => simp [step]
  | zeroCoefficient => simp [step]
  | nonzero h => simp [step, h]
  | _ => rfl

/-- Every executable transition satisfies the independent primitive rules. -/
theorem step_sound {j : ℕ} {s t : Configuration F} {c : Cost}
    (h : step j s = some (t, c)) : Step j s c t := by
  cases s with
  | terms ts out => cases ts with
    | nil => cases h; exact Step.finish
    | cons t ts => cases t; cases h; exact Step.term
  | scan c fs pre ts out => cases fs with
    | nil => cases h; exact Step.absent
    | cons p fs =>
        rcases p with ⟨i, e⟩
        by_cases hi : i = j
        · subst i
          cases e <;> simp only [step] at h <;> cases h <;> constructor
        · simp only [step, if_neg hi] at h
          cases h; exact Step.skip hi
  | scale c k a fs pre ts out => cases k <;> cases h <;> constructor
  | test c fs pre ts out =>
      by_cases hc : c = 0
      · subst c
        simp only [step] at h
        cases h; exact Step.zeroCoefficient
      · simp only [step, if_neg hc] at h
        cases h; exact Step.nonzero hc
  | restore c pre fs ts out => cases pre <;> cases h <;> constructor
  | reverse ts out => cases ts <;> cases h <;> constructor
  | done out => simp [step] at h

/-- Finite execution traces retain exact primitive charges. -/
inductive Trace (j : ℕ) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace j 0 s 0 s
  | cons {n s u t c e} (head : Step j s c u) (tail : Trace j n u e t) :
      Trace j (n + 1) s (c + e) t

omit [DecidableEq F] in
/-- Compose traces without hiding work. -/
theorem Trace.trans {j n m : ℕ} {s u t : Configuration F} {c e : Cost}
    (h : Trace j n s c u) (h' : Trace j m u e t) : Trace j (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons head (ih h')

/-- Interpreter fuel is separate from the primitive cost model. -/
def runFuel (j : ℕ) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | k + 1, s => match step j s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel j k t; (z.1, c + z.2)

/-- Every run, including partial execution, refines an independent trace. -/
theorem runFuel_refines (j fuel : ℕ) (s : Configuration F) :
    ∃ k ≤ fuel, Trace j k s (runFuel j fuel s).2 (runFuel j fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step j s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨k, hk, ht⟩ := ih pair.1
          exact ⟨k + 1, Nat.succ_le_succ hk, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Execution after a certified trace continues from its endpoint. -/
theorem Trace.runFuel_add {j k : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace j k s c t) (extra : ℕ) :
    runFuel j (k + extra) s = ((runFuel j extra t).1, c + (runFuel j extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_assoc]

/-- A completed trace determines execution with any extra fuel. -/
theorem Trace.runFuel_done {j k : ℕ} {s : Configuration F} {out : List (Term F)} {c : Cost}
    (h : Trace j k s c (.done out)) (extra : ℕ) : runFuel j (k + extra) s = (.done out, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel j extra (.done out) = (.done out, (0 : Cost)) := by
    cases extra <;> simp [runFuel, step]
  simpa only [ht, cost_add_zero] using he

end MvPolynomial.PartialDerivativeMachine
