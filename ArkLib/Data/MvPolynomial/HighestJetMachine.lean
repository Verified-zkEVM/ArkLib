/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.DenseNormalizeRefinement

/-!
# Charged highest-jet selection

Normalization is executed before any scan. Index zero represents the distinguished variable;
positive indices represent jets. Each scan step reads one factor and charges five natural
comparisons conservatively, together with cursor and best-register updates. There are no
polynomial degree, support, coefficient, maximum-list or polynomial-zero operations in dispatch.
Every delegated normalization step also pays one control operation and two data operations
for its wrapper.
-/

@[expose] public section

namespace MvPolynomial.HighestJetMachine

abbrev Term := EvaluationMachine.Term
abbrev Cost := DenseNormalizeMachine.Cost
abbrev charge := DenseNormalizeMachine.charge

/-- A local register update examines just one variable/exponent pair. -/
def update (p : ℕ × ℕ) (best : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  if p.1 = 0 ∨ p.2 = 0 then best else
    match best with
    | none => some p
    | some b => if b.1 < p.1 then some p
        else if p.1 = b.1 ∧ b.2 < p.2 then some p else some b

/-- Independent register rules distinguish excluded pairs and the two improving comparisons. -/
inductive Update : (ℕ × ℕ) → Option (ℕ × ℕ) → Option (ℕ × ℕ) → Prop where
  | skip {p b} (h : p.1 = 0 ∨ p.2 = 0) : Update p b b
  | first {p} (h : p.1 ≠ 0 ∧ p.2 ≠ 0) : Update p none (some p)
  | higher {p b} (h : p.1 ≠ 0 ∧ p.2 ≠ 0) (hi : b.1 < p.1) :
      Update p (some b) (some p)
  | larger {p b} (h : p.1 ≠ 0 ∧ p.2 ≠ 0) (hi : p.1 = b.1) (he : b.2 < p.2) :
      Update p (some b) (some p)
  | keep {p b} (h : p.1 ≠ 0 ∧ p.2 ≠ 0) (hi : p.1 ≤ b.1)
      (he : p.1 = b.1 → p.2 ≤ b.2) : Update p (some b) (some b)

/-- Register specifications agree with the executable comparisons. -/
theorem Update.eq {p b r} (h : Update p b r) : update p b = r := by
  cases h with
  | skip h => simp [update, h]
  | first h => simp [update, h.1, h.2]
  | higher h hi => simp [update, h.1, h.2, hi]
  | larger h hi he =>
      simp only [update, h.1, h.2, or_self, if_false]
      simp [hi, he]
  | @keep b h hi he =>
      have hn : ¬(p.1 = b.1 ∧ b.2 < p.2) := by omega
      simp [update, h.1, h.2, Nat.not_lt.mpr hi, hn]

/-- Every local update satisfies an independent register rule. -/
theorem update_sound (p : ℕ × ℕ) (b : Option (ℕ × ℕ)) : Update p b (update p b) := by
  by_cases hp : p.1 = 0 ∨ p.2 = 0
  · simpa [update, hp] using Update.skip (b := b) hp
  · have h : p.1 ≠ 0 ∧ p.2 ≠ 0 := not_or.mp hp
    cases b with
    | none => simpa [update, hp] using Update.first h
    | some b =>
        by_cases hi : b.1 < p.1
        · simpa [update, hp, hi] using Update.higher h hi
        · by_cases he : p.1 = b.1 ∧ b.2 < p.2
          · simpa only [update, if_neg hp, if_neg hi, if_pos he] using
              Update.larger h he.1 he.2
          · simpa [update, hp, hi, he] using Update.keep h (Nat.le_of_not_lt hi)
              (by omega)

/-- Normalization and scan cursors, with a single best-pair register. -/
inductive Configuration (F : Type*) where
  | normalizing (state : DenseNormalizeMachine.Configuration F)
  | terms (pending : List (Term F)) (best : Option (ℕ × ℕ))
  | factors (pending : List (ℕ × ℕ)) (terms : List (Term F)) (best : Option (ℕ × ℕ))
  | done (best : Option (ℕ × ℕ))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Independent rules charge normalization, cursor changes and every register update. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | normalize {s t c} (h : DenseNormalizeMachine.Step s c t) :
      Step (.normalizing s) (charge 0 2 0 0 0 + c) (.normalizing t)
  | normalized {out} : Step (.normalizing (.done out)) (charge 0 2 0 0 0) (.terms out none)
  | term {c fs ts b} : Step (.terms ((c, fs) :: ts) b) (charge 0 3 0 0 0) (.factors fs ts b)
  | factor {p fs ts b r} (h : Update p b r) :
      Step (.factors (p :: fs) ts b) (charge 0 6 5 0 0) (.factors fs ts r)
  | next {ts b} : Step (.factors [] ts b) (charge 0 2 0 0 0) (.terms ts b)
  | emit {b} : Step (.terms [] b) (charge 0 2 0 0 1) (.done b)

/-- One charged local transition. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .normalizing (.done out) => some (.terms out none, charge 0 2 0 0 0)
  | .normalizing s => (DenseNormalizeMachine.step s).map
      (fun z => (.normalizing z.1, charge 0 2 0 0 0 + z.2))
  | .terms [] b => some (.done b, charge 0 2 0 0 1)
  | .terms ((_, fs) :: ts) b => some (.factors fs ts b, charge 0 3 0 0 0)
  | .factors [] ts b => some (.terms ts b, charge 0 2 0 0 0)
  | .factors (p :: fs) ts b => some (.factors fs ts (update p b), charge 0 6 5 0 0)
  | .done _ => none

/-- Independent transitions determine exact executable states and charges. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | normalize h =>
      have he := h.step_eq
      cases h <;> simp only [step, he, Option.map_some]
  | factor h => simp [step, h.eq]
  | _ => rfl

/-- Finite traces include all normalization and scan charges. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : Step s c u) (tail : Trace n u e t) : Trace (n + 1) s (c + e) t

omit [DecidableEq F] in
/-- Compose two charged traces. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c e : Cost}
    (h : Trace n s c u) (h' : Trace m u e t) : Trace (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [PartialDerivativeMachine.cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the partial state, including any unfinished normalization. -/
def runFuel : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel n t; (z.1, c + z.2)

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

/-- A completed trace remains completed with arbitrary extra fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F} {b : Option (ℕ × ℕ)} {c : Cost}
    (h : Trace n s c (.done b)) (extra : ℕ) : runFuel (n + extra) s = (.done b, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel extra (.done b : Configuration F) = (.done b, (0 : Cost)) := by
    cases extra <;> simp [runFuel, step]
  simpa only [ht, PartialDerivativeMachine.cost_add_zero] using he

end MvPolynomial.HighestJetMachine
