/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.HighestJetMachine

/-!
# Charged ordered separant-chain execution

Each stage runs the normalized highest-jet selector, stores the original sparse equation and
its selection, then executes the sparse partial derivative when a jet is active. A terminal
selection is stored before explicitly reversing the stage list. Every nested instruction pays
one wrapper control operation and two wrapper data operations on top of its child's charges.
-/

@[expose] public section

namespace MvPolynomial.SeparantChainMachine

abbrev Term := EvaluationMachine.Term
abbrev Cost := PartialDerivativeMachine.Cost
abbrev charge := PartialDerivativeMachine.charge

/-- A retained sparse equation and its selected variable index and exact exponent, if active. -/
@[ext] structure Stage (F : Type*) where
  equation : List (Term F)
  selected : Option (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Suspended selector, derivative, recording and output-order restoration phases. -/
inductive Configuration (F : Type*) where
  | selecting (equation : List (Term F)) (saved : List (Stage F))
      (state : HighestJetMachine.Configuration F)
  | record (equation : List (Term F)) (selected : Option (ℕ × ℕ)) (saved : List (Stage F))
  | derivingAt (index : ℕ) (saved : List (Stage F))
      (state : PartialDerivativeMachine.Configuration F)
  | reverse (pending output : List (Stage F))
  | done (stages : List (Stage F))
  deriving DecidableEq, Repr

/-- Input construction retains the already materialized sparse representation. -/
def initial {F : Type*} (ts : List (Term F)) (saved : List (Stage F) := []) : Configuration F :=
  .selecting ts saved (.normalizing (.terms ts []))

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Local rules compose actual child instructions, with independent wrapper and cell charges. -/
inductive Step : Configuration F → Cost → Configuration F → Prop where
  | selector {eqs pre s t c} (h : HighestJetMachine.step s = some (t, c)) :
      Step (.selecting eqs pre s) (charge 0 2 0 0 0 + c) (.selecting eqs pre t)
  | selected {eqs pre b} : Step (.selecting eqs pre (.done b)) (charge 0 2 0 0 0)
      (.record eqs b pre)
  | terminal {eqs pre} : Step (.record eqs none pre) (charge 0 6 0 0 1)
      (.reverse (⟨eqs, none⟩ :: pre) [])
  | active {eqs pre i e} : Step (.record eqs (some (i, e)) pre) (charge 0 8 0 0 1)
      (.derivingAt i (⟨eqs, some (i, e)⟩ :: pre) (.terms eqs []))
  | derivative {i pre s t c} (h : PartialDerivativeMachine.step i s = some (t, c)) :
      Step (.derivingAt i pre s) (charge 0 2 0 0 0 + c) (.derivingAt i pre t)
  | derived {i pre ts} : Step (.derivingAt i pre (.done ts)) (charge 0 5 0 0 0) (initial ts pre)
  | reverse {r pre out} : Step (.reverse (r :: pre) out) (charge 0 5 0 0 1)
      (.reverse pre (r :: out))
  | emit {out} : Step (.reverse [] out) (charge 0 2 0 0 1) (.done out)

/-- One actual local instruction, with no semantic selector or derivative callback. -/
def step : Configuration F → Option (Configuration F × Cost)
  | .selecting eqs pre (.done b) => some (.record eqs b pre, charge 0 2 0 0 0)
  | .selecting eqs pre s => (HighestJetMachine.step s).map
      (fun z => (.selecting eqs pre z.1, charge 0 2 0 0 0 + z.2))
  | .record eqs none pre => some (.reverse (⟨eqs, none⟩ :: pre) [], charge 0 6 0 0 1)
  | .record eqs (some (i, e)) pre =>
      some (.derivingAt i (⟨eqs, some (i, e)⟩ :: pre) (.terms eqs []), charge 0 8 0 0 1)
  | .derivingAt _ pre (.done ts) => some (initial ts pre, charge 0 5 0 0 0)
  | .derivingAt i pre s => (PartialDerivativeMachine.step i s).map
      (fun z => (.derivingAt i pre z.1, charge 0 2 0 0 0 + z.2))
  | .reverse (r :: pre) out => some (.reverse pre (r :: out), charge 0 5 0 0 1)
  | .reverse [] out => some (.done out, charge 0 2 0 0 1)
  | .done _ => none

/-- Independent parent rules agree with execution, including nested wrapper charges. -/
theorem Step.step_eq {s t : Configuration F} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by
  cases h with
  | selector h =>
      rename_i s _ _
      cases s <;> simp_all only [step, HighestJetMachine.step, Option.map_some, reduceCtorEq]
  | derivative h =>
      rename_i s _ _
      cases s <;> simp_all only [step, PartialDerivativeMachine.step,
        Option.map_some, reduceCtorEq]
  | _ => rfl

/-- A trace retains all child, wrapper, cell and output charges. -/
inductive Trace : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : Step s c u) (tail : Trace n u e t) : Trace (n + 1) s (c + e) t

/-- Compose exact traces. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration F} {c e : Cost}
    (h : Trace n s c u) (h' : Trace m u e t) : Trace (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [PartialDerivativeMachine.cost_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the partial chain and any suspended child machine. -/
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

/-- Completed chains remain completed with additional fuel. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F} {out : List (Stage F)} {c : Cost}
    (h : Trace n s c (.done out)) (extra : ℕ) : runFuel (n + extra) s = (.done out, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel extra (.done out : Configuration F) = (.done out, (0 : Cost)) := by
    cases extra <;> simp [runFuel, step]
  simpa only [ht, PartialDerivativeMachine.cost_add_zero] using he

end MvPolynomial.SeparantChainMachine
