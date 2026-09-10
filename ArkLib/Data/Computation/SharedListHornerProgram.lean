/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FieldLiteralMachine
public import ArkLib.Data.Computation.SharedListHornerRefinement

-- The physical-output refinement reduces the executable Horner fold.
import all CompPoly.Univariate.Basic

/-!
# Complete physical Horner entry with charged scalar reset

The zero child materializes the accumulator directly on tape zero while retaining the modulus
on tape four. The point and list pointer stay on eight and twelve. One control handoff enters
the actual shared-list Horner loop, on the same twenty-one tapes and RAM. Initial coefficient
and point representations remain explicit inputs; no supplied zero accumulator is required.
-/

@[expose] public section

namespace Computation.SharedListHornerProgram

open AddressedBits (Memory)
open BinaryWordMachine (Word value)
open SharedListHeap (RepList nilPointer)

inductive Control where
  | initializing (point pointer : Word) (child : FieldLiteralMachine.Control)
  | evaluating (child : SharedListHornerMachine.Control)
  deriving DecidableEq, Repr

structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

def step : Configuration → Option Configuration
  | ⟨mem, .initializing point pointer child⟩ =>
      match FieldLiteralMachine.step child with
      | some next => some ⟨mem, .initializing point pointer next⟩
      | none => match child with
          | .done q out => some ⟨mem, .evaluating (.taking out point (.scan q pointer [] false))⟩
          | _ => none
  | ⟨mem, .evaluating child⟩ =>
      match SharedListHornerMachine.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .evaluating next.control⟩
      | none => none

def tapes : Control → Fin 21 → Word
  | .initializing point pointer child =>
      let t := FieldLiteralMachine.tapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, [], [], point, [], [], [],
        pointer, [], [], [], [], [], [], [], []]
  | .evaluating child => SharedListHornerMachine.tapes child

theorem handoff_tapes (q point pointer out : Word) :
    tapes (.initializing point pointer (.done q out)) =
      tapes (.evaluating (.taking out point (.scan q pointer [] false))) := by
  funext i
  fin_cases i <;> rfl

theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s.control) (tapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | initializing point pointer child =>
      cases hs : FieldLiteralMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := FieldLiteralMachine.step_local hs
          intro i
          fin_cases i
          · exact hl 0
          · exact hl 1
          · exact hl 2
          · exact hl 3
          · exact hl 4
          · exact hl 5
          all_goals exact .keep _
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [handoff_tapes]
          intro i
          exact .keep _
  | evaluating child =>
      cases hs : SharedListHornerMachine.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact SharedListHornerMachine.step_local hs
      | none => simp only [step, hs] at h; cases h

inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_literal (mem : Memory) (point pointer : Word) {n : ℕ}
    {s t : FieldLiteralMachine.Control} (h : FieldLiteralMachine.Trace n s t) :
    Trace n ⟨mem, .initializing point pointer s⟩ ⟨mem, .initializing point pointer t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_loop {n : ℕ} {s t : SharedListHornerMachine.Configuration}
    (h : SharedListHornerMachine.Trace n s t) :
    Trace n ⟨s.memory, .evaluating s.control⟩ ⟨t.memory, .evaluating t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Reset plus its handoff and the complete heap-based loop. -/
def totalBound (w : ℕ) (q : Word) (length : ℕ) : ℕ :=
  2 * q.length + 6 + SharedListHornerMachine.totalBound w q length

/-- A complete physical run, from an empty accumulator tape, realizes the zero-start Horner fold. -/
theorem execution {mem : Memory} {w : ℕ} {q point p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q) (hwpoint : point.length = q.length) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .initializing point p (.start q false)⟩
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      runFuel n ⟨mem, .initializing point p (.start q false)⟩ =
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      (value out : ZMod (value q)) =
        (xs.map (fun c ↦ (value c : ZMod (value q)))).foldl
          (fun a c ↦ a * (value point : ZMod (value q)) + c) 0 := by
  obtain ⟨zero, hz, _hrz, hwz, hvz⟩ := FieldLiteralMachine.zero_correct q
  have hred : value zero < value q := by rw [hvz]; omega
  obtain ⟨n, hn, out, ht, _hrt, hw, hb, hv⟩ :=
    SharedListHornerMachine.loop_execution hr hred hpoint hcoeff hwz hwpoint
  have hh : Trace 1 ⟨mem, .initializing point p (.done q zero)⟩
      ⟨mem, .evaluating (.taking zero point (.scan q p [] false))⟩ := .cons rfl (.nil _)
  have hall := ((lift_literal mem point p hz).append hh).append (lift_loop ht)
  exact ⟨_, by unfold totalBound; omega, out, hall, hall.runFuel_eq, hw, hb,
    by simpa only [hvz, Nat.cast_zero] using hv⟩

/-- Both actual programs halt at the same value; the source starts at its reset instruction. -/
theorem source_execution {mem : Memory} {w : ℕ} {q point p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q) (hwpoint : point.length = q.length) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .initializing point p (.start q false)⟩
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      runFuel n ⟨mem, .initializing point p (.start q false)⟩ =
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      Polynomial.HornerMachine.runFuel Polynomial.HornerMachine.hornerCode
        (value point : ZMod (value q)) (3 * xs.length + 3)
        (.running 0 (xs.map (fun c ↦ (value c : ZMod (value q)))) 0 0) =
        (.halted (value out : ZMod (value q)), Polynomial.HornerMachine.hornerCost xs.length) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hv⟩ := execution hr hpoint hcoeff hwpoint
  have hs := Polynomial.HornerMachine.horner_runFuel
    (value point : ZMod (value q)) (xs.map (fun c ↦ (value c : ZMod (value q))))
  rw [← hv] at hs
  exact ⟨n, hn, out, ht, hf, hw, hb, by simpa only [List.length_map] using hs⟩

/-- Polynomial evaluation includes physical zero initialization in this same trace and bound. -/
theorem polynomial_execution {mem : Memory} {w : ℕ} {q point p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q) (hwpoint : point.length = q.length)
    (poly : CompPoly.CPolynomial (ZMod (value q)))
    (hpoly : xs.map (fun c ↦ (value c : ZMod (value q))) = poly.val.toList.reverse) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .initializing point p (.start q false)⟩
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      runFuel n ⟨mem, .initializing point p (.start q false)⟩ =
        ⟨mem, .evaluating (.done q point (nilPointer w) out)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      (value out : ZMod (value q)) = poly.eval (value point : ZMod (value q)) := by
  obtain ⟨n, hn, out, ht, hf, hw, hb, hv⟩ := execution hr hpoint hcoeff hwpoint
  refine ⟨n, hn, out, ht, hf, hw, hb, ?_⟩
  rw [hv, hpoly, List.foldl_reverse]
  change poly.val.toList.foldr
    (fun coeff acc ↦ acc * (value point : ZMod (value q)) + coeff) 0 = poly.eval _
  rw [Array.foldr_toList]
  exact CompPoly.CPolynomial.eval_horner_eq_eval _ poly

end Computation.SharedListHornerProgram
