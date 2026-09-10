/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryRetainedNegateField
public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Fixed-width scalar negation

The retained-modulus negation program feeds its actual output to physical width construction
and padding. Both children use the same six tapes; their handoff changes no tape contents.
The exact modulus word is retained, while the input operand is consumed. This is a local-bit
instruction on materialized words, not a whole-decoder bit-time theorem.
-/

@[expose] public section

namespace Computation.PaddedNegate

open BinaryWordMachine (Word value)

inductive Control where
  | negating (child : BinaryRetainedNegateMachine.Configuration)
  | padding (child : ScalarWordPadding.Control)
  deriving DecidableEq, Repr

/-- Actual child steps and one literal, tape-preserving handoff. -/
def step : Control → Option Control
  | .negating child =>
      match BinaryRetainedNegateMachine.step child with
      | some next => some (.negating next)
      | none => match child with
          | .done q word => some (.padding (.shaping word (.shapeStart q)))
          | _ => none
  | .padding child => (ScalarWordPadding.step child).map .padding

/-- Modulus stays on slot four. The final padded scalar is on slot zero. -/
def tapes : Control → Fin 6 → Word
  | .negating child => BinaryRetainedNegateMachine.tapes child
  | .padding child =>
      let t := ScalarWordPadding.tapes child
      ![t 4, t 1, t 2, t 3, t 0, t 5]

theorem handoff_tapes (q word : Word) :
    tapes (.negating (.done q word)) = tapes (.padding (.shaping word (.shapeStart q))) := by
  funext i
  fin_cases i <;> rfl

/-- All successors satisfy the shared fixed-bank local-cell rule. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | negating child =>
      cases hs : BinaryRetainedNegateMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact BinaryRetainedNegateMachine.step_local hs
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [handoff_tapes]
          intro i
          exact .keep _
  | padding child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      have hl := ScalarWordPadding.step_local hs
      intro i
      fin_cases i
      · exact hl 4
      · exact hl 1
      · exact hl 2
      · exact hl 3
      · exact hl 0
      · exact hl 5

/-- The number of actual combined-controller successors. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Control}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_negate {n : ℕ} {s t : BinaryRetainedNegateMachine.Configuration}
    (h : BinaryRetainedNegateMachine.Trace n s t) : Trace n (.negating s) (.negating t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_padding {n : ℕ} {s t : ScalarWordPadding.Control}
    (h : ScalarWordPadding.Trace n s t) : Trace n (.padding s) (.padding t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- One actual run returns the fixed-width scalar negative and retains its original modulus. -/
theorem negate_correct (q x : Word) (hx : value x < value q) :
    ∃ n ≤ 6 * max q.length x.length + 4 * q.length + 19, ∃ out : Word,
      Trace n (.negating (.start q x)) (.padding (.padding q (.done out))) ∧
      runFuel n (.negating (.start q x)) = .padding (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) = -(value x : ZMod (value q)) ∧ value out < value q := by
  obtain ⟨n, hn, word, ht, _hr, hv, hb, hc, _hw⟩ :=
    BinaryRetainedNegateMachine.negate_zmod q x hx
  obtain ⟨out, hp, _hr, hlen, he, hred⟩ := ScalarWordPadding.padding_reduced q word hc hb
  have hh : Trace 1 (.negating (.done q word))
      (.padding (.shaping word (.shapeStart q))) := .cons rfl (.nil _)
  have hall := ((lift_negate ht).append hh).append (lift_padding hp)
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hlen, by rw [he, hv], hred⟩

/-- Fixed-width scalar negation has a same-run linear physical-width bound. -/
theorem negate_fixed_width (q x : Word) (hx : value x < value q) (hw : x.length = q.length) :
    ∃ n ≤ 10 * q.length + 19, ∃ out : Word,
      Trace n (.negating (.start q x)) (.padding (.padding q (.done out))) ∧
      runFuel n (.negating (.start q x)) = .padding (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) = -(value x : ZMod (value q)) ∧ value out < value q := by
  obtain ⟨n, hn, out, ht, hr, hlen, hv, hb⟩ := negate_correct q x hx
  refine ⟨n, ?_, out, ht, hr, hlen, hv, hb⟩
  simp only [hw, max_self] at hn
  omega

/-- Lift this same program into unchanged RAM. -/
def ramStep (s : AddressedBits.Memory × Control) : Option (AddressedBits.Memory × Control) :=
  (step s.2).map fun t ↦ (s.1, t)

def ramRunFuel : ℕ → AddressedBits.Memory × Control → AddressedBits.Memory × Control
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

theorem ramRunFuel_eq (mem : AddressedBits.Memory) (n : ℕ) (s : Control) :
    ramRunFuel n (mem, s) = (mem, runFuel n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

theorem Trace.ramRunFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t)
    (mem : AddressedBits.Memory) : ramRunFuel n (mem, s) = (mem, t) := by
  rw [PaddedNegate.ramRunFuel_eq, h.runFuel_eq]

end Computation.PaddedNegate
