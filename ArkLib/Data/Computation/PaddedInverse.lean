/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryInverseField
public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Fixed-width prime-field inversion

The actual inverse search feeds its returned word into physical width construction and padding.
The modulus and input words remain on their original tapes. A finite-control handoff changes no
tape contents; both phases execute on one thirteen-tape bank. Zero and padded inputs are covered.

The stated cost concerns this local-bit program on already materialized inputs, not native Lean
execution, heap loading, or an assumed whole-decoder backend.
-/

@[expose] public section

namespace Computation.PaddedInverse

open BinaryWordMachine (Word value)

inductive Control where
  | inverting (child : BinaryInverseMachine.Configuration)
  | padding (input : Word) (child : ScalarWordPadding.Control)
  deriving DecidableEq, Repr

/-- Literal inverse instructions, one tape-preserving handoff, and actual padding instructions. -/
def step : Control → Option Control
  | .inverting child =>
      match BinaryInverseMachine.step child with
      | some next => some (.inverting next)
      | none => match child with
          | .done q x word => some (.padding x (.shaping word (.shapeStart q)))
          | _ => none
  | .padding x child => (ScalarWordPadding.step child).map (.padding x)

/-- Modulus at four and retained input at eight stay fixed. The padded result is on zero. -/
def tapes : Control → Fin 13 → Word
  | .inverting child => BinaryInverseMachine.tapes child
  | .padding x child =>
      let t := ScalarWordPadding.tapes child
      ![t 4, t 1, t 2, t 3, t 0, t 5, [], [], x, [], [], [], []]

theorem handoff_tapes (q x word : Word) :
    tapes (.inverting (.done q x word)) =
      tapes (.padding x (.shaping word (.shapeStart q))) := by
  funext i
  fin_cases i <;> rfl

private theorem pad_bank {s t : ScalarWordPadding.Control}
    (h : BitLocalActions.BankStep (ScalarWordPadding.tapes s) (ScalarWordPadding.tapes t))
    (x : Word) : BitLocalActions.BankStep (tapes (.padding x s)) (tapes (.padding x t)) := by
  intro i
  fin_cases i
  · exact h 4
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 0
  · exact h 5
  · exact .keep _
  · exact .keep _
  · exact .keep _
  · exact .keep _
  · exact .keep _
  · exact .keep _
  · exact .keep _

/-- All successors obey the same fixed-bank local-cell rule. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | inverting child =>
      cases hs : BinaryInverseMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact BinaryInverseMachine.step_local hs
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [handoff_tapes]
          intro i
          exact .keep _
  | padding x child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      exact pad_bank (ScalarWordPadding.step_local hs) x

/-- The count is the number of actual combined-controller successors. -/
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

theorem lift_inverse {n : ℕ} {s t : BinaryInverseMachine.Configuration}
    (h : BinaryInverseMachine.Trace n s t) : Trace n (.inverting s) (.inverting t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_padding (x : Word) {n : ℕ} {s t : ScalarWordPadding.Control}
    (h : ScalarWordPadding.Trace n s t) : Trace n (.padding x s) (.padding x t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- The same execution computes the prime-field inverse and returns the exact representation
width, with an absolute quadratic modulus overhead. Zero needs no exceptional contract. -/
theorem inverse_correct (q x : Word) (hp : Nat.Prime (value q)) (hx : value x < value q) :
    ∃ n ≤ value q *
        (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) +
        2 * x.length + 4 * q.length + 12, ∃ out : Word,
      Trace n (.inverting (.start q x)) (.padding x (.padding q (.done out))) ∧
      runFuel n (.inverting (.start q x)) = .padding x (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) = (value x : ZMod (value q))⁻¹ ∧ value out < value q := by
  obtain ⟨n, hn, word, ht, _hr, hv, hb, hc, _hw⟩ := BinaryInverseMachine.inverse_zmod q x hp hx
  obtain ⟨out, hp, _hr, hlen, he, hred⟩ := ScalarWordPadding.padding_reduced q word hc hb
  have hh : Trace 1 (.inverting (.done q x word))
      (.padding x (.shaping word (.shapeStart q))) := .cons rfl (.nil _)
  have hall := ((lift_inverse ht).append hh).append (lift_padding x hp)
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hlen, by rw [he, hv], hred⟩

/-- Fixed-width inputs give the corresponding width-only polynomial bound for the same run. -/
theorem inverse_fixed_width (q x : Word) (hp : Nat.Prime (value q))
    (hx : value x < value q) (hw : x.length = q.length) :
    ∃ n ≤ value q * (value q * (24 * q.length + 48) + 16 * q.length + 32) +
      6 * q.length + 12, ∃ out : Word,
      Trace n (.inverting (.start q x)) (.padding x (.padding q (.done out))) ∧
      runFuel n (.inverting (.start q x)) = .padding x (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) = (value x : ZMod (value q))⁻¹ ∧ value out < value q := by
  obtain ⟨n, hn, out, ht, hr, hlen, hv, hb⟩ := inverse_correct q x hp hx
  refine ⟨n, ?_, out, ht, hr, hlen, hv, hb⟩
  simp only [hw, max_self] at hn
  omega

/-- RAM is retained by every actual local instruction. -/
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
  rw [PaddedInverse.ramRunFuel_eq, h.runFuel_eq]

end Computation.PaddedInverse
