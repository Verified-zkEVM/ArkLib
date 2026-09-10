/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryNegateMachine
public import ArkLib.Data.Computation.BinarySubtractSemantics

/-!
# Same-run modular negation

All zero testing, operand restoration and clearing are included in the same transition count.
Numeric values and the modulus operation occur only in the specification and proofs.
-/

@[expose] public section

namespace Computation.BinaryNegateMachine

open BinaryWordMachine (Word value bitValue Canonical)

/-- Proof-side nonzero flag accumulated by the actual Boolean scan. -/
def nonzero : Word → Bool
  | [] => false
  | x :: xs => x || nonzero xs

theorem nonzero_value (xs : Word) : nonzero xs = true ↔ 0 < value xs := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    cases x
    · simpa [nonzero, value, bitValue] using ih
    · simp only [nonzero, Bool.true_or, value, bitValue, if_true, true_iff]
      omega

/-- Scan every stored bit and retain its reversal on the fixed saved tape. -/
theorem scan_trace (q xs saved : Word) (nz : Bool) :
    Trace (xs.length + 1) (.scan q xs saved nz)
      (.restore q (xs.reverse ++ saved) [] (nz || nonzero xs)) := by
  induction xs generalizing saved nz with
  | nil => simpa [nonzero] using Trace.cons (by rfl) (Trace.nil (.restore q saved [] nz))
  | cons x xs ih =>
    simpa [nonzero, List.reverse_cons, List.append_assoc, Bool.or_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: saved) (nz || x))

/-- Restore the original operand before deciding between subtraction and explicit clearing. -/
theorem restore_trace (q saved xs : Word) (nz : Bool) :
    Trace (saved.length + 1) (.restore q saved xs nz)
      (if nz then .subtract (.start q (saved.reverse ++ xs) false)
       else .clear q (saved.reverse ++ xs)) := by
  induction saved generalizing xs with
  | nil => cases nz <;> exact .cons rfl (.nil _)
  | cons x saved ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: xs))

/-- Zero operands still consume their physical input and modulus tapes explicitly. -/
theorem clear_trace (q xs : Word) :
    Trace (max q.length xs.length + 1) (.clear q xs)
      (.subtract (.normalize (.word []))) := by
  induction q generalizing xs with
  | nil =>
    induction xs with
    | nil => exact .cons rfl (.nil _)
    | cons x xs ih => simpa using Trace.cons (by rfl) ih
  | cons x q ih =>
    cases xs with
    | nil => simpa using Trace.cons (by rfl) (ih [])
    | cons y xs => simpa using Trace.cons (by rfl) (ih xs)

/-- Testing and restoring leaves the original operands on their original physical tapes. -/
theorem prepare_trace (q xs : Word) :
    Trace (2 * xs.length + 3) (.start q xs)
      (if nonzero xs then .subtract (.start q xs false) else .clear q xs) := by
  have hs := scan_trace q xs [] false
  have hr := restore_trace q xs.reverse [] (nonzero xs)
  simp only [List.append_nil, Bool.false_or] at hs
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  convert Trace.cons (s := .start q xs) (by rfl) (hs.append hr) using 1
  omega

/-- Reduced modular negation, with the same actual trace, canonical result and physical width. -/
theorem negate_correct (q xs : Word) (hx : value xs < value q) :
    ∃ n ≤ 4 * max q.length xs.length + 7, ∃ out : Word,
      Trace n (.start q xs) (.subtract (.normalize (.word out))) ∧
      runFuel n (.start q xs) = .subtract (.normalize (.word out)) ∧
      value out = (value q - value xs) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ max q.length xs.length := by
  have hp := prepare_trace q xs
  cases hz : nonzero xs
  · simp only [hz, Bool.false_eq_true, if_false] at hp
    have hv : value xs = 0 := by
      have := nonzero_value xs
      simp only [hz, Bool.false_eq_true, false_iff] at this
      omega
    have ht := hp.append (clear_trace q xs)
    refine ⟨_, ?_, [], ht, ht.runFuel_eq, ?_, ?_, Or.inl rfl, ?_⟩
    · have := Nat.le_max_right q.length xs.length
      omega
    · simp [value, hv]
    · simpa [value] using (show 0 < value q by omega)
    · simp
  · simp only [hz, if_true] at hp
    have hv : 0 < value xs := (nonzero_value xs).mp hz
    obtain ⟨n, hn, out, hs, _hr, ho, hc, hw⟩ :=
      BinarySubtractMachine.subtract_correct q xs false
    simp only [bitValue, Bool.false_eq_true, if_false, Nat.add_zero] at ho
    have ht := hp.append (lift_trace hs)
    refine ⟨_, ?_, out, ht, ht.runFuel_eq, ?_, ?_, hc, hw⟩
    · have := Nat.le_max_right q.length xs.length
      omega
    · rw [ho, Nat.mod_eq_of_lt (by omega)]
    · omega

/-- Input-width-only observation budget for the same modular negation with unchanged RAM. -/
theorem negate_runFuel (mem : AddressedBits.Memory) (q xs : Word) (hx : value xs < value q) :
    ∃ out : Word,
      ramRunFuel (4 * max q.length xs.length + 7) (mem, .start q xs) =
        (mem, .subtract (.normalize (.word out))) ∧
      value out = (value q - value xs) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ max q.length xs.length := by
  obtain ⟨n, hn, out, ht, _hr, hv, hb, hc, hw⟩ := negate_correct q xs hx
  have h := ht.runFuel_done rfl (4 * max q.length xs.length + 7 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hb, hc, hw⟩

end Computation.BinaryNegateMachine
