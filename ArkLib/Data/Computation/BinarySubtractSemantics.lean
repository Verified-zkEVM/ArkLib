/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinarySubtractMachine
public import ArkLib.Data.Computation.BinaryWordSemantics

/-!
# Saturating subtraction correctness and literal execution bounds

Proof-side bit lists describe the scan only. The actual machine uses finite Boolean borrow
control and explicit local-cell clearing and normalization, including on underflow.
-/

@[expose] public section

namespace Computation.BinarySubtractMachine

open BinaryWordMachine (Word value bitValue Canonical sumBit trimSpec)

/-- The full-subtractor equation uses only its three input bits. -/
theorem borrow_equation (x y b : Bool) :
    bitValue x + 2 * bitValue (borrowBit x y b) =
      bitValue y + bitValue b + bitValue (sumBit x y b) := by
  cases x <;> cases y <;> cases b <;> decide

/-- Proof-side emitted bits and final borrow; never evaluated by a successor. -/
def rawSubtract : Word → Word → Bool → Word × Bool
  | [], [], b => ([], b)
  | x :: xs, [], b =>
      let r := rawSubtract xs [] (borrowBit x false b)
      (sumBit x false b :: r.1, r.2)
  | [], y :: ys, b =>
      let r := rawSubtract [] ys (borrowBit false y b)
      (sumBit false y b :: r.1, r.2)
  | x :: xs, y :: ys, b =>
      let r := rawSubtract xs ys (borrowBit x y b)
      (sumBit x y b :: r.1, r.2)
termination_by xs ys _ => xs.length + ys.length

/-- Every input column emits one physical bit, even if that bit is zero. -/
theorem rawSubtract_length (xs ys : Word) (b : Bool) :
    (rawSubtract xs ys b).1.length = max xs.length ys.length := by
  fun_induction rawSubtract xs ys b with
  | case1 b => rfl
  | case2 x xs b r ih => simpa [r] using congrArg Nat.succ ih
  | case3 y ys b r ih => simpa [r] using congrArg Nat.succ ih
  | case4 x xs y ys b r ih => simpa [r] using congrArg Nat.succ ih

/-- A successful higher-bit subtraction extends through the current full-subtractor column. -/
theorem column_success (x y b : Bool) (a c r : ℕ)
    (h : r + c + bitValue (borrowBit x y b) = a) :
    bitValue (sumBit x y b) + 2 * r + (bitValue y + 2 * c) + bitValue b =
      bitValue x + 2 * a := by
  have := borrow_equation x y b
  omega

/-- A higher-bit underflow cannot be undone by the lower result bit. -/
theorem column_underflow (x y b : Bool) (a c : ℕ)
    (h : a < c + bitValue (borrowBit x y b)) :
    bitValue x + 2 * a < bitValue y + 2 * c + bitValue b := by
  have := borrow_equation x y b
  have hd : bitValue (sumBit x y b) ≤ 1 := by cases sumBit x y b <;> decide
  omega

/-- The final borrow reports underflow; otherwise the emitted value is the exact difference. -/
theorem rawSubtract_value (xs ys : Word) (b : Bool) :
    if (rawSubtract xs ys b).2 then value xs < value ys + bitValue b
    else value (rawSubtract xs ys b).1 + value ys + bitValue b = value xs := by
  fun_induction rawSubtract xs ys b with
  | case1 b => cases b <;> decide
  | case2 x xs b r ih =>
    dsimp only [r]
    cases h : (rawSubtract xs [] (borrowBit x false b)).2
    · simp only [h, Bool.false_eq_true, if_false] at ih ⊢
      simpa [value, bitValue] using column_success x false b (value xs) (value [])
        (value (rawSubtract xs [] (borrowBit x false b)).1) ih
    · simp only [h, if_true] at ih ⊢
      simpa [value, bitValue] using column_underflow x false b (value xs) (value []) ih
  | case3 y ys b r ih =>
    dsimp only [r]
    cases h : (rawSubtract [] ys (borrowBit false y b)).2
    · simp only [h, Bool.false_eq_true, if_false] at ih ⊢
      simpa [value, bitValue] using column_success false y b (value []) (value ys)
        (value (rawSubtract [] ys (borrowBit false y b)).1) ih
    · simp only [h, if_true] at ih ⊢
      simpa [value, bitValue] using column_underflow false y b (value []) (value ys) ih
  | case4 x xs y ys b r ih =>
    dsimp only [r]
    cases h : (rawSubtract xs ys (borrowBit x y b)).2
    · simp only [h, Bool.false_eq_true, if_false] at ih ⊢
      exact column_success x y b (value xs) (value ys)
        (value (rawSubtract xs ys (borrowBit x y b)).1) ih
    · simp only [h, if_true] at ih ⊢
      exact column_underflow x y b (value xs) (value ys) ih

/-- Underflow explicitly clears every temporary bit before emitting zero. -/
theorem discard_trace (saved : Word) :
    Trace (saved.length + 1) (.discard saved) (.normalize (.word [])) := by
  induction saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => simpa [Nat.add_assoc] using Trace.cons (by rfl) ih

/-- The fixed borrow scan consumes exactly the maximum physical input width. -/
theorem scan_trace (xs ys : Word) (b : Bool) (saved : Word) :
    Trace (max xs.length ys.length + 1) (.scan xs ys b saved)
      (if (rawSubtract xs ys b).2 then
        .discard ((rawSubtract xs ys b).1.reverse ++ saved)
      else .normalize (.trim ((rawSubtract xs ys b).1.reverse ++ saved))) := by
  fun_induction rawSubtract xs ys b generalizing saved with
  | case1 b => cases b <;> exact .cons rfl (.nil _)
  | case2 x xs b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x false b :: saved))
  | case3 y ys b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit false y b :: saved))
  | case4 x xs y ys b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x y b :: saved))

/-- Same-run saturating subtraction, including borrow-in, padding, and canonical output. -/
theorem subtract_correct (xs ys : Word) (b : Bool) :
    ∃ n ≤ 2 * max xs.length ys.length + 4, ∃ out : Word,
      Trace n (.start xs ys b) (.normalize (.word out)) ∧
      runFuel n (.start xs ys b) = .normalize (.word out) ∧
      value out = value xs - (value ys + bitValue b) ∧ Canonical out ∧
      out.length ≤ max xs.length ys.length := by
  have hs := scan_trace xs ys b []
  simp only [List.append_nil] at hs
  have hv := rawSubtract_value xs ys b
  have hw := rawSubtract_length xs ys b
  have hstart : step (.start xs ys b) = some (.scan xs ys b []) := rfl
  cases hb : (rawSubtract xs ys b).2
  · simp only [hb, Bool.false_eq_true, if_false] at hs hv
    obtain ⟨n, hn, ht⟩ := BinaryWordMachine.trim_trace (rawSubtract xs ys b).1.reverse
    have h := Trace.cons hstart (hs.append (lift_trace ht))
    refine ⟨_, ?_, _, h, h.runFuel_eq, ?_, BinaryWordMachine.trimSpec_canonical _, ?_⟩
    · simp only [List.length_reverse] at hn
      omega
    · rw [BinaryWordMachine.trimSpec_value, List.reverse_reverse]
      omega
    · have := BinaryWordMachine.trimSpec_length (rawSubtract xs ys b).1.reverse
      simp only [List.length_reverse] at this ⊢
      omega
  · simp only [hb, if_true] at hs hv
    have h := Trace.cons hstart (hs.append (discard_trace (rawSubtract xs ys b).1.reverse))
    refine ⟨_, ?_, [], h, h.runFuel_eq, ?_, Or.inl rfl, ?_⟩
    · simp only [List.length_reverse]
      omega
    · simp only [value]
      omega
    · simp

/-- A width-only budget returns the proved difference and preserves the identical memory. -/
theorem subtract_runFuel (mem : AddressedBits.Memory) (xs ys : Word) (b : Bool) :
    ∃ out : Word,
      ramRunFuel (2 * max xs.length ys.length + 4) (mem, .start xs ys b) =
        (mem, .normalize (.word out)) ∧
      value out = value xs - (value ys + bitValue b) ∧ Canonical out ∧
      out.length ≤ max xs.length ys.length := by
  obtain ⟨n, hn, out, ht, _hr, hv, hc, hw⟩ := subtract_correct xs ys b
  have h := ht.runFuel_done rfl (2 * max xs.length ys.length + 4 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hc, hw⟩

/-- Decrement runs the same borrow controller with an empty right tape and initial borrow. -/
theorem decrement_correct (xs : Word) :
    ∃ n ≤ 2 * xs.length + 4, ∃ out : Word,
      Trace n (.start xs [] true) (.normalize (.word out)) ∧
      runFuel n (.start xs [] true) = .normalize (.word out) ∧
      value out = value xs - 1 ∧ Canonical out ∧ out.length ≤ xs.length := by
  simpa [bitValue, value] using subtract_correct xs [] true

end Computation.BinarySubtractMachine
