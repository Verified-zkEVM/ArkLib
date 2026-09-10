/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryBorrowMachine
public import ArkLib.Data.Computation.BinarySubtractSemantics

/-!
# Same-trace final-borrow semantics

The wrapper records the actual scan's final Boolean borrow at the very transition that selects
normalization or clearing. Correctness and cost refer to that same wrapped execution.
-/

@[expose] public section

namespace Computation.BinaryBorrowMachine

open BinaryWordMachine (Word value bitValue Canonical sumBit)
open BinarySubtractMachine (rawSubtract borrowBit)

/-- Every normalization successor retains the final borrow flag. -/
theorem normalize_trace {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) (b : Bool) :
    Trace n ⟨.normalize s, b⟩ ⟨.normalize t, b⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp [step, nextBorrow, BinarySubtractMachine.step, head]) ih

/-- Clearing does not alter the already recorded final borrow. -/
theorem discard_trace (saved : Word) (b : Bool) :
    Trace (saved.length + 1) ⟨.discard saved, b⟩ ⟨.normalize (.word []), b⟩ := by
  induction saved with
  | nil => exact .cons rfl (.nil _)
  | cons x saved ih => simpa [Nat.add_assoc] using Trace.cons (by rfl) ih

/-- The scan records its own final borrow, independently of the flag's initial value. -/
theorem scan_trace (xs ys : Word) (b : Bool) (saved : Word) (old : Bool) :
    Trace (max xs.length ys.length + 1) ⟨.scan xs ys b saved, old⟩
      ⟨if (rawSubtract xs ys b).2 then
          .discard ((rawSubtract xs ys b).1.reverse ++ saved)
        else .normalize (.trim ((rawSubtract xs ys b).1.reverse ++ saved)),
        (rawSubtract xs ys b).2⟩ := by
  fun_induction rawSubtract xs ys b generalizing saved old with
  | case1 b => cases b <;> exact .cons rfl (.nil _)
  | case2 x xs b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x false b :: saved) old)
  | case3 y ys b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit false y b :: saved) old)
  | case4 x xs y ys b r ih =>
    dsimp only [r]
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x y b :: saved) old)

/-- Saturating subtraction and its actual underflow flag share one literal execution witness. -/
theorem subtract_correct (xs ys : Word) (b : Bool) :
    ∃ n ≤ 2 * max xs.length ys.length + 4, ∃ out : Word, ∃ underflow : Bool,
      Trace n ⟨.start xs ys b, false⟩ ⟨.normalize (.word out), underflow⟩ ∧
      runFuel n ⟨.start xs ys b, false⟩ = ⟨.normalize (.word out), underflow⟩ ∧
      (underflow = true ↔ value xs < value ys + bitValue b) ∧
      (underflow = true → out = []) ∧
      value out = value xs - (value ys + bitValue b) ∧ Canonical out ∧
      out.length ≤ max xs.length ys.length := by
  have hs := scan_trace xs ys b [] false
  simp only [List.append_nil] at hs
  have hv := BinarySubtractMachine.rawSubtract_value xs ys b
  have hw := BinarySubtractMachine.rawSubtract_length xs ys b
  have hstart : step ⟨.start xs ys b, false⟩ = some ⟨.scan xs ys b [], false⟩ := rfl
  cases hb : (rawSubtract xs ys b).2
  · simp only [hb, Bool.false_eq_true, if_false] at hs hv
    obtain ⟨n, hn, ht⟩ := BinaryWordMachine.trim_trace (rawSubtract xs ys b).1.reverse
    have h := Trace.cons hstart (hs.append (normalize_trace ht false))
    refine ⟨_, ?_, _, false, h, h.runFuel_eq, ?_, by simp, ?_,
      BinaryWordMachine.trimSpec_canonical _, ?_⟩
    · simp only [List.length_reverse] at hn
      omega
    · simp only [Bool.false_eq_true, false_iff]
      omega
    · rw [BinaryWordMachine.trimSpec_value, List.reverse_reverse]
      omega
    · have := BinaryWordMachine.trimSpec_length (rawSubtract xs ys b).1.reverse
      simp only [List.length_reverse] at this ⊢
      omega
  · simp only [hb, if_true] at hs hv
    have h := Trace.cons hstart
      (hs.append (discard_trace (rawSubtract xs ys b).1.reverse true))
    refine ⟨_, ?_, [], true, h, h.runFuel_eq, by simpa using hv, by simp,
      ?_, Or.inl rfl, by simp⟩
    · simp only [List.length_reverse]
      omega
    · simp only [value]
      omega

end Computation.BinaryBorrowMachine
