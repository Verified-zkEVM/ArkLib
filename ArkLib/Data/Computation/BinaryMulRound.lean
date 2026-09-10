/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulMachine
public import ArkLib.Data.Computation.BinaryModAddSemantics
public import ArkLib.Data.Computation.BinarySubtractSemantics
public import ArkLib.Data.Computation.BinaryWordBounds

/-!
# Literal multiplication round traces

Each round holds the accumulator, transfers and decrements its binary counter, restores the
counter, copies the retained multiplicand, restores the accumulator, and calls modular addition.
All eleven physical tapes retain their identity and every transfer phase contributes to the bound.
-/

@[expose] public section

namespace Computation.BinaryMulMachine

open BinaryWordMachine (Word value Canonical)

/-- Embed a decrement successor into its arithmetic slot with the retained tapes unchanged. -/
theorem decrement_step {s t : BinarySubtractMachine.Configuration}
    (h : BinarySubtractMachine.step s = some t) (q y held : Word) :
    step (.decrement q y held s) = some (.decrement q y held t) := by
  cases s <;> try exact congrArg (Option.map (Configuration.decrement q y held)) h
  rename_i state
  cases state <;> first
  | exact congrArg (Option.map (Configuration.decrement q y held)) h
  | cases h

theorem decrement_trace {n : ℕ} {s t : BinarySubtractMachine.Configuration}
    (h : BinarySubtractMachine.Trace n s t) (q y held : Word) :
    Trace n (.decrement q y held s) (.decrement q y held t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (decrement_step head q y held) ih

/-- Embed a modular-add successor in the same seven inner tapes and four retained outer tapes. -/
theorem add_step {s t : BinaryModAddMachine.Configuration}
    (h : BinaryModAddMachine.step s = some t) (count y : Word) :
    step (.add count y s) = some (.add count y t) := by
  cases s <;> first
  | exact congrArg (Option.map (Configuration.add count y)) h
  | cases h

theorem add_trace {n : ℕ} {s t : BinaryModAddMachine.Configuration}
    (h : BinaryModAddMachine.Trace n s t) (count y : Word) :
    Trace n (.add count y s) (.add count y t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (add_step head count y) ih

/-- Every holdReverse pass moves one bit per successor and charges its phase transition. -/
theorem holdReverse_trace (q count y acc saved : Word) :
    Trace (acc.length + 1) (.holdReverse q count y acc saved)
      (.holdCopy q count y (acc.reverse ++ saved) []) := by
  induction acc generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every holdCopy pass moves one bit per successor and charges its phase transition. -/
theorem holdCopy_trace (q count y saved held : Word) :
    Trace (saved.length + 1) (.holdCopy q count y saved held)
      (.countReverse q count y [] (saved.reverse ++ held)) := by
  induction saved generalizing held with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: held))

/-- Every countReverse pass moves one bit per successor and charges its phase transition. -/
theorem countReverse_trace (q count y saved held : Word) :
    Trace (count.length + 1) (.countReverse q count y saved held)
      (.countCopy q (count.reverse ++ saved) y [] held) := by
  induction count generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every countCopy pass moves one bit per successor and charges its phase transition. -/
theorem countCopy_trace (q saved y count held : Word) :
    Trace (saved.length + 1) (.countCopy q saved y count held)
      (.decrement q y held (.start (saved.reverse ++ count) [] true)) := by
  induction saved generalizing count with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: count))

/-- Every countOutReverse pass moves one bit per successor and charges its phase transition. -/
theorem countOutReverse_trace (q y held out saved : Word) :
    Trace (out.length + 1) (.countOutReverse q y held out saved)
      (.countOutCopy q y held (out.reverse ++ saved) []) := by
  induction out generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every countOutCopy pass moves one bit per successor and charges its phase transition. -/
theorem countOutCopy_trace (q y held saved count : Word) :
    Trace (saved.length + 1) (.countOutCopy q y held saved count)
      (.factorReverse q (saved.reverse ++ count) y [] held) := by
  induction saved generalizing count with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: count))

/-- Every factorReverse pass moves one bit per successor and charges its phase transition. -/
theorem factorReverse_trace (q count y saved held : Word) :
    Trace (y.length + 1) (.factorReverse q count y saved held)
      (.factorCopy q count (y.reverse ++ saved) [] [] held) := by
  induction y generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every factorCopy pass moves one bit per successor and charges its phase transition. -/
theorem factorCopy_trace (q count saved y right held : Word) :
    Trace (saved.length + 1) (.factorCopy q count saved y right held)
      (.accReverse q count (saved.reverse ++ y) (saved.reverse ++ right) held []) := by
  induction saved generalizing y right with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: y) (b :: right))

/-- Every accReverse pass moves one bit per successor and charges its phase transition. -/
theorem accReverse_trace (q count y right held saved : Word) :
    Trace (held.length + 1) (.accReverse q count y right held saved)
      (.accCopy q count y right (held.reverse ++ saved) []) := by
  induction held generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every accCopy pass moves one bit per successor and charges its phase transition. -/
theorem accCopy_trace (q count y right saved left : Word) :
    Trace (saved.length + 1) (.accCopy q count y right saved left)
      (.add count y (.start q (saved.reverse ++ left) right)) := by
  induction saved generalizing left with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: left))

/-- Holding the accumulator and moving the countdown uses four explicit tape passes. -/
theorem prepare_decrement_trace (q count y acc : Word) (hn : count ≠ []) :
    Trace (2 * acc.length + 2 * count.length + 5) (.loop q count y acc)
      (.decrement q y acc (.start count [] true)) := by
  have h₁ := holdReverse_trace q count y acc []
  have h₂ := holdCopy_trace q count y acc.reverse []
  have h₃ := countReverse_trace q count y [] acc
  have h₄ := countCopy_trace q count.reverse y [] acc
  simp only [List.append_nil] at h₁ h₃
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂ h₄
  have hs : step (.loop q count y acc) = some (.holdReverse q count y acc []) := by
    cases count with
    | nil => exact (hn rfl).elim
    | cons b bs => rfl
  convert Trace.cons hs (((h₁.append h₂).append h₃).append h₄) using 1
  omega

/-- Restore the new counter, copy the multiplicand, and restore the held accumulator. -/
theorem prepare_add_trace (q y acc next : Word) :
    Trace (2 * next.length + 2 * y.length + 2 * acc.length + 7)
      (.decrement q y acc (.normalize (.word next))) (.add next y (.start q acc y)) := by
  have h₁ := countOutReverse_trace q y acc next []
  have h₂ := countOutCopy_trace q y acc next.reverse []
  have h₃ := factorReverse_trace q next y [] acc
  have h₄ := factorCopy_trace q next y.reverse [] [] acc
  have h₅ := accReverse_trace q next y y acc []
  have h₆ := accCopy_trace q next y y acc.reverse []
  simp only [List.append_nil] at h₁ h₃ h₅
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂ h₄ h₆
  have h := ((((h₁.append h₂).append h₃).append h₄).append h₅).append h₆
  convert Trace.cons (s := .decrement q y acc (.normalize (.word next))) (by rfl) h using 1
  omega

/-- One actual round decrements its physical counter and adds its retained scalar modulo q. -/
theorem round_correct (q count y acc : Word) (hc : Canonical count) (hn : count ≠ [])
    (hx : value count < value q) (hy : value y < value q)
    (ha : value acc < value q) (hca : Canonical acc) :
    ∃ n ≤ 24 * max q.length y.length + 48, ∃ next out : Word,
      Trace n (.loop q count y acc) (.loop q next y out) ∧
      value next = value count - 1 ∧ value next < value count ∧ Canonical next ∧
      value out = (value acc + value y) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨nd, hnd, next, hd, _hrd, hvd, hcd, hwd⟩ :=
    BinarySubtractMachine.decrement_correct count
  obtain ⟨na, hna, out, ha', _hra, hva, hba, hcoa, _hwa⟩ :=
    BinaryModAddMachine.add_correct q acc y ha hy
  have h₁ := prepare_decrement_trace q count y acc hn
  have h₂ := decrement_trace hd q y acc
  have h₃ := prepare_add_trace q y acc next
  have h₄ := add_trace ha' next y
  have h₅ : Trace 1 (.add next y (.done q out)) (.loop q next y out) := .cons rfl (.nil _)
  have ht := (((h₁.append h₂).append h₃).append h₄).append h₅
  have hwc := hc.width_le_of_value_lt count q hx
  have hwa := hca.width_le_of_value_lt acc q ha
  have hp := hc.value_pos count hn
  refine ⟨_, ?_, next, out, ht, hvd, by omega, hcd, hva, hba, hcoa,
    hcoa.width_le_of_value_lt out q hba⟩
  omega

end Computation.BinaryMulMachine
