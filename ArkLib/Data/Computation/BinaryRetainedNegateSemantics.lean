/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryRetainedNegateMachine
public import ArkLib.Data.Computation.BinaryNegateSemantics
public import ArkLib.Data.Computation.BinaryWordBounds

/-!
# Same-run retained-modulus negation

The arithmetic modulus copy is constructed by the trace itself. Correctness, canonical output,
modulus retention and width bounds all refer to the same literal execution.
-/

@[expose] public section

namespace Computation.BinaryRetainedNegateMachine

open BinaryWordMachine (Word value Canonical)

/-- Negation successors retain the outer modulus tape without adding hidden arithmetic. -/
theorem negate_step {s t : BinaryNegateMachine.Configuration}
    (h : BinaryNegateMachine.step s = some t) (q : Word) :
    step (.negate q s) = some (.negate q t) := by
  cases s <;> try exact congrArg (Option.map (Configuration.negate q)) h
  rename_i state
  cases state <;> try exact congrArg (Option.map (Configuration.negate q)) h
  rename_i state
  cases state <;> first
  | exact congrArg (Option.map (Configuration.negate q)) h
  | cases h

theorem negate_trace {n : ℕ} {s t : BinaryNegateMachine.Configuration}
    (h : BinaryNegateMachine.Trace n s t) (q : Word) : Trace n (.negate q s) (.negate q t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (negate_step head q) ih

/-- Every original modulus bit is moved into scratch individually. -/
theorem copyReverse_trace (q x saved : Word) :
    Trace (q.length + 1) (.copyReverse q x saved) (.copyRestore (q.reverse ++ saved) [] [] x) := by
  induction q generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Restore the retained modulus while writing a distinct arithmetic copy. -/
theorem copyRestore_trace (saved q left x : Word) :
    Trace (saved.length + 1) (.copyRestore saved q left x)
      (.negate (saved.reverse ++ q) (.start (saved.reverse ++ left) x)) := by
  induction saved generalizing q left with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: q) (b :: left))

/-- Preparing both physical modulus copies includes entry and both pass boundaries. -/
theorem prepare_trace (q x : Word) :
    Trace (2 * q.length + 3) (.start q x) (.negate q (.start q x)) := by
  have h₁ := copyReverse_trace q x []
  have h₂ := copyRestore_trace q.reverse [] [] x
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  convert Trace.cons (s := .start q x) (by rfl) (h₁.append h₂) using 1
  omega

/-- The same six-tape run retains its exact modulus and emits a reduced canonical negative. -/
theorem negate_correct (q x : Word) (hx : value x < value q) :
    ∃ n ≤ 6 * max q.length x.length + 11, ∃ out : Word,
      Trace n (.start q x) (.done q out) ∧ runFuel n (.start q x) = .done q out ∧
      value out = (value q - value x) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨nn, hnn, out, hn, _hrn, hv, hb, hc, _hw⟩ :=
    BinaryNegateMachine.negate_correct q x hx
  have h₁ := prepare_trace q x
  have h₂ := negate_trace hn q
  have h₃ : Trace 1 (.negate q (.subtract (.normalize (.word out)))) (.done q out) :=
    .cons rfl (.nil _)
  have ht := (h₁.append h₂).append h₃
  exact ⟨_, by omega, out, ht, ht.runFuel_eq, hv, hb, hc,
    hc.width_le_of_value_lt out q hb⟩

/-- Width-only observation fuel preserves both the original modulus tape and RAM memory. -/
theorem negate_runFuel (mem : AddressedBits.Memory) (q x : Word) (hx : value x < value q) :
    ∃ out : Word,
      ramRunFuel (6 * max q.length x.length + 11) (mem, .start q x) = (mem, .done q out) ∧
      value out = (value q - value x) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨n, hn, out, ht, _hr, hv, hb, hc, hw⟩ := negate_correct q x hx
  have h := ht.runFuel_done rfl (6 * max q.length x.length + 11 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hb, hc, hw⟩

end Computation.BinaryRetainedNegateMachine
