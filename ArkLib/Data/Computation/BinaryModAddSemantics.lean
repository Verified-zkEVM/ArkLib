/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryModAddMachine
public import ArkLib.Data.Computation.BinaryBorrowSemantics

/-!
# Modular addition correctness with charged storage

The same trace includes addition, two physical copies, the recorded-borrow subtraction, and
backup recovery or clearing. The modulus is retained exactly and all scratch tapes are empty
at the final state. Numeric modulus and width arithmetic occur only in specifications.
-/

@[expose] public section

namespace Computation.BinaryModAddMachine

open BinaryWordMachine (Word value bitValue Canonical)

/-- Lift an actual addition successor into its fixed physical subprogram slot. -/
theorem add_step {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.step s = some t) (q : Word) :
    step (.add q s) = some (.add q t) := by
  cases s <;> first
  | exact congrArg (Option.map (Configuration.add q)) h
  | cases h

theorem add_trace {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) (q : Word) : Trace n (.add q s) (.add q t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (add_step head q) ih

/-- Lift an actual borrow-tracking successor; terminal dispatch is a separate charged phase. -/
theorem subtract_step {s t : BinaryBorrowMachine.Configuration}
    (h : BinaryBorrowMachine.step s = some t) (q backup : Word) :
    step (.subtract q backup s) = some (.subtract q backup t) := by
  rcases s with ⟨state, b⟩
  cases state <;> try exact congrArg (Option.map (Configuration.subtract q backup)) h
  rename_i state
  cases state <;> first
  | exact congrArg (Option.map (Configuration.subtract q backup)) h
  | cases h

theorem subtract_trace {n : ℕ} {s t : BinaryBorrowMachine.Configuration}
    (h : BinaryBorrowMachine.Trace n s t) (q backup : Word) :
    Trace n (.subtract q backup s) (.subtract q backup t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (subtract_step head q backup) ih

/-- Reverse the sum from the output tape into the arithmetic saved tape. -/
theorem sumReverse_trace (q xs saved : Word) :
    Trace (xs.length + 1) (.sumReverse q xs saved)
      (.sumCopy q (xs.reverse ++ saved) [] []) := by
  induction xs generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: saved))

/-- Each restored sum bit is physically written to both its arithmetic input and backup tape. -/
theorem sumCopy_trace (q saved left backup : Word) :
    Trace (saved.length + 1) (.sumCopy q saved left backup)
      (.modReverse q [] (saved.reverse ++ left) (saved.reverse ++ backup)) := by
  induction saved generalizing left backup with
  | nil => exact .cons rfl (.nil _)
  | cons x saved ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: left) (x :: backup))

/-- Temporarily reverse the retained modulus into the separate scratch tape. -/
theorem modReverse_trace (q saved left backup : Word) :
    Trace (q.length + 1) (.modReverse q saved left backup)
      (.modCopy (q.reverse ++ saved) [] left [] backup) := by
  induction q generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons x q ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: saved))

/-- Restore the original modulus and write its arithmetic copy, one bit per successor. -/
theorem modCopy_trace (saved q left right backup : Word) :
    Trace (saved.length + 1) (.modCopy saved q left right backup)
      (.subtract (saved.reverse ++ q) backup
        ⟨.start left (saved.reverse ++ right) false, false⟩) := by
  induction saved generalizing q right with
  | nil => exact .cons rfl (.nil _)
  | cons x saved ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: q) (x :: right))

/-- Both arithmetic inputs and the retained copies come from explicit local-cell runs. -/
theorem prepare_trace (q sum : Word) :
    Trace (2 * sum.length + 2 * q.length + 4) (.sumReverse q sum [])
      (.subtract q sum ⟨.start sum q false, false⟩) := by
  have h₁ := sumReverse_trace q sum []
  have h₂ := sumCopy_trace q sum.reverse [] []
  have h₃ := modReverse_trace q [] sum sum
  have h₄ := modCopy_trace q.reverse [] sum [] sum
  simp only [List.append_nil] at h₁ h₃
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂ h₄
  convert ((h₁.append h₂).append h₃).append h₄ using 1
  omega

/-- Clear the unused sum backup without changing the already reduced output. -/
theorem clearBackup_trace (q backup out : Word) :
    Trace (backup.length + 1) (.clearBackup q backup out) (.done q out) := by
  induction backup with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih => simpa [Nat.add_assoc] using Trace.cons (by rfl) ih

/-- Reverse the saved sum when subtraction underflow requires it as the result. -/
theorem recoverReverse_trace (q backup saved : Word) :
    Trace (backup.length + 1) (.recoverReverse q backup saved)
      (.recoverCopy q (backup.reverse ++ saved) []) := by
  induction backup generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: saved))

/-- Return the saved sum on the output tape through an explicit restoration pass. -/
theorem recoverCopy_trace (q saved out : Word) :
    Trace (saved.length + 1) (.recoverCopy q saved out) (.done q (saved.reverse ++ out)) := by
  induction saved generalizing out with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (x :: out))

/-- Successful reduction discards its backup with every clearing and dispatch step counted. -/
theorem finish_success_trace (q backup out : Word) :
    Trace (backup.length + 2) (.subtract q backup ⟨.normalize (.word out), false⟩)
      (.done q out) := Trace.cons rfl (clearBackup_trace q backup out)

/-- Underflow returns the literal backup, including both restoration passes and dispatches. -/
theorem finish_underflow_trace (q backup : Word) :
    Trace (2 * backup.length + 4) (.subtract q backup ⟨.normalize (.word []), true⟩)
      (.done q backup) := by
  have h₁ := recoverReverse_trace q backup []
  have h₂ := recoverCopy_trace q backup.reverse []
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  have h := Trace.cons (s := .subtract q backup ⟨.normalize (.word []), true⟩) (by rfl)
    (Trace.cons (s := .discardResult q backup []) (by rfl) (h₁.append h₂))
  convert h using 1
  omega

/-- Same-run reduced modular addition; the original modulus and only the output remain. -/
theorem add_correct (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ 10 * max q.length (max xs.length ys.length) + 25, ∃ out : Word,
      Trace n (.start q xs ys) (.done q out) ∧ runFuel n (.start q xs ys) = .done q out ∧
      value out = (value xs + value ys) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ max q.length (max xs.length ys.length) + 1 := by
  obtain ⟨na, hna, sum, ha, _hra, hva, hca, hwa⟩ := BinaryWordMachine.add_correct xs ys false
  simp only [bitValue, Bool.false_eq_true, if_false, Nat.add_zero] at hva
  obtain ⟨ns, hns, diff, underflow, hs, _hrs, hu, hz, hvd, hcd, hwd⟩ :=
    BinaryBorrowMachine.subtract_correct sum q false
  simp only [bitValue, Bool.false_eq_true, if_false, Nat.add_zero] at hu hvd
  have h₁ := Trace.cons (s := .start q xs ys) (by rfl) (add_trace ha q)
  have h₂ := Trace.cons (s := .add q (.word sum)) (by rfl) (prepare_trace q sum)
  have h := (h₁.append h₂).append (subtract_trace hs q sum)
  cases underflow
  · have hnlt : ¬ value sum < value q := by simpa using hu.symm
    have hd : value sum - value q < value q := by omega
    have hm : value sum % value q = value sum - value q := by
      calc
        _ = ((value sum - value q) + value q) % value q := by congr 1; omega
        _ = value sum - value q := by simp [Nat.mod_eq_of_lt hd]
    have ht := h.append (finish_success_trace q sum diff)
    refine ⟨_, ?_, diff, ht, ht.runFuel_eq, ?_, ?_, hcd, ?_⟩
    · omega
    · rw [hvd, ← hm, hva]
    · omega
    · omega
  · have hlt : value sum < value q := hu.mp rfl
    have he : diff = [] := hz rfl
    subst diff
    have ht := h.append (finish_underflow_trace q sum)
    refine ⟨_, ?_, sum, ht, ht.runFuel_eq, ?_, hlt, hca, ?_⟩
    · omega
    · rw [← hva, Nat.mod_eq_of_lt hlt]
    · omega

/-- The same modular-addition run uses an input-width budget and preserves RAM memory. -/
theorem add_runFuel (mem : AddressedBits.Memory) (q xs ys : Word)
    (hx : value xs < value q) (hy : value ys < value q) :
    ∃ out : Word,
      ramRunFuel (10 * max q.length (max xs.length ys.length) + 25) (mem, .start q xs ys) =
        (mem, .done q out) ∧
      value out = (value xs + value ys) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ max q.length (max xs.length ys.length) + 1 := by
  obtain ⟨n, hn, out, ht, _hr, hv, hb, hc, hw⟩ := add_correct q xs ys hx hy
  have h := ht.runFuel_done rfl (10 * max q.length (max xs.length ys.length) + 25 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hb, hc, hw⟩

end Computation.BinaryModAddMachine
