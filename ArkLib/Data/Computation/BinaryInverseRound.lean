/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryInverseMachine
public import ArkLib.Data.Computation.BinaryMulSemantics
public import ArkLib.Data.Computation.BinaryNegateSemantics

/-!
# Literal inverse-search preparation and round traces

The input zero test restores its original tape. Candidate copies, increments, product checks
and output recovery use actual physical transitions, with explicit phase and bit counts.
-/

@[expose] public section

namespace Computation.BinaryInverseMachine

open BinaryWordMachine (Word value bitValue Canonical)
open BinaryNegateMachine (nonzero)

/-- Embed one literal multiplication successor, keeping the candidate on its own physical tape. -/
theorem multiply_step {s t : BinaryMulMachine.Configuration}
    (h : BinaryMulMachine.step s = some t) (candidate : Word) :
    step (.multiply candidate s) = some (.multiply candidate t) := by
  cases s <;> first
  | exact congrArg (Option.map (Configuration.multiply candidate)) h
  | cases h

theorem multiply_trace {n : ℕ} {s t : BinaryMulMachine.Configuration}
    (h : BinaryMulMachine.Trace n s t) (candidate : Word) :
    Trace n (.multiply candidate s) (.multiply candidate t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (multiply_step head candidate) ih

/-- Candidate increment is the same full-adder trace with initial carry, not a numeric update. -/
theorem increment_step {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.step s = some t) (q x : Word) :
    step (.increment q x s) = some (.increment q x t) := by
  cases s <;> first
  | exact congrArg (Option.map (Configuration.increment q x)) h
  | cases h

theorem increment_trace {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) (q x : Word) :
    Trace n (.increment q x s) (.increment q x t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (increment_step head q x) ih

/-- Scan and retain every input bit, including zero padding. -/
theorem scan_trace (q x saved : Word) (nz : Bool) :
    Trace (x.length + 1) (.scan q x saved nz)
      (.restore q (x.reverse ++ saved) [] (nz || nonzero x)) := by
  induction x generalizing saved nz with
  | nil => simpa [nonzero] using Trace.cons (by rfl) (Trace.nil (.restore q saved [] nz))
  | cons b bs ih =>
    simpa [nonzero, List.reverse_cons, List.append_assoc, Bool.or_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved) (nz || b))

/-- Restore the input before either starting candidate search or returning the inverse of zero. -/
theorem restore_trace (q saved x : Word) (nz : Bool) :
    Trace (saved.length + 1) (.restore q saved x nz)
      (if nz then .seed q (saved.reverse ++ x) else .done q (saved.reverse ++ x) []) := by
  induction saved generalizing x with
  | nil => cases nz <;> exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: x))

/-- The zero test and restoration use a width-only count and retain the exact original input. -/
theorem prepare_trace (q x : Word) :
    Trace (2 * x.length + 3) (.start q x)
      (if nonzero x then .seed q x else .done q x []) := by
  have h₁ := scan_trace q x [] false
  have h₂ := restore_trace q x.reverse [] (nonzero x)
  simp only [List.append_nil, Bool.false_or] at h₁
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  convert Trace.cons (s := .start q x) (by rfl) (h₁.append h₂) using 1
  omega

/-- A failed product is removed cell by cell before touching the next candidate. -/
theorem clearProduct_trace (q x candidate out : Word) :
    Trace (out.length + 1) (.clearProduct q x candidate out)
      (.incrementReverse q x candidate []) := by
  induction out with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => simpa [Nat.add_assoc] using Trace.cons (by rfl) ih

/-- A canonical product equals one exactly when the literal low-bit and exhaustion tests succeed. -/
theorem check_trace (q x candidate out : Word) (hc : Canonical out) :
    ∃ n ≤ out.length + 2, Trace n (.checkProduct q x candidate out)
      (if value out = 1 then .recoverReverse q x candidate []
       else .incrementReverse q x candidate []) := by
  cases out with
  | nil => exact ⟨1, by decide, Trace.cons rfl (Trace.nil _)⟩
  | cons b bs =>
    cases b
    · have hn : value (false :: bs) ≠ 1 := by
        change 0 + 2 * value bs ≠ 1
        omega
      refine ⟨bs.length + 2, by simp, ?_⟩
      simpa only [if_neg hn] using Trace.cons (s := .checkProduct q x candidate (false :: bs))
        (by rfl) (clearProduct_trace q x candidate bs)
    · cases bs with
      | nil => exact ⟨2, by decide, Trace.cons rfl (Trace.cons rfl (Trace.nil _))⟩
      | cons b bs =>
        have hp := hc.tail.value_pos (b :: bs) (by simp)
        have hn : value (true :: b :: bs) ≠ 1 := by
          change 1 + 2 * value (b :: bs) ≠ 1
          omega
        refine ⟨(b :: bs).length + 3, by simp [Nat.add_assoc], ?_⟩
        simpa only [if_neg hn] using
          Trace.cons (s := .checkProduct q x candidate (true :: b :: bs)) (by rfl)
            (Trace.cons (s := .afterOne q x candidate (b :: bs)) (by rfl)
              (clearProduct_trace q x candidate (b :: bs)))

/-- Every incrementReverse pass moves one physical bit and charges its final phase transition. -/
theorem incrementReverse_trace (q x candidate saved : Word) :
    Trace (candidate.length + 1) (.incrementReverse q x candidate saved)
      (.incrementCopy q x (candidate.reverse ++ saved) []) := by
  induction candidate generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every incrementCopy pass moves one physical bit and charges its final phase transition. -/
theorem incrementCopy_trace (q x saved left : Word) :
    Trace (saved.length + 1) (.incrementCopy q x saved left)
      (.increment q x (.startAdd (saved.reverse ++ left) [] true)) := by
  induction saved generalizing left with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: left))

/-- Every candidateReverse pass moves one physical bit and charges its final phase transition. -/
theorem candidateReverse_trace (q x out saved : Word) :
    Trace (out.length + 1) (.candidateReverse q x out saved)
      (.candidateCopy q x (out.reverse ++ saved) [] []) := by
  induction out generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every candidateCopy pass moves one physical bit and charges its final phase transition. -/
theorem candidateCopy_trace (q x saved count candidate : Word) :
    Trace (saved.length + 1) (.candidateCopy q x saved count candidate)
      (.multiply (saved.reverse ++ candidate) (.start q (saved.reverse ++ count) x)) := by
  induction saved generalizing count candidate with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: count) (b :: candidate))

/-- Every recoverReverse pass moves one physical bit and charges its final phase transition. -/
theorem recoverReverse_trace (q x candidate saved : Word) :
    Trace (candidate.length + 1) (.recoverReverse q x candidate saved)
      (.recoverCopy q x (candidate.reverse ++ saved) []) := by
  induction candidate generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: saved))

/-- Every recoverCopy pass moves one physical bit and charges its final phase transition. -/
theorem recoverCopy_trace (q x saved out : Word) :
    Trace (saved.length + 1) (.recoverCopy q x saved out)
      (.done q x (saved.reverse ++ out)) := by
  induction saved generalizing out with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: out))

/-- The successful candidate is transferred to output through both charged reversal passes. -/
theorem recover_trace (q x candidate : Word) :
    Trace (2 * candidate.length + 2) (.recoverReverse q x candidate []) (.done q x candidate) := by
  have h₁ := recoverReverse_trace q x candidate []
  have h₂ := recoverCopy_trace q x candidate.reverse []
  simp only [List.append_nil] at h₁
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂
  convert h₁.append h₂ using 1
  omega

/-- Literal increment followed by charged candidate duplication for the next multiplication. -/
theorem increment_correct (q x candidate : Word) (hc : Canonical candidate)
    (hb : value candidate + 1 < value q) :
    ∃ n ≤ 6 * q.length + 10, ∃ next : Word,
      Trace n (.incrementReverse q x candidate []) (.multiply next (.start q next x)) ∧
      value next = value candidate + 1 ∧ Canonical next ∧ next.length ≤ q.length := by
  obtain ⟨na, hna, next, ha, _hra, hva, hca, _hwa⟩ :=
    BinaryWordMachine.add_correct candidate [] true
  simp only [value, bitValue, if_true, Nat.add_zero] at hva
  simp only [List.length_nil, Nat.max_zero] at hna
  have h₁ := incrementReverse_trace q x candidate []
  have h₂ := incrementCopy_trace q x candidate.reverse []
  have h₃ := increment_trace ha q x
  have h₄ := candidateReverse_trace q x next []
  have h₅ := candidateCopy_trace q x next.reverse [] []
  simp only [List.append_nil] at h₁ h₄
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h₂ h₅
  have hp := Trace.cons (s := .increment q x (.word next)) (by rfl) (h₄.append h₅)
  have ht := ((h₁.append h₂).append h₃).append hp
  have hwc := hc.width_le_of_value_lt candidate q (by omega)
  have hwn := hca.width_le_of_value_lt next q (by omega)
  refine ⟨_, ?_, next, ht, hva, hca, hwn⟩
  omega

end Computation.BinaryInverseMachine
