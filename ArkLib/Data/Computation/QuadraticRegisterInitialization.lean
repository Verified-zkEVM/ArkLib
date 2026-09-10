/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.FieldLiteralMachine
public import ArkLib.Data.Computation.WordCopyMachine
public import Mathlib.Data.Fintype.Sum

/-!
# Physical initialization of the quadratic arithmetic register bank

The modulus is supplied on work tape four; the eight scalar registers and both flag tapes
start blank. One literal-zero controller constructs a word of the modulus width. Eight actual
copy controllers fill the registers, after which the temporary word is cleared and the two
false flags are pushed. A bounded `Fin 8` cursor is control, not an unbounded integer tape.
The five immutable input words and the RAM are retained. This is initialization, not a complete
arithmetic-program or decoder bit-complexity theorem.
-/

@[expose] public section

namespace Computation.QuadraticRegisterInitialization

open BinaryWordMachine (Word value)
abbrev Registers := Fin 8 → Word
abbrev Slot := Fin 13 ⊕ (Fin 8 ⊕ (Fin 5 ⊕ Fin 2))

inductive Control where
  | literal (child : FieldLiteralMachine.Control)
  | copying (q : Word) (i : Fin 8) (r : Registers) (child : WordCopyMachine.Control)
  | clearing (q : Word) (r : Registers) (word : Word)
  | flags (q : Word) (r : Registers)
  | done (q : Word) (r : Registers)

/-- Copy sources stay on work tape zero. Each copy owns one physical destination register. -/
def step : Control → Option Control
  | .literal child => match FieldLiteralMachine.step child with
      | some next => some (.literal next)
      | none => match child with
          | .done q z => some (.copying q 0 (fun _ ↦ []) (.clear z []))
          | _ => none
  | .copying q i r child => match WordCopyMachine.step child with
      | some next => some (.copying q i r next)
      | none => match child with
          | .done source out =>
              let filled := Function.update r i out
              if h : i.val < 7 then
                let j : Fin 8 := ⟨i.val + 1, by omega⟩
                some (.copying q j (Function.update filled j []) (.clear source (filled j)))
              else some (.clearing q filled source)
          | _ => none
  | .clearing q r (_ :: rest) => some (.clearing q r rest)
  | .clearing q r [] => some (.flags q r)
  | .flags q r => some (.done q r)
  | .done _ _ => none

def work : Control → Fin 13 → Word
  | .literal child =>
      let t := FieldLiteralMachine.tapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, [], [], [], [], [], [], []]
  | .copying q _ _ child =>
      let t := WordCopyMachine.tapes child
      ![t 0, [], t 1, [], q, [], [], [], [], [], [], [], []]
  | .clearing q _ word => ![word, [], [], [], q, [], [], [], [], [], [], [], []]
  | .flags q _ | .done q _ => ![[], [], [], [], q, [], [], [], [], [], [], [], []]

def registers : Control → Registers
  | .literal _ => fun _ ↦ []
  | .copying _ i r child => Function.update r i (WordCopyMachine.tapes child 2)
  | .clearing _ r _ | .flags _ r | .done _ r => r

/-- The two Boolean constants are absent until an actual transition pushes their bits. -/
def flagWords : Control → Fin 2 → Word
  | .done _ _ => fun _ ↦ [false]
  | _ => fun _ ↦ []

def tapes (input : Fin 5 → Word) (s : Control) : Slot → Word
  | .inl i => work s i
  | .inr (.inl i) => registers s i
  | .inr (.inr (.inl i)) => input i
  | .inr (.inr (.inr i)) => flagWords s i

private theorem restore (r : Registers) (i : Fin 8) :
    Function.update (Function.update r i []) i (r i) = r := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

private theorem update_local (r : Registers) (i : Fin 8) {a b : Word}
    (h : BitLocalActions.CellStep a b) :
    BitLocalActions.BankStep (Function.update r i a) (Function.update r i b) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using h
  · simp only [Function.update_of_ne hj]; exact .keep _

/-- All tape writes and handoffs, including initialization of flags, are bit-local. -/
theorem step_local {s t : Control} (h : step s = some t) (input : Fin 5 → Word) :
    BitLocalActions.BankStep (tapes input s) (tapes input t) := by
  suffices H : BitLocalActions.BankStep (work s) (work t) ∧
      BitLocalActions.BankStep (registers s) (registers t) ∧
      BitLocalActions.BankStep (flagWords s) (flagWords t) by
    intro slot
    rcases slot with i | i
    · exact H.1 i
    · rcases i with i | i
      · exact H.2.1 i
      · cases i with
        | inl i => exact .keep _
        | inr i => exact H.2.2 i
  cases s with
  | literal child =>
      cases hs : FieldLiteralMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := FieldLiteralMachine.step_local hs
          refine ⟨?_, fun _ ↦ .keep _, fun _ ↦ .keep _⟩
          intro i
          fin_cases i <;>
            first | exact hl 0 | exact hl 1 | exact hl 2 | exact hl 3 |
              exact hl 4 | exact hl 5 | exact .keep _
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          refine ⟨?_, ?_, fun _ ↦ .keep _⟩
          · intro i; fin_cases i <;> exact .keep _
          · intro i
            change BitLocalActions.CellStep [] (Function.update (fun _ : Fin 8 ↦ []) 0 [] i)
            by_cases hi : i = 0
            · subst i; exact .keep _
            · rw [Function.update_of_ne hi]; exact .keep _
  | copying q i r child =>
      cases hs : WordCopyMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := WordCopyMachine.step_local hs
          refine ⟨?_, update_local r i (hl 2), fun _ ↦ .keep _⟩
          intro j
          fin_cases j <;> first | exact hl 0 | exact hl 1 | exact .keep _
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child with
          | clear source destination | save source scratch | restore scratch source destination =>
              cases h
          | done source out =>
            dsimp only at h
            split at h <;> cases h
            · refine ⟨?_, ?_, fun _ ↦ .keep _⟩
              · intro j; fin_cases j <;> exact .keep _
              · let j : Fin 8 := ⟨i.val + 1, by omega⟩
                change BitLocalActions.BankStep (Function.update r i out)
                  (Function.update (Function.update (Function.update r i out) j []) j
                    ((Function.update r i out) j))
                rw [restore]
                intro j; exact .keep _
            · exact ⟨fun _ ↦ .keep _, fun _ ↦ .keep _, fun _ ↦ .keep _⟩
  | clearing q r word =>
      cases word <;> cases h
      · exact ⟨fun _ ↦ .keep _, fun _ ↦ .keep _, fun _ ↦ .keep _⟩
      · refine ⟨?_, fun _ ↦ .keep _, fun _ ↦ .keep _⟩
        intro i; fin_cases i <;> constructor
  | flags q r => cases h; exact ⟨fun _ ↦ .keep _, fun _ ↦ .keep _, fun _ ↦ .push _ _⟩
  | done _ _ => cases h

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

theorem lift_literal {n : ℕ} {s t : FieldLiteralMachine.Control}
    (h : FieldLiteralMachine.Trace n s t) : Trace n (.literal s) (.literal t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_copy (q : Word) (i : Fin 8) (r : Registers) {n : ℕ}
    {s t : WordCopyMachine.Control} (h : WordCopyMachine.Trace n s t) :
    Trace n (.copying q i r s) (.copying q i r t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The proof-side prefix of initialized registers; runtime does not evaluate this map. -/
def initializedPrefix (z : Word) (n : ℕ) : Registers := fun i ↦ if i.val < n then z else []

private theorem prefix_update (z : Word) (i : Fin 8) :
    Function.update (initializedPrefix z i.val) i z = initializedPrefix z (i.val + 1) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [initializedPrefix]
  · have hne : j.val ≠ i.val := fun h ↦ hj (Fin.ext h)
    simp only [Function.update_of_ne hj, initializedPrefix]
    have hlt : j.val < i.val ↔ j.val < i.val + 1 := by omega
    simp only [hlt]

/-- The remaining bounded register cursor executes exactly the indicated copy instructions. -/
theorem copying_trace (q z : Word) (i : Fin 8) :
    Trace ((8 - i.val) * (2 * z.length + 4))
      (.copying q i (initializedPrefix z i.val) (.clear z []))
      (.clearing q (fun _ ↦ z) z) := by
  have aux : ∀ l : ℕ, ∀ i : Fin 8, 8 - i.val = l →
      Trace ((8 - i.val) * (2 * z.length + 4))
        (.copying q i (initializedPrefix z i.val) (.clear z []))
        (.clearing q (fun _ ↦ z) z) := by
    intro l
    induction l using Nat.strong_induction_on with
    | h l ih =>
      intro i hi
      have hc := lift_copy q i (initializedPrefix z i.val) (WordCopyMachine.copy_correct z []).1
      simp only [List.length_nil, Nat.zero_add] at hc
      by_cases hn : i.val < 7
      · let j : Fin 8 := ⟨i.val + 1, by omega⟩
        have hj : (initializedPrefix z (i.val + 1)) j = [] := by simp [initializedPrefix, j]
        have he : Function.update (initializedPrefix z (i.val + 1)) j [] =
            initializedPrefix z j.val := by rw [← hj, Function.update_eq_self]
        have hh : Trace 1 (.copying q i (initializedPrefix z i.val) (.done z z))
            (.copying q j (initializedPrefix z j.val) (.clear z [])) := by
          apply Trace.cons (tail := Trace.nil _)
          simp only [step, WordCopyMachine.step, dif_pos hn, prefix_update]
          change some (Control.copying q j
            (Function.update (initializedPrefix z (i.val + 1)) j [])
            (.clear z ((initializedPrefix z (i.val + 1)) j))) = _
          rw [hj, he]
        have hr := ih (8 - j.val) (by dsimp [j]; omega) j rfl
        convert (hc.append hh).append hr using 1
        dsimp [j]
        have hsub : 8 - i.val = (8 - (i.val + 1)) + 1 := by omega
        rw [hsub, Nat.add_mul]
        omega
      · have hi7 : i.val = 7 := by omega
        have he : initializedPrefix z (i.val + 1) = fun _ ↦ z := by
          funext j; simp only [initializedPrefix, hi7]; rw [if_pos (by omega)]
        have hh : Trace 1 (.copying q i (initializedPrefix z i.val) (.done z z))
            (.clearing q (fun _ ↦ z) z) := by
          apply Trace.cons (tail := Trace.nil _)
          simp only [step, WordCopyMachine.step, dif_neg hn, prefix_update, he]
        convert hc.append hh using 1
        rw [hi7]
        omega
  exact aux _ i rfl

theorem clearing_trace (q : Word) (r : Registers) (word : Word) :
    Trace (word.length + 2) (.clearing q r word) (.done q r) := by
  induction word with
  | nil => exact .cons rfl (.cons rfl (.nil _))
  | cons b bs ih => exact .cons rfl ih

/-- Initialize all eight scalar zeros and both flags, with the exact actual transition count. -/
theorem initialization_trace (q : Word) :
    Trace (19 * q.length + 40) (.literal (.start q false))
      (.done q (fun _ ↦ List.replicate q.length false)) := by
  let z := List.replicate q.length false
  have hl := lift_literal (FieldLiteralMachine.zero_trace q)
  have hh : Trace 1 (.literal (.done q z))
      (.copying q 0 (initializedPrefix z 0) (.clear z [])) := .cons rfl (.nil _)
  have hc := copying_trace q z 0
  have hf := clearing_trace q (fun _ ↦ z) z
  convert ((hl.append hh).append hc).append hf using 1
  dsimp [z]
  simp only [List.length_replicate]
  omega

/-- The actual initializer executes with unchanged RAM and immutable input words. -/
structure Configuration where
  memory : AddressedBits.Memory
  input : Fin 5 → Word
  control : Control

def ramStep (s : Configuration) : Option Configuration :=
  (step s.control).map fun next ↦ { s with control := next }

def ramRunFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

theorem ramRunFuel_eq (s : Configuration) (n : ℕ) :
    ramRunFuel n s = { s with control := runFuel n s.control } := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s.control <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

/-- The same fixed-count execution produces all scalar zeros and physical false flags.
No initialized register bank or zero word is supplied by the caller. -/
theorem initialization_execution (mem : AddressedBits.Memory) (input : Fin 5 → Word) (q : Word) :
    let final := Control.done q (fun _ ↦ List.replicate q.length false)
    Trace (19 * q.length + 40) (.literal (.start q false)) final ∧
      ramRunFuel (19 * q.length + 40) ⟨mem, input, .literal (.start q false)⟩ =
        ⟨mem, input, final⟩ ∧
      (∀ i, (registers final i).length = q.length ∧ value (registers final i) = 0) ∧
      (∀ i, flagWords final i = [false]) := by
  dsimp only
  refine ⟨initialization_trace q, ?_, ?_, fun _ ↦ rfl⟩
  · rw [ramRunFuel_eq, (initialization_trace q).runFuel_eq]
  · intro i
    exact ⟨List.length_replicate, FieldLiteralMachine.zero_value _⟩

end Computation.QuadraticRegisterInitialization
