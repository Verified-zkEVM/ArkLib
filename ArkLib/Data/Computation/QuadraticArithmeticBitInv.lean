/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.WordCopyMachine
public import ArkLib.Data.Computation.PaddedInverse

/-!
# A literal alias-safe scalar-register INV instruction

Eight scalar registers are physical word tapes. The operand is copied and its source restored
before the destination is cleared. This handles a destination aliasing the source. The arithmetic
child retains its input copy on tape eight, which is explicitly cleared before write-back. The
result is copied into the destination and its temporary cleared with actual local-bit successors.

Thirteen work tapes, eight register tapes, five immutable input tapes and two one-bit flag tapes
form one fixed bank. A register owned by a copy child is blanked in the inactive frame and viewed
only through that child's corresponding tape. No hidden old word is retained for restoration.
This module lowers one INV instruction; it does not initialize registers or compile a full program.
-/

@[expose] public section

namespace Computation.QuadraticArithmeticBitInv

open BinaryWordMachine (Word)
abbrev Register := Fin 8
abbrev Registers := Register → Word
abbrev Slot := Fin 13 ⊕ (Register ⊕ (Fin 5 ⊕ Fin 2))

inductive Control where
  | start (q : Word) (x dst : Register) (r : Registers)
  | loading (q : Word) (x dst : Register) (r : Registers) (child : WordCopyMachine.Control)
  | inverting (dst : Register) (r : Registers) (child : PaddedInverse.Control)
  | clearInput (q : Word) (dst : Register) (r : Registers) (out operand : Word)
  | storing (q : Word) (dst : Register) (r : Registers) (child : WordCopyMachine.Control)
  | clearing (q : Word) (r : Registers) (word : Word)
  | done (q : Word) (r : Registers)

/-- The finite source selectors never become scalar words or unbounded addresses. -/
def step : Control → Option Control
  | .start q x dst r =>
      some (.loading q x dst (Function.update r x []) (.clear (r x) []))
  | .loading q x dst r child =>
      match WordCopyMachine.step child with
      | some next => some (.loading q x dst r next)
      | none => match child with
          | .done source operand =>
              some (.inverting dst (Function.update r x source) (.inverting (.start q operand)))
          | _ => none
  | .inverting dst r child =>
      match PaddedInverse.step child with
      | some next => some (.inverting dst r next)
      | none => match child with
          | .padding operand (.padding q (.done out)) =>
              some (.clearInput q dst r out operand)
          | _ => none
  | .clearInput q dst r out (_ :: rest) => some (.clearInput q dst r out rest)
  | .clearInput q dst r out [] =>
      some (.storing q dst (Function.update r dst []) (.clear out (r dst)))
  | .storing q dst r child =>
      match WordCopyMachine.step child with
      | some next => some (.storing q dst r next)
      | none => match child with
          | .done source out => some (.clearing q (Function.update r dst out) source)
          | _ => none
  | .clearing q r (_ :: rest) => some (.clearing q r rest)
  | .clearing q r [] => some (.done q r)
  | .done _ _ => none

/-- Work slot eight holds the operand copy, two is copy scratch, four retains the modulus. -/
def work : Control → Fin 13 → Word
  | .start q _ _ _ | .done q _ =>
      ![[], [], [], [], q, [], [], [], [], [], [], [], []]
  | .loading q _ _ _ child =>
      let t := WordCopyMachine.tapes child
      ![[], [], t 1, [], q, [], [], [], t 2, [], [], [], []]
  | .inverting _ _ child =>
      let t := PaddedInverse.tapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, t 11, t 12]
  | .clearInput q _ _ out operand =>
      ![out, [], [], [], q, [], [], [], operand, [], [], [], []]
  | .storing q _ _ child =>
      let t := WordCopyMachine.tapes child
      ![t 0, [], t 1, [], q, [], [], [], [], [], [], [], []]
  | .clearing q _ word =>
      ![word, [], [], [], q, [], [], [], [], [], [], [], []]

/-- A copy child owns exactly one register tape; every other register stays in the frame. -/
def registers : Control → Registers
  | .start _ _ _ r | .inverting _ r _ | .clearInput _ _ r _ _ | .clearing _ r _ | .done _ r => r
  | .loading _ x _ r child => Function.update r x (WordCopyMachine.tapes child 0)
  | .storing _ dst r child => Function.update r dst (WordCopyMachine.tapes child 2)

/-- All five immutable inputs and both physical flag bits are framed throughout the instruction. -/
def tapes (input : Fin 5 → Word) (flags : Fin 2 → Bool) (s : Control) : Slot → Word
  | .inl i => work s i
  | .inr (.inl i) => registers s i
  | .inr (.inr (.inl i)) => input i
  | .inr (.inr (.inr i)) => [flags i]

theorem restore_original (r : Registers) (i : Register) :
    Function.update (Function.update r i []) i (r i) = r := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Function.update_of_ne h]

private theorem update_local (r : Registers) (i : Register) {a b : Word}
    (h : BitLocalActions.CellStep a b) :
    BitLocalActions.BankStep (Function.update r i a) (Function.update r i b) := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa using h
  · simp only [Function.update_of_ne hj]
    exact .keep _

private theorem bank_thirteen
    {a b c d e f g h i j k l m a' b' c' d' e' f' g' h' i' j' k' l' m' : Word}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') (hl : BitLocalActions.CellStep l l')
    (hm : BitLocalActions.CellStep m m') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k, l, m]
      ![a', b', c', d', e', f', g', h', i', j', k', l', m'] := by
  intro x
  fin_cases x
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf
  · exact hg
  · exact hh
  · exact hi
  · exact hj
  · exact hk
  · exact hl
  · exact hm

/-- Every dynamic register handoff restores the tape occupied by the child, with no word copy. -/
theorem step_local {s t : Control} (h : step s = some t)
    (input : Fin 5 → Word) (flags : Fin 2 → Bool) :
    BitLocalActions.BankStep (tapes input flags s) (tapes input flags t) := by
  suffices hw : BitLocalActions.BankStep (work s) (work t) ∧
      BitLocalActions.BankStep (registers s) (registers t) by
    intro i
    rcases i with i | i
    · exact hw.1 i
    · rcases i with i | i
      · exact hw.2 i
      · cases i <;> exact .keep _
  cases s with
  | start q x dst r =>
      cases h
      constructor
      · apply bank_thirteen <;> constructor
      · simp only [registers, WordCopyMachine.tapes, Matrix.cons_val_zero]
        rw [restore_original]
        intro i
        exact .keep _
  | loading q x dst r child =>
      cases hs : WordCopyMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := WordCopyMachine.step_local hs
          constructor
          · exact bank_thirteen (.keep _) (.keep _) (hl 1) (.keep _) (.keep _) (.keep _)
              (.keep _) (.keep _) (hl 2) (.keep _) (.keep _) (.keep _) (.keep _)
          · exact update_local r x (hl 0)
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          constructor
          · apply bank_thirteen <;> constructor
          · intro i; exact .keep _
  | inverting dst r child =>
      cases hs : PaddedInverse.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := PaddedInverse.step_local hs
          constructor
          · exact bank_thirteen (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5) (hl 6)
              (hl 7) (hl 8) (hl 9) (hl 10) (hl 11) (hl 12)
          · intro i; exact .keep _
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child with
          | inverting _ => cases h
          | padding operand child =>
              cases child with
              | shaping _ _ => cases h
              | padding q child =>
                  cases child <;> try cases h
                  constructor
                  · apply bank_thirteen <;> constructor
                  · intro i; exact .keep _
  | clearInput q dst r out operand =>
      cases operand with
      | nil =>
          cases h
          constructor
          · apply bank_thirteen <;> constructor
          · change BitLocalActions.BankStep r
              (Function.update (Function.update r dst []) dst (r dst))
            rw [restore_original]
            intro i
            exact .keep _
      | cons b bs =>
          cases h
          constructor
          · apply bank_thirteen <;> constructor
          · intro i; exact .keep _
  | storing q dst r child =>
      cases hs : WordCopyMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := WordCopyMachine.step_local hs
          constructor
          · exact bank_thirteen (hl 0) (.keep _) (hl 1) (.keep _) (.keep _) (.keep _)
              (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
          · exact update_local r dst (hl 2)
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          constructor
          · apply bank_thirteen <;> constructor
          · intro i; exact .keep _
  | clearing q r word =>
      cases word <;> cases h <;> constructor
      all_goals first | (apply bank_thirteen <;> constructor) | (intro i; exact .keep _)
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

/-- Memory, immutable source inputs and flags are concrete retained parts of the execution state. -/
structure Configuration where
  memory : AddressedBits.Memory
  input : Fin 5 → Word
  flags : Fin 2 → Bool
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

end Computation.QuadraticArithmeticBitInv
