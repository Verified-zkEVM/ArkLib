/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListUncons
public import ArkLib.Data.Computation.PaddedMul
public import ArkLib.Data.Computation.PaddedModAdd

/-!
# A physical shared-list Horner loop

The same RAM and twenty-one physical tapes execute uncons, pointer/index cleanup, two-pass
movement of the tail pointer, scalar multiplication and scalar addition. Coefficients are
consumed highest degree first. No list operation, scalar encoding, whole-word relocation or
clearing is an instruction. Child terminal handoffs preserve every tape literally.

The loop-header entry takes an already materialized accumulator, point, modulus and coefficient
pointer. Initial accumulator reset is outside this entry. Only the existing local-bit RAM model
is claimed; the interpreter's native running time is not the transition cost.
-/

@[expose] public section

namespace Computation.SharedListHornerMachine

open AddressedBits (Memory)
open BinaryWordMachine (Word)

inductive Control where
  | taking (acc point : Word) (child : SharedListUncons.Control)
  | clearPointer (q point acc coeff pointer index tail : Word)
  | clearIndex (q point acc coeff index tail : Word)
  | reverseTail (q point acc coeff source saved : Word)
  | restorePointer (q point acc coeff source pointer : Word)
  | multiplying (coeff pointer : Word) (child : PaddedMul.Control)
  | adding (point pointer : Word) (child : PaddedModAdd.Control)
  | done (q point pointer acc : Word)
  deriving DecidableEq, Repr

structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- All child transitions act on this same memory; cleanup is one pop or push per tape. -/
def step : Configuration → Option Configuration
  | ⟨mem, .taking acc point child⟩ =>
      match SharedListUncons.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .taking acc point next.control⟩
      | none => match child with
          | .empty q pointer => some ⟨mem, .done q point pointer acc⟩
          | .reading (.reading q (.done pointer index coeff tail)) =>
              some ⟨mem, .clearPointer q point acc coeff pointer index tail⟩
          | _ => none
  | ⟨mem, .clearPointer q point acc coeff (_ :: rest) index tail⟩ =>
      some ⟨mem, .clearPointer q point acc coeff rest index tail⟩
  | ⟨mem, .clearPointer q point acc coeff [] index tail⟩ =>
      some ⟨mem, .clearIndex q point acc coeff index tail⟩
  | ⟨mem, .clearIndex q point acc coeff (_ :: rest) tail⟩ =>
      some ⟨mem, .clearIndex q point acc coeff rest tail⟩
  | ⟨mem, .clearIndex q point acc coeff [] tail⟩ =>
      some ⟨mem, .reverseTail q point acc coeff tail []⟩
  | ⟨mem, .reverseTail q point acc coeff (b :: rest) saved⟩ =>
      some ⟨mem, .reverseTail q point acc coeff rest (b :: saved)⟩
  | ⟨mem, .reverseTail q point acc coeff [] saved⟩ =>
      some ⟨mem, .restorePointer q point acc coeff saved []⟩
  | ⟨mem, .restorePointer q point acc coeff (b :: rest) pointer⟩ =>
      some ⟨mem, .restorePointer q point acc coeff rest (b :: pointer)⟩
  | ⟨mem, .restorePointer q point acc coeff [] pointer⟩ =>
      some ⟨mem, .multiplying coeff pointer (.normalizing q point (.startAdd acc [] false))⟩
  | ⟨mem, .multiplying coeff pointer child⟩ =>
      match PaddedMul.step child with
      | some next => some ⟨mem, .multiplying coeff pointer next⟩
      | none => match child with
          | .padding point (.padding q (.done out)) =>
              some ⟨mem, .adding point pointer (.adding (.start q out coeff))⟩
          | _ => none
  | ⟨mem, .adding point pointer child⟩ =>
      match PaddedModAdd.step child with
      | some next => some ⟨mem, .adding point pointer next⟩
      | none => match child with
          | .padding (.padding q (.done out)) =>
              some ⟨mem, .taking out point (.scan q pointer [] false)⟩
          | _ => none
  | ⟨_, .done _ _ _ _⟩ => none

/-- Accumulator zero, modulus four, point eight, coefficient eleven, current pointer twelve,
tail sixteen and old index seventeen are fixed positions. Remaining positions are child scratch. -/
def tapes : Control → Fin 21 → Word
  | .taking acc point child =>
      let t := SharedListUncons.tapes child
      ![acc, [], [], [], t 14, t 5, t 6, t 7, point, t 8, t 9, t 13,
        t 0, t 1, t 3, t 4, t 10, t 2, t 11, t 12, t 15]
  | .clearPointer q point acc coeff pointer index tail =>
      ![acc, [], [], [], q, [], [], [], point, [], [], coeff,
        pointer, [], [], [], tail, index, [], [], []]
  | .clearIndex q point acc coeff index tail =>
      ![acc, [], [], [], q, [], [], [], point, [], [], coeff,
        [], [], [], [], tail, index, [], [], []]
  | .reverseTail q point acc coeff source saved =>
      ![acc, [], [], [], q, [], [], [], point, [], [], coeff,
        [], saved, [], [], source, [], [], [], []]
  | .restorePointer q point acc coeff source pointer =>
      ![acc, [], [], [], q, [], [], [], point, [], [], coeff,
        pointer, source, [], [], [], [], [], [], []]
  | .multiplying coeff pointer child =>
      let t := PaddedMul.tapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, coeff,
        pointer, [], [], [], [], [], [], [], []]
  | .adding point pointer child =>
      let t := PaddedModAdd.tapes child
      ![t 0, [], t 2, t 3, t 4, t 5, t 6, [], point, [], [], t 1,
        pointer, [], [], [], [], [], [], [], []]
  | .done q point pointer acc =>
      ![acc, [], [], [], q, [], [], [], point, [], [], [],
        pointer, [], [], [], [], [], [], [], []]

private theorem bank_twenty_one
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
      a0' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10'
      a11' a12' a13' a14' a15' a16' a17' a18' a19' a20' : Word}
    (h0 : BitLocalActions.CellStep a0 a0') (h1 : BitLocalActions.CellStep a1 a1')
    (h2 : BitLocalActions.CellStep a2 a2') (h3 : BitLocalActions.CellStep a3 a3')
    (h4 : BitLocalActions.CellStep a4 a4') (h5 : BitLocalActions.CellStep a5 a5')
    (h6 : BitLocalActions.CellStep a6 a6') (h7 : BitLocalActions.CellStep a7 a7')
    (h8 : BitLocalActions.CellStep a8 a8') (h9 : BitLocalActions.CellStep a9 a9')
    (h10 : BitLocalActions.CellStep a10 a10') (h11 : BitLocalActions.CellStep a11 a11')
    (h12 : BitLocalActions.CellStep a12 a12') (h13 : BitLocalActions.CellStep a13 a13')
    (h14 : BitLocalActions.CellStep a14 a14') (h15 : BitLocalActions.CellStep a15 a15')
    (h16 : BitLocalActions.CellStep a16 a16') (h17 : BitLocalActions.CellStep a17 a17')
    (h18 : BitLocalActions.CellStep a18 a18') (h19 : BitLocalActions.CellStep a19 a19')
    (h20 : BitLocalActions.CellStep a20 a20') :
    BitLocalActions.BankStep
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
        a12, a13, a14, a15, a16, a17, a18, a19, a20]
      ![a0', a1', a2', a3', a4', a5', a6', a7', a8', a9', a10',
        a11', a12', a13', a14', a15', a16', a17', a18', a19', a20'] := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20

/-- Nil emits the retained accumulator without moving its word. -/
theorem empty_handoff (q point pointer acc : Word) :
    tapes (.taking acc point (.empty q pointer)) = tapes (.done q point pointer acc) := by
  funext i
  fin_cases i <;> rfl

theorem take_handoff (q point pointer index coeff tail acc : Word) :
    tapes (.taking acc point (.reading (.reading q (.done pointer index coeff tail)))) =
      tapes (.clearPointer q point acc coeff pointer index tail) := by
  funext i
  fin_cases i <;> rfl

theorem multiply_handoff (q point pointer coeff out : Word) :
    tapes (.multiplying coeff pointer (.padding point (.padding q (.done out)))) =
      tapes (.adding point pointer (.adding (.start q out coeff))) := by
  funext i
  fin_cases i <;> rfl

theorem add_handoff (q point pointer out : Word) :
    tapes (.adding point pointer (.padding (.padding q (.done out)))) =
      tapes (.taking out point (.scan q pointer [] false)) := by
  funext i
  fin_cases i <;> rfl

/-- Every successor obeys the same fixed-bank local-bit rule. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s.control) (tapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | taking acc point child =>
      cases hs : SharedListUncons.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := SharedListUncons.step_local hs
          exact bank_twenty_one (.keep _) (.keep _) (.keep _) (.keep _) (hl 14)
            (hl 5) (hl 6) (hl 7) (.keep _) (hl 8) (hl 9) (hl 13) (hl 0) (hl 1)
            (hl 3) (hl 4) (hl 10) (hl 2) (hl 11) (hl 12) (hl 15)
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child with
          | empty q pointer =>
              cases h
              rw [empty_handoff]
              intro i
              exact .keep _
          | scan _ _ _ _ | restore _ _ _ _ => cases h
          | reading child =>
              cases child with
              | building _ | shaping _ _ _ => cases h
              | reading q child =>
                  cases child <;> try cases h
                  rw [take_handoff]
                  intro i
                  exact .keep _
  | clearPointer q point acc coeff pointer index tail =>
      cases pointer <;> cases h <;> apply bank_twenty_one <;> constructor
  | clearIndex q point acc coeff index tail =>
      cases index <;> cases h <;> apply bank_twenty_one <;> constructor
  | reverseTail q point acc coeff source saved =>
      cases source <;> cases h <;> apply bank_twenty_one <;> constructor
  | restorePointer q point acc coeff source pointer =>
      cases source <;> cases h <;> apply bank_twenty_one <;> constructor
  | multiplying coeff pointer child =>
      cases hs : PaddedMul.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := PaddedMul.step_local hs
          exact bank_twenty_one (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5)
            (hl 6) (hl 7) (hl 8) (hl 9) (hl 10) (.keep _) (.keep _) (.keep _)
            (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child with
          | normalizing _ _ _ | multiplying _ => cases h
          | padding point child =>
              cases child with
              | shaping _ _ => cases h
              | padding q child =>
                  cases child <;> try cases h
                  rw [multiply_handoff]
                  intro i
                  exact .keep _
  | adding point pointer child =>
      cases hs : PaddedModAdd.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := PaddedModAdd.step_local hs
          exact bank_twenty_one (hl 0) (.keep _) (hl 2) (hl 3) (hl 4) (hl 5)
            (hl 6) (.keep _) (.keep _) (.keep _) (.keep _) (hl 1) (.keep _) (.keep _)
            (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child with
          | adding _ => cases h
          | padding child =>
              cases child with
              | shaping _ _ => cases h
              | padding q child =>
                  cases child <;> try cases h
                  rw [add_handoff]
                  intro i
                  exact .keep _
  | done _ _ _ _ => cases h

inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

theorem lift_uncons (acc point : Word) {n : ℕ} {s t : SharedListUncons.Configuration}
    (h : SharedListUncons.Trace n s t) :
    Trace n ⟨s.memory, .taking acc point s.control⟩
      ⟨t.memory, .taking acc point t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_mul (mem : Memory) (coeff pointer : Word) {n : ℕ} {s t : PaddedMul.Control}
    (h : PaddedMul.Trace n s t) :
    Trace n ⟨mem, .multiplying coeff pointer s⟩ ⟨mem, .multiplying coeff pointer t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_add (mem : Memory) (point pointer : Word) {n : ℕ} {s t : PaddedModAdd.Control}
    (h : PaddedModAdd.Trace n s t) :
    Trace n ⟨mem, .adding point pointer s⟩ ⟨mem, .adding point pointer t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

end Computation.SharedListHornerMachine
