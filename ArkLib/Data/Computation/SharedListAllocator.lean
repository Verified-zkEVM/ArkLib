/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.HeapPointerSemantics

/-!
# Literal fixed-width bump allocation

One twelve-tape program increments the supplied current pointer, checks the actual carry flag,
and either performs the actual payload/cell writer or stops with explicit overflow. Current
pointer bits stay on tape zero, next-pointer bits on tape eleven, and supplied head/tail words
on tapes nine/ten. The successful handoff to the writer changes no tape content. Overflow also
retains all tapes and the entire RAM; it never writes through the wrapped nil pointer.

Inputs satisfy a common fixed width, a non-nil current pointer and the `AboveFree` heap invariant.
The total successor function is not a validator for malformed inputs outside those contracts.
Numerical pointer labels are proof-side codeword labels, not architectural addresses. Input-word
materialization, heap initialization, and a complete decoder refinement remain separate.
-/

@[expose] public section

namespace Computation.SharedListAllocator

open AddressedBits (Address Memory)
open SharedListHeap (Cell RepList Fresh nilPointer writeCell)
open HeapPointerMachine (increment)
open HeapPointerSemantics (AboveFree)

/-- Fixed finite phases; overflow explicitly retains original and wrapped pointer words. -/
inductive Control where
  | incrementing (head tail : List Bool) (child : HeapPointerMachine.Control)
  | writing (next : Address) (child : SharedListCellMachine.Control)
  | overflow (current next head tail : List Bool)
  deriving DecidableEq, Repr

/-- The same unique RAM is passed through increment and actual cell writing. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Only literal child successors and one Boolean-controlled handoff are executed. -/
def step : Configuration → Option Configuration
  | ⟨mem, .incrementing head tail child⟩ =>
      match HeapPointerMachine.step child with
      | some next => some ⟨mem, .incrementing head tail next⟩
      | none => match child with
          | .done current next false =>
              some ⟨mem, .writing next (.building current (.copyTail head tail [] []))⟩
          | .done current next true => some ⟨mem, .overflow current next head tail⟩
          | _ => none
  | ⟨mem, .writing next child⟩ =>
      match SharedListCellMachine.step ⟨mem, child⟩ with
      | some updated => some ⟨updated.memory, .writing next updated.control⟩
      | none => none
  | ⟨_, .overflow _ _ _ _⟩ => none

/-- Counts of the same combined allocator's actual successors. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External trace observer; no numeric fuel/width register is stored in the program. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Composition retains the exact intermediate memory and tape state. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel produces the very same final configuration as the literal trace. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Increment retains RAM and both supplied cell words while moving pointer bits locally. -/
theorem lift_increment (mem : Memory) (head tail : List Bool) {n : ℕ}
    {s t : HeapPointerMachine.Control} (h : HeapPointerMachine.Trace n s t) :
    Trace n ⟨mem, .incrementing head tail s⟩ ⟨mem, .incrementing head tail t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The actual writer changes this allocator's RAM while retaining the next-pointer tape. -/
theorem lift_writer (next : Address) {n : ℕ} {s t : SharedListCellMachine.Configuration}
    (h : SharedListCellMachine.Trace n s t) :
    Trace n ⟨s.memory, .writing next s.control⟩ ⟨t.memory, .writing next t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Successful increment, explicit carry handoff, payload construction and cell write count. -/
def steps (w h : ℕ) : ℕ := 3 * w + 4 + SharedListCellMachine.steps w h

/-- The successful branch is one full execution with the actual written cell memory. -/
theorem success_trace (mem : Memory) (w h : ℕ) (current head tail : List Bool)
    (hw : current.length = w) (hh : head.length = h) (ht : tail.length = w)
    (hnext : (increment current true).2 = false) :
    Trace (steps w h) ⟨mem, .incrementing head tail (.scan current [] [] true)⟩
      ⟨writeCell mem current head tail, .writing (increment current true).1
        (.writing head tail (.done current (List.replicate (1 + h + w) true)))⟩ := by
  have hi := lift_increment mem head tail (HeapPointerMachine.increment_trace current)
  rw [hw, hnext] at hi
  have hh' : Trace 1
      ⟨mem, .incrementing head tail (.done current (increment current true).1 false)⟩
      ⟨mem, .writing (increment current true).1 (.building current (.copyTail head tail [] []))⟩ :=
    .cons rfl (.nil _)
  have hw' := lift_writer (increment current true).1
    (SharedListCellMachine.write_trace mem w h current head tail hw hh ht)
  convert (hi.append hh').append hw' using 1
  simp only [steps]

/-- Overflow stops before any heap write, retains all words, and exposes the wrapped nil pointer. -/
theorem overflow_trace (mem : Memory) (w : ℕ) (current head tail : List Bool)
    (hw : current.length = w) (hov : (increment current true).2 = true) :
    Trace (3 * w + 4) ⟨mem, .incrementing head tail (.scan current [] [] true)⟩
      ⟨mem, .overflow current (nilPointer w) head tail⟩ := by
  have hi := lift_increment mem head tail (HeapPointerMachine.increment_trace current)
  rw [hw, hov, HeapPointerSemantics.increment_overflow_nil current hov, hw] at hi
  have hh : Trace 1 ⟨mem, .incrementing head tail (.done current (nilPointer w) true)⟩
      ⟨mem, .overflow current (nilPointer w) head tail⟩ := .cons rfl (.nil _)
  simpa only [Nat.add_assoc] using hi.append hh

/-- The full successful allocator advances the heap invariant on its actual final RAM.
Both returned pointers are non-nil under the input invariant; every old list remains represented. -/
theorem success_execution {mem : Memory} {w h : ℕ} {current head tail : List Bool}
    {xs : List (List Bool)} (hf : AboveFree mem w current) (hw : current.length = w)
    (hnil : current ≠ nilPointer w) (hh : head.length = h) (hr : RepList mem w h tail xs)
    (hnext : (increment current true).2 = false) :
    ∃ final : Configuration,
      Trace (steps w h) ⟨mem, .incrementing head tail (.scan current [] [] true)⟩ final ∧
      runFuel (steps w h) ⟨mem, .incrementing head tail (.scan current [] [] true)⟩ = final ∧
      final.control = .writing (increment current true).1
        (.writing head tail (.done current (List.replicate (1 + h + w) true))) ∧
      Cell final.memory w h current head tail ∧ RepList final.memory w h current (head :: xs) ∧
      RepList final.memory w h tail xs ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) ∧
      AboveFree final.memory w (increment current true).1 ∧
      Fresh final.memory (increment current true).1 ∧
      (increment current true).1.length = w ∧ (increment current true).1 ≠ nilPointer w ∧
      BinaryWordMachine.value (increment current true).1 = BinaryWordMachine.value current + 1 := by
  have ht := success_trace mem w h current head tail hw hh hr.pointer_width hnext
  have ha := SharedListHeap.cons_allocation hr (hf.current hw) hw hh hnil
  refine ⟨_, ht, ht.runFuel_eq, rfl, ?_, ha.1, ha.2, ?_, hf.writeCell hw hnext head tail,
    hf.next_fresh hw hnext head tail, (HeapPointerMachine.increment_length _ _).trans hw,
    ?_, HeapPointerSemantics.increment_success current hnext⟩
  · exact SharedListHeap.writeCell_cell mem w h current head tail hw hh hr.pointer_width hnil
  · intro old ys hold
    exact hold.writeCell (hf.current hw) hw
  · simpa only [hw] using HeapPointerSemantics.increment_not_nil current hnext

/-- The observed overflow branch returns the exact original memory and performs no allocation. -/
theorem overflow_runFuel (mem : Memory) (w : ℕ) (current head tail : List Bool)
    (hw : current.length = w) (hov : (increment current true).2 = true) :
    runFuel (3 * w + 4) ⟨mem, .incrementing head tail (.scan current [] [] true)⟩ =
      ⟨mem, .overflow current (nilPointer w) head tail⟩ :=
  (overflow_trace mem w current head tail hw hov).runFuel_eq

/-- The same twelve physical tapes span both children and the terminal overflow state. -/
def physicalTapes : Control → Fin 12 → List Bool
  | .incrementing head tail child =>
      let t := HeapPointerMachine.tapes child
      ![t.left, t.right, t.saved, [], [], [], [], [], [], head, tail, t.output]
  | .writing next child =>
      let t := SharedListCellMachine.physicalTapes child
      ![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7, t 8, t 9, t 10, next]
  | .overflow current next head tail =>
      ![current, [], [], [], [], [], [], [], [], head, tail, next]

/-- Successful child handoff changes no physical tape contents. -/
theorem success_handoff_tapes (current next head tail : List Bool) :
    physicalTapes (.incrementing head tail (.done current next false)) =
      physicalTapes (.writing next (.building current (.copyTail head tail [] []))) := rfl

/-- Overflow preserves every physical tape rather than silently clearing or re-encoding words. -/
theorem overflow_handoff_tapes (current next head tail : List Bool) :
    physicalTapes (.incrementing head tail (.done current next true)) =
      physicalTapes (.overflow current next head tail) := rfl

private theorem increment_none (child : HeapPointerMachine.Control)
    (h : HeapPointerMachine.step child = none) :
    ∃ current next flag, child = .done current next flag := by
  cases child with
  | scan remaining original result carry => cases remaining <;> simp [HeapPointerMachine.step] at h
  | restoreOld source original result overflow =>
      cases source <;> simp [HeapPointerMachine.step] at h
  | restoreNext original source next overflow =>
      cases source <;> simp [HeapPointerMachine.step] at h
  | done original next overflow => exact ⟨original, next, overflow, rfl⟩

private theorem bank_twelve
    {a b c d e f g h i j k l a' b' c' d' e' f' g' h' i' j' k' l' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') (hl : BitLocalActions.CellStep l l') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k, l]
      ![a', b', c', d', e', f', g', h', i', j', k', l'] := by
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

/-- Every allocator successor uses the same fixed twelve-tape local-bit interface. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | incrementing head tail child =>
      cases hs : HeapPointerMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := HeapPointerMachine.step_local hs
          exact bank_twelve hl.1 hl.2.1 hl.2.2.1 (.keep _) (.keep _) (.keep _)
            (.keep _) (.keep _) (.keep _) (.keep _) (.keep _) hl.2.2.2
      | none =>
          obtain ⟨current, next, flag, rfl⟩ := increment_none child hs
          cases flag <;> cases h
          · rw [success_handoff_tapes]
            intro i
            exact .keep _
          · rw [overflow_handoff_tapes]
            intro i
            exact .keep _
  | writing next child =>
      cases hs : SharedListCellMachine.step ⟨mem, child⟩ with
      | some updated =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := SharedListCellMachine.step_local hs
          exact bank_twelve (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) (hl 5)
            (hl 6) (hl 7) (hl 8) (hl 9) (hl 10) (.keep _)
      | none => simp only [step, hs] at h; contradiction
  | overflow current next head tail => cases h

end Computation.SharedListAllocator
