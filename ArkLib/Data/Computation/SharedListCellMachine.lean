/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.CellPayloadMachine
public import ArkLib.Data.Computation.SharedListHeapExecution

/-!
# Literal payload construction and shared-list cell writing

One fixed eleven-tape controller first materializes the payload, then writes it through the actual
bit-block child. The base stays on tape zero and payload output on tape four through the one-step
handoff. Retained head/tail words stay on tapes nine/ten while the writer uses tapes zero to eight.
No phase change relocates or copies a whole tape. The same memory flows into every writer step.

The supplied words and fresh fixed-width pointer are already materialized. Pointer selection,
scalar encoding, reads, and a full decoder bit-cost refinement are separate obligations. The
transition count includes payload construction, the literal handoff, and every writer transition.
It is a count in the stated bit-RAM model, not native Lean execution time.
-/

@[expose] public section

namespace Computation.SharedListCellMachine

open AddressedBits (Address Memory)
open SharedListHeap (Cell RepList Fresh nilPointer writeCell)

/-- The two child controllers share one fixed physical tape bank. -/
inductive Control where
  | building (base : Address) (child : CellPayloadMachine.Control)
  | writing (head tail : List Bool) (child : BitMemoryBlock.Control)
  deriving DecidableEq, Repr

/-- The unique memory is retained throughout payload construction and actual bit writes. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- Literal child successors and one tape-preserving control handoff. -/
def step : Configuration → Option Configuration
  | ⟨mem, .building base child⟩ =>
      match CellPayloadMachine.step child with
      | some next => some ⟨mem, .building base next⟩
      | none => match child with
          | .done head tail payload => some ⟨mem, .writing head tail (.next base [] payload)⟩
          | _ => none
  | ⟨mem, .writing head tail child⟩ =>
      match BitMemoryBlock.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .writing head tail next.control⟩
      | none => none

/-- Counts of actual successors of the combined controller. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External fuel observer for the literal combined controller. -/
def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Trace composition retains the exact intermediate configuration. -/
theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact fuel returns the same final memory and physical child state. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Payload steps retain the supplied pointer and the entire RAM. -/
theorem lift_payload (mem : Memory) (base : Address) {n : ℕ}
    {s t : CellPayloadMachine.Control} (h : CellPayloadMachine.Trace n s t) :
    Trace n ⟨mem, .building base s⟩ ⟨mem, .building base t⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- Writer steps carry the actual changed RAM while retaining both original words. -/
theorem lift_writer (head tail : List Bool) {n : ℕ}
    {s t : BitMemoryBlock.Configuration} (h : BitMemoryBlock.Trace n s t) :
    Trace n ⟨s.memory, .writing head tail s.control⟩
      ⟨t.memory, .writing head tail t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons next _ ih => exact .cons (by simp only [step, next]) ih

/-- Exact count, including the one actual control handoff between fixed-bank children. -/
def steps (w h : ℕ) : ℕ := 2 * h + 2 * w + 6 + BitMemoryBlock.steps w 0 (1 + h + w)

/-- Payload construction and cell writing belong to this one complete physical execution. -/
theorem write_trace (mem : Memory) (w h : ℕ) (base head tail : List Bool)
    (hb : base.length = w) (hh : head.length = h) (ht : tail.length = w) :
    Trace (steps w h) ⟨mem, .building base (.copyTail head tail [] [])⟩
      ⟨writeCell mem base head tail,
        .writing head tail (.done base (List.replicate (1 + h + w) true))⟩ := by
  have hp := lift_payload mem base (CellPayloadMachine.materialize_trace head tail)
  have hnext : Trace 1
      ⟨mem, .building base (.done head tail (true :: (head ++ tail)))⟩
      ⟨mem, .writing head tail (.next base [] (true :: (head ++ tail)))⟩ :=
    .cons rfl (.nil _)
  have hw := lift_writer head tail
    (SharedListHeapExecution.writeCell_trace mem base head tail (true :: (head ++ tail)) rfl)
  have hlen : (true :: (head ++ tail)).length = 1 + h + w := by simp [hh, ht]; omega
  rw [hb, hlen] at hw
  have he := (hp.append hnext).append hw
  convert he using 1
  simp only [steps, hh, ht]

/-- Exact observed execution allocates a cons and retains every previously represented list. -/
theorem cons_execution {mem : Memory} {w h : ℕ} {base head tail : List Bool}
    {xs : List (List Bool)} (hr : RepList mem w h tail xs) (hf : Fresh mem base)
    (hb : base.length = w) (hh : head.length = h) (hnil : base ≠ nilPointer w) :
    ∃ final : Configuration,
      Trace (steps w h) ⟨mem, .building base (.copyTail head tail [] [])⟩ final ∧
      runFuel (steps w h) ⟨mem, .building base (.copyTail head tail [] [])⟩ = final ∧
      final.control = .writing head tail (.done base (List.replicate (1 + h + w) true)) ∧
      Cell final.memory w h base head tail ∧ RepList final.memory w h base (head :: xs) ∧
      RepList final.memory w h tail xs ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) := by
  have he := write_trace mem w h base head tail hb hh hr.pointer_width
  have ha := SharedListHeap.cons_allocation hr hf hb hh hnil
  refine ⟨_, he, he.runFuel_eq, rfl, ?_, ha.1, ha.2, ?_⟩
  · exact SharedListHeap.writeCell_cell mem w h base head tail hb hh hr.pointer_width hnil
  · intro old ys hold
    exact hold.writeCell hf hb

/-- Both child layouts use permanent physical positions; the writer frames retained words. -/
def physicalTapes : Control → Fin 11 → List Bool
  | .building base child =>
      let ts := CellPayloadMachine.physicalTapes child
      ![base, ts 1, [], ts 3, ts 4, [], [], [], [], ts 0, ts 2]
  | .writing head tail child =>
      let ts := BitMemoryBlock.physicalTapes child
      ![ts 0, ts 1, ts 2, ts 3, ts 4, ts 5, ts 6, ts 7, ts 8, head, tail]

/-- The literal handoff changes no physical tape content. -/
theorem handoff_tapes (base head tail payload : List Bool) :
    physicalTapes (.building base (.done head tail payload)) =
      physicalTapes (.writing head tail (.next base [] payload)) := rfl

private theorem payload_none (child : CellPayloadMachine.Control)
    (h : CellPayloadMachine.step child = none) :
    ∃ head tail payload, child = .done head tail payload := by
  cases child with
  | copyTail head source saved output => cases source <;> simp [CellPayloadMachine.step] at h
  | restoreTail head source tail output => cases source <;> simp [CellPayloadMachine.step] at h
  | copyHead source saved tail output => cases source <;> simp [CellPayloadMachine.step] at h
  | restoreHead source head tail output => cases source <;> simp [CellPayloadMachine.step] at h
  | tag head tail output => simp [CellPayloadMachine.step] at h
  | done head tail payload => exact ⟨head, tail, payload, rfl⟩

private theorem bank_eleven {a b c d e f g h i j k a' b' c' d' e' f' g' h' i' j' k' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k]
      ![a', b', c', d', e', f', g', h', i', j', k'] := by
  intro z
  fin_cases z
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

/-- Every combined successor performs only local actions on the same fixed eleven bit tapes. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | building base child =>
      cases hs : CellPayloadMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := CellPayloadMachine.step_local hs
          exact bank_eleven (.keep _) (hl 1) (.keep _) (hl 3) (hl 4)
            (.keep _) (.keep _) (.keep _) (.keep _) (hl 0) (hl 2)
      | none =>
          obtain ⟨head, tail, payload, rfl⟩ := payload_none child hs
          cases h
          rw [handoff_tapes]
          intro i
          exact .keep _
  | writing head tail child =>
      cases hs : BitMemoryBlock.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := BitMemoryBlock.step_local hs
          exact bank_eleven (hl 0) (hl 1) (hl 2) (hl 3) (hl 4)
            (hl 5) (hl 6) (hl 7) (hl 8) (.keep _) (.keep _)
      | none => simp only [step, hs] at h; contradiction

end Computation.SharedListCellMachine
