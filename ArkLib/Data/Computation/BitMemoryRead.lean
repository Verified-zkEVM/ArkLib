/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitMemoryBlock

/-!
# Bit-by-bit reads from prefix-addressed memory blocks

The caller supplies a binary block pointer and a materialized length tape: one cell for
each requested bit. The values on the length tape are ignored. Pointer and within-word index
copying/restoration, address access/reset, and output reversal all use literal bit transitions.
No transition decodes a length or loads an entire word. The starting length tape and pointer
must be constructed by the caller; this module does not charge their construction for free.
-/

@[expose] public section

namespace Computation.BitMemoryRead

open AddressedBits (Memory Address)
open BitMemoryBlock (slot)

/-- Fixed phases and physical bit tapes of the read controller. -/
inductive Control where
  | next (base index remaining savedOutput : List Bool)
  | copyBase (index remaining source saved bus savedOutput : List Bool)
  | restoreBase (index remaining source base bus savedOutput : List Bool)
  | copyIndex (base remaining source saved bus savedOutput : List Bool)
  | restoreIndex (base remaining source index bus savedOutput : List Bool)
  | reading (base index remaining savedOutput : List Bool) (child : AddressedBits.Control)
  | reverse (base index source output : List Bool)
  | done (base index output : List Bool)
  | failed (base index remaining savedOutput : List Bool) (child : AddressedBits.Control)
  deriving DecidableEq, Repr

/-- The parent and its retained access child share one actual memory. -/
structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- A single fixed local-bit action, or an actual addressed-bit controller successor. -/
def step : Configuration → Option Configuration
  | ⟨mem, .next base index [] out⟩ => some ⟨mem, .reverse base index out []⟩
  | ⟨mem, .next base index (_ :: bs) out⟩ =>
      some ⟨mem, .copyBase index bs base [] [true] out⟩
  | ⟨mem, .copyBase index bs (x :: xs) saved bus out⟩ =>
      some ⟨mem, .copyBase index bs xs (x :: saved) (x :: bus) out⟩
  | ⟨mem, .copyBase index bs [] saved bus out⟩ =>
      some ⟨mem, .restoreBase index bs saved [] bus out⟩
  | ⟨mem, .restoreBase index bs (x :: xs) base bus out⟩ =>
      some ⟨mem, .restoreBase index bs xs (x :: base) bus out⟩
  | ⟨mem, .restoreBase index bs [] base bus out⟩ =>
      some ⟨mem, .copyIndex base bs index [] bus out⟩
  | ⟨mem, .copyIndex base bs (x :: xs) saved bus out⟩ =>
      some ⟨mem, .copyIndex base bs xs (x :: saved) (x :: bus) out⟩
  | ⟨mem, .copyIndex base bs [] saved bus out⟩ =>
      some ⟨mem, .restoreIndex base bs saved [] (false :: bus) out⟩
  | ⟨mem, .restoreIndex base bs (x :: xs) index bus out⟩ =>
      some ⟨mem, .restoreIndex base bs xs (x :: index) bus out⟩
  | ⟨mem, .restoreIndex base bs [] index bus out⟩ =>
      some ⟨mem, .reading base index bs out (.restore .read bus [])⟩
  | ⟨mem, .reading base index bs out child⟩ =>
      match AddressedBits.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .reading base index bs out next.control⟩
      | none => match child with
          | .done (some b) => some ⟨mem, .next base (true :: index) bs (b :: out)⟩
          | _ => some ⟨mem, .failed base index bs out child⟩
  | ⟨mem, .reverse base index (b :: bs) out⟩ =>
      some ⟨mem, .reverse base index bs (b :: out)⟩
  | ⟨mem, .reverse base index [] out⟩ => some ⟨mem, .done base index out⟩
  | ⟨_, .done _ _ _⟩ | ⟨_, .failed _ _ _ _ _⟩ => none

/-- The counted successors are those of this same concrete read controller. -/
inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- Fuel is an external observer, not an unbounded numeric register in the controller. -/
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

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) :
    runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- The retained child executes on the exact memory of the enclosing read program. -/
theorem lift_access (base index remaining out : List Bool) {n : ℕ}
    {s t : AddressedBits.Configuration} (h : AddressedBits.Trace n s t) :
    Trace n ⟨s.memory, .reading base index remaining out s.control⟩
      ⟨t.memory, .reading base index remaining out t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem restoreIndex_trace (mem : Memory)
    (base remaining source index bus out : List Bool) :
    Trace (source.length + 1) ⟨mem, .restoreIndex base remaining source index bus out⟩
      ⟨mem, .reading base (source.reverse ++ index) remaining out (.restore .read bus [])⟩ := by
  induction source generalizing index with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: index))

theorem copyIndex_trace (mem : Memory)
    (base remaining source saved bus out : List Bool) :
    Trace (source.length + 1) ⟨mem, .copyIndex base remaining source saved bus out⟩
      ⟨mem, .restoreIndex base remaining (source.reverse ++ saved) []
        (false :: (source.reverse ++ bus)) out⟩ := by
  induction source generalizing saved bus with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: saved) (x :: bus))

theorem restoreBase_trace (mem : Memory)
    (index remaining source base bus out : List Bool) :
    Trace (source.length + 1) ⟨mem, .restoreBase index remaining source base bus out⟩
      ⟨mem, .copyIndex (source.reverse ++ base) remaining index [] bus out⟩ := by
  induction source generalizing base with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: base))

theorem copyBase_trace (mem : Memory)
    (index remaining source saved bus out : List Bool) :
    Trace (source.length + 1) ⟨mem, .copyBase index remaining source saved bus out⟩
      ⟨mem, .restoreBase index remaining (source.reverse ++ saved) []
        (source.reverse ++ bus) out⟩ := by
  induction source generalizing saved bus with
  | nil => exact .cons rfl (.nil _)
  | cons x xs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (x :: saved) (x :: bus))

/-- One actual read retains the memory and pushes exactly the observed bit onto the output tape. -/
theorem read_bit_trace (mem : Memory) (base index remaining out : List Bool) (marker : Bool) :
    Trace (4 * base.length + 4 * index.length + 13)
      ⟨mem, .next base index (marker :: remaining) out⟩
      ⟨mem, .next base (true :: index) remaining (mem.lookup (slot base index) :: out)⟩ := by
  let bus := false :: (index.reverse ++ (base.reverse ++ [true]))
  have hb : bus.reverse = true :: slot base index := by
    simp [bus, slot, List.reverse_append, List.append_assoc]
  have hc := copyBase_trace mem index remaining base [] [true] out
  have hr := restoreBase_trace mem index remaining base.reverse [] (base.reverse ++ [true]) out
  have hi := copyIndex_trace mem base remaining index [] (base.reverse ++ [true]) out
  have hj := restoreIndex_trace mem base remaining index.reverse [] bus out
  simp only [List.append_nil] at hc hi
  simp only [List.reverse_reverse, List.append_nil] at hr hj
  have hrestore := AddressedBits.restore_trace mem .read bus []
  rw [hb, List.append_nil] at hrestore
  have haccess := AddressedBits.access_trace mem .read (slot base index)
  simp only [AddressedBits.effect] at haccess
  have hfinish : Trace 1
      ⟨mem, .reading base index remaining out (.done (some (mem.lookup (slot base index))))⟩
      ⟨mem, .next base (true :: index) remaining (mem.lookup (slot base index) :: out)⟩ :=
    .cons rfl (.nil _)
  have h := Trace.cons (show step ⟨mem, .next base index (marker :: remaining) out⟩ = _ from rfl)
    (((((hc.append hr).append hi).append hj).append
      (lift_access base index remaining out (hrestore.append haccess))).append hfinish)
  convert h using 1
  simp only [bus, slot, List.length_cons, List.length_append, List.length_reverse,
    List.length_nil]
  omega

/-- Semantic block contents; this specification is not used by the successor function. -/
def load (mem : Memory) (base : Address) : List Bool → List Bool → List Bool
  | _, [] => []
  | index, _ :: rest => mem.lookup (slot base index) :: load mem base (true :: index) rest

theorem load_length (mem : Memory) (base index shape : List Bool) :
    (load mem base index shape).length = shape.length := by
  induction shape generalizing index with
  | nil => rfl
  | cons _ _ ih => simpa [load] using congrArg Nat.succ (ih (true :: index))

/-- Each returned position reads the corresponding physical block slot. -/
theorem load_getElem (mem : Memory) (base index shape : List Bool) (i : ℕ)
    (hi : i < shape.length) :
    (load mem base index shape)[i]'(by rw [load_length]; exact hi) =
      mem.lookup (slot base (List.replicate i true ++ index)) := by
  induction shape generalizing index i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < bs.length := by simpa using hi
          simpa only [load, List.getElem_cons_succ, List.replicate_add,
            List.replicate_one, List.singleton_append, List.append_assoc] using
            ih (true :: index) i hi'

/-- Reading precisely the supplied word width after its semantic store recovers all bits. -/
theorem load_store (mem : Memory) (base index bits shape : List Bool)
    (hlen : shape.length = bits.length) :
    load (BitMemoryBlock.store mem base index bits) base index shape = bits := by
  apply List.ext_getElem
  · simpa only [load_length] using hlen
  · intro i hi hi'
    rw [load_getElem _ _ _ _ i (by rw [load_length] at hi; exact hi)]
    exact BitMemoryBlock.store_lookup mem base index bits i hi'

/-- The full read scan includes all addressed accesses and its handoff to output reversal. -/
theorem scan_trace (mem : Memory) (base index shape out : List Bool) :
    Trace (BitMemoryBlock.steps base.length index.length shape.length)
      ⟨mem, .next base index shape out⟩
      ⟨mem, .reverse base (List.replicate shape.length true ++ index)
        ((load mem base index shape).reverse ++ out) []⟩ := by
  induction shape generalizing index out with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      have h := (read_bit_trace mem base index bs out b).append
        (ih (true :: index) (mem.lookup (slot base index) :: out))
      convert h using 1
      · simp only [List.length_cons, BitMemoryBlock.steps]
        ring
      · simp only [load, List.reverse_cons, List.append_assoc, List.length_cons,
          List.singleton_append]
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]

/-- Output reversal explicitly transfers each bit to the final output tape. -/
theorem reverse_trace (mem : Memory) (base index source out : List Bool) :
    Trace (source.length + 1) ⟨mem, .reverse base index source out⟩
      ⟨mem, .done base index (source.reverse ++ out)⟩ := by
  induction source generalizing out with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: out))

/-- Exact count, including address bus reset and the final physical output reversal. -/
def steps (B I L : ℕ) : ℕ := 2 * L ^ 2 + (4 * B + 4 * I + 12) * L + 2

/-- The complete run returns all requested bits in order and retains the entire memory. -/
theorem load_trace (mem : Memory) (base index shape : List Bool) :
    Trace (steps base.length index.length shape.length) ⟨mem, .next base index shape []⟩
      ⟨mem, .done base (List.replicate shape.length true ++ index)
        (load mem base index shape)⟩ := by
  have hs := scan_trace mem base index shape []
  simp only [List.append_nil] at hs
  have hr := reverse_trace mem base (List.replicate shape.length true ++ index)
    (load mem base index shape).reverse []
  simp only [List.reverse_reverse, List.append_nil] at hr
  convert hs.append hr using 1
  simp only [steps, BitMemoryBlock.steps, List.length_reverse, load_length]
  ring

theorem load_runFuel (mem : Memory) (base index shape : List Bool) :
    runFuel (steps base.length index.length shape.length) ⟨mem, .next base index shape []⟩ =
      ⟨mem, .done base (List.replicate shape.length true ++ index) (load mem base index shape)⟩ :=
  (load_trace mem base index shape).runFuel_eq

/-- Eleven physical tapes; the reversed output stays on tape 9 until it is transferred to 10. -/
def physicalTapes : Control → Fin 11 → List Bool
  | .next base index remaining out => ![base, [], index, [], remaining, [], [], [], [], out, []]
  | .copyBase index remaining source saved bus out =>
      ![source, saved, index, [], remaining, bus, [], [], [], out, []]
  | .restoreBase index remaining source base bus out =>
      ![base, source, index, [], remaining, bus, [], [], [], out, []]
  | .copyIndex base remaining source saved bus out =>
      ![base, [], source, saved, remaining, bus, [], [], [], out, []]
  | .restoreIndex base remaining source index bus out =>
      ![base, [], index, source, remaining, bus, [], [], [], out, []]
  | .reading base index remaining out child | .failed base index remaining out child =>
      let tapes := BitLocalActions.addressTapes child
      ![base, [], index, [], remaining, tapes.right, tapes.left, tapes.saved, tapes.output, out, []]
  | .reverse base index source out => ![base, [], index, [], [], [], [], [], [], source, out]
  | .done base index out => ![base, [], index, [], [], [], [], [], [], [], out]

private theorem bank_eleven
    {a b c d e f g h i j k a' b' c' d' e' f' g' h' i' j' k' : List Bool}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k]
      ![a', b', c', d', e', f', g', h', i', j', k'] := by
  intro l
  fin_cases l
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

private theorem access_none (mem : Memory) (child : AddressedBits.Control)
    (h : AddressedBits.step ⟨mem, child⟩ = none) : ∃ result, child = .done result := by
  cases child with
  | start => simp [AddressedBits.step] at h
  | transfer op remaining bus => cases remaining <;> simp [AddressedBits.step] at h
  | restore op remaining bus => cases remaining <;> simp [AddressedBits.step] at h
  | access op bus =>
      cases op <;> cases bus with
      | nil => simp [AddressedBits.step] at h
      | cons b bs => cases b <;> simp [AddressedBits.step] at h
  | reset result bus => cases bus <;> simp [AddressedBits.step] at h
  | done result => exact ⟨result, rfl⟩

/-- The fixed physical-bank invariant holds for every literal successor, including failures. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (physicalTapes s.control) (physicalTapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | next base index remaining out =>
      cases remaining <;> cases h <;> apply bank_eleven <;> constructor
  | copyBase index remaining source saved bus out =>
      cases source <;> cases h <;> apply bank_eleven <;> constructor
  | restoreBase index remaining source base bus out =>
      cases source <;> cases h <;> apply bank_eleven <;> constructor
  | copyIndex base remaining source saved bus out =>
      cases source <;> cases h <;> apply bank_eleven <;> constructor
  | restoreIndex base remaining source index bus out =>
      cases source <;> cases h <;> apply bank_eleven <;> constructor
  | reading base index remaining out child =>
      cases hs : AddressedBits.step ⟨mem, child⟩ with
      | some u =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := BitLocalActions.address_step hs
          exact bank_eleven (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)
            hl.2.1 hl.1 hl.2.2.1 hl.2.2.2 (.keep _) (.keep _)
      | none =>
          obtain ⟨result, rfl⟩ := access_none mem child hs
          cases result <;> cases h <;> apply bank_eleven <;> constructor
  | reverse base index source out =>
      cases source <;> cases h <;> apply bank_eleven <;> constructor
  | done base index out => cases h
  | failed base index remaining out child => cases h

end Computation.BitMemoryRead
