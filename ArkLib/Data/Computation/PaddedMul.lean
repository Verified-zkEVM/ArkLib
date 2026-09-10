/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulField
public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Multiplication of fixed-width scalar words

One eleven-tape controller normalizes the first operand by literal addition to zero, runs
the binary-countdown multiplier, and constructs the width tape for physical output padding.
The two handoffs change no tape contents. The modulus and second operand are retained on
their original tapes. Leading-zero operands, including nonempty zero words, are supported.

Inputs are already materialized reduced scalar words. The theorem bounds this explicit
local-bit program, not native Lean execution or a complete decoder compiler.
-/

@[expose] public section

namespace Computation.PaddedMul

open BinaryWordMachine (Word value)

/-- Three fixed child phases; numerical values and widths occur only in proof-side bounds. -/
inductive Control where
  | normalizing (modulus factor : Word) (child : BinaryWordMachine.Configuration)
  | multiplying (child : BinaryMulMachine.Configuration)
  | padding (factor : Word) (child : ScalarWordPadding.Control)
  deriving DecidableEq, Repr

/-- Normalize by actual addition to zero, then multiply and physically pad the actual result. -/
def step : Control → Option Control
  | .normalizing q y child =>
      match BinaryWordMachine.step child with
      | some next => some (.normalizing q y next)
      | none => match child with
          | .word count => some (.multiplying (.start q count y))
          | _ => none
  | .multiplying child =>
      match BinaryMulMachine.step child with
      | some next => some (.multiplying next)
      | none => match child with
          | .done q y word => some (.padding y (.shaping word (.shapeStart q)))
          | _ => none
  | .padding y child => (ScalarWordPadding.step child).map (.padding y)

/-- Eleven fixed slots, with modulus at four and retained multiplicand at eight throughout.
Normalization writes the countdown directly on seven; final padded output is on zero. -/
def tapes : Control → Fin 11 → Word
  | .normalizing q y child =>
      let t := BinaryWordMachine.tapes child
      ![t.left, t.right, t.saved, [], q, [], [], t.output, y, [], []]
  | .multiplying child => BinaryMulMachine.tapes child
  | .padding y child =>
      let t := ScalarWordPadding.tapes child
      ![t 4, t 1, t 2, t 3, t 0, t 5, [], [], y, [], []]

theorem normalize_handoff_tapes (q y count : Word) :
    tapes (.normalizing q y (.word count)) = tapes (.multiplying (.start q count y)) := by
  funext i
  fin_cases i <;> rfl

theorem multiply_handoff_tapes (q y word : Word) :
    tapes (.multiplying (.done q y word)) =
      tapes (.padding y (.shaping word (.shapeStart q))) := by
  funext i
  fin_cases i <;> rfl

private theorem bank_eleven {a b c d e f g h i j k a' b' c' d' e' f' g' h' i' j' k' : Word}
    (ha : BitLocalActions.CellStep a a') (hb : BitLocalActions.CellStep b b')
    (hc : BitLocalActions.CellStep c c') (hd : BitLocalActions.CellStep d d')
    (he : BitLocalActions.CellStep e e') (hf : BitLocalActions.CellStep f f')
    (hg : BitLocalActions.CellStep g g') (hh : BitLocalActions.CellStep h h')
    (hi : BitLocalActions.CellStep i i') (hj : BitLocalActions.CellStep j j')
    (hk : BitLocalActions.CellStep k k') :
    BitLocalActions.BankStep ![a, b, c, d, e, f, g, h, i, j, k]
      ![a', b', c', d', e', f', g', h', i', j', k'] := by
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

private theorem normalize_local (q y : Word) (child : BinaryWordMachine.Configuration)
    {t : Control} (h : step (.normalizing q y child) = some t) :
    BitLocalActions.BankStep (tapes (.normalizing q y child)) (tapes t) := by
      cases hs : BinaryWordMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          have hl := BinaryWordMachine.step_local hs
          exact bank_eleven hl.1 hl.2.1 hl.2.2.1 (.keep _) (.keep _)
            (.keep _) (.keep _) hl.2.2.2 (.keep _) (.keep _) (.keep _)
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [normalize_handoff_tapes]
          intro i
          exact .keep _
private theorem multiply_local (child : BinaryMulMachine.Configuration)
    {t : Control} (h : step (.multiplying child) = some t) :
    BitLocalActions.BankStep (tapes (.multiplying child)) (tapes t) := by
      cases hs : BinaryMulMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact BinaryMulMachine.step_local hs
      | none =>
          simp only [step, hs] at h
          clear hs
          cases child <;> try cases h
          rw [multiply_handoff_tapes]
          intro i
          exact .keep _
private theorem padding_local (y : Word) (child : ScalarWordPadding.Control)
    {t : Control} (h : step (.padding y child) = some t) :
    BitLocalActions.BankStep (tapes (.padding y child)) (tapes t) := by
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      have hl := ScalarWordPadding.step_local hs
      exact bank_eleven (hl 4) (hl 1) (hl 2) (hl 3) (hl 0) (hl 5)
        (.keep _) (.keep _) (.keep _) (.keep _) (.keep _)

/-- All successors act locally on the same physical tape bank, including both handoffs. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | normalizing q y child => exact normalize_local q y child h
  | multiplying child => exact multiply_local child h
  | padding y child => exact padding_local y child h

/-- The actual combined successor count. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External observation of the same controller. -/
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

theorem lift_normalize (q y : Word) {n : ℕ} {s t : BinaryWordMachine.Configuration}
    (h : BinaryWordMachine.Trace n s t) : Trace n (.normalizing q y s) (.normalizing q y t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_multiply {n : ℕ} {s t : BinaryMulMachine.Configuration}
    (h : BinaryMulMachine.Trace n s t) : Trace n (.multiplying s) (.multiplying t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

theorem lift_padding (y : Word) {n : ℕ} {s t : ScalarWordPadding.Control}
    (h : ScalarWordPadding.Trace n s t) : Trace n (.padding y s) (.padding y t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- The same execution normalizes, multiplies and pads. No canonical-input premise or
precomputed width tape is required. The exact modulus and multiplicand words are retained. -/
theorem multiply_correct (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ value q * (24 * max q.length ys.length + 48) +
      2 * xs.length + 4 * q.length + 16, ∃ out : Word,
      Trace n (.normalizing q ys (.startAdd xs [] false))
        (.padding ys (.padding q (.done out))) ∧
      runFuel n (.normalizing q ys (.startAdd xs [] false)) =
        .padding ys (.padding q (.done out)) ∧
      out.length = q.length ∧ value out = (value xs * value ys) % value q ∧
      value out < value q := by
  obtain ⟨nn, hnn, count, hn, _hrn, hvn, hcn, _hwn⟩ :=
    BinaryWordMachine.add_correct xs [] false
  have hvalue : value count = value xs := by
    simpa [value, BinaryWordMachine.bitValue] using hvn
  obtain ⟨nm, hnm, word, hm, _hrm, hvm, hbm, hcm, _hwm⟩ :=
    BinaryMulMachine.multiply_correct q count ys hcn (by simpa [hvalue] using hx) hy
  obtain ⟨out, hp, _hrp, hlen, he, hred⟩ := ScalarWordPadding.padding_reduced q word hcm hbm
  have hh₁ : Trace 1 (.normalizing q ys (.word count)) (.multiplying (.start q count ys)) :=
    .cons rfl (.nil _)
  have hh₂ : Trace 1 (.multiplying (.done q ys word))
      (.padding ys (.shaping word (.shapeStart q))) := .cons rfl (.nil _)
  have hall := ((((lift_normalize q ys hn).append hh₁).append
    (lift_multiply hm)).append hh₂).append (lift_padding ys hp)
  refine ⟨_, ?_, out, hall, hall.runFuel_eq, hlen, ?_, hred⟩
  · simp only [List.length_nil, Nat.max_zero] at hnn
    omega
  · rw [he, hvm, hvalue]

/-- Fixed-width operands produce a fixed-width scalar product with a same-run bound.
The factor polynomial in the modulus has absolute degree, independent of decoder order. -/
theorem multiply_fixed_width (q xs ys : Word)
    (hx : value xs < value q) (hy : value ys < value q)
    (hwx : xs.length = q.length) (hwy : ys.length = q.length) :
    ∃ n ≤ value q * (24 * q.length + 48) + 6 * q.length + 16, ∃ out : Word,
      Trace n (.normalizing q ys (.startAdd xs [] false))
        (.padding ys (.padding q (.done out))) ∧
      runFuel n (.normalizing q ys (.startAdd xs [] false)) =
        .padding ys (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) =
        (value xs : ZMod (value q)) * (value ys : ZMod (value q)) ∧
      value out < value q := by
  obtain ⟨n, hn, out, ht, hr, hlen, hv, hb⟩ := multiply_correct q xs ys hx hy
  refine ⟨n, ?_, out, ht, hr, hlen, ?_, hb⟩
  · simp only [hwx, hwy, max_self] at hn
    omega
  · rw [hv, ZMod.natCast_mod, Nat.cast_mul]

/-- Run the same local program in RAM without changing any memory bit. -/
def ramStep (s : AddressedBits.Memory × Control) : Option (AddressedBits.Memory × Control) :=
  (step s.2).map fun t ↦ (s.1, t)

def ramRunFuel : ℕ → AddressedBits.Memory × Control → AddressedBits.Memory × Control
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

theorem ramRunFuel_eq (mem : AddressedBits.Memory) (n : ℕ) (s : Control) :
    ramRunFuel n (mem, s) = (mem, runFuel n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

theorem Trace.ramRunFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t)
    (mem : AddressedBits.Memory) : ramRunFuel n (mem, s) = (mem, t) := by
  rw [PaddedMul.ramRunFuel_eq, h.runFuel_eq]

end Computation.PaddedMul
