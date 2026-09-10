/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryModAddField
public import ArkLib.Data.Computation.ScalarWordPadding

/-!
# Fixed-width scalar addition on one physical tape bank

The literal modular adder feeds its actual result into reference-width construction and
padding. The modulus is retained throughout. The only handoff changes finite control, not
tape contents; all copying, clearing and padding is charged by the two child programs.

This instruction consumes its two already materialized operands and returns a reduced word
of exactly the modulus's physical width. It is not a complete decoder compiler or a claim
about native Lean execution time.
-/

@[expose] public section

namespace Computation.PaddedModAdd

open BinaryWordMachine (Word value)

/-- Two fixed child phases, with no numerical width or decoded field value in the control. -/
inductive Control where
  | adding (child : BinaryModAddMachine.Configuration)
  | padding (child : ScalarWordPadding.Control)
  deriving DecidableEq, Repr

/-- Actual child successors and one literal, tape-preserving successful handoff. -/
def step : Control → Option Control
  | .adding child =>
      match BinaryModAddMachine.step child with
      | some next => some (.adding next)
      | none => match child with
          | .done modulus word => some (.padding (.shaping word (.shapeStart modulus)))
          | _ => none
  | .padding child => (ScalarWordPadding.step child).map .padding

/-- Addition keeps its seven slots; padding uses the same slots with a fixed wiring map.
The modulus is always on slot four. Addition returns on slot three, padding on slot zero. -/
def tapes : Control → Fin 7 → Word
  | .adding child => BinaryModAddMachine.tapes child
  | .padding child =>
      let t := ScalarWordPadding.tapes child
      ![t 4, t 1, t 2, t 3, t 0, t 5, []]

/-- No word is moved, copied or dropped at the finite-control handoff. -/
theorem handoff_tapes (modulus word : Word) :
    tapes (.adding (.done modulus word)) =
      tapes (.padding (.shaping word (.shapeStart modulus))) := by
  funext i
  fin_cases i <;> rfl

/-- Every instruction transition obeys the same fixed-bank local-bit rule. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s) (tapes t) := by
  cases s with
  | adding child =>
      cases hs : BinaryModAddMachine.step child with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact BinaryModAddMachine.step_local hs
      | none =>
          simp only [step, hs] at h
          cases child <;> try cases h
          rw [handoff_tapes]
          intro i
          exact .keep _
  | padding child =>
      obtain ⟨next, hs, ht⟩ := Option.map_eq_some_iff.mp h
      cases ht
      have hl := ScalarWordPadding.step_local hs
      intro i
      fin_cases i
      · exact hl 4
      · exact hl 1
      · exact hl 2
      · exact hl 3
      · exact hl 0
      · exact hl 5
      · exact .keep _

/-- Counts the actual combined instruction successors. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- External observation of this same literal controller. -/
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

/-- The actual adder trace is lifted without changing its states or cost. -/
theorem lift_add {n : ℕ} {s t : BinaryModAddMachine.Configuration}
    (h : BinaryModAddMachine.Trace n s t) : Trace n (.adding s) (.adding t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The actual padding trace is lifted without re-encoding the intermediate result. -/
theorem lift_padding {n : ℕ} {s t : ScalarWordPadding.Control}
    (h : ScalarWordPadding.Trace n s t) : Trace n (.padding s) (.padding t) := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head, Option.map_some]) ih

/-- One bounded execution performs modular addition and physically returns exactly the
modulus width. Its output and bound concern the same trace and observed run. -/
theorem add_correct (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ 10 * max q.length (max xs.length ys.length) + 4 * q.length + 33,
      ∃ out : Word,
        Trace n (.adding (.start q xs ys)) (.padding (.padding q (.done out))) ∧
        runFuel n (.adding (.start q xs ys)) = .padding (.padding q (.done out)) ∧
        out.length = q.length ∧ value out = (value xs + value ys) % value q ∧
        value out < value q := by
  obtain ⟨n, hn, word, ht, _hr, hv, hb, hc, _hw⟩ :=
    BinaryModAddMachine.add_correct q xs ys hx hy
  obtain ⟨out, hp, _hr, hlen, he, hred⟩ := ScalarWordPadding.padding_reduced q word hc hb
  have hh : Trace 1 (.adding (.done q word))
      (.padding (.shaping word (.shapeStart q))) := .cons rfl (.nil _)
  have hall := ((lift_add ht).append hh).append (lift_padding hp)
  exact ⟨_, by omega, out, hall, hall.runFuel_eq, hlen, he.trans hv, hred⟩

/-- When operands already have the representation width, the whole instruction is linear
in that width, including the internally constructed padding marker. -/
theorem add_fixed_width (q xs ys : Word) (hx : value xs < value q) (hy : value ys < value q)
    (hwx : xs.length = q.length) (hwy : ys.length = q.length) :
    ∃ n ≤ 14 * q.length + 33, ∃ out : Word,
      Trace n (.adding (.start q xs ys)) (.padding (.padding q (.done out))) ∧
      runFuel n (.adding (.start q xs ys)) = .padding (.padding q (.done out)) ∧
      out.length = q.length ∧
      (value out : ZMod (value q)) =
        (value xs : ZMod (value q)) + (value ys : ZMod (value q)) ∧
      value out < value q := by
  obtain ⟨n, hn, out, ht, hr, hlen, hv, hb⟩ := add_correct q xs ys hx hy
  refine ⟨n, ?_, out, ht, hr, hlen, ?_, hb⟩
  · simp only [hwx, hwy, max_self] at hn
    omega
  · rw [hv, ZMod.natCast_mod, Nat.cast_add]

/-- The memory component is literally retained at every instruction successor. -/
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

/-- The same successful instruction trace runs in the unchanged RAM with the same count. -/
theorem Trace.ramRunFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t)
    (mem : AddressedBits.Memory) : ramRunFuel n (mem, s) = (mem, t) := by
  rw [PaddedModAdd.ramRunFuel_eq, h.runFuel_eq]

end Computation.PaddedModAdd
