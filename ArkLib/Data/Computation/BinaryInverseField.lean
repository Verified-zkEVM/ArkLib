/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryInverseSemantics
public import Mathlib.Algebra.Field.ZMod

/-!
# Literal inverse search refines prime-field inversion

Prime-field inverse existence supplies a proof-side search bound. It supplies no runtime word,
answer, or fuel. The actual thirteen-tape program includes the zero case, and its same execution
witness computes the `ZMod` inverse with an absolute quadratic field-size overhead.
-/

@[expose] public section

namespace Computation.BinaryInverseMachine

open BinaryWordMachine (Word value Canonical)

/-- A nonzero reduced prime-field scalar has an inverse candidate strictly below the modulus. -/
theorem inverse_target (q x : Word) (hp : Nat.Prime (value q))
    (hx : value x < value q) (hn : 0 < value x) :
    ∃ target : ℕ, 0 < target ∧ target < value q ∧ (target * value x) % value q = 1 := by
  let : Fact (Nat.Prime (value q)) := ⟨hp⟩
  let : NeZero (value q) := ⟨hp.ne_zero⟩
  let : Fact (1 < value q) := ⟨hp.one_lt⟩
  let a : ZMod (value q) := value x
  have ha : a ≠ 0 := by
    intro hzero
    have hz := (ZMod.val_eq_zero a).mpr hzero
    have hv : a.val = value x := ZMod.val_natCast_of_lt hx
    omega
  refine ⟨(a⁻¹).val, ?_, ZMod.val_lt _, ?_⟩
  · have hz : (a⁻¹).val ≠ 0 := by
      intro hzero
      exact inv_ne_zero ha ((ZMod.val_eq_zero _).mp hzero)
    omega
  · have hprod : (((a⁻¹).val * value x : ℕ) : ZMod (value q)) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      exact inv_mul_cancel₀ ha
    have hv := congrArg ZMod.val hprod
    simpa only [ZMod.val_natCast, ZMod.val_one] using hv

/-- The same literal search computes the prime-field inverse, including zero and padded input. -/
theorem inverse_zmod (q x : Word) (hp : Nat.Prime (value q)) (hx : value x < value q) :
    ∃ n ≤ value q *
        (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) +
        2 * x.length + 4, ∃ out : Word,
      Trace n (.start q x) (.done q x out) ∧ runFuel n (.start q x) = .done q x out ∧
      (value out : ZMod (value q)) = (value x : ZMod (value q))⁻¹ ∧
      value out < value q ∧ Canonical out ∧ out.length ≤ q.length := by
  let : Fact (Nat.Prime (value q)) := ⟨hp⟩
  by_cases hz : value x = 0
  · have ht := inverse_zero_trace q x hz
    refine ⟨_, by omega, [], ht, ht.runFuel_eq, ?_, ?_, Or.inl rfl, by simp⟩
    · simp [value, hz]
    · simpa [value] using hp.pos
  · obtain ⟨target, htp, htq, hi⟩ := inverse_target q x hp hx (by omega)
    obtain ⟨n, hn, out, ht, hr, hio, hb, hc, hw⟩ :=
      inverse_given_target q x target (by omega) hx htp htq hi
    have hmul := congrArg (fun n : ℕ ↦ (n : ZMod (value q))) hio
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at hmul
    exact ⟨n, hn, out, ht, hr, eq_inv_of_mul_eq_one_left hmul, hb, hc, hw⟩

/-- A modulus-and-width-only observation budget returns the same inverse and unchanged RAM. -/
theorem inverse_runFuel (mem : AddressedBits.Memory) (q x : Word)
    (hp : Nat.Prime (value q)) (hx : value x < value q) :
    ∃ out : Word,
      ramRunFuel (value q *
        (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) +
        2 * x.length + 4) (mem, .start q x) = (mem, .done q x out) ∧
      (value out : ZMod (value q)) = (value x : ZMod (value q))⁻¹ ∧
      value out < value q ∧ Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨n, hn, out, ht, _hr, hv, hb, hc, hw⟩ := inverse_zmod q x hp hx
  have h := ht.runFuel_done rfl (value q *
    (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) +
    2 * x.length + 4 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hb, hc, hw⟩

end Computation.BinaryInverseMachine
