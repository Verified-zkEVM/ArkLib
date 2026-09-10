/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryMulRound

/-!
# Same-run multiplication by a physical binary countdown

The proof inducts on the value of the actual canonical countdown tape. Each nonempty counter
executes a complete literal decrement/copy/modular-add round. The cost is linear in the counter
value and physical widths, hence has absolute polynomial degree in the field size.
-/

@[expose] public section

namespace Computation.BinaryMulMachine

open BinaryWordMachine (Word value Canonical)

/-- The actual countdown loop computes its accumulator plus the remaining repeated additions. -/
theorem loop_correct (q count y acc : Word) (hc : Canonical count)
    (hx : value count < value q) (hy : value y < value q)
    (ha : value acc < value q) (hca : Canonical acc) :
    ∃ n ≤ value count * (24 * max q.length y.length + 48) + 1, ∃ out : Word,
      Trace n (.loop q count y acc) (.done q y out) ∧
      value out = (value acc + value count * value y) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  have aux : ∀ k : ℕ, ∀ count acc : Word, value count = k → Canonical count →
      value count < value q → value acc < value q → Canonical acc →
      ∃ n ≤ k * (24 * max q.length y.length + 48) + 1, ∃ out : Word,
        Trace n (.loop q count y acc) (.done q y out) ∧
        value out = (value acc + k * value y) % value q ∧ value out < value q ∧
        Canonical out ∧ out.length ≤ q.length := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro count acc he hc hx ha hca
      cases count with
      | nil =>
        have hk : k = 0 := by simpa [value] using he.symm
        refine ⟨1, by omega, acc, Trace.cons rfl (Trace.nil _), ?_, ha, hca,
          hca.width_le_of_value_lt acc q ha⟩
        simp [hk, Nat.mod_eq_of_lt ha]
      | cons b bs =>
        obtain ⟨nr, hnr, next, sum, hr, hvn, hlt, hcn, hvs, hbs, hcs, _hws⟩ :=
          round_correct q (b :: bs) y acc hc (by simp) hx hy ha hca
        obtain ⟨nt, hnt, out, ht, hvo, hbo, hco, hwo⟩ :=
          ih (value next) (by omega) next sum rfl hcn (by omega) hbs hcs
        have heq : k = value next + 1 := by
          have := hc.value_pos (b :: bs) (by simp)
          omega
        refine ⟨nr + nt, ?_, out, hr.append ht, ?_, hbo, hco, hwo⟩
        · rw [heq, Nat.add_mul, Nat.one_mul]
          omega
        · rw [hvo, hvs, Nat.mod_add_mod, heq, Nat.add_mul, Nat.one_mul]
          congr 1
          omega
  exact aux (value count) count acc rfl hc hx ha hca

/-- Literal modular multiplication with a modulus-only loop budget and preserved operands. -/
theorem multiply_correct (q xs ys : Word) (hc : Canonical xs)
    (hx : value xs < value q) (hy : value ys < value q) :
    ∃ n ≤ value q * (24 * max q.length ys.length + 48) + 2, ∃ out : Word,
      Trace n (.start q xs ys) (.done q ys out) ∧
      runFuel n (.start q xs ys) = .done q ys out ∧
      value out = (value xs * value ys) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  have hq : 0 < value q := by omega
  obtain ⟨n, hn, out, ht, hv, hb, hco, hw⟩ :=
    loop_correct q xs ys [] hc hx hy (by simpa [value] using hq) (Or.inl rfl)
  have h := Trace.cons (s := .start q xs ys) (by rfl) ht
  refine ⟨n + 1, ?_, out, h, h.runFuel_eq, ?_, hb, hco, hw⟩
  · have := Nat.mul_le_mul_right (24 * max q.length ys.length + 48) hx.le
    omega
  · simpa [value] using hv

/-- Fixed input-modulus observation fuel runs the same multiplication and preserves RAM. -/
theorem multiply_runFuel (mem : AddressedBits.Memory) (q xs ys : Word) (hc : Canonical xs)
    (hx : value xs < value q) (hy : value ys < value q) :
    ∃ out : Word,
      ramRunFuel (value q * (24 * max q.length ys.length + 48) + 2) (mem, .start q xs ys) =
        (mem, .done q ys out) ∧
      value out = (value xs * value ys) % value q ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  obtain ⟨n, hn, out, ht, _hr, hv, hb, hco, hw⟩ := multiply_correct q xs ys hc hx hy
  have h := ht.runFuel_done rfl (value q * (24 * max q.length ys.length + 48) + 2 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hb, hco, hw⟩

end Computation.BinaryMulMachine
