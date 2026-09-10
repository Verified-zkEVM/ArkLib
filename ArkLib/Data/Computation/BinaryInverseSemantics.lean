/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryInverseRound

/-!
# Same-run bounded inverse search

An inverse candidate bounds the actual incrementing search in the proof only. The target never
appears in runtime state or dispatch. Every candidate below it is multiplied and tested by the
same literal controller; failed candidates are physically incremented and copied for the next run.
-/

@[expose] public section

namespace Computation.BinaryInverseMachine

open BinaryWordMachine (Word value Canonical)
open BinaryNegateMachine (nonzero)

/-- An existing inverse bounds the actual search, without supplying a runtime answer or fuel. -/
theorem search_correct (q x : Word) (target : ℕ) (candidate : Word)
    (hx : value x < value q) (ht : target < value q)
    (hi : (target * value x) % value q = 1) (hc : Canonical candidate)
    (hp : 0 < value candidate) (hle : value candidate ≤ target) :
    ∃ n ≤ (target - value candidate + 1) *
        (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32),
      ∃ out : Word, Trace n (.multiply candidate (.start q candidate x)) (.done q x out) ∧
        (value out * value x) % value q = 1 ∧ 0 < value out ∧ value out ≤ target ∧
        Canonical out ∧ out.length ≤ q.length := by
  let B := value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32
  have aux : ∀ d : ℕ, ∀ candidate : Word, Canonical candidate → 0 < value candidate →
      value candidate ≤ target → target - value candidate = d →
      ∃ n ≤ (d + 1) * B, ∃ out : Word,
        Trace n (.multiply candidate (.start q candidate x)) (.done q x out) ∧
        (value out * value x) % value q = 1 ∧ 0 < value out ∧ value out ≤ target ∧
        Canonical out ∧ out.length ≤ q.length := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro candidate hc hp hle he
      have hlt : value candidate < value q := by omega
      have hwc := hc.width_le_of_value_lt candidate q hlt
      obtain ⟨nm, hnm, product, hm, _hrm, hvp, _hbp, hcp, hwp⟩ :=
        BinaryMulMachine.multiply_correct q candidate x hc hlt hx
      obtain ⟨nc, hnc, hcheck⟩ := check_trace q x candidate product hcp
      have hdispatch : step (.multiply candidate (.done q x product)) =
          some (.checkProduct q x candidate product) := rfl
      have hprefix := (multiply_trace hm candidate).append (Trace.cons hdispatch hcheck)
      by_cases hprod : value product = 1
      · rw [if_pos hprod] at hprefix
        have hfin := hprefix.append (recover_trace q x candidate)
        have hshort : nm + (nc + 1) + (2 * candidate.length + 2) ≤ B := by
          dsimp [B]
          omega
        have hlarge := Nat.mul_le_mul_right B (show 1 ≤ d + 1 by omega)
        simp only [Nat.one_mul] at hlarge
        refine ⟨_, by omega, candidate, hfin, hvp.symm.trans hprod, hp, hle, hc, hwc⟩
      · rw [if_neg hprod] at hprefix
        have hbefore : value candidate < target := by
          by_contra hnot
          have heq : value candidate = target := by omega
          exact hprod (by rw [hvp, heq, hi])
        obtain ⟨ni, hni, next, hincr, hvn, hcn, _hwn⟩ :=
          increment_correct q x candidate hc (by omega)
        have hround := hprefix.append hincr
        have hshort : nm + (nc + 1) + ni ≤ B := by
          dsimp [B]
          omega
        obtain ⟨nt, hnt, out, htail, hio, hpo, hleo, hco, hwo⟩ :=
          ih (target - value next) (by omega) next hcn (by omega) (by omega) rfl
        have hfin := hround.append htail
        refine ⟨_, ?_, out, hfin, hio, hpo, hleo, hco, hwo⟩
        have heq : d + 1 = (target - value next + 1) + 1 := by omega
        rw [heq, Nat.add_mul, Nat.one_mul]
        omega
  exact aux (target - value candidate) candidate hc hp hle rfl

/-- Scan and restore all input bits before returning the inverse of zero. -/
theorem inverse_zero_trace (q x : Word) (hx : value x = 0) :
    Trace (2 * x.length + 3) (.start q x) (.done q x []) := by
  have hz : nonzero x = false := by
    have h := BinaryNegateMachine.nonzero_value x
    cases hn : nonzero x
    · rfl
    · simp [hn, hx] at h
  simpa only [hz, Bool.false_eq_true, if_false] using prepare_trace q x

/-- Nonzero inverse search starts at one and uses a modulus-only, absolute polynomial budget. -/
theorem inverse_given_target (q x : Word) (target : ℕ) (hx : 0 < value x)
    (hr : value x < value q) (htp : 0 < target) (ht : target < value q)
    (hi : (target * value x) % value q = 1) :
    ∃ n ≤ value q *
        (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) +
        2 * x.length + 4, ∃ out : Word,
      Trace n (.start q x) (.done q x out) ∧ runFuel n (.start q x) = .done q x out ∧
      (value out * value x) % value q = 1 ∧ value out < value q ∧
      Canonical out ∧ out.length ≤ q.length := by
  have hz : nonzero x = true := (BinaryNegateMachine.nonzero_value x).mpr hx
  have hp := prepare_trace q x
  simp only [hz, if_true] at hp
  obtain ⟨ns, hns, out, hs, hio, _hpo, hleo, hco, hwo⟩ :=
    search_correct q x target [true] hr ht hi (Or.inr rfl) (by decide)
      (by change 1 ≤ target; omega)
  have hseed : step (.seed q x) = some (.multiply [true] (.start q [true] x)) := rfl
  have hfin := hp.append (Trace.cons hseed hs)
  refine ⟨_, ?_, out, hfin, hfin.runFuel_eq, hio, by omega, hco, hwo⟩
  have he : target - value [true] + 1 = target := by
    change target - 1 + 1 = target
    omega
  rw [he] at hns
  have hm := Nat.mul_le_mul_right
    (value q * (24 * max q.length x.length + 48) + 16 * max q.length x.length + 32) ht.le
  omega

end Computation.BinaryInverseMachine
