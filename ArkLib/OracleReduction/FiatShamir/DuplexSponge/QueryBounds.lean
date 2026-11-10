/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù, Chung Thai Nguyen
-/
module

public import ArkLib.Data.Hash.DuplexSponge
public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Duplex operation and transcript block counts

Exact per-operation query counts and their rate-block bounds, extracted from the
Claim 5.24 accounting for reuse by the Section 7 proof.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
namespace DuplexSpongeFS.QueryBounds
section DuplexQueryCount

open OracleComp

/-- Rate-position walk shared by the lazy duplex `absorb` and `squeeze`: from rate position
`p`, processing `k` units fires a permutation query exactly when `p = R` (resetting the
position to `1` — permute, process one unit at position `0`, advance), else advances. -/
def duplexOpQueryCount (R : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | p, k + 1 =>
      if p = R then 1 + duplexOpQueryCount R 1 k else duplexOpQueryCount R (p + 1) k

@[simp] lemma duplexOpQueryCount_zero (R p : ℕ) : duplexOpQueryCount R p 0 = 0 := rfl

/-- Exact closed form of the lazy-duplex boundary-crossing count: from rate position
`p ≤ R`, processing `k` units makes exactly `(k + p − 1) / R` permutation queries. -/
lemma duplexOpQueryCount_eq_div (R : ℕ) [NeZero R] :
    ∀ (k p : ℕ), p ≤ R → duplexOpQueryCount R p k = (k + p - 1) / R := by
  have hR : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  intro k
  induction k with
  | zero => intro p hp; simp [duplexOpQueryCount, Nat.div_eq_of_lt (show p - 1 < R by omega)]
  | succ k ih =>
    intro p hp
    rw [duplexOpQueryCount]
    split <;> rename_i h
    · subst p
      rw [ih 1 hR]
      rw [show k + 1 + R - 1 = k + R by omega, Nat.add_sub_cancel,
        Nat.add_div_right _ hR, Nat.add_comm]
    · rw [ih (p + 1) (by omega)]
      congr 1; omega

/-- The boundary-crossing count is monotone in the start position and bounded by the fully
padded block count `⌈k/R⌉ = (k + R − 1)/R`, uniformly in `p ≤ R`. -/
lemma duplexOpQueryCount_le_ceilDiv (R : ℕ) [NeZero R] (k p : ℕ) (hp : p ≤ R) :
    duplexOpQueryCount R p k ≤ (k + R - 1) / R := by
  rw [duplexOpQueryCount_eq_div R k p hp]
  exact Nat.div_le_div_right (by omega)

variable {U : Type} [SpongeUnit U] [SpongeSize] {C : Type} [SpongeState U C]

/-- **Exact query count for the lazy `DuplexSponge.absorb`**: absorbing `ls` from rate
position `absorbPos` makes exactly `duplexOpQueryCount R absorbPos ls.length`
permutation queries. -/
lemma isTotalQueryBound_absorb (sponge : DuplexSponge U C) (ls : List U) :
    IsTotalQueryBound (DuplexSponge.absorb sponge ls)
      (duplexOpQueryCount SpongeSize.R (sponge.absorbPos : ℕ) ls.length) := by
  have hRpos : 0 < SpongeSize.R := Nat.pos_of_ne_zero (NeZero.ne SpongeSize.R)
  have hone : 1 % (SpongeSize.R + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  induction ls generalizing sponge with
  | nil => exact trivial
  | cons x xs ih =>
      rw [DuplexSponge.absorb, List.length_cons, duplexOpQueryCount]
      by_cases h : (sponge.absorbPos : ℕ) = SpongeSize.R
      · simp only [h, ite_true]
        exact isTotalQueryBound_query_bind_iff.mpr
          ⟨by omega, fun u => by
            simpa [hone] using ih (sponge := {
              state := SpongeState.modify u (Vector.set · 0 x),
              absorbPos := 1,
              squeezePos := Fin.last SpongeSize.R })⟩
      · simp only [h, ite_false]
        have hlt : sponge.absorbPos < Fin.last SpongeSize.R := by
          rw [Fin.lt_def, Fin.val_last]
          omega
        have hval : ((sponge.absorbPos + 1 : Fin (SpongeSize.R + 1)) : ℕ)
            = (sponge.absorbPos : ℕ) + 1 := Fin.val_add_one_of_lt hlt
        have := ih (sponge := {
          state := SpongeState.modify sponge.state (Vector.set · (sponge.absorbPos : ℕ) x),
          absorbPos := sponge.absorbPos + 1,
          squeezePos := Fin.last SpongeSize.R })
        simpa [hval] using this

/-- **Exact query count for the lazy `DuplexSponge.squeeze`**: squeezing `len` units from
rate position `squeezePos` makes exactly `duplexOpQueryCount R squeezePos len`
permutation queries. -/
lemma isTotalQueryBound_squeeze (sponge : DuplexSponge U C) (len : ℕ) :
    IsTotalQueryBound (DuplexSponge.squeeze sponge len)
      (duplexOpQueryCount SpongeSize.R (sponge.squeezePos : ℕ) len) := by
  have hRpos : 0 < SpongeSize.R := Nat.pos_of_ne_zero (NeZero.ne SpongeSize.R)
  have hone : 1 % (SpongeSize.R + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  induction len generalizing sponge with
  | zero => exact trivial
  | succ n ih =>
      rw [DuplexSponge.squeeze, duplexOpQueryCount]
      by_cases h : (sponge.squeezePos : ℕ) = SpongeSize.R
      · simp only [h, ite_true, pure_bind]
        refine isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun u => ?_⟩
        refine (isTotalQueryBound_bind
          (n₁ := duplexOpQueryCount SpongeSize.R 1 n) (n₂ := 0) ?_
          fun _ => (show IsTotalQueryBound (pure _) 0 from trivial)).mono (by omega)
        simpa [hone] using ih (sponge := {
          state := u, absorbPos := 0, squeezePos := (0 : Fin (SpongeSize.R + 1)) + 1 })
      · simp only [h, ite_false, pure_bind]
        refine (isTotalQueryBound_bind
          (n₁ := duplexOpQueryCount SpongeSize.R ((sponge.squeezePos : ℕ) + 1) n) (n₂ := 0) ?_
          fun _ => (show IsTotalQueryBound (pure _) 0 from trivial)).mono (by omega)
        have hlt : sponge.squeezePos < Fin.last SpongeSize.R := by
          rw [Fin.lt_def, Fin.val_last]
          omega
        have hval : ((sponge.squeezePos + 1 : Fin (SpongeSize.R + 1)) : ℕ)
            = (sponge.squeezePos : ℕ) + 1 := Fin.val_add_one_of_lt hlt
        simpa [hval] using
          ih (sponge := { sponge with absorbPos := 0, squeezePos := sponge.squeezePos + 1 })

end DuplexQueryCount

end DuplexSpongeFS.QueryBounds

/-!
## Internal sponge queries and cursor invariants

Internal prover calls must be included in the Hybrid 0--1 collision analysis. These bounds
count calls made by the executable sponge, independently of the adversary's public-query budget.
They apply to every answer-dependent execution path and do not assume that queried states are
fresh. Block-count bounds account for the executable cursors; the unit-count bounds remain
available as conservative alternatives.
-/

open OracleComp OracleSpec

namespace DuplexSponge

variable {U C : Type} [SpongeUnit U] [SpongeSize] [SpongeState U C]

/-- Absorption preserves an already-armed squeeze cursor. Every branch that consumes a unit
re-arms it, and the empty absorb is a complete no-op, so the property is stable in both cases. -/
theorem absorb_squeezePos_eq_of_mem_support_of_armed (sponge : DuplexSponge U C)
    (units : List U) (harmed : sponge.squeezePos = Fin.last SpongeSize.R)
    {result : DuplexSponge U C} (h : result ∈ support (sponge.absorb units)) :
    result.squeezePos = Fin.last SpongeSize.R := by
  induction units generalizing sponge with
  | nil =>
    simp only [absorb, support_pure, Set.mem_singleton_iff] at h
    subst result
    exact harmed
  | cons x xs ih =>
    simp only [absorb] at h
    split at h
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨state, _, h⟩ := h
      exact ih _ rfl h
    · exact ih _ rfl h

/-- Absorbing a *non-empty* message forces the next positive squeeze to permute first.

Emptiness is essential: under the overwrite-mode duplex an empty absorb is a complete no-op and
does not re-arm the cursor, so this fails for `units = []`. Non-degenerate protocols supply the
side condition, since every prover message is non-empty. -/
theorem absorb_squeezePos_eq_of_mem_support (sponge : DuplexSponge U C) (units : List U)
    (hne : units ≠ []) {result : DuplexSponge U C}
    (h : result ∈ support (sponge.absorb units)) :
    result.squeezePos = Fin.last SpongeSize.R := by
  cases units with
  | nil => exact absurd rfl hne
  | cons x xs =>
    simp only [absorb] at h
    split at h
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨state, _, h⟩ := h
      exact absorb_squeezePos_eq_of_mem_support_of_armed _ xs rfl h
    · exact absorb_squeezePos_eq_of_mem_support_of_armed _ xs rfl h

/-- Initialization arms the squeeze cursor. This is what lets the salt absorb preserve alignment
without assuming the salt is non-empty, so `δ = 0` remains supported. -/
theorem start_squeezePos {α : Type} (a : α) {result : DuplexSponge U C}
    (h : result ∈ support (start (U := U) (C := C) a)) :
    result.squeezePos = Fin.last SpongeSize.R := by
  simp only [start, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨c, _, rfl⟩ := h
  rfl

/-- Absorbing `units` uses at most `⌈units.length / R⌉` permutation calls, from any cursor.
Consecutive absorbs can share a rate block, so this is an upper bound rather than an equality. -/
theorem absorb_isTotalQueryBound_blocks (sponge : DuplexSponge U C) (units : List U) :
    IsTotalQueryBound (sponge.absorb units)
      ((units.length + SpongeSize.R - 1) / SpongeSize.R) := by
  exact (DuplexSpongeFS.QueryBounds.isTotalQueryBound_absorb sponge units).mono
    (DuplexSpongeFS.QueryBounds.duplexOpQueryCount_le_ceilDiv _ _ _ (Fin.is_le _))

/-- Squeezing `len` units uses at most `⌈len / R⌉` permutation calls, from any cursor.
The bound includes a possible initial permutation when the squeeze cursor is armed. -/
theorem squeeze_isTotalQueryBound_blocks (sponge : DuplexSponge U C) (len : ℕ) :
    IsTotalQueryBound (sponge.squeeze len)
      ((len + SpongeSize.R - 1) / SpongeSize.R) := by
  exact (DuplexSpongeFS.QueryBounds.isTotalQueryBound_squeeze sponge len).mono
    (DuplexSpongeFS.QueryBounds.duplexOpQueryCount_le_ceilDiv _ _ _ (Fin.is_le _))

/-- Squeezing makes at most one permutation call per requested output unit. -/
theorem squeeze_isTotalQueryBound (sponge : DuplexSponge U C) (len : ℕ) :
    IsTotalQueryBound (sponge.squeeze len) len := by
  refine (squeeze_isTotalQueryBound_blocks sponge len).mono ?_
  rw [Nat.div_le_iff_le_mul_add_pred SpongeSize.R_pos]
  have h := Nat.le_mul_of_pos_right len SpongeSize.R_pos
  rw [Nat.mul_comm]
  omega

end DuplexSponge
