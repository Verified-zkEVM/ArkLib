/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.BinaryTraceQuotient

/-!
# Agreement counts from binary trace quotients

The normalized binary trace quotient agrees with `x^(q/2 - 1) + s⁻¹/x` on exactly
`q/2` field elements when `s ≠ 0`, using totalized inversion at zero. At `s = 1`,
it agrees with the pure power at `q/2 - 1` nonzero trace-zero points. These are the
counts used by `ReedSolomon.Binary.TraceLine` to treat its prescribed value at zero.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon.Binary

open Polynomial FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [DecidableEq F] in
/-- For a nonzero evaluation point, the quotient agrees with the power-plus-reciprocal word
exactly on a trace-one fiber after the reciprocal coefficient is normalized as `s⁻¹`. -/
lemma binaryTraceQuotient_agreement_iff {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s x : F} (hs : s ≠ 0) (hx : x ≠ 0) :
    (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹ ↔
      binaryTrace m (s ^ 2 * x) = 1 := by
  have hnorm := eval_binaryNormalizedTracePoly (by omega) hcard hs x
  rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X] at hnorm
  constructor
  · intro hagree
    rw [hagree] at hnorm
    have hxpow : x * x ^ (binaryTraceTopDegree m - 1) = x ^ binaryTraceTopDegree m := by
      rw [← pow_succ']
      congr 1
      exact Nat.sub_add_cancel (by
        simp only [binaryTraceTopDegree]
        have hp : 0 < 2 ^ (m - 1) := pow_pos Nat.zero_lt_two _
        omega)
    have hxrecip : x * (s⁻¹ * x⁻¹) = s⁻¹ := by field_simp
    rw [mul_add, hxpow, hxrecip] at hnorm
    have hs_inv : s⁻¹ ≠ 0 := inv_ne_zero hs
    have hcancel : x ^ binaryTraceTopDegree m +
        (x ^ binaryTraceTopDegree m + s⁻¹) = s⁻¹ := by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    exact (mul_left_cancel₀ hs_inv) (by simpa [hnorm] using hcancel)
  · intro htrace
    rw [htrace, mul_one] at hnorm
    have hxpow : x * x ^ (binaryTraceTopDegree m - 1) = x ^ binaryTraceTopDegree m := by
      rw [← pow_succ']
      congr 1
      exact Nat.sub_add_cancel (by
        simp only [binaryTraceTopDegree]
        have hp : 0 < 2 ^ (m - 1) := pow_pos Nat.zero_lt_two _
        omega)
    have hxrecip : x * (s⁻¹ * x⁻¹) = s⁻¹ := by field_simp
    apply (mul_left_cancel₀ hx)
    rw [mul_add, hxpow, hxrecip]
    calc
      x * (binaryTraceQuotient m s).eval x =
          (x ^ binaryTraceTopDegree m + x ^ binaryTraceTopDegree m) +
            x * (binaryTraceQuotient m s).eval x := by
              rw [CharTwo.add_self_eq_zero, zero_add]
      _ = x ^ binaryTraceTopDegree m +
          (x ^ binaryTraceTopDegree m + x * (binaryTraceQuotient m s).eval x) := by
            rw [add_assoc]
      _ = x ^ binaryTraceTopDegree m + s⁻¹ := by rw [hnorm]

/-- Exactly half the field agrees with the power-plus-reciprocal word; zero is not an agreement. -/
lemma binaryTraceQuotient_agreement_card {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s : F} (hs : s ≠ 0) :
    (Finset.univ.filter fun x : F ↦
      (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹).card =
      Fintype.card F / 2 := by
  classical
  -- Totalized inversion is zero at the origin, while the quotient has constant term s.
  have hzero_not_agree :
      ¬(binaryTraceQuotient m s).eval 0 =
        (0 : F) ^ (binaryTraceTopDegree m - 1) + s⁻¹ * (0 : F)⁻¹ := by
    rw [eval_binaryTraceQuotient_zero (by omega) s]
    simp only [inv_zero, mul_zero, add_zero]
    rw [zero_pow (by
      simp [binaryTraceTopDegree]
      have : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      norm_num at this
      omega)]
    exact hs
  --
  -- Multiplication by s² permutes the field and preserves the trace-fiber count.
  have himage : Function.Bijective (fun x : F ↦ s ^ 2 * x) := by
    exact (Equiv.mulLeft₀ (s ^ 2) (pow_ne_zero 2 hs)).bijective
  let traceSet := Finset.univ.filter fun y : F ↦ binaryTrace m y = 1
  have hcard_trace : traceSet.card = Fintype.card F / 2 := by
    simpa [traceSet, binaryTraceFiber] using binaryTraceFiber_one_card (F := F) (by omega) hcard
  calc
    (Finset.univ.filter fun x : F ↦
      (binaryTraceQuotient m s).eval x =
        x ^ (binaryTraceTopDegree m - 1) + s⁻¹ * x⁻¹).card
        = (Finset.univ.filter fun x : F ↦ binaryTrace m (s ^ 2 * x) = 1).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hx : x = 0
          · subst x
            exact iff_of_false hzero_not_agree (by simp)
          · exact binaryTraceQuotient_agreement_iff hm hcard hs hx
    _ = traceSet.card := by
      apply Finset.card_bij (fun x _ ↦ s ^ 2 * x)
      · intro x hx
        simpa [traceSet] using hx
      · intro x₁ _ x₂ _ h
        exact himage.1 h
      · intro y hy
        obtain ⟨x, rfl⟩ := himage.2 y
        refine ⟨x, ?_, rfl⟩
        simpa [traceSet] using hy
    _ = Fintype.card F / 2 := hcard_trace

/-- At `s = 1`, the quotient agrees with the pure power at the nonzero trace-zero points. -/
lemma binaryTraceQuotient_one_nonzero_agreement_card {m : ℕ} (hm : 3 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    (Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x =
        x ^ (binaryTraceTopDegree m - 1)).card =
      Fintype.card F / 2 - 1 := by
  classical
  let traceSet := Finset.univ.filter fun x : F ↦ binaryTrace m x = 0
  have hcard_trace : traceSet.card = Fintype.card F / 2 := by
    simpa [traceSet, binaryTraceFiber] using binaryTraceFiber_zero_card (F := F) (by omega) hcard
  have hzero_trace : (0 : F) ∈ traceSet := by simp [traceSet]
  calc
    (Finset.univ.filter fun x : F ↦ x ≠ 0 ∧
      (binaryTraceQuotient m 1).eval x =
        x ^ (binaryTraceTopDegree m - 1)).card
        = (traceSet.erase 0).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            traceSet]
          constructor
          · rintro ⟨hx, hagree⟩
            refine ⟨hx, ?_⟩
            have hnorm := eval_binaryNormalizedTracePoly (by omega) hcard one_ne_zero x
            rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X,
              hagree] at hnorm
            have hxpow : x * x ^ (binaryTraceTopDegree m - 1) =
                x ^ binaryTraceTopDegree m := by
              rw [← pow_succ']
              congr 1
              exact Nat.sub_add_cancel (by
                simp only [binaryTraceTopDegree]
                have hp : 0 < 2 ^ (m - 1) := pow_pos Nat.zero_lt_two _
                omega)
            rw [hxpow] at hnorm
            have hz : 0 = binaryTrace m x := by
              simpa only [one_pow, one_mul, inv_one, ← add_assoc,
                CharTwo.add_self_eq_zero, zero_add] using hnorm
            exact hz.symm
          · rintro ⟨hx, htrace⟩
            refine ⟨hx, ?_⟩
            have hnorm := eval_binaryNormalizedTracePoly (by omega) hcard one_ne_zero x
            rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X] at hnorm
            simp only [one_pow, one_mul, inv_one] at hnorm
            rw [htrace] at hnorm
            apply (mul_left_cancel₀ hx)
            have hxpow : x * x ^ (binaryTraceTopDegree m - 1) =
                x ^ binaryTraceTopDegree m := by
              rw [← pow_succ']
              congr 1
              exact Nat.sub_add_cancel (by
                simp only [binaryTraceTopDegree]
                have hp : 0 < 2 ^ (m - 1) := pow_pos Nat.zero_lt_two _
                omega)
            rw [hxpow]
            calc
              x * (binaryTraceQuotient m 1).eval x =
                  (x ^ binaryTraceTopDegree m + x ^ binaryTraceTopDegree m) +
                    x * (binaryTraceQuotient m 1).eval x := by
                      rw [CharTwo.add_self_eq_zero, zero_add]
              _ = x ^ binaryTraceTopDegree m +
                  (x ^ binaryTraceTopDegree m + x * (binaryTraceQuotient m 1).eval x) := by
                    rw [add_assoc]
              _ = x ^ binaryTraceTopDegree m := by rw [hnorm, add_zero]
    _ = traceSet.card - 1 := Finset.card_erase_of_mem hzero_trace
    _ = Fintype.card F / 2 - 1 := by rw [hcard_trace]


end ReedSolomon.Binary
