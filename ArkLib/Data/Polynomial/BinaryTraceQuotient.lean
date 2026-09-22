/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FieldTheory.BinaryTrace

/-!
# Low-degree quotients of normalized binary trace polynomials

For a binary field of size `q = 2^m` with `m ≥ 3`, this module constructs an explicit polynomial
`binaryTraceQuotient m s` of degree strictly below `q / 4`. Its constant term is `s`.
For `s ≠ 0`, adjoining the leading monomial and multiplying the quotient by `X` gives a monic
polynomial whose value at `x` is `s⁻¹ * binaryTrace m (s² * x)`.

## Which theorem should I use?

* `natDegree_binaryTraceQuotient_lt` gives the strict quarter-field bound.
* `eval_binaryNormalizedTracePoly` connects the explicit sum to the absolute trace.

The sum stops before the leading trace monomial. Removing the remaining factor of `X` makes its
largest possible exponent `q/4 - 1`, which is why the bound is strict. The normalized polynomial
is defined without division by `X`, so its value at zero remains available explicitly. Callers
that prescribe a different value at the reciprocal pole must account for that coordinate
separately; `ReedSolomon.Binary.TraceLine` does so.

The coding-theoretic agreement counts live in `ReedSolomon.Binary.TraceAgreement`.
-/

@[expose] public section

open scoped BigOperators

open FiniteField

namespace Polynomial

section Definitions

/-- The leading exponent in an `m`-term binary trace. -/
def binaryTraceTopDegree (m : ℕ) : ℕ := 2 ^ (m - 1)

/-- The quarter-field degree threshold used by the quotient polynomial. -/
def binaryTraceQuarterDegree (m : ℕ) : ℕ := 2 ^ (m - 2)

/-- The explicit quotient obtained after the leading trace monomial cancels and `X` is removed. -/
noncomputable def binaryTraceQuotient {F : Type*} [Semiring F] (m : ℕ) (s : F) : F[X] :=
  ∑ i ∈ Finset.range (m - 1),
    C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)

/-- A normalized trace polynomial with leading coefficient one. -/
noncomputable def binaryNormalizedTracePoly {F : Type*} [Semiring F]
    (m : ℕ) (s : F) : F[X] :=
  X ^ binaryTraceTopDegree m + X * binaryTraceQuotient m s

end Definitions

section Field

variable {F : Type*} [Field F]

/-- Every quotient has degree strictly below the quarter-field threshold, including at `s = 0`. -/
lemma natDegree_binaryTraceQuotient_lt {m : ℕ} (hm : 3 ≤ m) (s : F) :
    (binaryTraceQuotient m s).natDegree < binaryTraceQuarterDegree m := by
  classical
  apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le (Finset.range (m - 1)) _ ?_)
  · simp only [binaryTraceQuarterDegree]
    apply Nat.sub_lt_self Nat.one_pos
    have hp : 0 < 2 ^ (m - 2) := pow_pos Nat.zero_lt_two _
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    calc
      (C (s ^ (2 ^ (i + 1) - 1)) * X ^ (2 ^ i - 1)).natDegree
          ≤ (C (s ^ (2 ^ (i + 1) - 1))).natDegree +
            (X ^ (2 ^ i - 1) : F[X]).natDegree := natDegree_mul_le
      _ ≤ 2 ^ i - 1 := by simp
      _ ≤ 2 ^ (m - 2) - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) (by omega)) 1

/-- The constant term is the parameter `s`; it must be accounted for at the reciprocal pole. -/
lemma eval_binaryTraceQuotient_zero {m : ℕ} (hm : 2 ≤ m) (s : F) :
    (binaryTraceQuotient m s).eval 0 = s := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, m - 1 = n + 1 := by
    exact ⟨m - 2, by omega⟩
  rw [binaryTraceQuotient, hn, eval_finsetSum, Finset.sum_range_succ']
  simp only [eval_mul, eval_C, eval_X_pow]
  have hzero : ∀ i ∈ Finset.range n,
      s ^ (2 ^ (i + 1 + 1) - 1) * 0 ^ (2 ^ (i + 1) - 1) = 0 := by
    intro i hi
    rw [zero_pow (Nat.sub_ne_zero_of_lt (by
      exact one_lt_pow₀ (by omega) (by omega))), mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add]
  norm_num

/-- The normalized trace polynomial vanishes at the origin, for every truncation length. -/
lemma eval_binaryNormalizedTracePoly_zero (m : ℕ) (s : F) :
    (binaryNormalizedTracePoly m s).eval 0 = 0 := by
  simp [binaryNormalizedTracePoly, binaryTraceTopDegree,
    zero_pow (pow_ne_zero _ (by omega : (2 : ℕ) ≠ 0))]

/-- The lower quotient terms do not disturb the normalized leading coefficient. -/
lemma monic_binaryNormalizedTracePoly {m : ℕ} (hm : 3 ≤ m) (s : F) :
    (binaryNormalizedTracePoly m s).Monic := by
  rw [binaryNormalizedTracePoly]
  apply monic_X_pow_add
  by_cases hq : binaryTraceQuotient m s = 0
  · simp only [hq, mul_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  rw [← natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero hq), natDegree_X_mul hq]
  have hqdeg := natDegree_binaryTraceQuotient_lt hm s
  simp only [binaryTraceTopDegree, binaryTraceQuarterDegree] at hqdeg ⊢
  have hquarter : 2 ^ (m - 2) + 1 ≤ 2 ^ (m - 1) := by
    have hm2 : 1 ≤ m - 2 := by omega
    calc
      2 ^ (m - 2) + 1 ≤ 2 ^ (m - 2) + 2 ^ (m - 2) := by omega
      _ = 2 ^ (m - 1) := by
        rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
        omega
  omega

/-- The normalized polynomial has the half-field degree threshold. -/
lemma natDegree_binaryNormalizedTracePoly {m : ℕ} (hm : 3 ≤ m) (s : F) :
    (binaryNormalizedTracePoly m s).natDegree = binaryTraceTopDegree m := by
  rw [binaryNormalizedTracePoly]
  calc
    (X ^ binaryTraceTopDegree m + X * binaryTraceQuotient m s).natDegree =
        (X ^ binaryTraceTopDegree m : F[X]).natDegree := by
      apply natDegree_add_eq_left_of_natDegree_lt
      by_cases hq : binaryTraceQuotient m s = 0
      · simp [hq, binaryTraceTopDegree]
      rw [natDegree_X_mul hq, natDegree_X_pow]
      have hqdeg := natDegree_binaryTraceQuotient_lt hm s
      simp only [binaryTraceTopDegree, binaryTraceQuarterDegree] at hqdeg ⊢
      have hquarter : 2 ^ (m - 2) + 1 ≤ 2 ^ (m - 1) := by
        calc
          2 ^ (m - 2) + 1 ≤ 2 ^ (m - 2) + 2 ^ (m - 2) := by
            have hp : 0 < 2 ^ (m - 2) := pow_pos Nat.zero_lt_two _
            omega
          _ = 2 ^ (m - 1) := by
            rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
            omega
      omega
    _ = binaryTraceTopDegree m := natDegree_X_pow _

lemma binaryTraceQuotient_identity {F : Type*} [Field F] [CharP F 2]
    (m : ℕ) (s : F) :
    X * binaryTraceQuotient m s =
      X ^ binaryTraceTopDegree m + binaryNormalizedTracePoly m s := by
  rw [binaryNormalizedTracePoly]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end Field

section FiniteBinaryField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Field F] [DecidableEq F] [CharP F 2] in
lemma binaryTraceTopDegree_eq_card_div_two {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) :
    binaryTraceTopDegree m = Fintype.card F / 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [hcard, binaryTraceTopDegree]
  simp [pow_succ]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma inv_mul_trace_term (s x : F) (hs : s ≠ 0) (i : ℕ) :
    s⁻¹ * (s ^ 2 * x) ^ (2 ^ i) =
      s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i) := by
  rw [mul_pow]
  have hexp : 2 * 2 ^ i = 2 ^ (i + 1) := by rw [pow_succ]; omega
  rw [show (s ^ 2) ^ (2 ^ i) = s ^ (2 ^ (i + 1)) by rw [← pow_mul, hexp]]
  have hpos : 0 < 2 ^ (i + 1) := by positivity
  have hcoeff : s⁻¹ * s ^ (2 ^ (i + 1)) = s ^ (2 ^ (i + 1) - 1) := by
    calc
      s⁻¹ * s ^ (2 ^ (i + 1)) =
          s⁻¹ * (s ^ (2 ^ (i + 1) - 1) * s) := by
            congr 2
            rw [← pow_succ]
            congr 1
            omega
      _ =
          (s⁻¹ * s) * s ^ (2 ^ (i + 1) - 1) := by ac_rfl
      _ = s ^ (2 ^ (i + 1) - 1) := by rw [inv_mul_cancel₀ hs, one_mul]
  rw [show s⁻¹ * (s ^ (2 ^ (i + 1)) * x ^ (2 ^ i)) =
      (s⁻¹ * s ^ (2 ^ (i + 1))) * x ^ (2 ^ i) by ac_rfl, hcoeff]

omit [DecidableEq F] [CharP F 2] in
/-- The normalized polynomial evaluates to a scaled absolute trace when `s ≠ 0`. -/
lemma eval_binaryNormalizedTracePoly {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card F = 2 ^ m) {s : F} (hs : s ≠ 0) (x : F) :
    (binaryNormalizedTracePoly m s).eval x = s⁻¹ * binaryTrace m (s ^ 2 * x) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [binaryNormalizedTracePoly, eval_add, eval_X_pow, eval_mul, eval_X,
    binaryTrace, hn, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  simp only [binaryTraceTopDegree, Nat.add_sub_cancel]
  -- The finite-field power identity normalizes the leading coefficient to one.
  have htop : s ^ (2 ^ (n + 1) - 1) = 1 := by
    rw [← hn, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one s hs
  have htopterm : s⁻¹ * (s ^ 2 * x) ^ (2 ^ n) = x ^ (2 ^ n) := by
    rw [inv_mul_trace_term s x hs n, htop, one_mul]
  --
  -- Match every remaining monomial with its term in the scaled Frobenius sum.
  have hlower : x * (binaryTraceQuotient (n + 1) s).eval x =
      ∑ i ∈ Finset.range n, s⁻¹ * (s ^ 2 * x) ^ (2 ^ i) := by
    rw [binaryTraceQuotient, Nat.add_sub_cancel, eval_finsetSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eval_mul, eval_C, eval_X_pow]
    have hexp : 2 ^ i - 1 + 1 = 2 ^ i := by
      exact Nat.sub_add_cancel (by
        have hp : 0 < 2 ^ i := pow_pos Nat.zero_lt_two _
        omega)
    rw [show x * (s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i - 1)) =
        s ^ (2 ^ (i + 1) - 1) * x ^ (2 ^ i) by
      rw [mul_left_comm, ← pow_succ', hexp]]
    exact (inv_mul_trace_term s x hs i).symm
  rw [hlower, htopterm]
  ac_rfl


end FiniteBinaryField

end Polynomial
