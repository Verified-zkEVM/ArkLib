/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Counting
public import ArkLib.ToMathlib.Analysis.SpecificLimits.GeometricBounds

/-!
# Geometric bounds for the local coordinate budget

The coarse local coordinate budget is
`localCoordinateBudget d m W B = B ∑_{r<m} ⌈(m - r) / (d + 1)⌉ · N_d(W + r)`, where
`N_d(W) = weightedHigherJetCount d W` counts the higher-jet exponents of anisotropic weight at most
`W`. This file bounds it by an explicit closed expression in `x = (d - 1) / W`.

1. The weighted-simplex sandwich `Finset.natWeightedSimplex_succ_sandwich` gives
   `((d-1)!)^2 N_d(W + r) ≤ (W + r + C(d, 2))^(d-1)`, and
   `Real.add_pow_le_pow_mul_exp` turns the right side into
   `W^(d-1) exp(x (r + C(d, 2)))` (`weightedHigherJetCount_le_exp`).
2. Reflecting the contact sum `r ↦ m - 1 - r`, the ceiling is at most `(j + 1) / d + 1` and the
   exponential factor is `exp(x (m + B)) exp(-x)^(j+1)`. The finite linear-geometric bound
   `Real.sum_range_linear_mul_exp_neg_pow_succ_le` then gives
   `∑_{r<m} ⌈(m - r) / (d + 1)⌉ exp(x (r + B)) ≤ exp(x (m + B)) (1 / (d x^2) + 1 / x)`
   (`sum_contactThreshold_mul_exp_le`).
3. Combining, `localCoordinateBudget_le_geometric`; in the notation `κ = (d - 1) m / W`,
   `localCoordinateBudget_le_kappa`; and after dividing by `V m^3` with
   `V = W^(d-1) / ((d-1)!)^2`, `localCoordinateBudget_div_volume_mul_cube_le`.

No asymptotic hypothesis is made: the offset `C(d, 2)` and the additive error of the ceiling stay
in the final bound. The hypotheses `2 ≤ d` and `0 < W` make `x` positive; without them the right
sides are zero while the budget is positive.

## Main statements

* `localRank_ceilDiv_le`, `weightedHigherJetCount_le_exp`, `sum_contactThreshold_mul_exp_le`
* `localCoordinateBudget_le_geometric`, `localCoordinateBudget_le_kappa`,
  `localCoordinateBudget_div_volume_mul_cube_le`
* `sum_contactThreshold_mul_exp_le_slots` and `localDerivativeCoordinateBudget_le_geometric`: the
  contact sum for any number of slots, and the geometric bound for the derivative-order budget of
  the partition support.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1, (72), and Appendix D.2, (131)
  in the proof of Lemma 6.2
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

open Finset

/-- The ceiling in the local contact count is at most `j / d + 1`. The hypothesis `0 < d` is
needed: for `d = 0` and `j = 2` the left side is `2` and the right side is `1`. -/
theorem localRank_ceilDiv_le (d j : ℕ) (hd : 0 < d) :
    ((j ⌈/⌉ (d + 1) : ℕ) : ℝ) ≤ (j : ℝ) / d + 1 := by
  refine (Nat.cast_ceilDiv_le_div_add_one j (d + 1)).trans ?_
  gcongr
  simp

/-- Exponential envelope of the weighted-simplex count: for `W > 0`,
`N_d(W + r) ≤ W^(d-1) / ((d-1)!)^2 · exp((d - 1) / W · (r + C(d, 2)))`. The offset `C(d, 2)` is
the total weight `1 + ⋯ + (d - 1)` from the sandwich. The hypothesis `0 < W` is needed: for
`W = 0` the right side is zero when `d ≥ 2`, while the count is positive. -/
theorem weightedHigherJetCount_le_exp (d W r : ℕ) (hW : 0 < W) :
    (weightedHigherJetCount d (W + r) : ℝ) ≤
      (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (r + d.choose 2)) := by
  have hchoose : (d - 1 + 1).choose 2 = d.choose 2 := by
    rcases d with _ | d
    · rfl
    · rfl
  have h := (Finset.natWeightedSimplex_succ_sandwich (d - 1) (W + r)).2
  rw [hchoose] at h
  have hnat : ((d - 1).factorial : ℝ) ^ 2 * (weightedHigherJetCount d (W + r) : ℝ) ≤
      ((W : ℝ) + (r + d.choose 2)) ^ (d - 1) := by
    rw [← add_assoc]
    exact_mod_cast h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hexp := Real.add_pow_le_pow_mul_exp (d - 1) hW' (y := r + d.choose 2) (by positivity)
  have hfac : (0 : ℝ) < ((d - 1).factorial : ℝ) ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hfac, mul_comm _ (_ ^ 2)]
  refine hnat.trans (hexp.trans_eq ?_)
  rw [mul_div_assoc', div_mul_eq_mul_div]

/-- The contact sum weighted by exponentials, for any number `s` of contact slots and `0 < x`:
`∑_{r<m} ⌈(m - r) / s⌉ exp(x (r + B)) ≤ exp(x (m + B)) (1 / (s x^2) + 1 / x)`. After the
substitution `r = m - 1 - j` the ceiling is at most `(j + 1) / s + 1`
(`Nat.cast_ceilDiv_le_div_add_one`) and the exponential is `exp(x (m + B)) exp(-x)^(j+1)`, so the
finite linear-geometric bound `Real.sum_range_linear_mul_exp_neg_pow_succ_le` applies. No
hypothesis on `s` is needed: for `s = 0` every ceiling is `0`. The hypothesis `0 < x` is needed:
at `x = 0` the right side is zero while the sum is positive for `m ≥ 1` and `s ≥ 1`. -/
theorem sum_contactThreshold_mul_exp_le_slots (s m : ℕ) {x B : ℝ} (hx : 0 < x) :
    ∑ r ∈ range m, (contactThreshold s m r : ℝ) * Real.exp (x * (r + B)) ≤
      Real.exp (x * (m + B)) * (1 / ((s : ℝ) * x ^ 2) + 1 / x) := by
  rw [← sum_range_reflect _ m]
  have hterm : ∀ j ∈ range m,
      (contactThreshold s m (m - 1 - j) : ℝ) * Real.exp (x * ((m - 1 - j : ℕ) + B)) ≤
        Real.exp (x * (m + B)) *
          ((1 / (s : ℝ) * ((j + 1 : ℕ) : ℝ) + 1) * Real.exp (-x) ^ (j + 1)) := by
    intro j hj
    have hjm := mem_range.mp hj
    have heq : m - (m - 1 - j) = j + 1 := by omega
    have hcast : ((m - 1 - j : ℕ) : ℝ) = m - (j + 1 : ℕ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    have hexp : Real.exp (x * ((m - 1 - j : ℕ) + B)) =
        Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, hcast]
      congr 1
      ring
    rw [contactThreshold, heq, hexp]
    have h := mul_le_mul_of_nonneg_right (Nat.cast_ceilDiv_le_div_add_one (K := ℝ) (j + 1) s)
      (by positivity : 0 ≤ Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1))
    calc
      _ = ((((j + 1) ⌈/⌉ s : ℕ) : ℝ)) *
          (Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1)) := by ring
      _ ≤ (((j + 1 : ℕ) : ℝ) / s + 1) *
          (Real.exp (x * (m + B)) * Real.exp (-x) ^ (j + 1)) := h
      _ = _ := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine (Real.sum_range_linear_mul_exp_neg_pow_succ_le m (by positivity) zero_le_one hx).trans_eq
    ?_
  rw [div_div]

/-- The contact sum with `d + 1` slots, for `0 < d` and `0 < x`:
`∑_{r<m} ⌈(m - r) / (d + 1)⌉ exp(x (r + B)) ≤ exp(x (m + B)) (1 / (d x^2) + 1 / x)`. This is
`sum_contactThreshold_mul_exp_le_slots` with `s = d + 1`, followed by
`1 / ((d + 1) x^2) ≤ 1 / (d x^2)`; the sharper form keeps the denominator `d + 1`. The hypothesis
`0 < d` is needed for the weakened denominator `d`. -/
theorem sum_contactThreshold_mul_exp_le (d m : ℕ) (hd : 0 < d) {x B : ℝ} (hx : 0 < x) :
    ∑ r ∈ range m, (contactThreshold (d + 1) m r : ℝ) * Real.exp (x * (r + B)) ≤
      Real.exp (x * (m + B)) * (1 / ((d : ℝ) * x ^ 2) + 1 / x) := by
  refine (sum_contactThreshold_mul_exp_le_slots (d + 1) m (B := B) hx).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Real.exp_pos _).le
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  gcongr
  linarith

/-- Absolute upper bound for the local coordinate budget, with `x = (d - 1) / W`:
`localCoordinateBudget d m W B ≤ B V exp(x (m + C(d, 2))) (1 / (d x^2) + 1 / x)` for
`V = W^(d-1) / ((d-1)!)^2`. The hypotheses `2 ≤ d` and `0 < W` make `x` positive; for `d = 1` or
`W = 0` the right side is zero while the budget can be positive. -/
theorem localCoordinateBudget_le_geometric (d m W Be : ℕ) (hd : 2 ≤ d) (hW : 0 < W) :
    (localCoordinateBudget d m W Be : ℝ) ≤
      Be * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp ((((d - 1 : ℕ) : ℝ) / W) * (m + d.choose 2)) *
          (1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) +
            1 / (((d - 1 : ℕ) : ℝ) / W)) := by
  set x : ℝ := ((d - 1 : ℕ) : ℝ) / W with hxdef
  set V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 with hVdef
  have hx : 0 < x := div_pos (by exact_mod_cast (show 0 < d - 1 by omega))
    (by exact_mod_cast hW)
  have hV : 0 ≤ V := by positivity
  have hsum : (∑ r ∈ range m,
      (contactThreshold (d + 1) m r : ℝ) * weightedHigherJetCount d (W + r)) ≤
        V * ∑ r ∈ range m,
          (contactThreshold (d + 1) m r : ℝ) * Real.exp (x * (r + d.choose 2)) := by
    rw [mul_sum]
    refine sum_le_sum fun r _ => ?_
    have h := mul_le_mul_of_nonneg_left (weightedHigherJetCount_le_exp d W r hW)
      (Nat.cast_nonneg (contactThreshold (d + 1) m r))
    calc
      _ ≤ _ := h
      _ = _ := by rw [hxdef, hVdef]; ring
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_left
    (sum_contactThreshold_mul_exp_le d m (by omega) (B := (d.choose 2 : ℝ)) hx) hV)
  have h := mul_le_mul_of_nonneg_left hsum' (Nat.cast_nonneg Be)
  rw [localCoordinateBudget]
  push_cast
  calc
    _ ≤ _ := h
    _ = _ := by ring

/-- Absolute upper bound for the derivative-order coordinate budget, with `x = d / W` and
`V = W^d / (d!)^2`:
`localDerivativeCoordinateBudget d m W ≤ V exp(x (m + C(d + 1, 2))) (1 / ((d + 1) x^2) + 1 / x)`.
The count of exponents of `Y₁, ..., Y_d` of derivative-order weight at most `W + r` is bounded by
`weightedHigherJetCount_le_exp` at order `d + 1`, and the contact sum with `d + 1` slots by
`sum_contactThreshold_mul_exp_le_slots`; the offset `C(d + 1, 2) = 1 + ⋯ + d` and the additive
ceiling error `1 / x` are kept. The hypotheses `0 < d` and `0 < W` make `x` positive; for `d = 0`
or `W = 0` the right side is zero while the budget is positive for `m ≥ 1`. -/
theorem localDerivativeCoordinateBudget_le_geometric (d m W : ℕ) (hd : 0 < d) (hW : 0 < W) :
    (localDerivativeCoordinateBudget d m W : ℝ) ≤
      ((W : ℝ) ^ d / (d.factorial : ℝ) ^ 2) *
        Real.exp (((d : ℝ) / W) * (m + (d + 1).choose 2)) *
          (1 / (((d : ℝ) + 1) * ((d : ℝ) / W) ^ 2) + 1 / ((d : ℝ) / W)) := by
  set x : ℝ := (d : ℝ) / W with hxdef
  set V : ℝ := (W : ℝ) ^ d / (d.factorial : ℝ) ^ 2 with hVdef
  have hx : 0 < x := div_pos (by exact_mod_cast hd) (by exact_mod_cast hW)
  have hV : 0 ≤ V := by positivity
  have hsum : (localDerivativeCoordinateBudget d m W : ℝ) ≤
      V * ∑ r ∈ range m,
        (contactThreshold (d + 1) m r : ℝ) * Real.exp (x * (r + (d + 1).choose 2)) := by
    rw [localDerivativeCoordinateBudget, mul_sum]
    push_cast
    refine sum_le_sum fun r _ => ?_
    have h := mul_le_mul_of_nonneg_left (weightedHigherJetCount_le_exp (d + 1) W r hW)
      (Nat.cast_nonneg (contactThreshold (d + 1) m r))
    simp only [Nat.add_sub_cancel] at h
    calc
      _ ≤ _ := h
      _ = _ := by rw [hxdef, hVdef]; ring
  have htail := sum_contactThreshold_mul_exp_le_slots (d + 1) m
    (B := ((d + 1).choose 2 : ℝ)) hx
  push_cast at htail
  calc
    _ ≤ _ := hsum.trans (mul_le_mul_of_nonneg_left htail hV)
    _ = _ := by ring

/-- The geometric budget bound in the notation `κ = (d - 1) m / W`:
`localCoordinateBudget d m W B ≤ B V exp(κ (1 + C(d, 2) / m)) (m^2 / (d κ^2) + m / κ)`. The
hypothesis `0 < m` is needed to divide by `m`; the others are those of
`localCoordinateBudget_le_geometric`. -/
theorem localCoordinateBudget_le_kappa (d m W Be : ℕ) (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W) :
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (localCoordinateBudget d m W Be : ℝ) ≤
      Be * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
          ((m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ) := by
  intro κ
  have h := localCoordinateBudget_le_geometric d m W Be hd hW
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hk' : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
  have hexp : (((d - 1 : ℕ) : ℝ) / W) * (m + d.choose 2) = κ * (1 + (d.choose 2 : ℝ) / m) := by
    simp only [κ]
    field_simp
  have hrecip : 1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) + 1 / (((d - 1 : ℕ) : ℝ) / W) =
      (m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ := by
    simp only [κ]
    field_simp
  rwa [hexp, hrecip] at h

/-- The budget normalized by the weighted simplex volume `V = W^(d-1) / ((d-1)!)^2` and by `m^3`:
`localCoordinateBudget d m W B / (V m^3) ≤ (B / m) exp(κ (1 + C(d, 2) / m))
(1 / (d κ^2) + 1 / (m κ))`. The ceiling error remains in the term `1 / (m κ)`. -/
theorem localCoordinateBudget_div_volume_mul_cube_le (d m W Be : ℕ)
    (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (localCoordinateBudget d m W Be : ℝ) / (V * m ^ 3) ≤
      ((Be : ℝ) / m) * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  intro V κ
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hκ : 0 < κ := by
    have : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast (by omega : 0 < d - 1)
    positivity
  have hV : 0 < V := by positivity
  have h : (localCoordinateBudget d m W Be : ℝ) ≤ Be * V *
      Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        ((m : ℝ) ^ 2 / ((d : ℝ) * κ ^ 2) + m / κ) :=
    localCoordinateBudget_le_kappa d m W Be hd hm hW
  rw [div_le_iff₀ (by positivity : 0 < V * (m : ℝ) ^ 3)]
  refine h.trans_eq ?_
  field_simp

end ReedSolomon.HiddenDerivative
