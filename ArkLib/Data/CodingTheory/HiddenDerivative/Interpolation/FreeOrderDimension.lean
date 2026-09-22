/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FreeOrder

/-!
# The free-order interpolation dimension comparison

At multiplicity `m = d³`, this file compares `n` copies of the certified bound on the rank of
the local constraint map with the dimension of the exact interpolation space with `D = K - 1`
and `M = m`. The comparison is the inequality the interpolation argument needs to find a nonzero
polynomial in the kernel of all `n` local constraint maps.

The certified bound is at most `4 d⁸ Λ_d(W + d³)`, where `Λ_d` is `weightedHigherJetCount d`. A
shell estimate `Λ_d(W + d³) ≤ R #(goodHigherExponents d W C)` and the scalar inequality
`n 4 d⁸ R < (K - 1) H³` then place `n` certified bounds below the rectangular lower bound
`#(goodHigherExponents d W C) (K - 1) H³` on the dimension. The scalar inequality follows from
three real estimates: `H ≥ θ d³ / 32`, `R ≤ 2 d^((5 - θ) / (5 + θ))`, and the rank comparison
`1 < (θ³ / 2¹⁸) ((K - 1) / n) d^(2θ / (5 + θ))`; the two exponents of `d` add up to `1`.

This file bounds the certified rank budget of the exhibited local kernel. It does not identify
that budget with the rank of the local constraint map.

## Main statements

* `certifiedEnlargedRankBound_le_four_mul_d_pow_eight`: the certified bound at `m = M = d³` is at
  most `4 d⁸ Λ_d(W + d³)`, for every `d`.
* `shellExponent_add_rankSavingExponent`: `(5 - θ) / (5 + θ) + 2θ / (5 + θ) = 1`.
* `rankShellBound_lt_interpolationBox`: the three real estimates imply
  `n 4 d⁸ R < (K - 1) H³`.
* `n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace`: the shell estimate and
  the scalar inequality imply that `n` certified bounds are below the exact dimension.
* `localRankBound_lt_interpolationSpace_of_shell_bounds`: the same conclusion from the shell
  estimate and the three real estimates.

Parts of this file are adapted, with permission, from Kai Zhe Zheng's `kz99/rs-ld-mca`
formalization.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26].
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26].
-/

@[expose] public section

open Finset

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- At multiplicity and first-jet cap `m = M = d³` the certified bound is at most
`4 d⁸ Λ_d(W + d³)`. This is `certifiedEnlargedRankBound_le_of_le_mul` with `k = d²`, which gives
`d⁵ (2 d³ + 1) ≤ 4 d⁸`. It holds for every `d`: at `d = 0` both sides are `0`. -/
theorem certifiedEnlargedRankBound_le_four_mul_d_pow_eight (d W : ℕ) :
    certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W ≤
      4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3) := by
  refine (certifiedEnlargedRankBound_le_of_le_mul (k := d ^ 2) (pow_succ' d 2).le).trans
    (Nat.mul_le_mul_right _ ?_)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hone : 1 ≤ d ^ 3 := Nat.one_le_pow 3 d hd
  have e₁ : d ^ 3 * (d ^ 2 * (d ^ 3 + d ^ 3 + 1)) = d ^ 5 * (2 * d ^ 3 + 1) := by ring
  have e₂ : 4 * d ^ 8 = d ^ 5 * (4 * d ^ 3) := by ring
  rw [e₁, e₂]
  exact Nat.mul_le_mul_left _ (by omega)

/-- The exponent `(5 - θ) / (5 + θ)` of `d` in the shell estimate. -/
def shellExponent (θ : ℝ) : ℝ :=
  (5 - θ) / (5 + θ)

/-- The shell exponent and the saved exponent add up to `1`, for `θ ≠ -5`. At `θ = -5` both
divide by `0` and the sum is `0`. -/
theorem shellExponent_add_rankSavingExponent {θ : ℝ} (hθ : θ ≠ -5) :
    shellExponent θ + rankSavingExponent θ = 1 := by
  have h : 5 + θ ≠ 0 := fun h => hθ (by linarith)
  unfold shellExponent rankSavingExponent
  field_simp
  ring

/-- The three real estimates `θ d³ / 32 ≤ H`, `R ≤ 2 d^((5 - θ) / (5 + θ))`, and
`1 < (θ³ / 2¹⁸) ((K - 1) / n) d^(2θ / (5 + θ))` imply `n 4 d⁸ R < (K - 1) H³`. Multiplying the
third by `8 n d⁸ d^((5 - θ) / (5 + θ))` gives `8 n d⁸ d^((5 - θ) / (5 + θ)) < (K - 1) (θ d³ / 32)³`,
and the first two bound the two sides.

The rank comparison forces `θ > 0`, `n > 0`, and `d > 0`: otherwise its right side is at most
`0`. So these are not hypotheses. -/
theorem rankShellBound_lt_interpolationBox {θ : ℝ} {d K H R n : ℕ}
    (hH : θ * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (θ ^ 3 / 262144) * (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ rankSavingExponent θ) :
    n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3 := by
  have hrate : 0 ≤ ((K - 1 : ℕ) : ℝ) / (n : ℝ) := by positivity
  have hdpow : 0 ≤ (d : ℝ) ^ rankSavingExponent θ := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hθ : 0 < θ := by
    by_contra hθ
    have hcube : θ ^ 3 / 262144 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos (by decide) (not_lt.mp hθ)) (by norm_num)
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hcube hrate) hdpow
    linarith
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hcompare
      linarith
    · exact hn
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Real.zero_rpow (rankSavingExponent_pos hθ).ne'] at hcompare
      linarith
    · exact hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowShell : 0 < (d : ℝ) ^ shellExponent θ := Real.rpow_pos_of_pos hdR _
  have hscaled := mul_lt_mul_of_pos_left hcompare
    (by positivity : 0 < 8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ)
  have hpowers : (d : ℝ) ^ shellExponent θ * (d : ℝ) ^ rankSavingExponent θ = (d : ℝ) := by
    rw [← Real.rpow_add hdR, shellExponent_add_rankSavingExponent (by linarith), Real.rpow_one]
  have hmiddle :
      8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ <
        ((K - 1 : ℕ) : ℝ) * (θ * (d : ℝ) ^ 3 / 32) ^ 3 := by
    calc 8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ
        = 8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ * 1 := (mul_one _).symm
      _ < 8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ *
          ((θ ^ 3 / 262144) * (((K - 1 : ℕ) : ℝ) / (n : ℝ)) *
            (d : ℝ) ^ rankSavingExponent θ) := hscaled
      _ = (8 * (n : ℝ) * (θ ^ 3 / 262144) * (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ 8) *
          ((d : ℝ) ^ shellExponent θ * (d : ℝ) ^ rankSavingExponent θ) := by ring
      _ = ((K - 1 : ℕ) : ℝ) * (θ * (d : ℝ) ^ 3 / 32) ^ 3 := by
          rw [hpowers]
          field_simp
          ring
  have hleft : ((n * (4 * d ^ 8 * R) : ℕ) : ℝ) ≤
      8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ := by
    push_cast
    calc (n : ℝ) * (4 * (d : ℝ) ^ 8 * (R : ℝ))
        ≤ (n : ℝ) * (4 * (d : ℝ) ^ 8 * (2 * (d : ℝ) ^ shellExponent θ)) := by gcongr
      _ = 8 * (n : ℝ) * (d : ℝ) ^ 8 * (d : ℝ) ^ shellExponent θ := by ring
  have hright : ((K - 1 : ℕ) : ℝ) * (θ * (d : ℝ) ^ 3 / 32) ^ 3 ≤
      (((K - 1) * H ^ 3 : ℕ) : ℝ) := by
    push_cast
    gcongr
    simpa only [Nat.cast_pow] using hH
  exact_mod_cast hleft.trans_lt (hmiddle.trans_le hright)

/-- At multiplicity `m = d³`, with `D = K - 1` and `M = m`: if
`Λ_d(W + d³) ≤ R #(goodHigherExponents d W C)` (the shell estimate), `H ≤ d³`,
`(K - 1)(C + 3H) ≤ d³ A`, and `n 4 d⁸ R < (K - 1) H³`, then `n` certified rank bounds are below
the dimension of the exact interpolation space. The chain is
`n · certified ≤ n 4 d⁸ Λ_d(W + d³) ≤ n 4 d⁸ R #good < (K - 1) H³ #good ≤ dim`, using
`certifiedEnlargedRankBound_le_four_mul_d_pow_eight` and
`card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace`.

`0 < d` is not a hypothesis: at `d = 0` the bound `H ≤ d³` gives `H = 0`, and the scalar
inequality fails. -/
theorem n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace
    (F : Type*) [Field F] {d A K W C H R n : ℕ} (hdK : d < K - 1) (hH : H ≤ d ^ 3)
    (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤ R * #(goodHigherExponents d W C))
    (harithmetic : n * (4 * d ^ 8 * R) < (K - 1) * H ^ 3) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have hH0 : H = 0 := by simpa using hH
      subst hH0
      simp at harithmetic
    · exact hd
  have hgood : 0 < #(goodHigherExponents d W C) := by
    rw [card_pos]
    exact ⟨0, mem_goodHigherExponents.mpr ⟨by simp [higherJetWeight], by simp [higherJetDegree]⟩⟩
  calc n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W
      ≤ n * (4 * d ^ 8 * weightedHigherJetCount d (W + d ^ 3)) :=
        Nat.mul_le_mul_left n (certifiedEnlargedRankBound_le_four_mul_d_pow_eight d W)
    _ ≤ n * (4 * d ^ 8 * (R * #(goodHigherExponents d W C))) := by gcongr
    _ = n * (4 * d ^ 8 * R) * #(goodHigherExponents d W C) := by ring
    _ < (K - 1) * H ^ 3 * #(goodHigherExponents d W C) :=
        Nat.mul_lt_mul_of_pos_right harithmetic hgood
    _ = #(goodHigherExponents d W C) * (K - 1) * H ^ 3 := by ring
    _ ≤ _ := card_goodHigherExponents_mul_le_finrank_exactInterpolationSpace F hd hdK
        (by omega) hH hweighted

/-- The shell estimate and the three real estimates of `rankShellBound_lt_interpolationBox`,
together with `H ≤ d³` and `(K - 1)(C + 3H) ≤ d³ A`, imply that `n` certified rank bounds are
below the dimension of the exact interpolation space. -/
theorem localRankBound_lt_interpolationSpace_of_shell_bounds
    (F : Type*) [Field F] {θ : ℝ} {d A K W C H R n : ℕ} (hdK : d < K - 1)
    (hHle : H ≤ d ^ 3) (hweighted : (K - 1) * (C + 3 * H) ≤ d ^ 3 * A)
    (hH : θ * (d ^ 3 : ℕ) / 32 ≤ (H : ℝ))
    (hR : (R : ℝ) ≤ 2 * (d : ℝ) ^ shellExponent θ)
    (hcompare :
      1 < (θ ^ 3 / 262144) * (((K - 1 : ℕ) : ℝ) / (n : ℝ)) * (d : ℝ) ^ rankSavingExponent θ)
    (hshell : weightedHigherJetCount d (W + d ^ 3) ≤ R * #(goodHigherExponents d W C)) :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3) W <
      Module.finrank F (exactInterpolationSpace F (K - 1) A d (d ^ 3) (d ^ 3) W hdK) :=
  n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace F hdK hHle hweighted hshell
    (rankShellBound_lt_interpolationBox hH hR hcompare)

end

end ReedSolomon.HiddenDerivative
