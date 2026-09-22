/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
public import ArkLib.ToMathlib.Algebra.Order.Floor.Ratio
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Rounding and centering errors of the weighted support

The weighted-support interpolation rounds its weighted radius down, `W = ⌊a d m / H⌋₊` with
`a = 1 + θ g`, and its local rank integral works on the simplex enlarged to the budget
`W'_r = W + r + d.choose 2` for a contact residual `r < m`. The per-fiber mean gap is
`gap_r = m (1 + g) + (d - 1) - W'_r H / d` and the per-fiber variance is
`W'_r ^ 2 H₂ / (d (d + 1))`. This file bounds both.

The rounding lemmas are stated for arbitrary `a`, `θ` and relative errors `ε`:

* `floorRadius_mul_div_le`, `floorRadius_normalized_le`: flooring only decreases the mean
  `W H / d ≤ a m` and the normalized radius `W / (d g m) ≤ a / (g H)`.
* `floorRadius_sq_ge`: once `a d m / H ≥ N ≥ 1`, the squared normalized radius keeps the factor
  `(1 - 1 / N) ^ 2`.
* `remainingDegree_lower`, `remainingDegree_upper`: if the additive rounding errors are at most
  `ε (1 - θ) g m`, then `gap_r` lies within the factor `1 ∓ ε` of the residual `(1 - θ) g m`.
* `enlargedRadius_upper`: if `m + d.choose 2 ≤ ε a d m / H`, then `W'_r / d ≤ (a m / H) (1 + ε)`.
* `enlargedRadius_normalized`, `residualVariance_le`: the variance is at most
  `(g m) ^ 2 c ^ 2 / ξ ^ 2 · h` when `a / (g H) ≤ 1 / ξ`, `W'_r / d ≤ (a m / H) c` and `H₂ ≤ h`.

With the prescribed constants `θ = 3 / 8`, `ξ = 27 / 10` the three additive errors are at most
`(2 / 1000) (5 / 8) g m`, `(1 / 1000) (5 / 8) g m` and `(1 / 1000) a d m / H`
(`centeringErrorBounds`), and the mean gap and variance combine into the positive-part bound
`gap_r + variance_r / (4 gap_r) + 1 ≤ g m (448 / 625)` (`prescribedFiberMeanVariance_le`).

## Main statements

* `floorRadius_mul_div_le`, `floorRadius_normalized_le`, `floorRadius_sq_ge`
* `remainingDegree_lower`, `remainingDegree_upper`, `enlargedRadius_upper`
* `centeringErrorBounds`
* `residualMeanVariance_le`, `prescribedFiberMeanVariance_le`

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Parameters/WeightedSupport/Rounding.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `floorRadius_pos` is Mathlib's `Nat.floor_pos` and is not restated.
* `floorRadius_mul_div_le` and `floorRadius_normalized_le` are stated for the floor itself instead
  of a variable `W` with `W = ⌊a d m / H⌋₊`. The first drops the hypotheses `0 < H` and `0 < d`,
  the second `0 < d` and `0 < m`: in each dropped case both sides are handled by the convention
  `x / 0 = 0` or by `⌊x⌋₊ = 0` for `x ≤ 0`.
* `floorRadius_sq_ge` takes the threshold `N ≥ 1` of the unrounded radius as a parameter and
  concludes with `(1 - 1 / N) ^ 2`; the source fixed `N = 2000` and weakened `(1999 / 2000) ^ 2` to
  `999 / 1000`. The relative floor error is `Nat.one_sub_one_div_mul_lt_floor` in
  `ArkLib.ToMathlib.Algebra.Order.Floor.Ratio`. The hypothesis `0 < a` is dropped (it follows from
  `N ≤ a d m / H`).
* `remainingDegree_lower`, `remainingDegree_upper` and `enlargedRadius_upper` take the tilt `θ` and
  the relative error `ε` as parameters; the source fixed `θ = 3 / 8` and `ε = 2 / 1000`,
  `1 / 1000`, `1 / 1000`. The unused hypotheses `0 < m`, `0 < g` are dropped, `0 < d` is dropped
  from `remainingDegree_lower`, and `0 < H` is weakened to `0 ≤ H` there; `0 < g` is replaced by
  `0 ≤ 1 + θ g` where the floor needs a nonnegative argument.
* `enlargedRadius_normalized` takes `a`, `ξ` and the factor `c` as parameters (the source fixed
  `a = 1 + θ g`, `ξ = 27 / 10`, `c = 1001 / 1000`) and drops the unused `0 < d`.
* `residualVariance_le` takes `ξ`, `c` and the bound `h` of `H₂` as parameters (the source fixed
  `27 / 10`, `1001 / 1000` and `329 / 200`) and drops the unused `0 ≤ q`.
* `centeringErrorBounds`, `averageResidualError_le`, `residualMeanVariance_le` and
  `prescribedFiberMeanVariance_le` keep the source's constants and hypotheses.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- Flooring the radius only lowers the mean: `⌊a d m / H⌋₊ H / d ≤ a m` for `a ≥ 0`. If `H ≤ 0`
the floor is `0`; if `d = 0` the left side is `0`. The hypothesis `0 ≤ a` is needed: for `a < 0`
the floor is `0` while `a m < 0` when `m > 0`. -/
theorem floorRadius_mul_div_le (a H : ℝ) (d m : ℕ) (ha : 0 ≤ a) :
    (⌊a * d * m / H⌋₊ : ℝ) * H / d ≤ a * m := by
  have ham : 0 ≤ a * m := by positivity
  rcases le_or_gt H 0 with hH | hH
  · rw [Nat.floor_eq_zero.mpr ((div_nonpos_of_nonneg_of_nonpos (by positivity) hH).trans_lt
      one_pos)]
    simpa using ham
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using ham
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : (⌊a * d * m / H⌋₊ : ℝ) ≤ a * d * m / H := Nat.floor_le (by positivity)
  rw [div_le_iff₀ hdR]
  calc (⌊a * d * m / H⌋₊ : ℝ) * H ≤ a * d * m / H * H := mul_le_mul_of_nonneg_right hf hH.le
    _ = a * m * d := by field_simp

/-- Flooring the radius only lowers the normalized radius:
`⌊a d m / H⌋₊ / (d g m) ≤ a / (g H)` for `a ≥ 0` and `g, H > 0`. If `d m = 0` the left side is
`0`. -/
theorem floorRadius_normalized_le (a g H : ℝ) (d m : ℕ) (ha : 0 ≤ a) (hg : 0 < g) (hH : 0 < H) :
    (⌊a * d * m / H⌋₊ : ℝ) / (d * g * m) ≤ a / (g * H) := by
  have hrhs : 0 ≤ a / (g * H) := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using hrhs
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hrhs
  have hmean := floorRadius_mul_div_le a H d m ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [div_le_iff₀ hdR] at hmean
  nlinarith

/-- Once the unrounded radius `R = a d m / H` is at least `N ≥ 1`, the squared normalized floored
radius keeps the factor `(1 - 1 / N) ^ 2`:
`(1 - 1 / N) ^ 2 (a / (g H)) ^ 2 ≤ (⌊R⌋₊ / (d g m)) ^ 2`. The normalized unrounded radius is
`a / (g H) = R / (d g m)`, and `(1 - 1 / N) R < ⌊R⌋₊` by `Nat.one_sub_one_div_mul_lt_floor`. The
hypothesis `1 ≤ N` keeps `1 - 1 / N` nonnegative, so that squaring preserves the inequality. -/
theorem floorRadius_sq_ge (N a g H : ℝ) (d m : ℕ) (hN : 1 ≤ N) (hg : 0 < g) (hH : 0 < H)
    (hd : 0 < d) (hm : 0 < m) (hR : N ≤ a * d * m / H) :
    (1 - 1 / N) ^ 2 * (a / (g * H)) ^ 2 ≤ ((⌊a * d * m / H⌋₊ : ℝ) / (d * g * m)) ^ 2 := by
  have hden : (0 : ℝ) < d * g * m := by positivity
  have hid : a / (g * H) = (a * d * m / H) / (d * g * m) := by field_simp
  have hlt := Nat.one_sub_one_div_mul_lt_floor (by linarith : (0 : ℝ) < N) hR
  have hN0 : 0 ≤ 1 - 1 / N := by
    have : 1 / N ≤ 1 := (div_le_one (by linarith)).mpr hN
    linarith
  rw [hid, ← mul_pow, ← mul_div_assoc]
  exact pow_le_pow_left₀ (div_nonneg (mul_nonneg hN0 (by linarith)) hden.le)
    (div_le_div_of_nonneg_right hlt.le hden.le) 2

/-- The lower bound on the mean gap. Let `W = ⌊(1 + θ g) d m / H⌋₊` and `r < m`. If the additive
error `m H / d + d.choose 2 · H / d` is at most `ε (1 - θ) g m`, then
`(1 - θ) g m (1 - ε) ≤ m (1 + g) + (d - 1) - (W + r + d.choose 2) H / d`. The floor gives
`W H / d ≤ (1 + θ g) m` (`floorRadius_mul_div_le`, which needs `0 ≤ 1 + θ g`), and `r < m`
gives `r H / d ≤ m H / d` (which needs `0 ≤ H`); the residual `m (1 + g) - (1 + θ g) m` is
`(1 - θ) g m`. -/
theorem remainingDegree_lower (θ ε g H : ℝ) (d m r W : ℕ) (hr : r < m)
    (ha : 0 ≤ 1 + θ * g) (hH : 0 ≤ H) (hW : W = ⌊(1 + θ * g) * d * m / H⌋₊)
    (herror : (m : ℝ) * H / d + d.choose 2 * H / d ≤ ε * (1 - θ) * g * m) :
    (1 - θ) * g * m * (1 - ε) ≤
      (m : ℝ) * (1 + g) + (d - 1 : ℕ) - (W + r + d.choose 2 : ℕ) * H / d := by
  have hmean : (W : ℝ) * H / d ≤ (1 + θ * g) * m := hW ▸ floorRadius_mul_div_le _ H d m ha
  have hrR : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  have hrterm : (r : ℝ) * H / d ≤ m * H / d := by gcongr
  have hsplit : ((W + r + d.choose 2 : ℕ) : ℝ) * H / d =
      W * H / d + r * H / d + (d.choose 2 : ℝ) * H / d := by push_cast; ring
  have hsub : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hsplit]
  linarith

/-- The upper bound on the mean gap. Let `W = ⌊(1 + θ g) d m / H⌋₊`. If the additive error
`d + H / d` is at most `ε (1 - θ) g m`, then
`m (1 + g) + (d - 1) - (W + r + d.choose 2) H / d ≤ (1 - θ) g m (1 + ε)`. The floor loses less
than one unit, so `W H / d > (1 + θ g) m - H / d`; this needs `0 < d` and `0 < H`. -/
theorem remainingDegree_upper (θ ε g H : ℝ) (d m r W : ℕ) (hd : 0 < d) (hH : 0 < H)
    (hW : W = ⌊(1 + θ * g) * d * m / H⌋₊)
    (herror : (d : ℝ) + H / d ≤ ε * (1 - θ) * g * m) :
    (m : ℝ) * (1 + g) + (d - 1 : ℕ) - (W + r + d.choose 2 : ℕ) * H / d ≤
      (1 - θ) * g * m * (1 + ε) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor := Nat.sub_one_lt_floor ((1 + θ * g) * (d : ℝ) * m / H)
  rw [← hW] at hfloor
  have hscaled := mul_lt_mul_of_pos_right hfloor (div_pos hH hdR)
  have e1 : ((1 + θ * g) * (d : ℝ) * m / H - 1) * (H / d) = (1 + θ * g) * m - H / d := by
    field_simp
  have e2 : (W : ℝ) * (H / d) = W * H / d := by ring
  have hsplit : ((W + r + d.choose 2 : ℕ) : ℝ) * H / d =
      W * H / d + r * H / d + (d.choose 2 : ℝ) * H / d := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ r * H / d := by positivity
  have hB0 : (0 : ℝ) ≤ (d.choose 2 : ℝ) * H / d := by positivity
  have hdsub : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  rw [hsplit]
  linarith

/-- The enlarged radius. Let `W = ⌊(1 + θ g) d m / H⌋₊` and `r < m`. If
`m + d.choose 2 ≤ ε (1 + θ g) d m / H`, then
`(W + r + d.choose 2) / d ≤ ((1 + θ g) m / H) (1 + ε)`. The floor gives `W ≤ (1 + θ g) d m / H`,
which needs `0 ≤ 1 + θ g`. -/
theorem enlargedRadius_upper (θ ε g H : ℝ) (d m r W : ℕ) (hd : 0 < d) (hr : r < m)
    (ha : 0 ≤ 1 + θ * g) (hH : 0 < H) (hW : W = ⌊(1 + θ * g) * d * m / H⌋₊)
    (herror : (m : ℝ) + d.choose 2 ≤ ε * ((1 + θ * g) * d * m / H)) :
    ((W + r + d.choose 2 : ℕ) : ℝ) / d ≤ ((1 + θ * g) * m / H) * (1 + ε) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : (W : ℝ) ≤ (1 + θ * g) * d * m / H := hW ▸ Nat.floor_le (by positivity)
  have hrR : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  have hsum : ((W + r + d.choose 2 : ℕ) : ℝ) ≤ ((1 + θ * g) * d * m / H) * (1 + ε) := by
    push_cast
    linarith
  calc ((W + r + d.choose 2 : ℕ) : ℝ) / d ≤ ((1 + θ * g) * d * m / H) * (1 + ε) / d :=
        div_le_div_of_nonneg_right hsum hdR.le
    _ = ((1 + θ * g) * m / H) * (1 + ε) := by field_simp

/-- The prescribed error estimates. For `d ≥ 48000`, `54 / 5 ≤ H ≤ (19 / 365) √d`, `ξ ≤ g H`,
`m ≥ 100 d ^ 2 H` and `270 d H ≤ g m`, with `θ = 3 / 8` and `ξ = 27 / 10`:
`m H / d + d.choose 2 · H / d ≤ (2 / 1000) (5 / 8) g m`, `d + H / d ≤ (1 / 1000) (5 / 8) g m`,
and `m + d.choose 2 ≤ (1 / 1000) (1 + θ g) d m / H`. These are the hypotheses of
`remainingDegree_lower`, `remainingDegree_upper` and `enlargedRadius_upper`. The bound
`H ≤ (19 / 365) √d` controls `H / d`, and `m ≥ 100 d ^ 2 H` controls `d.choose 2 / m`. -/
theorem centeringErrorBounds (d m : ℕ) (g H : ℝ)
    (hd : 48000 ≤ d) (hm : 0 < m) (hg : 0 < g) (hH : 0 < H)
    (hHlower : 54 / 5 ≤ H)
    (hHupper : H ≤ (19 / 365) * Real.sqrt d)
    (hgH : xi ≤ g * H)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m)
    (hgm : 270 * d * H ≤ g * m) :
    ((m : ℝ) * H / d + d.choose 2 * H / d ≤
        (2 / 1000) * residualFraction * g * m) ∧
      ((d : ℝ) + H / d ≤
        (1 / 1000) * residualFraction * g * m) ∧
      ((m : ℝ) + d.choose 2 ≤
        (1 / 1000) * ((1 + theta * g) * d * m / H)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrtSq : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdR.le
  have hsqrtLower : (219 : ℝ) ≤ Real.sqrt d := by
    have hcast : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    have hs : Real.sqrt 48000 ≤ Real.sqrt d := Real.sqrt_le_sqrt hcast
    have h219 : (219 : ℝ) < Real.sqrt 48000 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    exact h219.le.trans hs
  have hHsq : H ^ 2 ≤ (19 / 365 : ℝ) ^ 2 * d := by
    have hs := pow_le_pow_left₀ hH.le hHupper 2
    nlinarith
  have hsqrtLeD : Real.sqrt d ≤ d := by
    nlinarith [sq_nonneg (Real.sqrt d - 1)]
  have hHd : H ≤ (19 / 365 : ℝ) * d :=
    hHupper.trans (mul_le_mul_of_nonneg_left hsqrtLeD (by norm_num))
  have hB : (d.choose 2 : ℝ) / m ≤ 1 / (200 * H) := by
    rw [Nat.cast_choose_two]
    apply (div_le_iff₀ hmR).2
    rw [show 1 / (200 * H) * (m : ℝ) = (m : ℝ) / (200 * H) by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 200 * H)).2
    have hd0 : (0 : ℝ) ≤ d := hdR.le
    nlinarith
  have hxiH : xi * H ≤ g * H ^ 2 := by
    have := mul_le_mul_of_nonneg_right hgH hH.le
    nlinarith
  have hterm1 : H / d ≤ g * (19 / 365 : ℝ) ^ 2 / xi := by
    apply (div_le_iff₀ hdR).2
    rw [show (g * (19 / 365 : ℝ) ^ 2 / xi) * d =
      (g * (19 / 365 : ℝ) ^ 2 * d) / xi by ring]
    apply (le_div_iff₀ xi_pos).2
    have hsqScaled := mul_le_mul_of_nonneg_left hHsq hg.le
    nlinarith
  have hxiD : xi ≤ g * (19 / 365 : ℝ) * d := by
    simpa [mul_assoc] using hgH.trans (mul_le_mul_of_nonneg_left hHd hg.le)
  have hterm2 : (d.choose 2 : ℝ) * H / (d * m) ≤
      g * (19 / 365) / (200 * xi) := by
    calc
      (d.choose 2 : ℝ) * H / (d * m) = ((d.choose 2 : ℝ) / m) * H / d := by ring
      _ ≤ (1 / (200 * H)) * H / d := by gcongr
      _ = 1 / (200 * d) := by field_simp
      _ ≤ g * (19 / 365) / (200 * xi) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 200 * d)
          (by norm_num [xi] : (0 : ℝ) < 200 * xi)).2
        nlinarith
  have hlowerCoeff :
      (19 / 365 : ℝ) ^ 2 / xi + (19 / 365) / (200 * xi) ≤
        (2 / 1000) * residualFraction := by
    norm_num [xi, residualFraction, theta]
  have hlowerNormalized : H / d + (d.choose 2 : ℝ) * H / (d * m) ≤
      (2 / 1000) * residualFraction * g := by
    have hscale := mul_le_mul_of_nonneg_left hlowerCoeff hg.le
    calc
      H / d + (d.choose 2 : ℝ) * H / (d * m) ≤
          g * (19 / 365 : ℝ) ^ 2 / xi + g * (19 / 365) / (200 * xi) :=
        add_le_add hterm1 hterm2
      _ = g * ((19 / 365 : ℝ) ^ 2 / xi + (19 / 365) / (200 * xi)) := by ring
      _ ≤ g * ((2 / 1000) * residualFraction) := hscale
      _ = (2 / 1000) * residualFraction * g := by ring
  have hlower : (m : ℝ) * H / d + d.choose 2 * H / d ≤
      (2 / 1000) * residualFraction * g * m := by
    have hscaled := mul_le_mul_of_nonneg_right hlowerNormalized hmR.le
    have e : (H / d + (d.choose 2 : ℝ) * H / (d * m)) * m =
        (m : ℝ) * H / d + d.choose 2 * H / d := by field_simp
    linarith
  have hdTerm : (d : ℝ) ≤ g * m / (270 * H) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 270 * H)).2
    nlinarith
  have hHterm : H / d ≤ g * m / (270 * d ^ 2) := by
    apply (div_le_iff₀ hdR).2
    rw [show (g * m / (270 * d ^ 2)) * d = g * m / (270 * d) by
      field_simp]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 270 * d)).2
    nlinarith [hgm]
  have hgm0 : 0 ≤ g * (m : ℝ) := by positivity
  have hdTerm' : (d : ℝ) ≤ g * m / (270 * (54 / 5)) :=
    hdTerm.trans (div_le_div_of_nonneg_left hgm0 (by norm_num)
      (mul_le_mul_of_nonneg_left hHlower (by norm_num)))
  have hHterm' : H / d ≤ g * m / (270 * (48000 : ℝ) ^ 2) := by
    apply hHterm.trans
    apply div_le_div_of_nonneg_left hgm0 (by positivity)
    have hdcast : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hupperCoeff :
      1 / (270 * (54 / 5 : ℝ)) + 1 / (270 * (48000 : ℝ) ^ 2) ≤
        (1 / 1000) * residualFraction := by
    norm_num [residualFraction, theta]
  have hupperScaled := mul_le_mul_of_nonneg_left hupperCoeff hgm0
  have hupper : (d : ℝ) + H / d ≤
      (1 / 1000) * residualFraction * g * m := by
    calc
      (d : ℝ) + H / d ≤ g * m / (270 * (54 / 5)) +
          g * m / (270 * (48000 : ℝ) ^ 2) := add_le_add hdTerm' hHterm'
      _ = (g * m) * (1 / (270 * (54 / 5)) +
          1 / (270 * (48000 : ℝ) ^ 2)) := by ring
      _ ≤ (g * m) * ((1 / 1000) * residualFraction) := hupperScaled
      _ = (1 / 1000) * residualFraction * g * m := by ring
  have hHoverD : H / d ≤ (19 / 365 : ℝ) / 219 := by
    calc
      H / d ≤ ((19 / 365 : ℝ) * Real.sqrt d) / d :=
        div_le_div_of_nonneg_right hHupper hdR.le
      _ = (19 / 365 : ℝ) / Real.sqrt d := by
        field_simp [hsqrt.ne', hdR.ne']
        nlinarith only [hsqrtSq]
      _ ≤ (19 / 365 : ℝ) / 219 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrtLower
  have hBterm : (d.choose 2 : ℝ) * H / (d * m) ≤ 1 / (200 * d) := by
    calc
      _ = ((d.choose 2 : ℝ) / m) * H / d := by ring
      _ ≤ (1 / (200 * H)) * H / d := by gcongr
      _ = 1 / (200 * d) := by field_simp
  have hBterm' : (d.choose 2 : ℝ) * H / (d * m) ≤ 1 / (200 * 48000) := by
    apply hBterm.trans
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 200 * 48000)
    have hdcast : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    exact mul_le_mul_of_nonneg_left hdcast (by norm_num)
  have hradiusNormalized : H / d + (d.choose 2 : ℝ) * H / (d * m) ≤
      (1 / 1000) * (1 + theta * g) := by
    have hθg : 0 ≤ theta * g := mul_nonneg theta_pos.le hg.le
    have hc : (19 / 365 : ℝ) / 219 + 1 / (200 * 48000) ≤ 1 / 1000 := by norm_num
    nlinarith
  have hradius : (m : ℝ) + d.choose 2 ≤
      (1 / 1000) * ((1 + theta * g) * d * m / H) := by
    calc
      (m : ℝ) + d.choose 2 =
          (H / d + (d.choose 2 : ℝ) * H / (d * m)) * (d * m / H) := by
        field_simp
      _ ≤ ((1 / 1000) * (1 + theta * g)) * (d * m / H) := by
        gcongr
      _ = (1 / 1000) * ((1 + theta * g) * d * m / H) := by ring
  exact ⟨hlower, hupper, hradius⟩

/-- If `a / (g H) ≤ 1 / ξ`, a radius bound `W' / d ≤ (a m / H) c` becomes the normalized bound
`W' / d ≤ g m / ξ · c`, since `a m / H = (a / (g H)) (g m)`. The hypotheses `0 ≤ m`, `0 < g` and
`0 ≤ c` make the rescaling monotone. -/
theorem enlargedRadius_normalized (d m W' a g H ξ c : ℝ) (hm : 0 ≤ m) (hg : 0 < g)
    (hH : 0 < H) (hc : 0 ≤ c) (hradius : W' / d ≤ (a * m / H) * c)
    (ha : a / (g * H) ≤ 1 / ξ) :
    W' / d ≤ g * m / ξ * c := by
  calc
    W' / d ≤ (a * m / H) * c := hradius
    _ = ((a / (g * H)) * (g * m)) * c := by field_simp
    _ ≤ ((1 / ξ) * (g * m)) * c := by gcongr
    _ = g * m / ξ * c := by ring

/-- The dimensionless mean-variance expression of the prescribed constants is at most `448 / 625`:
`(5 / 8) (1001 / 1000) + (329 / 200) (1001 / 1000) ^ 2 / (4 (5 / 8) (998 / 1000) ξ ^ 2) + 1 / 2000
≤ 448 / 625` with `ξ = 27 / 10`. -/
theorem averageResidualError_le :
    residualFraction * (1001 / 1000) +
        (329 / 200) * (1001 / 1000) ^ 2 /
          (4 * residualFraction * (998 / 1000) * xi ^ 2) +
        1 / 2000 ≤ (448 / 625 : ℝ) := by
  norm_num [residualFraction, theta, xi]

/-- A normalized radius bound gives the variance bound: if `W' / d ≤ q / ξ · c` with `d > 0`,
`W' ≥ 0`, and `0 ≤ H₂ ≤ h`, then `W' ^ 2 H₂ / (d (d + 1)) ≤ q ^ 2 c ^ 2 / ξ ^ 2 · h`. The
denominator `d (d + 1)` is at least `d ^ 2`. -/
theorem residualVariance_le (d W' H2 q ξ c h : ℝ)
    (hd : 0 < d) (hW' : 0 ≤ W') (hH2 : 0 ≤ H2)
    (hradius : W' / d ≤ q / ξ * c) (hH2max : H2 ≤ h) :
    W' ^ 2 * H2 / (d * (d + 1)) ≤ q ^ 2 * c ^ 2 / ξ ^ 2 * h := by
  have hdp : 0 < d + 1 := by linarith
  have hratio0 : 0 ≤ W' / d := div_nonneg hW' hd.le
  have hsq : W' ^ 2 / (d * (d + 1)) ≤ (W' / d) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg W') (by positivity) (by nlinarith)
  calc
    W' ^ 2 * H2 / (d * (d + 1)) =
        (W' ^ 2 / (d * (d + 1))) * H2 := by ring
    _ ≤ (W' / d) ^ 2 * H2 := by gcongr
    _ ≤ (q / ξ * c) ^ 2 * H2 := by gcongr
    _ ≤ (q / ξ * c) ^ 2 * h := by gcongr
    _ = q ^ 2 * c ^ 2 / ξ ^ 2 * h := by ring

/-- The scalar combination of the mean gap and the variance. If
`(5 / 8) q (998 / 1000) ≤ gap ≤ (5 / 8) q (1001 / 1000)`, the variance is at most
`q ^ 2 (1001 / 1000) ^ 2 / ξ ^ 2 · (329 / 200)` and `q ≥ 2000`, then `gap > 0` and
`gap + variance / (4 gap) + 1 ≤ q (448 / 625)`. The lower bound on the gap controls the division,
and `q ≥ 2000` absorbs the lattice-counting unit `1 ≤ q / 2000`. -/
theorem residualMeanVariance_le (gap variance q : ℝ)
    (hq : 0 < q)
    (hlower : residualFraction * q * (998 / 1000) ≤ gap)
    (hupper : gap ≤ residualFraction * q * (1001 / 1000))
    (hvariance : variance ≤
      q ^ 2 * (1001 / 1000) ^ 2 / xi ^ 2 * (329 / 200))
    (hunit : 2000 ≤ q) :
    0 < gap ∧ gap + variance / (4 * gap) + 1 ≤ q * (448 / 625) := by
  have hgap : 0 < gap := by
    have : 0 < residualFraction * q * (998 / 1000) := by
      norm_num [residualFraction, theta]
      positivity
    exact this.trans_le hlower
  have hvarCorrection : variance / (4 * gap) ≤
      q * ((329 / 200) * (1001 / 1000) ^ 2 /
        (4 * residualFraction * (998 / 1000) * xi ^ 2)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hgap)).2
    have hc : 0 < (329 / 200 : ℝ) * (1001 / 1000) ^ 2 /
        (4 * residualFraction * (998 / 1000) * xi ^ 2) := by
      norm_num [residualFraction, theta, xi]
    have hmul := mul_le_mul_of_nonneg_left hlower hc.le
    norm_num [residualFraction, theta, xi] at hvariance hmul ⊢
    nlinarith
  have hunit' : 1 ≤ q * (1 / 2000) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left averageResidualError_le hq.le
  refine ⟨hgap, ?_⟩
  nlinarith

/-- The per-fiber bound consumed by the weighted local-rank theorem. With `θ = 3 / 8`,
`ξ = 27 / 10`, `W = ⌊(1 + θ g) d m / H⌋₊` and a contact residual `r < m`, let
`gap = m (1 + g) + (d - 1) - (W + r + d.choose 2) H / d` and
`variance = (W + r + d.choose 2) ^ 2 H₂ / (d (d + 1))`. Under the hypotheses of
`centeringErrorBounds`, `(1 + θ g) / (g H) ≤ 1 / ξ` and `0 ≤ H₂ ≤ 329 / 200`: `0 < gap` and
`gap + variance / (4 gap) + 1 ≤ g m (448 / 625)`. -/
theorem prescribedFiberMeanVariance_le (d m r W : ℕ) (g H H2 : ℝ)
    (hd : 48000 ≤ d) (hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hHlower : 54 / 5 ≤ H)
    (hHupper : H ≤ (19 / 365) * Real.sqrt d)
    (hgH : xi ≤ g * H)
    (hnormalized : (1 + theta * g) / (g * H) ≤ 1 / xi)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m)
    (hgm : 270 * d * H ≤ g * m)
    (hW : W = ⌊(1 + theta * g) * d * m / H⌋₊)
    (hH2 : 0 ≤ H2) (hH2max : H2 ≤ 329 / 200) :
    let gap : ℝ := (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
      (W + r + d.choose 2 : ℕ) * H / d
    let variance : ℝ := ((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * H2 /
      (d * (d + 1))
    0 < gap ∧ gap + variance / (4 * gap) + 1 ≤ g * m * (448 / 625) := by
  intro gap variance
  have hd0 : 0 < d := by omega
  have ha : 0 ≤ 1 + theta * g := by have := theta_pos; positivity
  obtain ⟨herr1, herr2, herr3⟩ :=
    centeringErrorBounds d m g H hd hm hg hH hHlower hHupper hgH hsize hgm
  have hlower := remainingDegree_lower theta (2 / 1000) g H d m r W hr ha hH.le hW herr1
  have hupper := remainingDegree_upper theta (1 / 1000) g H d m r W hd0 hH hW herr2
  have hradius := enlargedRadius_upper theta (1 / 1000) g H d m r W hd0 hr ha hH hW herr3
  have hradius' := enlargedRadius_normalized (d : ℝ) (m : ℝ)
    ((W + r + d.choose 2 : ℕ) : ℝ) (1 + theta * g) g H xi (1 + 1 / 1000) (by positivity) hg hH
    (by norm_num) hradius hnormalized
  have hvariance := residualVariance_le (d : ℝ) ((W + r + d.choose 2 : ℕ) : ℝ) H2 (g * m) xi
    (1 + 1 / 1000) (329 / 200) (by exact_mod_cast hd0) (by positivity) hH2
    (by simpa [mul_assoc] using hradius') hH2max
  have hunit : (2000 : ℝ) ≤ g * m := by
    have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    have hHd : 0 ≤ (d : ℝ) * H := by positivity
    nlinarith
  refine residualMeanVariance_le gap variance (g * m) (by positivity) ?_ ?_ ?_ hunit
  · have e : residualFraction * (g * m) * (998 / 1000) = (1 - theta) * g * m * (1 - 2 / 1000) := by
      rw [residualFraction]; ring
    rw [e]; exact hlower
  · have e : residualFraction * (g * m) * (1001 / 1000) = (1 - theta) * g * m * (1 + 1 / 1000) := by
      rw [residualFraction]; ring
    rw [e]; exact hupper
  · have e : (g * m) ^ 2 * (1001 / 1000 : ℝ) ^ 2 / xi ^ 2 * (329 / 200) =
        (g * m) ^ 2 * (1 + 1 / 1000) ^ 2 / xi ^ 2 * (329 / 200) := by norm_num
    rw [e]; exact hvariance

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
