/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters

/-!
# Rounding and centering constants for the no-band support

The local-rank integral uses a simplex enlarged by `choose d 2`.  This file keeps the three
rounding errors separate: a two-thousandth lower centering loss, a one-thousandth upper
centering loss, and a one-thousandth radius enlargement.  Their only joint use is the exact
`448 / 625` mean-variance constant.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

noncomputable section

/-- The prescribed radius is positive once its unrounded value is at least one. -/
theorem floorRadius_pos (a H : ℝ) (d m : ℕ) (hR : 1 ≤ a * d * m / H) :
    0 < Nat.floor (a * d * m / H) :=
  Nat.floor_pos.mpr hR

/-- Flooring gives the exact upper bound on the simplex mean. -/
theorem floorRadius_mul_div_le (a H : ℝ) (d m : ℕ)
    (ha : 0 ≤ a) (hH : 0 < H) (hd : 0 < d)
    (W : ℕ) (hW : W = Nat.floor (a * d * m / H)) :
    (W : ℝ) * H / d ≤ a * m := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hraw : 0 ≤ a * (d : ℝ) * m / H := by positivity
  have hf : (W : ℝ) ≤ a * d * m / H := by
    rw [hW]
    exact Nat.floor_le hraw
  have := mul_le_mul_of_nonneg_right hf hH.le
  field_simp [hdR.ne', hH.ne'] at this ⊢
  nlinarith

/-- The normalized floored radius is at most its unrounded counterpart. -/
theorem floorRadius_normalized_le (a g H : ℝ) (d m W : ℕ)
    (ha : 0 ≤ a) (hg : 0 < g) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m)
    (hW : W = Nat.floor (a * d * m / H)) :
    (W : ℝ) / (d * g * m) ≤ a / (g * H) := by
  have hmean := floorRadius_mul_div_le a H d m ha hH hd W hW
  have hden : 0 < (d : ℝ) * g * m := by positivity
  apply (div_le_iff₀ hden).2
  field_simp [hH.ne'] at hmean ⊢
  nlinarith

/-- Flooring the prescribed radius loses less than one unit.  Once the unrounded radius is at
least `2000`, its squared normalized value retains the factor `999/1000` used by the dimension
comparison. -/
theorem floorRadius_sq_ge (a g H : ℝ) (d m : ℕ)
    (ha : 0 < a) (hg : 0 < g) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m)
    (hR : 2000 ≤ a * d * m / H) :
    (999 / 1000) * (a / (g * H)) ^ 2 ≤
      ((Nat.floor (a * d * m / H) : ℝ) / (d * g * m)) ^ 2 := by
  let R := a * (d : ℝ) * m / H
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hR' : 2000 ≤ R := by simpa [R] using hR
  have hden : 0 < (d : ℝ) * g * m := by positivity
  have hfloor := Nat.sub_one_lt_floor R
  have hfloorRatio : (1999 / 2000 : ℝ) * R < Nat.floor R := by
    have : R / 2000 ≥ 1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2000)).2
      (by simpa using hR')
    nlinarith
  have hnorm : (1999 / 2000 : ℝ) * (a / (g * H)) <
      (Nat.floor R : ℝ) / ((d : ℝ) * g * m) := by
    apply (lt_div_iff₀ hden).2
    have hid : (a / (g * H)) * ((d : ℝ) * g * m) = R := by
      dsimp [R]
      field_simp
    rw [mul_assoc, hid]
    exact hfloorRatio
  have hleft : 0 ≤ (1999 / 2000 : ℝ) * (a / (g * H)) := by positivity
  have hsquare := pow_le_pow_left₀ hleft hnorm.le 2
  have hconstant : (999 / 1000 : ℝ) ≤ (1999 / 2000) ^ 2 := by norm_num
  calc
    (999 / 1000) * (a / (g * H)) ^ 2 ≤
        (1999 / 2000) ^ 2 * (a / (g * H)) ^ 2 := by gcongr
    _ = ((1999 / 2000) * (a / (g * H))) ^ 2 := by ring
    _ ≤ _ := hsquare

/-- The floor and the upper end `r < m` leave at least `99.8%` of the nominal residual degree.
The displayed error premise is the two rounding terms before normalization. -/
theorem remainingDegree_lower (d m r W : ℕ) (g H : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (m : ℝ) * H / d + d.choose 2 * H / d ≤
      (2 / 1000) * residualFraction * g * m) :
    residualFraction * g * m * (998 / 1000) ≤
      (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
        (W + r + d.choose 2 : ℕ) * H / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < 1 + theta * g :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg theta_pos.le hg.le)
  have hraw : 0 ≤ (1 + theta * g) * (d : ℝ) * m / H := by positivity
  have hfloor : (W : ℝ) ≤ (1 + theta * g) * d * m / H := by
    rw [hW]
    exact Nat.floor_le hraw
  have hrR : (r : ℝ) ≤ (m : ℝ) - 1 := by
    have hr1 : r + 1 ≤ m := by omega
    have hr1R : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr1
    linarith
  have hmu : ((W + r + d.choose 2 : ℕ) : ℝ) * H / d ≤
      (1 + theta * g) * m + (m - 1) * H / d + d.choose 2 * H / d := by
    push_cast
    have := mul_le_mul_of_nonneg_right hfloor hH.le
    field_simp [hdR.ne', hH.ne'] at this ⊢
    nlinarith
  have hmu' : ((W + r + d.choose 2 : ℕ) : ℝ) * H / d ≤
      (1 + theta * g) * m + (m : ℝ) * H / d + d.choose 2 * H / d := by
    refine hmu.trans ?_
    have hterm : ((m : ℝ) - 1) * H / d ≤ (m : ℝ) * H / d := by
      gcongr
      linarith
    linarith
  have hresidual : (m : ℝ) * (1 + g) - (1 + theta * g) * m =
      residualFraction * g * m := by
    norm_num [theta, residualFraction]
    ring
  have hdsub : (0 : ℝ) ≤ (d - 1 : ℕ) := by positivity
  norm_num [residualFraction] at herror ⊢
  norm_num [residualFraction] at hresidual
  push_cast at hmu' ⊢
  nlinarith

/-- The opposite floor error raises the residual degree by at most one thousandth. -/
theorem remainingDegree_upper (d m r W : ℕ) (g H : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (d : ℝ) + H / d ≤
      (1 / 1000) * residualFraction * g * m) :
    (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
        (W + r + d.choose 2 : ℕ) * H / d ≤
      residualFraction * g * m * (1001 / 1000) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < 1 + theta * g :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg theta_pos.le hg.le)
  have hraw : 0 ≤ (1 + theta * g) * (d : ℝ) * m / H := by positivity
  have hfloor := Nat.sub_one_lt_floor ((1 + theta * g) * (d : ℝ) * m / H)
  rw [← hW] at hfloor
  have hmu : (1 + theta * g) * m - H / d <
      ((W + r + d.choose 2 : ℕ) : ℝ) * H / d := by
    push_cast
    have hscaled := mul_lt_mul_of_pos_right hfloor (div_pos hH hdR)
    field_simp [hdR.ne', hH.ne'] at hscaled ⊢
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hB0 : (0 : ℝ) ≤ d.choose 2 := Nat.cast_nonneg _
    nlinarith
  have hresidual : (m : ℝ) * (1 + g) - (1 + theta * g) * m =
      residualFraction * g * m := by
    norm_num [theta, residualFraction]
    ring
  have hdsub : ((d - 1 : ℕ) : ℝ) ≤ d := by
    exact_mod_cast Nat.sub_le d 1
  norm_num [residualFraction] at herror ⊢
  norm_num [residualFraction] at hresidual
  push_cast at hmu ⊢
  nlinarith

/-- The upper floor bound and `r < m` enlarge the simplex radius by at most one thousandth.
The premise is the unnormalized contribution of the two additive enlargements. -/
theorem enlargedRadius_upper (d m r W : ℕ) (g H : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (herror : (m : ℝ) + d.choose 2 ≤
      (1 / 1000) * ((1 + theta * g) * d * m / H)) :
    ((W + r + d.choose 2 : ℕ) : ℝ) / d ≤
      ((1 + theta * g) * m / H) * (1001 / 1000) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 0 < 1 + theta * g :=
    add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg theta_pos.le hg.le)
  have hraw : 0 ≤ (1 + theta * g) * (d : ℝ) * m / H := by positivity
  have hfloor : (W : ℝ) ≤ (1 + theta * g) * d * m / H := by
    rw [hW]
    exact Nat.floor_le hraw
  have hrR : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  have hsum : ((W + r + d.choose 2 : ℕ) : ℝ) ≤
      ((1 + theta * g) * d * m / H) * (1001 / 1000) := by
    push_cast
    nlinarith [hfloor, hrR, herror]
  calc
    ((W + r + d.choose 2 : ℕ) : ℝ) / d ≤
        (((1 + theta * g) * d * m / H) * (1001 / 1000)) / d :=
      div_le_div_of_nonneg_right hsum hdR.le
    _ = ((1 + theta * g) * m / H) * (1001 / 1000) := by
      field_simp

/-- The finite prescribed bounds imply all three additive error estimates used by the floor
and enlarged-simplex comparisons.  The harmonic hypotheses are the already audited consequences
of `d ≥ 48000`; no conclusion is repeated as an assumption. -/
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
    norm_num [xi, residualFraction]
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
    field_simp [hmR.ne'] at hscaled ⊢
    nlinarith
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
    norm_num [residualFraction]
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
  have hradiusCoeff : (19 / 365 : ℝ) / 219 + 1 / (200 * 48000) ≤ 1 / 1000 := by
    norm_num
  have hradiusNormalized : H / d + (d.choose 2 : ℝ) * H / (d * m) ≤
      (1 / 1000) * (1 + theta * g) := by
    have haone : (1 : ℝ) ≤ 1 + theta * g :=
      le_add_of_nonneg_right (mul_nonneg theta_pos.le hg.le)
    calc
      H / d + (d.choose 2 : ℝ) * H / (d * m) ≤
          (19 / 365 : ℝ) / 219 + 1 / (200 * 48000) :=
        add_le_add hHoverD hBterm'
      _ ≤ 1 / 1000 := hradiusCoeff
      _ ≤ (1 / 1000) * (1 + theta * g) := by
        have hs := mul_le_mul_of_nonneg_left haone
          (show (0 : ℝ) ≤ 1 / 1000 by norm_num)
        simpa using hs
  have hradius : (m : ℝ) + d.choose 2 ≤
      (1 / 1000) * ((1 + theta * g) * d * m / H) := by
    calc
      (m : ℝ) + d.choose 2 =
          (H / d + (d.choose 2 : ℝ) * H / (d * m)) * (d * m / H) := by
        field_simp [hdR.ne', hmR.ne', hH.ne']
      _ ≤ ((1 / 1000) * (1 + theta * g)) * (d * m / H) := by
        gcongr
      _ = (1 / 1000) * ((1 + theta * g) * d * m / H) := by ring
  exact ⟨hlower, hupper, hradius⟩

/-- Replacing `a/(gH)` by its prescribed upper bound converts the radius estimate into the
normalization expected by the variance calculation. -/
theorem enlargedRadius_normalized (d m W' : ℝ) (g H : ℝ)
    (_hd : 0 < d) (hm : 0 ≤ m) (hg : 0 < g) (hH : 0 < H)
    (hradius : W' / d ≤ ((1 + theta * g) * m / H) * (1001 / 1000))
    (ha : (1 + theta * g) / (g * H) ≤ 1 / xi) :
    W' / d ≤ g * m / xi * (1001 / 1000) := by
  calc
    W' / d ≤ ((1 + theta * g) * m / H) * (1001 / 1000) := hradius
    _ = (((1 + theta * g) / (g * H)) * (g * m)) * (1001 / 1000) := by
      field_simp
    _ ≤ ((1 / xi) * (g * m)) * (1001 / 1000) := by gcongr
    _ = g * m / xi * (1001 / 1000) := by ring

/-- The exact dimensionless mean-variance expression is at most `448/625`. -/
theorem averageResidualError_le :
    residualFraction * (1001 / 1000) +
        (329 / 200) * (1001 / 1000) ^ 2 /
          (4 * residualFraction * (998 / 1000) * xi ^ 2) +
        1 / 2000 ≤ (448 / 625 : ℝ) := by
  norm_num [residualFraction, xi]

/-- A normalized radius bound gives the variance estimate used by the local-rank integral. -/
theorem residualVariance_le (d W' H2 q : ℝ)
    (hd : 0 < d) (hW' : 0 ≤ W') (hH2 : 0 ≤ H2) (_hq : 0 ≤ q)
    (hradius : W' / d ≤ q / xi * (1001 / 1000))
    (hH2max : H2 ≤ 329 / 200) :
    W' ^ 2 * H2 / (d * (d + 1)) ≤
      q ^ 2 * (1001 / 1000) ^ 2 / xi ^ 2 * (329 / 200) := by
  have hdp : 0 < d + 1 := by linarith
  have hratio0 : 0 ≤ W' / d := div_nonneg hW' hd.le
  have hratioSq := pow_le_pow_left₀ hratio0 hradius 2
  have hsq : W' ^ 2 / (d * (d + 1)) ≤ (W' / d) ^ 2 := by
    apply (div_le_iff₀ (mul_pos hd hdp)).2
    field_simp [hd.ne']
    nlinarith [sq_nonneg W']
  calc
    W' ^ 2 * H2 / (d * (d + 1)) =
        (W' ^ 2 / (d * (d + 1))) * H2 := by ring
    _ ≤ (W' / d) ^ 2 * H2 := by gcongr
    _ ≤ (q / xi * (1001 / 1000)) ^ 2 * H2 := by gcongr
    _ ≤ (q / xi * (1001 / 1000)) ^ 2 * (329 / 200) := by gcongr
    _ = q ^ 2 * (1001 / 1000) ^ 2 / xi ^ 2 * (329 / 200) := by ring

/-- The compiled scalar seam for the rank integral.  Given the three independently audited
centering/radius estimates, it supplies positivity of the mean gap and its full positive-part
bound, including the extra lattice-counting unit. -/
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
      norm_num [residualFraction]
      positivity
    exact this.trans_le hlower
  have hvarCorrection : variance / (4 * gap) ≤
      q * ((329 / 200) * (1001 / 1000) ^ 2 /
        (4 * residualFraction * (998 / 1000) * xi ^ 2)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hgap)).2
    have hc : 0 < (329 / 200 : ℝ) * (1001 / 1000) ^ 2 /
        (4 * residualFraction * (998 / 1000) * xi ^ 2) := by
      norm_num [residualFraction, xi]
    have hmul := mul_le_mul_of_nonneg_left hlower hc.le
    norm_num [residualFraction, xi] at hvariance hmul ⊢
    nlinarith
  have hunit' : 1 ≤ q * (1 / 2000) := by nlinarith
  have hscalar := averageResidualError_le
  have hqnonneg : 0 ≤ q := hq.le
  have hscaled := mul_le_mul_of_nonneg_left hscalar hqnonneg
  constructor
  · exact hgap
  · nlinarith

/-- The per-fiber scalar package consumed by the weighted local-rank theorem.  It derives both
the strict mean gap and the exact `448/625` positive-part bound from the prescribed floor,
harmonic, multiplicity, and rate estimates. -/
theorem prescribedFiberMeanVariance_le (d m r W : ℕ) (g H H2 : ℝ)
    (hd : 48000 ≤ d) (hm : 0 < m) (hr : r < m) (hg : 0 < g) (hH : 0 < H)
    (hHlower : 54 / 5 ≤ H)
    (hHupper : H ≤ (19 / 365) * Real.sqrt d)
    (hgH : xi ≤ g * H)
    (hnormalized : (1 + theta * g) / (g * H) ≤ 1 / xi)
    (hsize : 100 * (d : ℝ) ^ 2 * H ≤ m)
    (hgm : 270 * d * H ≤ g * m)
    (hW : W = Nat.floor ((1 + theta * g) * d * m / H))
    (hH2 : 0 ≤ H2) (hH2max : H2 ≤ 329 / 200) :
    let gap : ℝ := (m : ℝ) * (1 + g) + (d - 1 : ℕ) -
      (W + r + d.choose 2 : ℕ) * H / d
    let variance : ℝ := ((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * H2 /
      (d * (d + 1))
    0 < gap ∧ gap + variance / (4 * gap) + 1 ≤ g * m * (448 / 625) := by
  dsimp only
  have hd0 : 0 < d := by omega
  have herr := centeringErrorBounds d m g H hd hm hg hH hHlower hHupper hgH hsize hgm
  have hlower := remainingDegree_lower d m r W g H hd0 hm hr hg hH hW herr.1
  have hupper := remainingDegree_upper d m r W g H hd0 hm hg hH hW herr.2.1
  have hradius := enlargedRadius_upper d m r W g H hd0 hm hr hg hH hW herr.2.2
  have hradius' := enlargedRadius_normalized (d : ℝ) (m : ℝ)
    ((W + r + d.choose 2 : ℕ) : ℝ) g H (by exact_mod_cast hd0)
    (by positivity) hg hH hradius hnormalized
  have hvariance := residualVariance_le (d : ℝ)
    ((W + r + d.choose 2 : ℕ) : ℝ) H2 (g * m)
    (by exact_mod_cast hd0) (by positivity) hH2 (by positivity) hradius' hH2max
  have hunit : (2000 : ℝ) ≤ g * m := by
    have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  exact residualMeanVariance_le _ _ (g * m) (by positivity)
    (by simpa [mul_assoc] using hlower) (by simpa [mul_assoc] using hupper)
    (by simpa [mul_assoc] using hvariance) hunit

end

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
