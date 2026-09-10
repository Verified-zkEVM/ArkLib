/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.RankBound
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.RankRounding
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Rounding
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.EndpointComparison

/-!
# Volume-normalized rank for the no-band weighted support

The inner weighted residual count is bounded by its enlarged-simplex expectation.  Uniform
per-fiber error bounds then feed the exact contact-dependent geometric sum.  This file keeps the
mean error, the `+1` ceiling charge, the triangular enlargement, and both reciprocal geometric
terms visible through the normalization.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory SimplexIntegration

namespace ReedSolomon.HiddenDerivative

noncomputable section

/-- A uniform harmonic error estimate for each contact fiber gives the absolute geometric rank
budget. -/
theorem localResidualCoordinateBudget_le_weighted_integral_geometric
    (d m W : ℕ) (T g Ee : ℝ) (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        T + (d - 1 : ℕ))
    (herror : ∀ r ∈ Finset.range m,
      (T + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((T + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * Ee) :
    (localResidualCoordinateBudget d m W T : ℝ) ≤
      (g * m * Ee) *
        ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
          Real.exp ((((d - 1 : ℕ) : ℝ) / W) * (m + d.choose 2)) *
            (1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) +
              1 / (((d - 1 : ℕ) : ℝ) / W)) := by
  let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
  let x : ℝ := ((d - 1 : ℕ) : ℝ) / W
  have hx : 0 < x := by
    dsimp [x]
    exact div_pos (by exact_mod_cast (by omega : 0 < d - 1)) (by exact_mod_cast hW)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact div_nonneg (pow_nonneg (Nat.cast_nonneg W) _) (sq_nonneg _)
  have hB : 0 ≤ g * m * Ee := by positivity
  apply localResidualCoordinateBudget_le_geometric d m W T (g * m * Ee) V x
    (d.choose 2) (by omega) hx hB hV
  intro r hr
  have hinner0 := weighted_residual_sum_le_volume_mul_harmonic_variance
    d (W + r) T (by omega) (by positivity) (by simpa using hgap r hr)
  have hinner :
      (∑ z ∈ weightedHigherJetTuples d (W + r),
          (max (T - higherJetTupleDegree z) 0 + 1)) ≤
        volume.real (weightedSimplex (d - 1) ((W + r + d.choose 2 : ℕ) : ℝ)) *
          ((T + (d - 1 : ℕ)) -
              ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
            (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
                (d * (d + 1))) /
              (4 * ((T + (d - 1 : ℕ)) -
                ((W + r + d.choose 2 : ℕ) : ℝ) *
                  harmonicPowerSum (d - 1) 1 / d)) + 1) := by
    simpa only [Nat.cast_add] using hinner0
  have herr := herror r hr
  have hvolnonneg :
      0 ≤ volume.real (weightedSimplex (d - 1) ((W + r + d.choose 2 : ℕ) : ℝ)) :=
    MeasureTheory.measureReal_nonneg
  have hinner' :
      (∑ z ∈ weightedHigherJetTuples d (W + r),
          (max (T - higherJetTupleDegree z) 0 + 1)) ≤
        volume.real (weightedSimplex (d - 1) ((W + r + d.choose 2 : ℕ) : ℝ)) *
          (g * m * Ee) := by
    exact hinner.trans (mul_le_mul_of_nonneg_left herr hvolnonneg)
  have hvolume0 := volume_weightedSimplex_add_choose_le_exp d W r hW
  have hvolume :
      volume.real (weightedSimplex (d - 1) ((W + r + d.choose 2 : ℕ) : ℝ)) ≤
        V * Real.exp (x * (r + d.choose 2)) := by
    simpa only [Nat.cast_add, V, x] using hvolume0
  have hscale := mul_le_mul_of_nonneg_right hvolume hB
  simpa [V, x, mul_assoc, mul_left_comm, mul_comm] using hinner'.trans hscale

/-- The preceding absolute estimate divided by the baseline volume and `m³`. -/
theorem localResidualCoordinateBudget_div_volume_mul_cube_le
    (d m W : ℕ) (T g Ee : ℝ) (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        T + (d - 1 : ℕ))
    (herror : ∀ r ∈ Finset.range m,
      (T + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((T + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * Ee) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (localResidualCoordinateBudget d m W T : ℝ) / (V * m ^ 3) ≤
      g * Ee * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  dsimp only
  have h := localResidualCoordinateBudget_le_weighted_integral_geometric
    d m W T g Ee hd hm hW hg hEe hgap herror
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hWR : (W : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hpred : (((d - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (by omega : d - 1 ≠ 0)
  have hVpos : 0 < (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 := by positivity
  apply (div_le_div_of_nonneg_right h (mul_nonneg hVpos.le (by positivity))).trans_eq
  field_simp

/-- The actual local map inherits the normalized residual-coordinate estimate. -/
theorem finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
    {F : Type*} [Field F] (d D m W : ℕ) (L g Ee : ℝ)
    (hd : 2 ≤ d) (hD : 0 < D) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        L / D + (d - 1 : ℕ))
    (herror : ∀ r ∈ Finset.range m,
      (L / D + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((L / D + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * Ee)
    (center received : F) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) ≤
      g * Ee * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  dsimp only
  have hrank := finrank_weightedSupportLocalConstraint_le
    (d := d) (m := m) (W := W) (L := L) (by omega) hD center received
  have hcast : (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) ≤ localResidualCoordinateBudget d m W (L / D) := by
    exact_mod_cast hrank
  exact (div_le_div_of_nonneg_right hcast (by positivity)).trans
    (localResidualCoordinateBudget_div_volume_mul_cube_le
      d m W (L / D) g Ee hd hm hW hg hEe hgap herror)

/-- The common rounding and exponential estimates promote the normalized geometric bound to the
strict constant used by the prescribed weighted support.  The theorem is stated for an arbitrary
nonnegative fiber constant `Ee`; clients discharge `Ee ≤ 448 / 625` from the scalar parameter
calculation. -/
theorem normalized_rank_lt_of_rounding_bounds
    (R g Ee a H E κ : ℝ) (d m : ℕ)
    (hg : 0 < g) (hEe : Ee ≤ 448 / 625)
    (ha : 1 ≤ a) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m) (hκ : 0 < κ)
    (hHlog : H ≤ Real.log d + 3 / 5) (hE : E ≤ H / a + 1 / 100)
    (hrec : 1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤
      101 / 100 * (1 / (H / a) ^ 2))
    (hR : R ≤ g * Ee * Real.exp E *
      (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ))) :
    R < g * (448 / 625) * (101 / 100) * (37 / 20) *
      a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hrec0 : 0 ≤ 1 / κ ^ 2 + (d : ℝ) / (m * κ) := by positivity
  have hfactor :
      1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ) =
        (1 / κ ^ 2 + (d : ℝ) / (m * κ)) / d := by
    field_simp
  have hrec' : 1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤
      101 / 100 * (a ^ 2 / H ^ 2) := by
    calc
      _ ≤ 101 / 100 * (1 / (H / a) ^ 2) := hrec
      _ = 101 / 100 * (a ^ 2 / H ^ 2) := by
        field_simp
  have hexp : Real.exp E < 37 / 20 * (d : ℝ) ^ (1 / a) := by
    have hbase := InterpolationRounding.exp_le_rpow
      a H E (Real.exp (61 / 100)) d ha hd hHlog hE le_rfl
    have hpow : 0 < (d : ℝ) ^ (1 / a) := Real.rpow_pos_of_pos hdR _
    exact hbase.trans_lt (by
      simpa only [mul_comm] using
        mul_lt_mul_of_pos_right WeightedSupportParameters.endpoint_exp_upper hpow)
  rw [hfactor] at hR
  calc
    R ≤ g * Ee * Real.exp E *
        ((1 / κ ^ 2 + (d : ℝ) / (m * κ)) / d) := hR
    _ ≤ g * (448 / 625) * Real.exp E *
        ((101 / 100 * (a ^ 2 / H ^ 2)) / d) := by
      gcongr
    _ < g * (448 / 625) * (37 / 20 * (d : ℝ) ^ (1 / a)) *
        ((101 / 100 * (a ^ 2 / H ^ 2)) / d) := by
      gcongr
    _ = _ := by ring

/-- The actual local constraint rank satisfies the final strict scalar estimate once the
per-contact harmonic error and the two common rounding inequalities are available. -/
theorem finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding
    {F : Type*} [Field F] (d D m W : ℕ) (L g a H : ℝ)
    (hd : 2 ≤ d) (hD : 0 < D) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 < g) (ha : 1 ≤ a) (hH : 0 < H)
    (hHlog : H ≤ Real.log d + 3 / 5)
    (hgap : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        L / D + (d - 1 : ℕ))
    (herror : ∀ r ∈ Finset.range m,
      (L / D + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((L / D + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) *
              harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * (448 / 625))
    (hκexp : let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
      κ * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + 1 / 100)
    (hκrec : let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
      1 / κ ^ 2 + (d : ℝ) / (m * κ) ≤
        101 / 100 * (1 / (H / a) ^ 2))
    (center received : F) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) *
        a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  dsimp only at hκexp hκrec ⊢
  let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (mul_pos (by exact_mod_cast (by omega : 0 < d - 1))
      (by exact_mod_cast hm)) (by exact_mod_cast hW)
  have hbase :=
    finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
      d D m W L g (448 / 625) hd hD hm hW hg.le (by norm_num) hgap herror
        center received
  exact normalized_rank_lt_of_rounding_bounds
    _ g (448 / 625) a H
      (κ * (1 + (d.choose 2 : ℝ) / m)) κ d m hg le_rfl ha hH
      (by omega) hm hκ hHlog hκexp hκrec hbase

/-- For the prescribed multiplicity and weighted radius, the shared rounding theorem discharges
all geometric-sum parameters.  Only the contactwise harmonic error remains for the scalar
centering module to supply. -/
theorem finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error
    {F : Type*} [Field F] (g H : ℝ) (d D : ℕ)
    (hg : 0 < g) (hH : 0 < H) (hd : 48000 ≤ d) (hD : 0 < D)
    (hHlog : H ≤ Real.log d + 3 / 5)
    (hgap :
      let a := 1 + 3 * g / 8
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      let W := Nat.floor (a * d * m / H)
      ∀ r ∈ Finset.range m,
        ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
          (m : ℝ) * (1 + g) + (d - 1 : ℕ))
    (herror :
      let a := 1 + 3 * g / 8
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      let W := Nat.floor (a * d * m / H)
      ∀ r ∈ Finset.range m,
        ((m : ℝ) * (1 + g) + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
          (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
              (d * (d + 1))) /
            (4 * (((m : ℝ) * (1 + g) + (d - 1 : ℕ)) -
              ((W + r + d.choose 2 : ℕ) : ℝ) *
                harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
          g * m * (448 / 625))
    (center received : F) :
    let a := 1 + 3 * g / 8
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD center received)) : ℝ) /
        (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) *
        a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  dsimp only at hgap herror ⊢
  let a : ℝ := 1 + 3 * g / 8
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  have ha : 1 ≤ a := by
    dsimp [a]
    have : 0 ≤ 3 * g / 8 := by positivity
    linarith
  obtain ⟨hm, hW, _hκ, _hκlo, _hκhi, hκexp, _hκsmall, hκrec⟩ :=
    InterpolationRounding.prescribed_kappa_bounds a H d ha hH (by omega)
  have hLD : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by
    field_simp
  have hgap' : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        ((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ) := by
    simpa only [hLD] using hgap
  have herror' : ∀ r ∈ Finset.range m,
      (((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) *
              harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * (448 / 625) := by
    simpa only [hLD] using herror
  exact finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding
    d D m W ((m : ℝ) * D * (1 + g)) g a H (by omega) hD hm hW hg ha hH hHlog
      hgap' herror' hκexp hκrec center received

/-- The prescribed weighted support has the paper's strict normalized local-rank bound.  The
harmonic and rate hypotheses are scalar consequences of the outer block parameters; the entire
contactwise simplex estimate, including all rounding errors, is discharged here. -/
theorem finrank_weightedSupportLocalConstraint_lt_prescribed
    {F : Type*} [Field F] (g : ℝ) (d D : ℕ)
    (hg : 0 < g) (hd : 48000 ≤ d) (hD : 0 < D)
    (hHlower : let H := harmonicPowerSum (d - 1) 1; 54 / 5 ≤ H)
    (hHlog : let H := harmonicPowerSum (d - 1) 1; H ≤ Real.log d + 3 / 5)
    (hgH : let H := harmonicPowerSum (d - 1) 1;
      WeightedSupportParameters.xi ≤ g * H)
    (hnormalized : let H := harmonicPowerSum (d - 1) 1;
      (1 + WeightedSupportParameters.theta * g) / (g * H) ≤
        1 / WeightedSupportParameters.xi)
    (hgm :
      let H := harmonicPowerSum (d - 1) 1
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      270 * d * H ≤ g * m)
    (center received : F) :
    let H := harmonicPowerSum (d - 1) 1
    let a := 1 + WeightedSupportParameters.theta * g
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD center received)) : ℝ) /
        (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) *
        a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  dsimp only at hHlower hHlog hgH hnormalized hgm ⊢
  let H : ℝ := harmonicPowerSum (d - 1) 1
  let H2 : ℝ := harmonicPowerSum (d - 1) 2
  let a : ℝ := 1 + WeightedSupportParameters.theta * g
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHlower
  have ha : a = 1 + 3 * g / 8 := by
    dsimp [a, WeightedSupportParameters.theta]
    ring
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hsize
  have hm : 0 < m := by exact_mod_cast hmR
  have hHupper : H ≤ (19 / 365) * Real.sqrt d :=
    WeightedSupportParameters.harmonic_le_nineteen_over_365_sqrt
      d H (by exact_mod_cast hd) hHlog
  have hH2 : 0 ≤ H2 := by
    dsimp [H2]
    rw [harmonicPowerSum_eq_range]
    positivity
  have hH2max : H2 ≤ 329 / 200 := by
    dsimp [H2]
    rw [harmonicPowerSum_eq_range]
    exact (Real.reciprocal_square_sum_lt _).le
  have hgap : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        (m : ℝ) * (1 + g) + (d - 1 : ℕ) := by
    intro r hr
    have hf := WeightedSupportParameters.prescribedFiberMeanVariance_le
      d m r W g H H2 hd hm (Finset.mem_range.mp hr) hg hH hHlower hHupper hgH
        hnormalized hsize hgm (by simp only [W, a, ha]) hH2 hH2max
    dsimp only at hf
    linarith [hf.1]
  have herror : ∀ r ∈ Finset.range m,
      ((m : ℝ) * (1 + g) + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * (((m : ℝ) * (1 + g) + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) *
              harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * (448 / 625) := by
    intro r hr
    have hf := WeightedSupportParameters.prescribedFiberMeanVariance_le
      d m r W g H H2 hd hm (Finset.mem_range.mp hr) hg hH hHlower hHupper hgH
        hnormalized hsize hgm (by simp only [W, a, ha]) hH2 hH2max
    dsimp only at hf
    simpa only [H, H2] using hf.2
  have haLe : 1 ≤ a := by
    rw [ha]
    have : 0 ≤ 3 * g / 8 := by positivity
    linarith
  obtain ⟨_, hW, _, _, _, hκexp, _, hκrec⟩ :=
    InterpolationRounding.prescribed_kappa_bounds a H d haLe hH (by omega)
  have hLD : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by
    field_simp
  have hgap' : ∀ r ∈ Finset.range m,
      ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d <
        ((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ) := by
    simpa only [hLD] using hgap
  have herror' : ∀ r ∈ Finset.range m,
      (((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ)) -
          ((W + r + d.choose 2 : ℕ) : ℝ) * harmonicPowerSum (d - 1) 1 / d +
        (((W + r + d.choose 2 : ℕ) : ℝ) ^ 2 * harmonicPowerSum (d - 1) 2 /
            (d * (d + 1))) /
          (4 * ((((m : ℝ) * D * (1 + g)) / D + (d - 1 : ℕ)) -
            ((W + r + d.choose 2 : ℕ) : ℝ) *
              harmonicPowerSum (d - 1) 1 / d)) + 1 ≤
        g * m * (448 / 625) := by
    simpa only [hLD] using herror
  exact finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding
    d D m W ((m : ℝ) * D * (1 + g)) g a H (by omega) hD hm hW hg haLe hH hHlog
      hgap' herror' hκexp hκrec center received

end

end ReedSolomon.HiddenDerivative
