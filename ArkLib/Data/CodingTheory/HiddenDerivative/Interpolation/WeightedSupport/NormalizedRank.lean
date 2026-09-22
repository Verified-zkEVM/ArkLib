/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankBound
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.RankIntegral
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RankRounding
public import ArkLib.ToMathlib.Analysis.SpecialFunctions.ExpLogRpow

/-!
# The volume-normalized local rank of the weighted support

Fix a derivative order `d ≥ 2`, a multiplicity `m`, a weighted radius `W > 0` and a cutoff `T`.
Write `W'_r = W + r + d.choose 2`, `H = harmonic (d - 1)`, `H₂ = ∑_{i < d - 1} 1 / (i + 1) ^ 2`,
`μ_r = W'_r H / d` and
`err_r = T + (d - 1) - μ_r + (W'_r ^ 2 H₂ / (d (d + 1))) / (4 (T + (d - 1) - μ_r)) + 1`.
For each contact residual `r < m`, `WeightedSupport/RankIntegral.lean` bounds the inner
positive-part sum of `WeightedSupport/RankBound.lean` by the volume of the enlarged weighted
simplex of budget `W'_r` times `err_r`, provided `μ_r < T + (d - 1)`. If every `err_r` is at most
`g m E`, the enlarged volumes are bounded by `V exp (x (r + d.choose 2))` with
`V = W ^ (d - 1) / ((d - 1)!) ^ 2` and `x = (d - 1) / W`, and the contact geometric sum gives
`localResidualCoordinateBudget d m W ⌈T⌉₊ / (V m ^ 3) ≤
  g E exp (κ (1 + d.choose 2 / m)) (1 / (d κ ^ 2) + 1 / (m κ))` with `κ = (d - 1) m / W`.

The second half converts this bound into the closed form
`g c ρ K a ^ 2 / H ^ 2 · d ^ (1 / a) / d`, strictly. The inputs are `E ≤ c`, a harmonic bound
`H ≤ log d + b`, the exponent bound `κ (1 + d.choose 2 / m) ≤ H / a + e`, the reciprocal bound
`1 / κ ^ 2 + d / (m κ) ≤ ρ / (H / a) ^ 2`, and the numerical bound `exp (b + e) < K`. For the
prescribed multiplicity `m = ⌈100 d ^ 2 H⌉₊` and radius `W = ⌊a d m / H⌋₊` with `d ≥ 1000`,
`InterpolationRounding.prescribed_kappa_bounds` supplies the exponent and reciprocal bounds with
`e = 1 / 100` and `ρ = 101 / 100`, so only the per-fiber inequalities remain as hypotheses.

## Main statements

* `localResidualCoordinateBudget_le_weighted_integral_geometric`: the absolute bound.
* `localResidualCoordinateBudget_div_volume_mul_cube_le` and
  `finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le`: the normalized bound, for the
  budget and for the local constraint map.
* `normalized_rank_lt_of_rounding_bounds`: the scalar conversion to the closed form.
* `finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding` and
  `finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error`: the strict
  normalized rank bound, with general rounding inputs and with the prescribed parameters.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/`
`NormalizedRank.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.
Throughout, the source's `harmonicPowerSum (d - 1) 1` is `harmonic (d - 1)`, its
`harmonicPowerSum (d - 1) 2` is `∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2`, and its real cutoff
`T` of `localResidualCoordinateBudget` is the natural cutoff `⌈T⌉₊`, following
`WeightedSupport/LocalRank.lean`.

* `localResidualCoordinateBudget_le_weighted_integral_geometric`,
  `localResidualCoordinateBudget_div_volume_mul_cube_le` and
  `finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le` have the source's statements
  with these substitutions. The unused hypothesis `0 < m` is dropped from the first.
* `normalized_rank_lt_of_rounding_bounds` generalizes the source theorem of the same name. The
  source fixed `c = 448 / 625`, `b = 3 / 5`, `e = 1 / 100`, `ρ = 101 / 100` and `K = 37 / 20`, and
  took `d` and `m` natural; here they are arbitrary, with `0 < c`, `0 ≤ b`, `exp (b + e) < K`, and
  `d, m` positive reals. The source's case is `exp_sixtyOne_div_hundred_lt`.
* `finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding` generalizes the source
  theorem of the same name in the same constants.
* `finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error` generalizes the
  source theorem of the same name: the source fixed `a = 1 + 3 g / 8`, `L = m D (1 + g)`,
  `c = 448 / 625`, `b = 3 / 5`, `K = 37 / 20` and required `48000 ≤ d`. Here `a ≥ 1` and `L` are
  arbitrary, and `1000 ≤ d`, the hypothesis of `prescribed_kappa_bounds`, suffices. The source's
  case is derived in the acceptance tests.

Deferred: the source's `finrank_weightedSupportLocalConstraint_lt_prescribed`, which discharges the
per-fiber inequalities from `WeightedSupportParameters.prescribedFiberMeanVariance_le` of
`Parameters/WeightedSupport/Rounding.lean` and the scalar parameters `theta` and `xi` of
`Parameters/WeightedSupport/ScalarParameters.lean`. Neither file is ported yet.
-/

@[expose] public section

open Finset MeasureTheory

namespace ReedSolomon.HiddenDerivative

/-- The absolute geometric bound on the residual budget. Let `d ≥ 2`, `W > 0`,
`W'_r = W + r + d.choose 2` and `μ_r = W'_r harmonic (d - 1) / d`. If for every contact residual
`r < m` the mean gap `μ_r < T + (d - 1)` holds and the per-fiber error
`T + (d - 1) - μ_r + (W'_r ^ 2 H₂ / (d (d + 1))) / (4 (T + (d - 1) - μ_r)) + 1` is at most
`g m E`, then
`localResidualCoordinateBudget d m W ⌈T⌉₊ ≤
  g m E · W ^ (d - 1) / ((d - 1)!) ^ 2 · exp (x (m + d.choose 2)) (1 / (d x ^ 2) + 1 / x)` with
`x = (d - 1) / W`. The mean gap is the hypothesis of the residual integral bound
`weighted_residual_sum_le_volume_mul_harmonic_variance`. The hypothesis `2 ≤ d` makes `x`
positive, and `0 ≤ g`, `0 ≤ E` keep the fiber bound nonnegative. -/
theorem localResidualCoordinateBudget_le_weighted_integral_geometric
    (d m W : ℕ) (T g Ee : ℝ) (hd : 2 ≤ d) (hW : 0 < W) (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ range m,
      (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d < T + (d - 1 : ℕ))
    (herror : ∀ r ∈ range m,
      T + (d - 1 : ℕ) - (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
          ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * (T + (d - 1 : ℕ) -
              (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
        g * m * Ee) :
    (localResidualCoordinateBudget d m W ⌈T⌉₊ : ℝ) ≤
      g * m * Ee * ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) *
        Real.exp (((d - 1 : ℕ) : ℝ) / W * (m + (d.choose 2 : ℕ))) *
          (1 / ((d : ℝ) * (((d - 1 : ℕ) : ℝ) / W) ^ 2) + 1 / (((d - 1 : ℕ) : ℝ) / W)) := by
  set V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2 with hVdef
  set x : ℝ := ((d - 1 : ℕ) : ℝ) / W with hxdef
  have hx : 0 < x :=
    div_pos (by exact_mod_cast (by omega : 0 < d - 1)) (by exact_mod_cast hW)
  have hV : 0 ≤ V := by positivity
  have hB : 0 ≤ g * m * Ee := by positivity
  refine localResidualCoordinateBudget_le_geometric d m W T (g * m * Ee) V x
    (d.choose 2 : ℕ) (by omega) hx hB hV fun r hr => ?_
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hgr := hgap r hr
  have her := herror r hr
  simp only [Nat.add_sub_cancel] at hgr her hVdef hxdef ⊢
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hgr her
  have hinner := weighted_residual_sum_le_volume_mul_harmonic_variance n (W + r) hgr
  have hvol := volume_weightedSimplex_add_choose_le_exp n W r hW
  rw [← Nat.cast_add] at hvol
  have hvol0 : 0 ≤ volume.real (Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
      (((W + r : ℕ) : ℝ) + ((n + 1).choose 2 : ℕ))) := measureReal_nonneg
  have hden : ((n : ℝ) + 1) * (n + 2) = ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) := by ring
  rw [hden] at hinner
  calc _ ≤ _ := hinner
    _ ≤ volume.real (Set.weightedSimplex (fun i : Fin n ↦ (i : ℝ) + 1)
          (((W + r : ℕ) : ℝ) + ((n + 1).choose 2 : ℕ))) * (g * m * Ee) :=
        mul_le_mul_of_nonneg_left her hvol0
    _ ≤ V * Real.exp (x * (r + ((n + 1).choose 2 : ℕ))) * (g * m * Ee) :=
        mul_le_mul_of_nonneg_right (by rw [hVdef, hxdef]; exact hvol) hB
    _ = _ := by ring

/-- The bound of `localResidualCoordinateBudget_le_weighted_integral_geometric` divided by the
baseline volume `V = W ^ (d - 1) / ((d - 1)!) ^ 2` and by `m ^ 3`: with `κ = (d - 1) m / W`,
`localResidualCoordinateBudget d m W ⌈T⌉₊ / (V m ^ 3) ≤
  g E exp (κ (1 + d.choose 2 / m)) (1 / (d κ ^ 2) + 1 / (m κ))`. The hypothesis `0 < m` is used
to cancel the factor `m` of the fiber bound `g m E`. -/
theorem localResidualCoordinateBudget_div_volume_mul_cube_le
    (d m W : ℕ) (T g Ee : ℝ) (hd : 2 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ range m,
      (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d < T + (d - 1 : ℕ))
    (herror : ∀ r ∈ range m,
      T + (d - 1 : ℕ) - (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
          ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * (T + (d - 1 : ℕ) -
              (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
        g * m * Ee) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (localResidualCoordinateBudget d m W ⌈T⌉₊ : ℝ) / (V * m ^ 3) ≤
      g * Ee * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  intro V κ
  have h := localResidualCoordinateBudget_le_weighted_integral_geometric
    d m W T g Ee hd hW hg hEe hgap herror
  have hmR : (m : ℝ) ≠ 0 := by positivity
  have hWR : (W : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hpred : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d - 1 ≠ 0)
  have hVpos : 0 < V := by positivity
  refine (div_le_div_of_nonneg_right h (by positivity)).trans_eq ?_
  simp only [V, κ]
  field_simp

/-- The rank of the local constraint map on the weighted support space satisfies the normalized
bound of `localResidualCoordinateBudget_div_volume_mul_cube_le` at the cutoff `T = L / D`, via
`finrank_weightedSupportLocalConstraint_le`. The hypothesis `0 < D` is needed to define the map. -/
theorem finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
    {F : Type*} [Field F] (d D m W : ℕ) (L g Ee : ℝ)
    (hd : 2 ≤ d) (hD : 0 < D) (hm : 0 < m) (hW : 0 < W) (hg : 0 ≤ g) (hEe : 0 ≤ Ee)
    (hgap : ∀ r ∈ range m,
      (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d < L / D + (d - 1 : ℕ))
    (herror : ∀ r ∈ range m,
      L / D + (d - 1 : ℕ) - (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
          ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * (L / D + (d - 1 : ℕ) -
              (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
        g * m * Ee)
    (center received : F) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) ≤
      g * Ee * Real.exp (κ * (1 + (d.choose 2 : ℝ) / m)) *
        (1 / ((d : ℝ) * κ ^ 2) + 1 / ((m : ℝ) * κ)) := by
  intro V κ
  have hrank := finrank_weightedSupportLocalConstraint_le
    (d := d) (m := m) (W := W) (L := L) (by omega) hD center received
  have hcast : (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) ≤ localResidualCoordinateBudget d m W ⌈L / D⌉₊ := by
    exact_mod_cast hrank
  exact (div_le_div_of_nonneg_right hcast (by positivity)).trans
    (localResidualCoordinateBudget_div_volume_mul_cube_le
      d m W (L / D) g Ee hd hm hW hg hEe hgap herror)

/-- The scalar conversion of the normalized geometric bound into a closed form. Let `R` be at most
`g E exp X (1 / (d κ ^ 2) + 1 / (m κ))` with `d, m, κ > 0`. Suppose `E ≤ c`, the harmonic bound
`H ≤ log d + b` with `H > 0` and `b ≥ 0`, the exponent bound `X ≤ H / a + e` with `a ≥ 1`, the
reciprocal bound `1 / κ ^ 2 + d / (m κ) ≤ ρ (1 / (H / a) ^ 2)`, and `exp (b + e) < K`. Then
`R < g c ρ K a ^ 2 / H ^ 2 · d ^ (1 / a) / d`.
The exponential is converted by `Real.exp_le_exp_add_mul_rpow_of_le_log_add`, which needs `a ≥ 1`
and `b ≥ 0`. Strictness comes from `exp (b + e) < K` and needs `0 < g` and `0 < c`; no sign
condition on `E` is needed. -/
theorem normalized_rank_lt_of_rounding_bounds
    (R g Ee c a b e ρ K H X κ d m : ℝ)
    (hg : 0 < g) (hc : 0 < c) (hEe : Ee ≤ c)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (hH : 0 < H) (hd : 0 < d) (hm : 0 < m) (hκ : 0 < κ)
    (hHlog : H ≤ Real.log d + b) (hX : X ≤ H / a + e) (hK : Real.exp (b + e) < K)
    (hrec : 1 / κ ^ 2 + d / (m * κ) ≤ ρ * (1 / (H / a) ^ 2))
    (hR : R ≤ g * Ee * Real.exp X * (1 / (d * κ ^ 2) + 1 / (m * κ))) :
    R < g * c * ρ * K * a ^ 2 / H ^ 2 * d ^ (1 / a) / d := by
  have ha0 : 0 < a := by linarith
  have hrec0 : 0 < 1 / κ ^ 2 + d / (m * κ) := by positivity
  have hfactor : 1 / (d * κ ^ 2) + 1 / (m * κ) = (1 / κ ^ 2 + d / (m * κ)) / d := by
    field_simp
  have hrec' : 1 / κ ^ 2 + d / (m * κ) ≤ ρ * (a ^ 2 / H ^ 2) := by
    calc _ ≤ ρ * (1 / (H / a) ^ 2) := hrec
      _ = ρ * (a ^ 2 / H ^ 2) := by field_simp
  have hρ : 0 < ρ * (a ^ 2 / H ^ 2) := hrec0.trans_le hrec'
  have hexp : Real.exp X < K * d ^ (1 / a) :=
    (Real.exp_le_exp_add_mul_rpow_of_le_log_add ha hb hd hHlog hX).trans_lt
      (mul_lt_mul_of_pos_right hK (Real.rpow_pos_of_pos hd _))
  rw [hfactor] at hR
  calc R ≤ g * Ee * Real.exp X * ((1 / κ ^ 2 + d / (m * κ)) / d) := hR
    _ ≤ g * c * Real.exp X * ((ρ * (a ^ 2 / H ^ 2)) / d) := by gcongr
    _ < g * c * (K * d ^ (1 / a)) * ((ρ * (a ^ 2 / H ^ 2)) / d) := by gcongr
    _ = _ := by ring

/-- The strict normalized rank bound for the local constraint map, from the per-fiber inequalities
and the rounding inputs. With `κ = (d - 1) m / W` and `V = W ^ (d - 1) / ((d - 1)!) ^ 2`, suppose
for every contact residual `r < m` the mean gap and the per-fiber error bound `≤ g m c` of
`finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le` hold at `T = L / D`, and suppose
`H ≤ log d + b`, `κ (1 + d.choose 2 / m) ≤ H / a + e`,
`1 / κ ^ 2 + d / (m κ) ≤ ρ (1 / (H / a) ^ 2)` and `exp (b + e) < K`. Then
`rank / (V m ^ 3) < g c ρ K a ^ 2 / H ^ 2 · d ^ (1 / a) / d`. The constraints on `a`, `b`, `c`,
`g` and `H` are those of `normalized_rank_lt_of_rounding_bounds`. -/
theorem finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding
    {F : Type*} [Field F] (d D m W : ℕ) (L g c a b e ρ K H : ℝ)
    (hd : 2 ≤ d) (hD : 0 < D) (hm : 0 < m) (hW : 0 < W)
    (hg : 0 < g) (hc : 0 < c) (ha : 1 ≤ a) (hb : 0 ≤ b) (hH : 0 < H)
    (hHlog : H ≤ Real.log d + b) (hK : Real.exp (b + e) < K)
    (hgap : ∀ r ∈ range m,
      (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d < L / D + (d - 1 : ℕ))
    (herror : ∀ r ∈ range m,
      L / D + (d - 1 : ℕ) - (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
          ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * (L / D + (d - 1 : ℕ) -
              (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
        g * m * c)
    (hκexp : ((d - 1 : ℕ) : ℝ) * m / W * (1 + (d.choose 2 : ℝ) / m) ≤ H / a + e)
    (hκrec : 1 / (((d - 1 : ℕ) : ℝ) * m / W) ^ 2 + (d : ℝ) / (m * (((d - 1 : ℕ) : ℝ) * m / W)) ≤
      ρ * (1 / (H / a) ^ 2))
    (center received : F) :
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) <
      g * c * ρ * K * a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  intro V
  have hκ : 0 < ((d - 1 : ℕ) : ℝ) * m / W :=
    div_pos (mul_pos (by exact_mod_cast (by omega : 0 < d - 1)) (by exact_mod_cast hm))
      (by exact_mod_cast hW)
  have hbase := finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
    d D m W L g c hd hD hm hW hg.le hc.le hgap herror center received
  exact normalized_rank_lt_of_rounding_bounds _ g c c a b e ρ K H _ _ d m hg hc le_rfl ha hb hH
    (by exact_mod_cast (by omega : 0 < d)) (by exact_mod_cast hm) hκ hHlog hκexp hK hκrec hbase

/-- The strict normalized rank bound at the prescribed multiplicity `m = ⌈100 d ^ 2 H⌉₊` and
weighted radius `W = ⌊a d m / H⌋₊`. For `d ≥ 1000`, `a ≥ 1` and `H > 0`,
`InterpolationRounding.prescribed_kappa_bounds` supplies `0 < m`, `0 < W`, the exponent bound
with `e = 1 / 100` and the reciprocal bound with `ρ = 101 / 100`. What remains are the per-fiber
inequalities at `T = L / D`, the harmonic bound `H ≤ log d + b` with `b ≥ 0`, and
`exp (b + 1 / 100) < K`. The conclusion is
`rank / (V m ^ 3) < g c (101 / 100) K a ^ 2 / H ^ 2 · d ^ (1 / a) / d`. -/
theorem finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error
    {F : Type*} [Field F] (d D : ℕ) (L g c a b K H : ℝ)
    (hd : 1000 ≤ d) (hD : 0 < D) (hg : 0 < g) (hc : 0 < c) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (hH : 0 < H) (hHlog : H ≤ Real.log d + b) (hK : Real.exp (b + 1 / 100) < K)
    (hgap : ∀ r ∈ range ⌈100 * (d : ℝ) ^ 2 * H⌉₊,
      (((⌊a * d * ⌈100 * (d : ℝ) ^ 2 * H⌉₊ / H⌋₊ + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) *
          harmonic (d - 1) / d < L / D + (d - 1 : ℕ))
    (herror : ∀ r ∈ range ⌈100 * (d : ℝ) ^ 2 * H⌉₊,
      L / D + (d - 1 : ℕ) -
          (((⌊a * d * ⌈100 * (d : ℝ) ^ 2 * H⌉₊ / H⌋₊ + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) *
            harmonic (d - 1) / d +
          ((((⌊a * d * ⌈100 * (d : ℝ) ^ 2 * H⌉₊ / H⌋₊ + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * (L / D + (d - 1 : ℕ) -
              (((⌊a * d * ⌈100 * (d : ℝ) ^ 2 * H⌉₊ / H⌋₊ + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) *
                harmonic (d - 1) / d)) + 1 ≤
        g * ⌈100 * (d : ℝ) ^ 2 * H⌉₊ * c)
    (center received : F) :
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊a * d * m / H⌋₊
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) <
      g * c * (101 / 100) * K * a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  intro m W V
  obtain ⟨hm, hW, _, _, _, hκexp, _, hκrec⟩ :=
    InterpolationRounding.prescribed_kappa_bounds a H d ha hH hd
  exact finrank_weightedSupportLocalConstraint_lt_of_harmonic_error_and_rounding
    d D m W L g c a b (1 / 100) (101 / 100) K H (by omega) hD hm hW hg hc ha hb hH hHlog hK
      hgap herror hκexp hκrec center received

end ReedSolomon.HiddenDerivative
