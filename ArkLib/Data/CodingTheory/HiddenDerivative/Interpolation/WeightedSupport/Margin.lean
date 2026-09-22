/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.Surplus
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.DimensionInputs
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Estimate
public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.NormalizedRank

/-!
# The strict surplus of the weighted support

Let `n` be the block length, `D` the polynomial degree, `g = rateGap δ (D / n)`, `a = 1 + θ g`,
`d = ⌈exp (ξ / δ)⌉₊`, `H = harmonic (d - 1)`, `m = ⌈100 d ^ 2 H⌉₊` and `W = ⌊a d m / H⌋₊`. This
file proves that the weighted support space at the cutoff `L = m D (1 + g)` has dimension
greater than `(543 / 500) n` times the rank of one local constraint map:
`(543 / 500) n rank < dim`. Both sides are compared after dividing by the simplex volume
`V = W ^ (d - 1) / ((d - 1)!) ^ 2` and `m ^ 3`; the rank enters only through an upper bound, so
rank `0` is allowed.

The proof has three parts.

* `finrank_weightedSupportLocalConstraint_lt_prescribed`: the per-fiber mean-variance bound of
  `prescribedFiberMeanVariance_le` discharges the fiber hypotheses of
  `finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error`, giving the
  normalized rank bound `rank / (V m ^ 3) < g (448 / 625) (101 / 100) (37 / 20) a ^ 2 / H ^ 2 ·
  d ^ (1 / a) / d`.
* `weightedSupport_margin_of_normalized_rank`: the dimension lower bound `weighted_dimension_lower`
  and a normalized rank bound give the margin through `multiplicative_margin_from_bounds`.
* `prescribed_weightedSupport_margin`: all scalar hypotheses are discharged for the prescribed
  parameters; only the rate interval `δ / 3 ≤ D / n ≤ 1 - δ` remains.

## Main statements

* `finrank_weightedSupportLocalConstraint_lt_prescribed`
* `weightedSupport_margin_of_normalized_rank`
* `prescribed_weightedSupport_margin`

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/WeightedSupport/Margin.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, together with
`finrank_weightedSupportLocalConstraint_lt_prescribed` of `NormalizedRank.lean` in the same
directory, which was deferred from the port of that file until `Rounding.lean` was ported.
Throughout, the source's `harmonicPowerSum (d - 1) 1` is `harmonic (d - 1)` and its
`harmonicPowerSum (d - 1) 2` is `∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2`.

* `finrank_weightedSupportLocalConstraint_lt_prescribed` drops the source's hypothesis
  `H ≤ log d + 3 / 5`, which holds for every `d` (`Real.harmonic_pred_lt_log_add_three_fifths`).
* `weightedSupport_margin_of_normalized_rank` weakens `48000 ≤ d` to `10000 ≤ d`, the hypothesis of
  `weighted_dimension_lower`.
* `prescribed_weightedSupport_margin` is unchanged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open WeightedSupportParameters

/-- The strict normalized rank bound at the prescribed parameters. Let `H = harmonic (d - 1)`,
`a = 1 + θ g`, `m = ⌈100 d ^ 2 H⌉₊`, `W = ⌊a d m / H⌋₊` and
`V = W ^ (d - 1) / ((d - 1)!) ^ 2`. For `d ≥ 48000`, `g > 0`, `54 / 5 ≤ H`, `ξ ≤ g H`,
`a / (g H) ≤ 1 / ξ` and `270 d H ≤ g m`, the local constraint map at the cutoff `m D (1 + g)`
satisfies `rank / (V m ^ 3) < g (448 / 625) (101 / 100) (37 / 20) a ^ 2 / H ^ 2 · d ^ (1 / a) / d`.
The hypotheses are those of `centeringErrorBounds`, through which `prescribedFiberMeanVariance_le`
supplies the per-fiber mean gap and error bound for every contact residual `r < m`; the harmonic
bounds `H ≤ log d + 3 / 5`, `H ≤ (19 / 365) √d` and `∑ 1 / (i + 1) ^ 2 < 329 / 200` hold for every
`d ≥ 48000`. -/
theorem finrank_weightedSupportLocalConstraint_lt_prescribed
    {F : Type*} [Field F] (g : ℝ) (d D : ℕ)
    (hg : 0 < g) (hd : 48000 ≤ d) (hD : 0 < D)
    (hHlower : 54 / 5 ≤ (harmonic (d - 1) : ℝ))
    (hgH : xi ≤ g * harmonic (d - 1))
    (hnormalized : (1 + theta * g) / (g * harmonic (d - 1)) ≤ 1 / xi)
    (hgm : 270 * d * (harmonic (d - 1) : ℝ) ≤ g * ⌈100 * (d : ℝ) ^ 2 * harmonic (d - 1)⌉₊)
    (center received : F) :
    let H : ℝ := harmonic (d - 1)
    let a := 1 + theta * g
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊a * d * m / H⌋₊
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD center received)) : ℝ) / (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d := by
  intro H a m W V
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHlower
  have ha : 1 ≤ a := le_add_of_nonneg_right (mul_nonneg theta_pos.le hg.le)
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hm : 0 < m := Nat.cast_pos.mp (lt_of_lt_of_le (by positivity) hsize)
  have hHlog : H ≤ Real.log d + 3 / 5 := (Real.harmonic_pred_lt_log_add_three_fifths d).le
  have hHupper : H ≤ (19 / 365) * Real.sqrt d :=
    hHlog.trans (Real.log_add_three_fifths_le_nineteen_div_365_mul_sqrt (by exact_mod_cast hd))
  have hH2 : 0 ≤ ∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2 := by positivity
  have hH2max : ∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2 ≤ 329 / 200 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ 1 / ((i : ℝ) + 1) ^ 2)]
    exact (Real.reciprocal_square_sum_lt _).le
  have hfiber (r : ℕ) (hr : r ∈ Finset.range m) :=
    prescribedFiberMeanVariance_le d m r W g H _ hd hm (Finset.mem_range.mp hr) hg hH hHlower
      hHupper hgH hnormalized hsize hgm rfl hH2 hH2max
  have hLD : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by
    have : (D : ℝ) ≠ 0 := by positivity
    field_simp
  have hK : Real.exp (3 / 5 + 1 / 100) < 37 / 20 := by
    norm_num
    exact Real.exp_sixtyOne_div_hundred_lt
  have hgap : ∀ r ∈ Finset.range m,
      (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d <
        (m : ℝ) * D * (1 + g) / D + (d - 1 : ℕ) := by
    intro r hr
    have h := (hfiber r hr).1
    rw [hLD]
    push_cast at h ⊢
    linarith
  have herror : ∀ r ∈ Finset.range m,
      (m : ℝ) * D * (1 + g) / D + (d - 1 : ℕ) -
          (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d +
          ((((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) ^ 2 *
              (∑ i : Fin (d - 1), 1 / ((i : ℝ) + 1) ^ 2) / ((d : ℝ) * (d + 1))) /
            (4 * ((m : ℝ) * D * (1 + g) / D + (d - 1 : ℕ) -
              (((W + r : ℕ) : ℝ) + (d.choose 2 : ℕ)) * harmonic (d - 1) / d)) + 1 ≤
        g * m * (448 / 625) := by
    intro r hr
    have h := (hfiber r hr).2
    rw [hLD]
    push_cast at h ⊢
    exact h
  exact finrank_weightedSupportLocalConstraint_lt_prescribed_rounding_of_harmonic_error
    d D ((m : ℝ) * D * (1 + g)) g (448 / 625) a (3 / 5) (37 / 20) H (by omega) hD hg
    (by norm_num) ha (by norm_num) hH hHlog hK hgap herror center received

/-- The strict surplus from a normalized rank bound. Let `g = rateGap δ (D / n)`, `a = 1 + θ g`,
`H = harmonic (d - 1)`, `V = W ^ (d - 1) / ((d - 1)!) ^ 2` and `L = m D (1 + g)`. Suppose
`0 < δ ≤ 1 / 4`, `δ / 3 ≤ D / n ≤ 1 - δ`, `ξ / δ ≤ H`, `ξ / δ ≤ log d`, `d ≥ 10000`, `m, W > 0`,
the dimension inputs `W H / d ≤ (1 + 3 g / 8) m`, `W / (d (g m)) ≤ 10 / 27` and
`(999 / 1000) (a / (g H)) ^ 2 ≤ (W / (d (g m))) ^ 2`, and the normalized rank bound
`rank / (V m ^ 3) ≤ g (448 / 625) (101 / 100) (37 / 20) a ^ 2 / H ^ 2 · d ^ (1 / a) / d`. Then
`(543 / 500) n rank < dim`, where `dim` is the dimension of the weighted support space at `L`.
The dimension inputs feed `weighted_dimension_lower`, which needs `d ≥ 10000`; `m, W > 0` make
`V m ^ 3` positive. -/
theorem weightedSupport_margin_of_normalized_rank {F : Type*} [Field F]
    (δ : ℝ) (n D d m W : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D) (hd : 10000 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hHlo : xi / δ ≤ harmonic (d - 1))
    (hlog : xi / δ ≤ Real.log d)
    (hmean : let g := rateGap δ ((D : ℝ) / n)
      W * (harmonic (d - 1) : ℝ) / d ≤ (1 + 3 * g / 8) * m)
    (hs : let g := rateGap δ ((D : ℝ) / n)
      W / ((d : ℝ) * (g * m)) ≤ 10 / 27)
    (hfloor : let g := rateGap δ ((D : ℝ) / n)
      (999 / 1000) * ((1 + theta * g) / (g * harmonic (d - 1))) ^ 2 ≤
        (W / ((d : ℝ) * (g * m))) ^ 2)
    (hrank : let g := rateGap δ ((D : ℝ) / n)
      let a := 1 + theta * g
      let H : ℝ := harmonic (d - 1)
      let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
      (Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) : ℝ) / (V * m ^ 3) ≤
        g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
          (d : ℝ) ^ (1 / a) / d) :
    let g := rateGap δ ((D : ℝ) / n)
    (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g)) hD) := by
  intro g
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdim := weighted_dimension_lower F (W := W) hd hD g m hmean hs
  exact multiplicative_margin_from_bounds δ ((D : ℝ) / n) (harmonic (d - 1)) d g
    (1 + theta * g) (W / ((d : ℝ) * (g * m)))
    ((W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2) m n D _ _
    hδ hδmax hρlo hρhi hHlo hlog (by positivity) rfl rfl (by positivity)
    (Nat.cast_pos.mpr hm) hnR (by field_simp) hfloor hdim hrank

/-- The strict surplus at the prescribed parameters. Let `0 < δ ≤ 1 / 4`, `0 < n`, `0 < D` and
`δ / 3 ≤ D / n ≤ 1 - δ`, and put `d = ⌈exp (ξ / δ)⌉₊`, `H = harmonic (d - 1)`,
`g = rateGap δ (D / n)`, `m = ⌈100 d ^ 2 H⌉₊` and `W = ⌊(1 + θ g) d m / H⌋₊`. Then the weighted
support space at the cutoff `m D (1 + g)` has dimension greater than `(543 / 500) n` times the rank
of the local constraint map. `prescribed_order_lower` gives `d ≥ 48000` and `ξ / δ ≤ log d ≤ H`,
`prescribed_dimension_inputs` the dimension inputs, and
`finrank_weightedSupportLocalConstraint_lt_prescribed` the normalized rank bound; its hypothesis
`270 d H ≤ g m` follows from `m ≥ 100 d ^ 2 H`, `g H ≥ ξ` and `H ≤ d`. -/
theorem prescribed_weightedSupport_margin {F : Type*} [Field F]
    (δ : ℝ) (n D : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ) :
    let d := ⌈Real.exp (xi / δ)⌉₊
    let H : ℝ := harmonic (d - 1)
    let g := rateGap δ ((D : ℝ) / n)
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊(1 + theta * g) * d * m / H⌋₊
    (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g)) hD) := by
  intro d H g m W
  obtain ⟨hd, hlog, hHlo⟩ := prescribed_order_lower δ hδ hδmax
  have hdR : (48000 : ℝ) ≤ d := by exact_mod_cast hd
  have hρ : 0 < (D : ℝ) / n := div_pos (Nat.cast_pos.mpr hD) (Nat.cast_pos.mpr hn)
  have hg : 0 < g := rateGap_pos hδ hρ
  have hH : 0 < H := (div_pos xi_pos hδ).trans_le hHlo
  have hHlower : 54 / 5 ≤ H := by
    have hx : 54 / 5 ≤ xi / δ := by
      rw [le_div_iff₀ hδ]
      norm_num [xi]
      linarith
    exact hx.trans hHlo
  have hgH : xi ≤ g * H := xi_le_rateGap_mul hδ hδmax hρ hρhi hHlo
  have hnorm : (1 + theta * g) / (g * H) ≤ 1 / xi :=
    le_inv_of_le_one_add_mul_rateGap_div xi_pos hδ hρ (max_add_theta_mul_le_one hδ hδmax hρhi)
      hHlo le_rfl
  obtain ⟨hm, hW, hmean, hs, hf⟩ :=
    prescribed_dimension_inputs δ _ H d hδ hδmax hρ hρhi (by omega) hHlo
  have hHsq := Real.sq_le_div_hundred_of_le_log_add_three_fifths (by linarith) hH.le
    (Real.harmonic_pred_lt_log_add_three_fifths d).le
  have hHd : H ≤ d := by nlinarith
  have hsize : 100 * (d : ℝ) ^ 2 * H ≤ m := Nat.le_ceil _
  have hgm : 270 * d * H ≤ g * m := by
    have h1 := mul_le_mul_of_nonneg_left hsize hg.le
    have h2 := mul_le_mul_of_nonneg_left hgH (show 0 ≤ 100 * (d : ℝ) ^ 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hHd (show 0 ≤ 270 * (d : ℝ) by positivity)
    norm_num [xi] at h2
    nlinarith
  have hrank := finrank_weightedSupportLocalConstraint_lt_prescribed g d D hg hd hD hHlower hgH
    hnorm hgm (0 : F) 0
  exact weightedSupport_margin_of_normalized_rank δ n D d m W hδ hδmax hn hD (by omega) hm hW
    hρlo hρhi hHlo hlog hmean hs hf hrank.le

end ReedSolomon.HiddenDerivative
