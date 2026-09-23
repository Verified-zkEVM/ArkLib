/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.FiniteRateParameters
import Mathlib.Order.Interval.Finset.Nat

/-!
# Acceptance tests for finite first-order rate parameters

Concrete rounded counts and their rational certificate, the source-count dimension bound, and
boundary cases for its degree and agreement hypotheses.
-/

namespace ReedSolomon.HiddenDerivative

open Filter Topology

/-! ### A concrete finite certificate -/

/-- The rate ratio is `1/4` at rate `1/2` and agreement `3/4`. -/
private theorem concrete_rate_ratio : firstOrderRateBeta (1 / 2) (3 / 4) = 1 / 4 := by
  norm_num [firstOrderRateBeta]

/-- At multiplicity `4`, the derivative and total jet caps are `1` and `6`. -/
example : firstOrderRateDerivativeCap (1 / 2) (3 / 4) 4 = 1 ∧
    firstOrderRateJetDegree (1 / 2) (3 / 4) 4 = 6 := by
  constructor <;> norm_num [firstOrderRateDerivativeCap, firstOrderRateJetDegree,
    firstOrderRateBeta]

/-- At these caps, the source count is `18` and the rank count is `17`. -/
example : firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 = 18 ∧
    firstOrderRankCount 4 1 = 17 := by
  constructor
  · norm_num [firstOrderSourceCount, Finset.sum_range_succ]
  · decide

/-- The rounded finite test holds at rate `1/2`, agreement `3/4`, and multiplicity `4`. -/
private def concreteParameters : FirstOrderFiniteRateParameters (1 / 2 : ℝ) (3 / 4 : ℝ) :=
  ⟨4, by norm_num, by norm_num [FirstOrderFiniteRateTest, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderSourceCount, firstOrderRankCount,
    Finset.sum_range_succ]⟩

example : concreteParameters.derivativeCap = 1 := by
  norm_num [FirstOrderFiniteRateParameters.derivativeCap, concreteParameters,
    firstOrderRateDerivativeCap, firstOrderRateBeta]

example : concreteParameters.jetDegree = 6 := by
  norm_num [FirstOrderFiniteRateParameters.jetDegree, concreteParameters,
    firstOrderRateJetDegree]

example : concreteParameters.rankCount = 17 := by
  norm_num [FirstOrderFiniteRateParameters.rankCount, concreteParameters,
    FirstOrderFiniteRateParameters.derivativeCap, firstOrderRankCount,
    firstOrderRateDerivativeCap, firstOrderRateBeta, Finset.sum_range_succ]

example : concreteParameters.sourceCount = 18 := by
  norm_num [FirstOrderFiniteRateParameters.sourceCount, concreteParameters,
    FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
    firstOrderRateDerivativeCap, firstOrderRateJetDegree, firstOrderRateBeta,
    firstOrderSourceCount, Finset.sum_range_succ]

example : concreteParameters.challengeDegree = 102 := by
  norm_num [FirstOrderFiniteRateParameters.challengeDegree, concreteParameters,
    firstOrderRateChallengeDegree, FirstOrderFiniteRateParameters.rankCount,
    FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
    FirstOrderFiniteRateParameters.sourceCount, firstOrderRateDerivativeCap,
    firstOrderRateJetDegree, firstOrderRateBeta, firstOrderRankCount, firstOrderSourceCount,
    Finset.sum_range_succ]

example : (concreteParameters.rankCount : ℝ) < concreteParameters.sourceCount :=
  concreteParameters.sourceCount_gt_rankCount

/-! ### Asymptotic rates for a concrete agreement -/

noncomputable section

private noncomputable def roundedSourcePolynomial (m M L : ℕ) : ℝ :=
  3 * (m : ℝ) * (M + 1) * (M + 2) / 8 -
    (M : ℝ) * (M + 1) * (M + 2) / 6 +
    (M + 1) * ((L - M : ℕ) * (3 * (m : ℝ) / 4) -
      ((L : ℝ) * (L + 1) - (M : ℝ) * (M + 1)) / 4)

private noncomputable def roundedRankPolynomial (m M : ℕ) : ℝ :=
  (M + 1) * (m : ℝ) * (m + 1) / 2 -
    ((m - 2 * M + 1 : ℕ) : ℝ) * M * (M + 1) / 2 -
    2 * (M : ℝ) * (M - 1) * (M + 1) / 3

private noncomputable def roundedSourceModel (p : (ℝ × ℝ) × ℝ) : ℝ :=
  let x := p.1.1
  let y := p.1.2
  let e := p.2
  3 / 8 * (x + e) * (x + 2 * e) -
    x * (x + e) * (x + 2 * e) / 6 +
    (x + e) * (3 / 4 * (y - x) - (y * (y + e) - x * (x + e)) / 4)

private noncomputable def roundedRankModel (p : ℝ × ℝ) : ℝ :=
  let x := p.1
  let e := p.2
  (x + e) * (1 + e) / 2 -
    (1 - 2 * x + e) * x * (x + e) / 2 - 2 * x * (x - e) * (x + e) / 3

private theorem sum_range_cast_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * (n - 1) / 2 := by
  rw [eq_div_iff two_ne_zero, Finset.sum_range_natCast_mul_two]

private theorem sum_range_cast_sq_eq (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ) ^ 2) =
      (n : ℝ) * (n - 1) * (2 * n - 1) / 6 := by
  rw [eq_div_iff (by norm_num : (6 : ℝ) ≠ 0), Finset.sum_range_natCast_sq_mul_six]

private theorem roundedSourceCount_eq_polynomial {m : ℕ} (hm : 0 < m) :
    firstOrderSourceCount (1 / 2) (3 / 4) m
      (firstOrderRateDerivativeCap (1 / 2) (3 / 4) m)
      (firstOrderRateJetDegree (1 / 2) (3 / 4) m) =
        roundedSourcePolynomial m ⌊(1 / 4 : ℝ) * m⌋₊ ⌊(3 / 2 : ℝ) * m⌋₊ := by
  let M := ⌊(1 / 4 : ℝ) * m⌋₊
  let L := ⌊(3 / 2 : ℝ) * m⌋₊
  have hMcap : firstOrderRateDerivativeCap (1 / 2) (3 / 4) m = M := by
    norm_num [M, firstOrderRateDerivativeCap, firstOrderRateBeta]
  have hLcap : firstOrderRateJetDegree (1 / 2) (3 / 4) m = ⌈(3 / 2 : ℝ) * m⌉₊ := by
    simp [firstOrderRateJetDegree]
    ring_nf
  have hML : M ≤ L := by
    apply Nat.floor_mono
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hMle : 2 * M ≤ m := by
    have hMreal : (M : ℝ) ≤ (1 / 4 : ℝ) * m :=
      Nat.floor_le (show (0 : ℝ) ≤ (1 / 4 : ℝ) * m by positivity)
    exact_mod_cast (by nlinarith [hMreal] : 2 * (M : ℝ) ≤ (m : ℝ))
  have hLreal : (L : ℝ) ≤ (3 / 2 : ℝ) * m :=
    Nat.floor_le (by positivity)
  have hceilLo : L ≤ ⌈(3 / 2 : ℝ) * m⌉₊ := Nat.floor_le_ceil _
  have hceilHi : ⌈(3 / 2 : ℝ) * m⌉₊ ≤ L + 1 := Nat.ceil_le_floor_add_one _
  have hceilRange :
      (∑ t ∈ Finset.range (⌈(3 / 2 : ℝ) * m⌉₊ + 1),
        (min t M + 1 : ℕ) * max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        ∑ t ∈ Finset.range (L + 1),
          (min t M + 1 : ℕ) * max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0 := by
    by_cases h : ⌈(3 / 2 : ℝ) * m⌉₊ = L
    · rw [h]
    · have h' : ⌈(3 / 2 : ℝ) * m⌉₊ = L + 1 := by omega
      rw [h', Finset.sum_range_succ]
      have htail : (3 / 2 : ℝ) * m < (L : ℝ) + 1 := Nat.lt_floor_add_one _
      have hneg : m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * (L + 1) < 0 := by
        nlinarith [htail]
      have hneg' : m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * ((L + 1 : ℕ) : ℝ) < 0 := by
        simpa using hneg
      rw [max_eq_right hneg'.le]
      simp
  have hres {t : ℕ} (ht : t ≤ L) :
      0 ≤ m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t := by
    have htR : (t : ℝ) ≤ L := by exact_mod_cast ht
    nlinarith
  have hfirst :
      (∑ t ∈ Finset.range (M + 1), (min t M + 1 : ℕ) *
        max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        3 * (m : ℝ) * (M + 1) * (M + 2) / 8 -
          (M : ℝ) * (M + 1) * (M + 2) / 6 := by
    have hsum1 (n : ℕ) :
        (∑ t ∈ Finset.range n, ((t : ℝ) + 1)) =
          (n : ℝ) * (n - 1) / 2 + n := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, sum_range_cast_eq]
    have hsumt2 (n : ℕ) :
        (∑ t ∈ Finset.range n, ((t : ℝ) ^ 2 + t)) =
          (n : ℝ) * (n - 1) * (2 * n - 1) / 6 + (n : ℝ) * (n - 1) / 2 := by
      rw [Finset.sum_add_distrib, sum_range_cast_sq_eq, sum_range_cast_eq]
    calc
      _ = ∑ t ∈ Finset.range (M + 1),
          ((3 * (m : ℝ) / 4) * ((t : ℝ) + 1) -
            (1 / 2 : ℝ) * ((t : ℝ) ^ 2 + t)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htM : t ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
        rw [min_eq_left htM, max_eq_left (hres (Nat.le_trans htM hML))]
        push_cast
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1, hsumt2]
        push_cast
        ring
  have htail :
      (∑ t ∈ Finset.Ico (M + 1) (L + 1), (min t M + 1 : ℕ) *
        max (m * (3 / 4 : ℝ) - (1 / 2 : ℝ) * t) 0) =
        (M + 1) * ((L - M : ℕ) * (3 * (m : ℝ) / 4) -
          ((L : ℝ) * (L + 1) - (M : ℝ) * (M + 1)) / 4) := by
    have hsumIco : (∑ t ∈ Finset.Ico (M + 1) (L + 1), (t : ℝ)) =
        ((L : ℝ) * L / 2 + L / 2) - ((M : ℝ) * M / 2 + M / 2) := by
      rw [Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hML), sum_range_cast_eq,
        sum_range_cast_eq]
      push_cast
      ring
    calc
      _ = ∑ t ∈ Finset.Ico (M + 1) (L + 1),
          ((M + 1 : ℝ) * (3 * (m : ℝ) / 4 - (1 / 2 : ℝ) * t)) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htmem := Finset.mem_Ico.mp ht
        have htM : M ≤ t := by omega
        have htL : t ≤ L := by omega
        rw [min_eq_right htM, max_eq_left (hres htL)]
        push_cast
        ring
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico,
          nsmul_eq_mul, ← Finset.mul_sum, hsumIco]
        rw [show L + 1 - (M + 1) = L - M by omega]
        ring
  rw [firstOrderSourceCount, hMcap, hLcap, hceilRange,
    ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hML), hfirst, htail]
  rfl

private theorem roundedRankCount_eq_polynomial {m : ℕ} (hm : 0 < m) :
    (firstOrderRankCount m ⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) =
      roundedRankPolynomial m ⌊(1 / 4 : ℝ) * m⌋₊ := by
  let M := ⌊(1 / 4 : ℝ) * m⌋₊
  have hMle : 2 * M ≤ m := by
    have hMreal : (M : ℝ) ≤ (1 / 4 : ℝ) * m :=
      Nat.floor_le (show (0 : ℝ) ≤ (1 / 4 : ℝ) * m by positivity)
    exact_mod_cast (by nlinarith [hMreal] : 2 * (M : ℝ) ≤ (m : ℝ))
  have hformula : (firstOrderRankCount m M : ℝ) =
      (M + 1) * (m : ℝ) * (m + 1) / 2 -
        ((m - 2 * M + 1 : ℕ) : ℝ) * M * (M + 1) / 2 -
        2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
    have hcast : (firstOrderRankCount m M : ℝ) =
        ∑ s ∈ Finset.range m,
          (((s + 1 : ℕ) : ℝ) * (M + 1) -
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) := by
      unfold firstOrderRankCount
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs : s < m := Finset.mem_range.mp hs
      have hsub : (2 * s + 1 - m) * (s + M + 1 - m) ≤ (s + 1) * (M + 1) := by
        apply Nat.mul_le_mul <;> omega
      rw [Nat.cast_sub hsub]
      push_cast
      rfl
    have hamb :
        (∑ s ∈ Finset.range m, ((s + 1 : ℕ) : ℝ) * (M + 1)) =
          (M + 1) * (m : ℝ) * (m + 1) / 2 := by
      have hsum : (∑ s ∈ Finset.range m, ((s : ℝ) + 1)) =
          (m : ℝ) * (m - 1) / 2 + m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, sum_range_cast_eq]
      calc
        _ = (∑ s ∈ Finset.range m, ((s : ℝ) + 1)) * (M + 1) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun s _ => ?_
          push_cast
          ring
        _ = _ := by rw [hsum]; ring
    have hcorr :
        (∑ s ∈ Finset.range m,
          ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) =
          ((m : ℝ) - 2 * M + 1) * M * (M + 1) / 2 +
            2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le m M)]
      have hprefix :
          (∑ s ∈ Finset.range (m - M),
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro s hs
        have hs : s < m - M := Finset.mem_range.mp hs
        have hz : s + M + 1 - m = 0 := by omega
        rw [hz]
        simp
      have htail :
          (∑ s ∈ Finset.Ico (m - M) m,
            ((2 * s + 1 - m : ℕ) : ℝ) * ((s + M + 1 - m : ℕ) : ℝ)) =
            ((m : ℝ) - 2 * M + 1) * M * (M + 1) / 2 +
              2 * (M : ℝ) * (M - 1) * (M + 1) / 3 := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.sub_sub_self (by omega : M ≤ m)]
        have hsum1 (n : ℕ) :
            (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) =
              (n : ℝ) * (n - 1) / 2 + n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one, sum_range_cast_eq]
        have hsumt2 (n : ℕ) :
            (∑ i ∈ Finset.range n, ((i : ℝ) ^ 2 + i)) =
              (n : ℝ) * (n - 1) * (2 * n - 1) / 6 +
                (n : ℝ) * (n - 1) / 2 := by
          rw [Finset.sum_add_distrib, sum_range_cast_sq_eq, sum_range_cast_eq]
        calc
          _ = ∑ i ∈ Finset.range M,
              (((m : ℝ) - 2 * M + 1) * ((i : ℝ) + 1) +
                2 * ((i : ℝ) ^ 2 + i)) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have hi : i < M := Finset.mem_range.mp hi
            have hfirst : m ≤ 2 * (m - M + i) + 1 := by omega
            have hsecond : m ≤ m - M + i + M + 1 := by omega
            have hsubM : ((m - M : ℕ) : ℝ) = (m : ℝ) - M := by
              rw [Nat.cast_sub (by omega : M ≤ m)]
            rw [Nat.cast_sub hfirst, Nat.cast_sub hsecond]
            push_cast
            rw [hsubM]
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum1,
              hsumt2]
            ring
      rw [hprefix, htail, zero_add]
    rw [hcast, Finset.sum_sub_distrib, hamb, hcorr]
    have hcoef : ((m - 2 * M + 1 : ℕ) : ℝ) =
        (m : ℝ) - 2 * (M : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hMle]
      push_cast
      ring
    rw [hcoef]
    ring
  simpa [roundedRankPolynomial, M] using hformula

private theorem roundedSourcePolynomial_div_cube_eq_model {m M L : ℕ} (hm : 0 < m)
    (hML : M ≤ L) :
    roundedSourcePolynomial m M L / (m : ℝ) ^ 3 =
      roundedSourceModel (((M : ℝ) / m, (L : ℝ) / m), (m : ℝ)⁻¹) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hsub : ((L - M : ℕ) : ℝ) = (L : ℝ) - M := by
    rw [Nat.cast_sub hML]
  unfold roundedSourcePolynomial roundedSourceModel
  rw [hsub]
  field_simp

private theorem roundedRankPolynomial_div_cube_eq_model {m M : ℕ} (hm : 0 < m)
    (hM : 2 * M ≤ m) :
    roundedRankPolynomial m M / (m : ℝ) ^ 3 =
      roundedRankModel ((M : ℝ) / m, (m : ℝ)⁻¹) := by
  have hmne : (m : ℝ) ≠ 0 := by positivity
  have hcast : ((m - 2 * M + 1 : ℕ) : ℝ) = (m : ℝ) - 2 * (M : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hM]
    push_cast
    ring
  unfold roundedRankPolynomial roundedRankModel
  rw [hcast]
  field_simp

private theorem roundedSourceNormalized_eq_model {m : ℕ} (hm : 0 < m) :
    firstOrderNormalizedSourceCount (1 / 2) (3 / 4) m =
      roundedSourceModel
        (((⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) / m,
          (⌊(3 / 2 : ℝ) * m⌋₊ : ℝ) / m), (m : ℝ)⁻¹) := by
  unfold firstOrderNormalizedSourceCount
  rw [roundedSourceCount_eq_polynomial hm,
    roundedSourcePolynomial_div_cube_eq_model hm (Nat.floor_mono (by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      nlinarith))]

private theorem roundedRankNormalized_eq_model {m : ℕ} (hm : 0 < m) :
    firstOrderNormalizedRankCount (1 / 2) (3 / 4) m =
      roundedRankModel ((⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) / m, (m : ℝ)⁻¹) := by
  have hMcap : firstOrderRateDerivativeCap (1 / 2) (3 / 4) m = ⌊(1 / 4 : ℝ) * m⌋₊ := by
    norm_num [firstOrderRateDerivativeCap, firstOrderRateBeta]
  unfold firstOrderNormalizedRankCount
  rw [hMcap, roundedRankCount_eq_polynomial hm,
    roundedRankPolynomial_div_cube_eq_model hm (by
      have hM : (⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) ≤ (1 / 4 : ℝ) * m :=
        Nat.floor_le (by positivity)
      exact_mod_cast (by nlinarith [hM] : 2 * (⌊(1 / 4 : ℝ) * m⌋₊ : ℝ) ≤ m))]

private theorem concreteSourceNormalized_tendsto :
    Tendsto (firstOrderNormalizedSourceCount (1 / 2) (3 / 4)) atTop
      (𝓝 (firstOrderSourceDensity (1 / 2) (3 / 4)
        (firstOrderRateBeta (1 / 2) (3 / 4)))) := by
  have hM : Tendsto (fun m : ℕ =>
      (⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (1 / 4 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (1 / 4 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun m : ℕ =>
      (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (3 / 2 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (3 / 2 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hpair : Tendsto (fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m)) atTop
      (𝓝 ((1 / 4 : ℝ), (3 / 2 : ℝ))) := hM.prodMk_nhds hL
  have hargs : Tendsto (fun m : ℕ =>
      (((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m), (m : ℝ)⁻¹)) atTop
      (𝓝 (((1 / 4 : ℝ), (3 / 2 : ℝ)), (0 : ℝ))) := hpair.prodMk_nhds he
  have hcont : ContinuousAt roundedSourceModel (((1 / 4 : ℝ), (3 / 2 : ℝ)), 0) := by
    unfold roundedSourceModel
    fun_prop
  have hmodel : Tendsto (roundedSourceModel ∘ fun m : ℕ =>
      (((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m,
        (⌊(3 / 2 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m), (m : ℝ)⁻¹)) atTop
      (𝓝 (91 / 768 : ℝ)) := by
    have h := hcont.tendsto.comp hargs
    have heval : roundedSourceModel (((1 / 4 : ℝ), (3 / 2 : ℝ)), 0) = 91 / 768 := by
      norm_num [roundedSourceModel]
    rw [heval] at h
    exact h
  have hlimit : firstOrderSourceDensity (1 / 2) (3 / 4)
      (firstOrderRateBeta (1 / 2) (3 / 4)) = 91 / 768 := by
    rw [concrete_rate_ratio]
    norm_num [firstOrderSourceDensity]
  rw [hlimit]
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Function.comp_apply]
  rw [roundedSourceNormalized_eq_model hm]

private theorem concreteRankNormalized_tendsto :
    Tendsto (firstOrderNormalizedRankCount (1 / 2) (3 / 4)) atTop
      (𝓝 (firstOrderRankDensity (firstOrderRateBeta (1 / 2) (3 / 4)))) := by
  have hM : Tendsto (fun m : ℕ =>
      (⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m) atTop (𝓝 (1 / 4 : ℝ)) :=
    (tendsto_nat_floor_mul_div_atTop (a := (1 / 4 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have he : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hargs : Tendsto (fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m, (m : ℝ)⁻¹)) atTop
      (𝓝 ((1 / 4 : ℝ), (0 : ℝ))) := hM.prodMk_nhds he
  have hcont : ContinuousAt roundedRankModel ((1 / 4 : ℝ), (0 : ℝ)) := by
    unfold roundedRankModel
    fun_prop
  have hmodel : Tendsto (roundedRankModel ∘ fun m : ℕ =>
      ((⌊(1 / 4 : ℝ) * (m : ℝ)⌋₊ : ℝ) / m, (m : ℝ)⁻¹)) atTop
      (𝓝 (19 / 192 : ℝ)) := by
    have h := hcont.tendsto.comp hargs
    have heval : roundedRankModel ((1 / 4 : ℝ), 0) = 19 / 192 := by
      norm_num [roundedRankModel]
    rw [heval] at h
    exact h
  have hlimit : firstOrderRankDensity (firstOrderRateBeta (1 / 2) (3 / 4)) = 19 / 192 := by
    rw [concrete_rate_ratio]
    norm_num [firstOrderRankDensity]
  rw [hlimit]
  apply hmodel.congr'
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Function.comp_apply]
  rw [roundedRankNormalized_eq_model hm]

private theorem concreteExistence_of_tendsto :
    Nonempty (FirstOrderFiniteRateParameters (1 / 2) (3 / 4)) := by
  apply exists_firstOrderFiniteRateParameters_of_tendsto concreteSourceNormalized_tendsto
    concreteRankNormalized_tendsto
  rw [concrete_rate_ratio]
  norm_num [firstOrderSourceDensity, firstOrderRankDensity]

private theorem concreteExistence_of_rate_limits :
    Nonempty (FirstOrderFiniteRateParameters (1 / 2) (3 / 4)) := by
  apply exists_firstOrderFiniteRateParameters_of_rate_limits (by norm_num) (by norm_num)
    (by norm_num)
  · calc
      firstOrderRateThreshold (1 / 2 : ℝ) < Real.sqrt (1 / 2) :=
        firstOrderRateThreshold_lt_sqrt (by norm_num) (by norm_num)
      _ < 3 / 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · exact concreteSourceNormalized_tendsto
  · exact concreteRankNormalized_tendsto

/-- The normalized source and rank limits yield a positive finite-rate certificate. -/
example : ∃ p : FirstOrderFiniteRateParameters (1 / 2) (3 / 4),
    0 < p.multiplicity ∧ FirstOrderFiniteRateTest (1 / 2) (3 / 4) p.multiplicity := by
  obtain ⟨p⟩ := concreteExistence_of_tendsto
  exact ⟨p, p.multiplicity_pos, p.surplus⟩

/-- The rate-threshold existence theorem returns a certificate at the same rate and agreement. -/
example : ∃ p : FirstOrderFiniteRateParameters (1 / 2) (3 / 4),
    0 < p.multiplicity ∧ FirstOrderFiniteRateTest (1 / 2) (3 / 4) p.multiplicity := by
  obtain ⟨p⟩ := concreteExistence_of_rate_limits
  exact ⟨p, p.multiplicity_pos, p.surplus⟩

/-! ### The rational finite test -/

/-- The rational finite test computes the same strict surplus, `17 < 18`. -/
example : FirstOrderRationalFiniteTest (1 / 2 : ℚ) (3 / 4 : ℚ) 4 := by
  norm_num [FirstOrderRationalFiniteTest, firstOrderRationalSourceCount,
    firstOrderRankCount, Finset.sum_range_succ]

/-! ### Source count and interpolation dimension -/

/-- At rate `1/2`, agreement `3/4`, block length `4`, the scaled source count is at most `91`. -/
example :
    4 * firstOrderSourceCount (1 / 2) (3 / 4) 4 1 6 ≤
      firstOrderDimensionCount 2 3 4 1 6 := by
  apply firstOrderSourceCount_mul_le_firstOrderDimensionCount <;> norm_num

/-- Without the agreement bound, the source count can exceed the dimension: `1 ≤ 0` fails. -/
example : firstOrderSourceCount 1 1 1 0 0 = 1 ∧ firstOrderDimensionCount 0 0 1 0 0 = 0 := by
  constructor <;> norm_num [firstOrderSourceCount, firstOrderDimensionCount,
    Finset.sum_range_succ]

/-- Without the degree bound, the source count can exceed the dimension: `3 ≤ 2` fails. -/
example : firstOrderSourceCount 1 2 1 0 1 = 3 ∧ firstOrderDimensionCount 2 2 1 0 1 = 2 := by
  constructor <;> norm_num [firstOrderSourceCount, firstOrderDimensionCount,
    Finset.sum_range_succ]

/-! ### Challenge height at the finite certificate -/

/-- At the concrete certificate, the scaled kernel-height estimate is its challenge degree `102`. -/
example : 1 * concreteParameters.rankCount * concreteParameters.jetDegree /
      (18 - 1 * concreteParameters.rankCount) ≤ concreteParameters.challengeDegree := by
  have hsurplus := concreteParameters.sourceCount_gt_rankCount
  have h := scaledKernelHeight_le_floor (n := 1) (N := 18)
    (r := concreteParameters.rankCount) (mu := concreteParameters.jetDegree) hsurplus (by
      norm_num [FirstOrderFiniteRateParameters.sourceCount, concreteParameters,
        FirstOrderFiniteRateParameters.derivativeCap, FirstOrderFiniteRateParameters.jetDegree,
        firstOrderRateDerivativeCap, firstOrderRateJetDegree, firstOrderRateBeta,
        firstOrderSourceCount, Finset.sum_range_succ])
  change 1 * concreteParameters.rankCount * concreteParameters.jetDegree /
      (18 - 1 * concreteParameters.rankCount) ≤
        max 1 ⌊(concreteParameters.rankCount : ℝ) * concreteParameters.jetDegree /
          (concreteParameters.sourceCount - concreteParameters.rankCount)⌋₊
  exact h.trans (le_max_right _ _)

end

end ReedSolomon.HiddenDerivative
