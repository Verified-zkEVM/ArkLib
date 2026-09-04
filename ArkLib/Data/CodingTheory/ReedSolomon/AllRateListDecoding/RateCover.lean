/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite rate cover for uniform additive-gap decoding

These definitions isolate the elementary real arithmetic behind the coarse phase-one reduction
from a theorem with agreement and multiplicative-slack parameters to a theorem uniform over all
rates. For a fixed additive gap `delta`, the mesh width is `delta / 2`. At a positive mesh endpoint
`a`, the local agreement and slack parameters are

`epsilon = a + delta / 2` and `theta = (delta / 2) / epsilon`.

The identity `(1 - theta) * epsilon = a` is proved below.  The canonical bin for a rate `r` is
the predecessor of `ceil (r / (delta / 2))`; at rate zero it is the first bin.  Truncating only the
last endpoint at `1 - delta` makes the same selection cover both boundary cases.
-/

namespace ReedSolomon
namespace AllRateListDecoding
namespace RateCover

noncomputable section

/-- Half of the requested additive capacity gap. -/
def halfGap (delta : ℝ) : ℝ := delta / 2

/-- Number of half-gap mesh intervals needed to cover rates up to `1 - delta`. -/
noncomputable def binCount (delta : ℝ) : ℕ :=
  Nat.ceil ((1 - delta) / halfGap delta)

/-- The endpoint of the `j`th zero-indexed mesh interval, truncated at `1 - delta`. -/
def endpoint (delta : ℝ) (j : ℕ) : ℝ :=
  min ((j + 1 : ℕ) * halfGap delta) (1 - delta)

/-- The zero-indexed mesh interval selected for `rate`.  Rate zero is assigned to the first bin. -/
noncomputable def binIndex (delta rate : ℝ) : ℕ :=
  (Nat.ceil (rate / halfGap delta)).pred

/-- Agreement parameter attached to a mesh endpoint. -/
def localAgreement (delta endpoint : ℝ) : ℝ :=
  endpoint + halfGap delta

/-- Multiplicative slack attached to a mesh endpoint. -/
def localSlack (delta endpoint : ℝ) : ℝ :=
  halfGap delta / localAgreement delta endpoint

lemma halfGap_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < halfGap delta := by
  exact div_pos hdelta (by norm_num)

lemma binCount_pos {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    0 < binCount delta := by
  rw [binCount]
  exact Nat.ceil_pos.mpr <| div_pos (sub_pos.mpr hdeltaOne) (halfGap_pos hdelta)

lemma endpoint_pos {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1) (j : ℕ) :
    0 < endpoint delta j := by
  rw [endpoint]
  exact lt_min
    (mul_pos (by positivity) (halfGap_pos hdelta))
    (sub_pos.mpr hdeltaOne)

lemma endpoint_le_one_sub (delta : ℝ) (j : ℕ) :
    endpoint delta j ≤ 1 - delta := by
  exact min_le_right _ _

/-- The zeroth endpoint is the least endpoint of the truncated mesh. -/
lemma endpoint_zero_le_endpoint {delta : ℝ} (hdelta : 0 < delta) (j : ℕ) :
    endpoint delta 0 ≤ endpoint delta j := by
  have hIndex : (1 : ℝ) ≤ (j + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  have hMesh : halfGap delta ≤ (j + 1 : ℕ) * halfGap delta := by
    simpa using mul_le_mul_of_nonneg_right hIndex (halfGap_pos hdelta).le
  simpa [endpoint] using min_le_min hMesh (le_refl (1 - delta))

/-- The last mesh endpoint is the truncated endpoint `1 - delta`. -/
lemma endpoint_last_eq_one_sub {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    endpoint delta (binCount delta - 1) = 1 - delta := by
  have hCount : 0 < binCount delta := binCount_pos hdelta hdeltaOne
  have hCeil :
      (1 - delta) / halfGap delta ≤ (binCount delta : ℝ) := by
    exact Nat.le_ceil _
  have hCap : 1 - delta ≤ (binCount delta : ℝ) * halfGap delta := by
    exact (div_le_iff₀ (halfGap_pos hdelta)).mp hCeil
  rw [endpoint, Nat.sub_add_cancel hCount, min_eq_right hCap]

lemma binIndex_lt_binCount {delta rate : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hRateNonneg : 0 ≤ rate) (hRate : rate ≤ 1 - delta) :
    binIndex delta rate < binCount delta := by
  by_cases hRateZero : rate = 0
  · simp only [binIndex, hRateZero, zero_div, Nat.ceil_zero, Nat.pred_zero]
    exact binCount_pos hdelta hdeltaOne
  · have hRatePos : 0 < rate := lt_of_le_of_ne hRateNonneg (Ne.symm hRateZero)
    have hQuotientPos : 0 < rate / halfGap delta :=
      div_pos hRatePos (halfGap_pos hdelta)
    have hCeilPos : 0 < Nat.ceil (rate / halfGap delta) := Nat.ceil_pos.mpr hQuotientPos
    have hCeilLe :
        Nat.ceil (rate / halfGap delta) ≤ binCount delta := by
      rw [binCount]
      exact Nat.ceil_mono <| (div_le_div_iff_of_pos_right (halfGap_pos hdelta)).mpr hRate
    exact (Nat.pred_lt (Nat.ne_of_gt hCeilPos)).trans_le hCeilLe

lemma rate_le_endpoint_binIndex {delta rate : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hRateNonneg : 0 ≤ rate) (hRate : rate ≤ 1 - delta) :
    rate ≤ endpoint delta (binIndex delta rate) := by
  by_cases hRateZero : rate = 0
  · subst rate
    simp only [binIndex, zero_div, Nat.ceil_zero, Nat.pred_zero]
    exact (endpoint_pos hdelta hdeltaOne 0).le
  · have hRatePos : 0 < rate := lt_of_le_of_ne hRateNonneg (Ne.symm hRateZero)
    have hCeilPos : 0 < Nat.ceil (rate / halfGap delta) :=
      Nat.ceil_pos.mpr <| div_pos hRatePos (halfGap_pos hdelta)
    have hCeil :
        rate / halfGap delta ≤ (Nat.ceil (rate / halfGap delta) : ℝ) := Nat.le_ceil _
    have hMesh :
        rate ≤ (Nat.ceil (rate / halfGap delta) : ℝ) * halfGap delta :=
      (div_le_iff₀ (halfGap_pos hdelta)).mp hCeil
    have hPred : (Nat.ceil (rate / halfGap delta)).pred + 1 =
        Nat.ceil (rate / halfGap delta) := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hCeilPos
    rw [endpoint, binIndex, hPred]
    exact le_min hMesh hRate

lemma endpoint_binIndex_le_rate_add_halfGap {delta rate : ℝ}
    (hdelta : 0 < delta) (hRateNonneg : 0 ≤ rate) :
    endpoint delta (binIndex delta rate) ≤ rate + halfGap delta := by
  by_cases hRateZero : rate = 0
  · subst rate
    simp [endpoint, binIndex]
  · have hRatePos : 0 < rate := lt_of_le_of_ne hRateNonneg (Ne.symm hRateZero)
    have hCeilPos : 0 < Nat.ceil (rate / halfGap delta) :=
      Nat.ceil_pos.mpr <| div_pos hRatePos (halfGap_pos hdelta)
    have hCeilLt :
        (Nat.ceil (rate / halfGap delta) : ℝ) < rate / halfGap delta + 1 :=
      Nat.ceil_lt_add_one <| div_nonneg hRateNonneg (halfGap_pos hdelta).le
    have hPred : (Nat.ceil (rate / halfGap delta)).pred + 1 =
        Nat.ceil (rate / halfGap delta) := by
      simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hCeilPos
    apply LT.lt.le
    calc
      endpoint delta (binIndex delta rate) ≤
          (Nat.ceil (rate / halfGap delta) : ℝ) * halfGap delta := by
        rw [endpoint, binIndex, hPred]
        exact min_le_left _ _
      _ < (rate / halfGap delta + 1) * halfGap delta :=
        mul_lt_mul_of_pos_right hCeilLt (halfGap_pos hdelta)
      _ = rate + halfGap delta := by
        rw [add_mul, div_mul_cancel₀ rate (ne_of_gt (halfGap_pos hdelta)), one_mul]

/-- Every feasible real rate lies in a half-gap mesh interval with a positive endpoint. -/
theorem exists_fin_endpoint_cover {delta rate : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hRateNonneg : 0 ≤ rate) (hRate : rate ≤ 1 - delta) :
    ∃ j : Fin (binCount delta),
      0 < endpoint delta j ∧
      rate ≤ endpoint delta j ∧ endpoint delta j ≤ rate + halfGap delta := by
  let j : Fin (binCount delta) :=
    ⟨binIndex delta rate, binIndex_lt_binCount hdelta hdeltaOne hRateNonneg hRate⟩
  exact ⟨j, endpoint_pos hdelta hdeltaOne j,
    rate_le_endpoint_binIndex hdelta hdeltaOne hRateNonneg hRate,
    endpoint_binIndex_le_rate_add_halfGap hdelta hRateNonneg⟩

/-- The finite-cover witness specialized to the rational code rate `messageDim / blockLength`. -/
theorem exists_fin_endpoint_cover_natRatio {delta : ℝ} {blockLength messageDim : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ 1 - delta) :
    ∃ j : Fin (binCount delta),
      0 < endpoint delta j ∧
      (messageDim : ℝ) / blockLength ≤ endpoint delta j ∧
      endpoint delta j ≤ (messageDim : ℝ) / blockLength + halfGap delta := by
  exact exists_fin_endpoint_cover hdelta hdeltaOne
    (div_nonneg (Nat.cast_nonneg _) (le_of_lt (by exact_mod_cast hBlockLength))) hRate

/-- Cross-multiplication for a nonempty block length, in the orientation used by ambient bounds. -/
lemma natRatio_le_iff {blockLength messageDim : ℕ} {a : ℝ}
    (hBlockLength : 0 < blockLength) :
    (messageDim : ℝ) / blockLength ≤ a ↔ (messageDim : ℝ) ≤ a * blockLength := by
  exact div_le_iff₀ (by exact_mod_cast hBlockLength)

/-- A real rate bound places the message dimension below the floored ambient dimension. -/
lemma messageDim_le_floor_mul_of_natRatio_le {blockLength messageDim : ℕ} {a : ℝ}
    (hBlockLength : 0 < blockLength)
    (hRate : (messageDim : ℝ) / blockLength ≤ a) :
    messageDim ≤ Nat.floor (a * blockLength) := by
  exact Nat.le_floor ((natRatio_le_iff hBlockLength).mp hRate)

/-- Adding one half-gap to a covering endpoint costs at most the full additive gap. -/
lemma localAgreement_mul_le_messageDim_add_gap_mul {delta a : ℝ}
    {blockLength messageDim : ℕ} (hBlockLength : 0 < blockLength)
    (hEndpoint : a ≤ (messageDim : ℝ) / blockLength + halfGap delta) :
    localAgreement delta a * blockLength ≤ messageDim + delta * blockLength := by
  have hLength : (0 : ℝ) < blockLength := by exact_mod_cast hBlockLength
  rw [halfGap] at hEndpoint
  rw [localAgreement, halfGap]
  have hCancel : (messageDim : ℝ) / blockLength * blockLength = messageDim := by
    exact div_mul_cancel₀ _ (ne_of_gt hLength)
  nlinarith

/-- The local rounded agreement threshold is below the requested additive-gap threshold. -/
lemma ceil_localAgreement_mul_le_messageDim_add_ceil_gap {delta a : ℝ}
    {blockLength messageDim : ℕ} (hdelta : 0 ≤ delta)
    (hBlockLength : 0 < blockLength)
    (hEndpoint : a ≤ (messageDim : ℝ) / blockLength + halfGap delta) :
    Nat.ceil (localAgreement delta a * blockLength) ≤
      messageDim + Nat.ceil (delta * blockLength) := by
  have hLocal :=
    localAgreement_mul_le_messageDim_add_gap_mul hBlockLength hEndpoint
  have hCeil := Nat.ceil_mono hLocal
  have hGapNonneg : 0 ≤ delta * (blockLength : ℝ) :=
    mul_nonneg hdelta (Nat.cast_nonneg _)
  rw [add_comm (messageDim : ℝ), Nat.ceil_add_natCast hGapNonneg, Nat.add_comm] at hCeil
  exact hCeil

lemma localAgreement_pos_of_endpoint_nonneg {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : 0 ≤ endpoint) :
    0 < localAgreement delta endpoint := by
  rw [localAgreement]
  exact add_pos_of_nonneg_of_pos hEndpoint (halfGap_pos hdelta)

/-- A covering endpoint makes the local agreement parameter at most `rate + delta`. -/
lemma localAgreement_le_rate_add {delta endpoint rate : ℝ}
    (hEndpoint : endpoint ≤ rate + halfGap delta) :
    localAgreement delta endpoint ≤ rate + delta := by
  rw [halfGap] at hEndpoint
  rw [localAgreement, halfGap]
  linarith

lemma localAgreement_lt_one_of_endpoint_le_one_sub {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : endpoint ≤ 1 - delta) :
    localAgreement delta endpoint < 1 := by
  rw [localAgreement, halfGap]
  linarith

lemma localSlack_pos_of_endpoint_nonneg {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : 0 ≤ endpoint) :
    0 < localSlack delta endpoint := by
  rw [localSlack]
  exact div_pos (halfGap_pos hdelta)
    (localAgreement_pos_of_endpoint_nonneg hdelta hEndpoint)

lemma localSlack_lt_one_of_endpoint_pos {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : 0 < endpoint) :
    localSlack delta endpoint < 1 := by
  rw [localSlack, div_lt_one (localAgreement_pos_of_endpoint_nonneg hdelta hEndpoint.le)]
  rw [localAgreement]
  linarith [halfGap_pos hdelta]

lemma localAgreement_endpoint_mem_Ioo {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (j : ℕ) :
    localAgreement delta (endpoint delta j) ∈ Set.Ioo 0 1 := by
  exact ⟨localAgreement_pos_of_endpoint_nonneg hdelta (endpoint_pos hdelta hdeltaOne j).le,
    localAgreement_lt_one_of_endpoint_le_one_sub hdelta (endpoint_le_one_sub delta j)⟩

lemma localSlack_endpoint_mem_Ioo {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (j : ℕ) :
    localSlack delta (endpoint delta j) ∈ Set.Ioo 0 1 := by
  exact ⟨localSlack_pos_of_endpoint_nonneg hdelta (endpoint_pos hdelta hdeltaOne j).le,
    localSlack_lt_one_of_endpoint_pos hdelta (endpoint_pos hdelta hdeltaOne j)⟩

/-- The local multiplicative-slack rate ceiling is exactly the mesh endpoint. -/
lemma one_sub_localSlack_mul_localAgreement {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : 0 ≤ endpoint) :
    (1 - localSlack delta endpoint) * localAgreement delta endpoint = endpoint := by
  have hAgreement : localAgreement delta endpoint ≠ 0 :=
    ne_of_gt (localAgreement_pos_of_endpoint_nonneg hdelta hEndpoint)
  rw [localSlack]
  field_simp
  rw [localAgreement, halfGap]
  ring

/-- The rate ceiling identity specialized to an endpoint of the half-gap mesh. -/
lemma one_sub_localSlack_mul_localAgreement_endpoint {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (j : ℕ) :
    (1 - localSlack delta (endpoint delta j)) * localAgreement delta (endpoint delta j) =
      endpoint delta j := by
  exact one_sub_localSlack_mul_localAgreement hdelta (endpoint_pos hdelta hdeltaOne j).le

/-- A boundary canary: for gap `1/2`, zero selects the first quarter endpoint and the top feasible
rate selects the second, truncated endpoint.  This detects off-by-one errors in `binIndex`. -/
lemma half_gap_mesh_boundary_canary :
    binCount (1 / 2 : ℝ) = 2 ∧
      binIndex (1 / 2 : ℝ) 0 = 0 ∧
      endpoint (1 / 2 : ℝ) 0 = 1 / 4 ∧
      binIndex (1 / 2 : ℝ) (1 / 2) = 1 ∧
      endpoint (1 / 2 : ℝ) 1 = 1 / 2 := by
  norm_num [binCount, binIndex, endpoint, halfGap]

/-- Nonintegral and single-bin boundary canaries for the ceiling and truncation conventions. -/
lemma rate_mesh_rounding_canary :
    binCount (3 / 10 : ℝ) = 5 ∧
      endpoint (3 / 10 : ℝ) 0 = 3 / 20 ∧
      endpoint (3 / 10 : ℝ) 4 = 7 / 10 ∧
      binCount (4 / 5 : ℝ) = 1 ∧
      endpoint (4 / 5 : ℝ) 0 = 1 / 5 := by
  norm_num [binCount, endpoint, halfGap, Nat.ceil_eq_iff]

/-- At a nonintegral bin boundary, the donor and requested integer thresholds agree exactly. -/
lemma rate_mesh_threshold_canary :
    Nat.ceil
        (localAgreement (3 / 10 : ℝ)
          (endpoint (3 / 10 : ℝ) (binIndex (3 / 10 : ℝ) ((2 : ℝ) / 3))) * 3) = 3 ∧
      2 + Nat.ceil ((3 / 10 : ℝ) * 3) = 3 := by
  have hIndex : Nat.ceil ((((2 : ℝ) / 3) / ((3 / 10 : ℝ) / 2))) = 5 := by
    norm_num [Nat.ceil_eq_iff]
  have hThreshold : Nat.ceil ((9 : ℝ) / 10) = 1 := by
    norm_num [Nat.ceil_eq_iff]
  rw [show binIndex (3 / 10 : ℝ) ((2 : ℝ) / 3) = 4 by
    rw [binIndex, halfGap, hIndex]
    norm_num]
  rw [show endpoint (3 / 10 : ℝ) 4 = 7 / 10 by
    norm_num [endpoint, halfGap]]
  rw [show localAgreement (3 / 10 : ℝ) (7 / 10) = 17 / 20 by
    norm_num [localAgreement, halfGap]]
  norm_num [hThreshold, Nat.ceil_eq_iff]

end
end RateCover
end AllRateListDecoding
end ReedSolomon
