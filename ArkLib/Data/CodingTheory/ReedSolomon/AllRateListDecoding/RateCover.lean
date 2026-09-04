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

The identity `(1 - theta) * epsilon = a` is proved below. Coverage of the full rate interval and
the integer rounding lemmas are deliberately separate later obligations.
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

/-- Agreement parameter attached to a mesh endpoint. -/
def localAgreement (delta endpoint : ℝ) : ℝ :=
  endpoint + halfGap delta

/-- Multiplicative slack attached to a mesh endpoint. -/
def localSlack (delta endpoint : ℝ) : ℝ :=
  halfGap delta / localAgreement delta endpoint

lemma halfGap_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < halfGap delta := by
  exact div_pos hdelta (by norm_num)

lemma endpoint_pos {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1) (j : ℕ) :
    0 < endpoint delta j := by
  rw [endpoint]
  exact lt_min
    (mul_pos (by positivity) (halfGap_pos hdelta))
    (sub_pos.mpr hdeltaOne)

lemma endpoint_le_one_sub (delta : ℝ) (j : ℕ) :
    endpoint delta j ≤ 1 - delta := by
  exact min_le_right _ _

lemma localAgreement_pos_of_endpoint_nonneg {delta endpoint : ℝ}
    (hdelta : 0 < delta) (hEndpoint : 0 ≤ endpoint) :
    0 < localAgreement delta endpoint := by
  rw [localAgreement]
  exact add_pos_of_nonneg_of_pos hEndpoint (halfGap_pos hdelta)

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

end
end RateCover
end AllRateListDecoding
end ReedSolomon
