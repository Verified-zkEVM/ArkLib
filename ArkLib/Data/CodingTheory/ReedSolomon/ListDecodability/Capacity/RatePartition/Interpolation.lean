/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.Cover
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.UniformThresholds
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FreeOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Free-order parameters on the finite rate cover

This module instantiates the free-order hidden-derivative parameter estimates at every endpoint of
the finite `delta / 2` rate cover.  It is the parameter bridge between `RateCover` and
`UniformThresholds`: first one derivative order is selected for all rate bins, then one block-length
threshold is selected after that shared order is fixed.

The imported source estimates are adapted from Kai Zhe Zheng's `rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`, as documented in
`HiddenDerivative.Parameters.FreeOrder`.  The finite-cover construction and uniformization in this
module are proved here for the finite rate cover; they are not attributed to a numbered theorem in
source development.  No interpolation-existence or root-counting conclusion is asserted here.
-/

@[expose] public section

namespace ReedSolomon
namespace RateBinInterpolation

open HiddenDerivative
open RateCover
open UniformThresholds

noncomputable section

/-- Agreement fraction attached to a finite rate bin. -/
def binAgreement (delta : ℝ) (i : Fin (binCount delta)) : ℝ :=
  localAgreement delta (endpoint delta i)

/-- Multiplicative slack attached to a finite rate bin. -/
def binSlack (delta : ℝ) (i : Fin (binCount delta)) : ℝ :=
  localSlack delta (endpoint delta i)

/-- Every rate bin supplies a pointwise free-order threshold for the source's elementary scalar
conditions. -/
theorem exists_bin_order_threshold {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (i : Fin (binCount delta)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧
      2 ≤ binSlack delta i * (HiddenDerivative.multiplicity d : ℝ) / 16 ∧
      1 < (binSlack delta i ^ 3 / 262144) *
          ((1 - binSlack delta i) * binAgreement delta i / 2) *
            (d : ℝ) ^ rankSavingExponent (binSlack delta i) := by
  have hepsilon := localAgreement_endpoint_mem_Ioo hdelta hdeltaOne i
  have htheta := localSlack_endpoint_mem_Ioo hdelta hdeltaOne i
  exact exists_freeOrderElementaryThreshold hepsilon.1 htheta.1 htheta.2

/-- One derivative order, chosen before the rate bin, satisfies the source's elementary scalar
conditions in every bin. -/
theorem exists_uniform_bin_order {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaOne : delta < 1) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ i : Fin (binCount delta),
      2 ≤ binSlack delta i * (HiddenDerivative.multiplicity d : ℝ) / 16 ∧
      1 < (binSlack delta i ^ 3 / 262144) *
          ((1 - binSlack delta i) * binAgreement delta i / 2) *
            (d : ℝ) ^ rankSavingExponent (binSlack delta i) := by
  let threshold : Fin (binCount delta) → ℕ := fun i =>
    (exists_bin_order_threshold hdelta hdeltaOne i).choose
  let d := protectedFamilyMaximum 2 threshold
  refine ⟨d, minimum_le_protectedFamilyMaximum 2 threshold, fun i => ?_⟩
  have hi : threshold i ≤ d := le_protectedFamilyMaximum 2 threshold i
  exact ((exists_bin_order_threshold hdelta hdeltaOne i).choose_spec d hi).2

/-- At a mesh endpoint, the ambient dimension is exactly the floor of that endpoint times
the block length. -/
theorem ambientDimension_eq_endpoint_floor {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaOne : delta < 1) (i : Fin (binCount delta)) (n : ℕ) :
    ambientDimension (binAgreement delta i) (binSlack delta i) n =
      ⌊endpoint delta i * n⌋₊ := by
  rw [ambientDimension]
  congr 1
  rw [binAgreement, binSlack,
    one_sub_localSlack_mul_localAgreement_endpoint hdelta hdeltaOne i]

/-- A code dimension whose rate is covered by a bin lies inside that bin's ambient
dimension. -/
theorem messageDim_le_bin_ambientDimension {delta : ℝ} {n k : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hn : 0 < n)
    (i : Fin (binCount delta)) (hRate : (k : ℝ) / n ≤ endpoint delta i) :
    k ≤ ambientDimension (binAgreement delta i) (binSlack delta i) n := by
  rw [ambientDimension_eq_endpoint_floor hdelta hdeltaOne]
  exact messageDim_le_floor_mul_of_natRatio_le hn hRate

/-- The bin agreement threshold of a covering bin is no larger than the requested additive-gap
threshold. -/
theorem bin_agreementThreshold_le_requested {delta : ℝ} {n k : ℕ}
    (hdelta : 0 ≤ delta) (hn : 0 < n) (i : Fin (binCount delta))
    (hEndpoint : endpoint delta i ≤ (k : ℝ) / n + halfGap delta) :
    agreementThreshold (binAgreement delta i) n ≤ k + ⌈delta * n⌉₊ := by
  simpa [agreementThreshold, binAgreement] using
    ceil_localAgreement_mul_le_messageDim_add_ceil_gap hdelta hn hEndpoint

/-- Select the free-order parameters for one actual code rate.

The endpoint identity turns the ambient rate into the covering endpoint.  Consequently the
actual message space embeds in the ambient space, while the bin agreement threshold is no
larger than the requested additive-gap threshold. -/
theorem exists_covering_bin_parameters {delta : ℝ} {n k : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hn : 0 < n)
    (hRate : (k : ℝ) / n ≤ 1 - delta) :
    ∃ i : Fin (binCount delta),
      binAgreement delta i ∈ Set.Ioo 0 1 ∧
      binSlack delta i ∈ Set.Ioo 0 1 ∧
      (1 - binSlack delta i) * binAgreement delta i = endpoint delta i ∧
      k ≤ ambientDimension (binAgreement delta i) (binSlack delta i) n ∧
      agreementThreshold (binAgreement delta i) n ≤ k + ⌈delta * n⌉₊ := by
  obtain ⟨i, hEndpointPos, hRateEndpoint, hEndpointRate⟩ :=
    exists_fin_endpoint_cover_natRatio hdelta hdeltaOne hn hRate
  refine ⟨i, localAgreement_endpoint_mem_Ioo hdelta hdeltaOne i,
    localSlack_endpoint_mem_Ioo hdelta hdeltaOne i,
    one_sub_localSlack_mul_localAgreement_endpoint hdelta hdeltaOne i,
    messageDim_le_bin_ambientDimension hdelta hdeltaOne hn i hRateEndpoint, ?_⟩
  exact bin_agreementThreshold_le_requested hdelta.le hn i hEndpointRate

/-- Every bin agreement threshold is at most the block length. -/
theorem bin_agreementThreshold_le_blockLength {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (i : Fin (binCount delta)) (n : ℕ) :
    agreementThreshold (binAgreement delta i) n ≤ n := by
  rw [agreementThreshold_le_iff]
  have hepsilon := (localAgreement_endpoint_mem_Ioo hdelta hdeltaOne i).2.le
  simpa [binAgreement] using mul_le_mul_of_nonneg_right hepsilon (Nat.cast_nonneg n)

/-- If an endpoint covers at least four units, its rounded ambient dimension minus one retains at
least half of the unrounded endpoint budget. -/
theorem half_endpoint_mul_le_ambientDimension_sub_one {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (i : Fin (binCount delta)) (n : ℕ)
    (hFour : (4 : ℝ) ≤ endpoint delta i * n) :
    endpoint delta i * n / 2 ≤
      ((ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 : ℕ) : ℝ) := by
  rw [ambientDimension_eq_endpoint_floor hdelta hdeltaOne]
  have hFloorFour : 4 ≤ ⌊endpoint delta i * (n : ℝ)⌋₊ := Nat.le_floor hFour
  have hFloorOne : 1 ≤ ⌊endpoint delta i * (n : ℝ)⌋₊ := hFloorFour.trans' (by omega)
  have hRound := Nat.lt_floor_add_one (endpoint delta i * (n : ℝ))
  rw [Nat.cast_sub hFloorOne]
  push_cast at hRound ⊢
  nlinarith

/-- Under the endpoint scale bound, the rounded interpolation budget is bounded by the simple
binwise constant `ceil(2m/a)`. -/
theorem interpolationDegreeBudget_le_bin_ceiling {delta : ℝ} {d n : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hn : 0 < n)
    (i : Fin (binCount delta)) (hFour : (4 : ℝ) ≤ endpoint delta i * n) :
    interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n ≤
      ⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta i⌉₊ := by
  have ha : 0 < endpoint delta i := endpoint_pos hdelta hdeltaOne i
  have hA := bin_agreementThreshold_le_blockLength hdelta hdeltaOne i n
  have hDenLower :=
    half_endpoint_mul_le_ambientDimension_sub_one hdelta hdeltaOne i n hFour
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hDenPos :
      0 < ((ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 : ℕ) : ℝ) :=
    lt_of_lt_of_le (by positivity : 0 < endpoint delta i * (n : ℝ) / 2) hDenLower
  rw [interpolationDegreeBudget]
  apply Nat.ceil_mono
  apply (div_le_iff₀ hDenPos).2
  have hNumerator :
      ((HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n : ℕ) : ℝ) ≤
        (HiddenDerivative.multiplicity d : ℝ) * n := by
    exact_mod_cast Nat.mul_le_mul_left (HiddenDerivative.multiplicity d) hA
  calc
    ((HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n : ℕ) : ℝ) ≤
        (HiddenDerivative.multiplicity d : ℝ) * n := hNumerator
    _ = ((2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta i) *
        (endpoint delta i * n / 2) := by field_simp
    _ ≤ ((2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta i) *
        ((ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 : ℕ) : ℝ) := by
      gcongr

/-- A single explicit block-length threshold for all rate bins at the already-selected derivative
order.  Its four components enforce `m ≤ n`, `d + 1 ≤ a₀ n`, `4 ≤ a₀ n`, and
`ceil(2m/a₀) < n`, respectively. -/
def binBlockLengthThreshold (delta : ℝ) (d : ℕ) : ℕ :=
  max (HiddenDerivative.multiplicity d)
    (max ⌈((d + 1 : ℕ) : ℝ) / endpoint delta 0⌉₊
      (max ⌈(4 : ℝ) / endpoint delta 0⌉₊
        (⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta 0⌉₊ + 1)))

/-- Once `n` clears `binBlockLengthThreshold`, every bin satisfies the four parameter conditions
needed later: the shared order lies below `K`, the agreement threshold is at most `n`, the degree
budget is strictly below `n`, and the contact budget is at most `n²`. -/
theorem bin_large_block_conditions {delta : ℝ} {d n : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hd : 2 ≤ d)
    (hThreshold : binBlockLengthThreshold delta d ≤ n)
    (i : Fin (binCount delta)) :
    d < ambientDimension (binAgreement delta i) (binSlack delta i) n ∧
      agreementThreshold (binAgreement delta i) n ≤ n ∧
      interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n < n ∧
      HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n ≤ n ^ 2 := by
  have haZero : 0 < endpoint delta 0 := endpoint_pos hdelta hdeltaOne 0
  have haMono : endpoint delta 0 ≤ endpoint delta i :=
    endpoint_zero_le_endpoint hdelta i
  have hMultiplicity : HiddenDerivative.multiplicity d ≤ n :=
    (show HiddenDerivative.multiplicity d ≤ binBlockLengthThreshold delta d by
      simp [binBlockLengthThreshold]).trans hThreshold
  have hn : 0 < n :=
    (multiplicity_pos (lt_of_lt_of_le (by omega) hd)).trans_le hMultiplicity
  have hOrderCeil :
      ⌈((d + 1 : ℕ) : ℝ) / endpoint delta 0⌉₊ ≤ n :=
    (show ⌈((d + 1 : ℕ) : ℝ) / endpoint delta 0⌉₊ ≤
        binBlockLengthThreshold delta d by simp [binBlockLengthThreshold]).trans hThreshold
  have hOrderZero : ((d + 1 : ℕ) : ℝ) ≤ endpoint delta 0 * n := by
    have := Nat.ceil_le.mp hOrderCeil
    exact (div_le_iff₀ haZero).mp this |>.trans_eq (mul_comm _ _)
  have hOrder : ((d + 1 : ℕ) : ℝ) ≤ endpoint delta i * n :=
    hOrderZero.trans <| mul_le_mul_of_nonneg_right haMono (Nat.cast_nonneg n)
  have hdK : d < ambientDimension (binAgreement delta i) (binSlack delta i) n := by
    rw [ambientDimension_eq_endpoint_floor hdelta hdeltaOne]
    have : d + 1 ≤ ⌊endpoint delta i * (n : ℝ)⌋₊ := Nat.le_floor hOrder
    omega
  have hFourCeil : ⌈(4 : ℝ) / endpoint delta 0⌉₊ ≤ n :=
    (show ⌈(4 : ℝ) / endpoint delta 0⌉₊ ≤ binBlockLengthThreshold delta d by
      simp [binBlockLengthThreshold]).trans hThreshold
  have hFourZero : (4 : ℝ) ≤ endpoint delta 0 * n := by
    have := Nat.ceil_le.mp hFourCeil
    exact (div_le_iff₀ haZero).mp this |>.trans_eq (mul_comm _ _)
  have hFour : (4 : ℝ) ≤ endpoint delta i * n :=
    hFourZero.trans <| mul_le_mul_of_nonneg_right haMono (Nat.cast_nonneg n)
  have hBudgetCeil :
      ⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta 0⌉₊ + 1 ≤ n :=
    (show ⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta 0⌉₊ + 1 ≤
        binBlockLengthThreshold delta d by simp [binBlockLengthThreshold]).trans hThreshold
  have hCeilMono :
      ⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta i⌉₊ ≤
        ⌈(2 * (HiddenDerivative.multiplicity d : ℝ)) / endpoint delta 0⌉₊ := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_left (by positivity) haZero haMono
  have hBudget :
      interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n < n :=
    (interpolationDegreeBudget_le_bin_ceiling hdelta hdeltaOne hn i hFour).trans_lt <| by
      omega
  have hAgreement := bin_agreementThreshold_le_blockLength hdelta hdeltaOne i n
  have hContact :
      HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n ≤ n ^ 2 := by
    calc
      HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n ≤ n * n :=
        Nat.mul_le_mul hMultiplicity hAgreement
      _ = n ^ 2 := by ring
  exact ⟨hdK, hAgreement, hBudget, hContact⟩

/-- The complete parameter certificate attached to one rate bin after uniformization. -/
structure InterpolationParameterBounds
    (delta : ℝ) (d n q : ℕ) (i : Fin (binCount delta)) : Prop where
  orderAtLeastTwo : 2 ≤ d
  order_lt_ambient : d < ambientDimension (binAgreement delta i) (binSlack delta i) n
  agreement_le_blockLength : agreementThreshold (binAgreement delta i) n ≤ n
  degreeBudget_lt_fieldSize :
    interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n < q
  contactBudget_le_fieldSize_sq :
    HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n ≤ q ^ 2
  boxWidthTargetAtLeastTwo :
    2 ≤ binSlack delta i * (HiddenDerivative.multiplicity d : ℝ) / 16
  boxWidth_le_multiplicity :
    interpolationBoxWidth (binSlack delta i) d ≤ HiddenDerivative.multiplicity d
  higherJets_fit_degreeBudget :
    higherJetDegreeBudget (binSlack delta i) d +
        2 * interpolationBoxWidth (binSlack delta i) d ≤
      interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n
  boxFamily_fits_contactBudget :
    (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1) *
        (higherJetDegreeBudget (binSlack delta i) d +
          3 * interpolationBoxWidth (binSlack delta i) d) ≤
      HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n
  rankComparison :
    1 < (binSlack delta i ^ 3 / 262144) *
      (((ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 : ℕ) : ℝ) /
        (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent (binSlack delta i)

/-- Complete free-order parameter uniformization for the finite rate mesh.

The witnesses `d` and `N` precede the block length, field size, and rate bin.  Besides the source's
scalar free-order inequalities, the conclusion uniformly supplies `d < K`, `A ≤ n`, `B < q`, and
`mA ≤ q²`. -/
theorem exists_uniform_rateBin_parameters {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ d N : ℕ, 2 ≤ d ∧ ∀ n q : ℕ, N ≤ n → n ≤ q →
      ∀ i : Fin (binCount delta),
        (2 ≤ binSlack delta i * (HiddenDerivative.multiplicity d : ℝ) / 16 ∧
          1 < (binSlack delta i ^ 3 / 262144) *
            ((1 - binSlack delta i) * binAgreement delta i / 2) *
              (d : ℝ) ^ rankSavingExponent (binSlack delta i)) ∧
        d < ambientDimension (binAgreement delta i) (binSlack delta i) n ∧
        agreementThreshold (binAgreement delta i) n ≤ n ∧
        interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n < q ∧
        HiddenDerivative.multiplicity d * agreementThreshold (binAgreement delta i) n ≤ q ^ 2 := by
  obtain ⟨d, hd, hScalar⟩ := exists_uniform_bin_order hdelta hdeltaOne
  refine ⟨d, binBlockLengthThreshold delta d, hd, fun n q hn hnq i => ?_⟩
  rcases bin_large_block_conditions hdelta hdeltaOne hd hn i with
    ⟨hdK, hAgreement, hBudget, hContact⟩
  exact ⟨hScalar i, hdK, hAgreement, hBudget.trans_le hnq,
    hContact.trans (Nat.pow_le_pow_left hnq 2)⟩

/-- One order and one block threshold, both depending only on `delta`, produce a complete source
certificate in every finite rate bin and over every later field size `q ≥ n`. -/
theorem exists_uniform_bin_certificates {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ d N : ℕ, 2 ≤ d ∧ ∀ n q : ℕ, N ≤ n → n ≤ q →
      ∀ i : Fin (binCount delta), InterpolationParameterBounds delta d n q i := by
  obtain ⟨d, N, hd, hUniform⟩ := exists_uniform_rateBin_parameters hdelta hdeltaOne
  refine ⟨d, N, hd, fun n q hn hnq i => ?_⟩
  rcases hUniform n q hn hnq i with
    ⟨⟨hWidth, hLarge⟩, hdK, hAgreement, hBudget, hContact⟩
  have hepsilon := localAgreement_endpoint_mem_Ioo hdelta hdeltaOne i
  have htheta := localSlack_endpoint_mem_Ioo hdelta hdeltaOne i
  have hnPos := blockLength_pos_of_order_lt_ambientDimension hdK
  have hSlacks := freeGlobalDimensionSlacks hepsilon.1 htheta.1 htheta.2
    (lt_of_lt_of_le (by omega) hd) hnPos hdK
  exact {
    orderAtLeastTwo := hd
    order_lt_ambient := hdK
    agreement_le_blockLength := hAgreement
    degreeBudget_lt_fieldSize := hBudget
    contactBudget_le_fieldSize_sq := hContact
    boxWidthTargetAtLeastTwo := hWidth
    boxWidth_le_multiplicity := hSlacks.1
    higherJets_fit_degreeBudget := hSlacks.2.1
    boxFamily_fits_contactBudget := hSlacks.2.2
    rankComparison := freeOrder_rank_comparison htheta.1 hd hdK hLarge
  }

/-- A certificate for the selected bin together with the two comparisons to the actual code
parameters. -/
structure CoveringInterpolationParameterBounds (delta : ℝ) (d n q k : ℕ)
    (i : Fin (binCount delta)) : Prop extends InterpolationParameterBounds delta d n q i where
  agreement_mem : binAgreement delta i ∈ Set.Ioo 0 1
  slack_mem : binSlack delta i ∈ Set.Ioo 0 1
  rateIdentity : (1 - binSlack delta i) * binAgreement delta i = endpoint delta i
  messageDim_le_ambient :
    k ≤ ambientDimension (binAgreement delta i) (binSlack delta i) n
  binAgreement_le_requested :
    agreementThreshold (binAgreement delta i) n ≤ k + ⌈delta * n⌉₊

/-- Uniform parameters for a covering rate bin.

The shared witnesses `d` and `N` depend only on `delta`.  After the actual block length, field size,
and message dimension arrive, the theorem chooses a covering bin and returns its complete parameter
certificate and the exact containment/rounding bridges to the requested code parameters. -/
theorem exists_uniform_covered_bin_certificates {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ d N : ℕ, 2 ≤ d ∧ ∀ n q k : ℕ, N ≤ n → n ≤ q →
      (k : ℝ) / n ≤ 1 - delta →
      ∃ i : Fin (binCount delta), CoveringInterpolationParameterBounds delta d n q k i := by
  obtain ⟨d, N, hd, hCertificates⟩ := exists_uniform_bin_certificates hdelta hdeltaOne
  refine ⟨d, N, hd, fun n q k hn hnq hRate => ?_⟩
  let i₀ : Fin (binCount delta) := ⟨0, binCount_pos hdelta hdeltaOne⟩
  have hnPos : 0 < n :=
    blockLength_pos_of_order_lt_ambientDimension
      (hCertificates n q hn hnq i₀).order_lt_ambient
  obtain ⟨i, hepsilon, htheta, hIdentity, hMessage, hAgreement⟩ :=
    exists_covering_bin_parameters hdelta hdeltaOne hnPos hRate
  exact ⟨i, {
    toInterpolationParameterBounds := hCertificates n q hn hnq i
    agreement_mem := hepsilon
    slack_mem := htheta
    rateIdentity := hIdentity
    messageDim_le_ambient := hMessage
    binAgreement_le_requested := hAgreement
  }⟩

/-! ### Rounding and bin-separation canaries -/

/-- For gap `1/2` and order two, the strict degree-budget component is the active maximum; its
final `+ 1` makes the explicit uniform block threshold exactly `65`. -/
example : binBlockLengthThreshold (1 / 2 : ℝ) 2 = 65 := by
  norm_num [binBlockLengthThreshold, HiddenDerivative.multiplicity, endpoint, halfGap,
    Nat.ceil_eq_iff]

/-- At the same threshold, the two distinct mesh bins produce different rounded ambient,
agreement, and interpolation budgets.  This rejects accidental use of one bin's parameters for
every rate. -/
example :
    let i₀ : Fin (binCount (1 / 2 : ℝ)) := ⟨0, by norm_num [binCount, halfGap]⟩
    let i₁ : Fin (binCount (1 / 2 : ℝ)) := ⟨1, by norm_num [binCount, halfGap]⟩
    ambientDimension (binAgreement (1 / 2 : ℝ) i₀) (binSlack (1 / 2 : ℝ) i₀) 65 = 16 ∧
      agreementThreshold (binAgreement (1 / 2 : ℝ) i₀) 65 = 33 ∧
      interpolationDegreeBudget 2 (binAgreement (1 / 2 : ℝ) i₀)
        (binSlack (1 / 2 : ℝ) i₀) 65 = 18 ∧
      ambientDimension (binAgreement (1 / 2 : ℝ) i₁) (binSlack (1 / 2 : ℝ) i₁) 65 = 32 ∧
      agreementThreshold (binAgreement (1 / 2 : ℝ) i₁) 65 = 49 ∧
      interpolationDegreeBudget 2 (binAgreement (1 / 2 : ℝ) i₁)
        (binSlack (1 / 2 : ℝ) i₁) 65 = 13 := by
  have h33 : ⌈(65 / 2 : ℝ)⌉₊ = 33 := by norm_num [Nat.ceil_eq_iff]
  have h49 : ⌈(195 / 4 : ℝ)⌉₊ = 49 := by norm_num [Nat.ceil_eq_iff]
  norm_num [binCount, binAgreement, binSlack, localAgreement, localSlack, endpoint, halfGap,
    ambientDimension, agreementThreshold, interpolationDegreeBudget,
    HiddenDerivative.multiplicity, h33, h49, Nat.ceil_eq_iff]

/-- The consumer theorem uses the same selected `d` and `N` at both extremes of the feasible rate
interval.  This rejects a regression that silently moves the order choice behind the rate. -/
example :
    ∃ d N : ℕ, 2 ≤ d ∧
      (∃ i₀ : Fin (binCount (1 / 2 : ℝ)),
        CoveringInterpolationParameterBounds (1 / 2 : ℝ) d (2 * (N + 1)) (2 * (N + 1)) 0 i₀) ∧
      (∃ i₁ : Fin (binCount (1 / 2 : ℝ)),
        CoveringInterpolationParameterBounds (1 / 2 : ℝ) d
          (2 * (N + 1)) (2 * (N + 1)) (N + 1) i₁) := by
  obtain ⟨d, N, hd, hUniform⟩ :=
    exists_uniform_covered_bin_certificates (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
  have hThreshold : N ≤ 2 * (N + 1) := by omega
  obtain ⟨i₀, hi₀⟩ := hUniform (2 * (N + 1)) (2 * (N + 1)) 0
    hThreshold le_rfl (by norm_num)
  obtain ⟨i₁, hi₁⟩ := hUniform (2 * (N + 1)) (2 * (N + 1)) (N + 1)
    hThreshold le_rfl (by
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((N : ℝ) + 1))]
      nlinarith)
  exact ⟨d, N, hd, ⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩⟩

end
end RateBinInterpolation
end ReedSolomon
