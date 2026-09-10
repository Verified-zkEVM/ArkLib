/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.Interpolation
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FreeOrderDimension
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Lattice.RoundedScaledShell


/-!
# Uniform interpolation-space dimension bounds

This module strengthens the finite-rate-bin parameter bounds with the strict finite comparison
between the certified enlarged local-rank budget and the dimension of the exact interpolation
space.  Both the derivative order and the block-length threshold depend only on the requested gap;
they are selected before the block length, field size, message dimension, rate bin, and coefficient
field.

The scalar rank comparison and scaled-shell estimates are adapted, with permission, from Kai Zhe
Zheng's `rs-ld-mca` formalization at commit
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`.  The free-order extension was contributed through
PR 1 by Pratyush Mishra; its source commit records Codex as author and Pratyush Mishra as committer.
The finite mesh, exact interpolation index, and uniform parameter choice here are ArkLib-specific.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace RateBinDimensionBound

open HiddenDerivative
open RateCover
open UniformThresholds
open RateBinInterpolation

noncomputable section

/-- Every bin has one eventual order threshold satisfying both the scalar free-order
conditions and the discrete shell comparison. -/
theorem exists_bin_order_threshold_with_shell {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (i : Fin (binCount delta)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧
      2 ≤ binSlack delta i * (multiplicity d : ℝ) / 16 ∧
      scaledExponentCount d (interpolationWeightBudget (binSlack delta i) d + d ^ 3) ≤
        scaledShellFactor (binSlack delta i) d *
          goodScaledExponentCount d (interpolationWeightBudget (binSlack delta i) d)
            (higherJetDegreeBudget (binSlack delta i) d) ∧
      (scaledShellFactor (binSlack delta i) d : ℝ) ≤
        2 * (d : ℝ) ^ ((5 - binSlack delta i) / (5 + binSlack delta i)) ∧
      1 < (binSlack delta i ^ 3 / 262144) *
        ((1 - binSlack delta i) * binAgreement delta i / 2) *
          (d : ℝ) ^ rankSavingExponent (binSlack delta i) := by
  have htheta := localSlack_endpoint_mem_Ioo hdelta hdeltaOne i
  obtain ⟨dScalar, hScalar⟩ :=
    RateBinInterpolation.exists_bin_order_threshold hdelta hdeltaOne i
  obtain ⟨dShell, hShell⟩ :=
    exists_scaledShellThreshold_for_freeParameters htheta.1 htheta.2
  refine ⟨max dScalar dShell, fun d hd ↦ ?_⟩
  have hdScalar : dScalar ≤ d := (Nat.le_max_left _ _).trans hd
  have hdShell : dShell ≤ d := (Nat.le_max_right _ _).trans hd
  rcases hScalar d hdScalar with ⟨hdTwo, hWidth, hRank⟩
  exact ⟨hdTwo, hWidth, hShell d hdShell,
    scaledShellFactor_cast_le_two_rpow_explicit htheta.1 htheta.2 (by omega), hRank⟩

/-- One derivative order clears both the scalar and shell thresholds in every rate bin.  The
finite maximum is taken after first combining the two pointwise thresholds in each bin. -/
theorem exists_uniform_bin_order_with_shell {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ i : Fin (binCount delta),
      2 ≤ binSlack delta i * (multiplicity d : ℝ) / 16 ∧
      scaledExponentCount d (interpolationWeightBudget (binSlack delta i) d + d ^ 3) ≤
        scaledShellFactor (binSlack delta i) d *
          goodScaledExponentCount d (interpolationWeightBudget (binSlack delta i) d)
            (higherJetDegreeBudget (binSlack delta i) d) ∧
      (scaledShellFactor (binSlack delta i) d : ℝ) ≤
        2 * (d : ℝ) ^ ((5 - binSlack delta i) / (5 + binSlack delta i)) ∧
      1 < (binSlack delta i ^ 3 / 262144) *
        ((1 - binSlack delta i) * binAgreement delta i / 2) *
          (d : ℝ) ^ rankSavingExponent (binSlack delta i) := by
  let threshold : Fin (binCount delta) → ℕ := fun i ↦
    (exists_bin_order_threshold_with_shell hdelta hdeltaOne i).choose
  let d := protectedFamilyMaximum 2 threshold
  refine ⟨d, minimum_le_protectedFamilyMaximum 2 threshold, fun i ↦ ?_⟩
  have hi : threshold i ≤ d := le_protectedFamilyMaximum 2 threshold i
  exact (exists_bin_order_threshold_with_shell hdelta hdeltaOne i).choose_spec d hi |>.2

/-- The finite certificate needs more room than the rectangular parameter bounds: `2d+3 < K`
supplies `d < K-1`, while the cubic threshold at order `2d+3` also makes the exact jet-degree
floor smaller than the later block length. -/
def finiteCertificateBlockLengthThreshold (delta : ℝ) (d : ℕ) : ℕ :=
  max (binBlockLengthThreshold delta d)
    (binBlockLengthThreshold delta (2 * d + 3))

/-- The strengthened block threshold retains all parameter side conditions and leaves a full unit
between the chosen order and `K-1`. -/
theorem finite_certificate_large_block_conditions {delta : ℝ} {d n : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hd : 2 ≤ d)
    (hThreshold : finiteCertificateBlockLengthThreshold delta d ≤ n)
    (i : Fin (binCount delta)) :
    d + 1 < ambientDimension (binAgreement delta i) (binSlack delta i) n ∧
      d < ambientDimension (binAgreement delta i) (binSlack delta i) n ∧
      agreementThreshold (binAgreement delta i) n ≤ n ∧
      interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n < n ∧
      HiddenDerivative.multiplicity d *
        agreementThreshold (binAgreement delta i) n ≤ n ^ 2 := by
  have hBase : binBlockLengthThreshold delta d ≤ n :=
    (Nat.le_max_left _ _).trans hThreshold
  have hLarge : binBlockLengthThreshold delta (2 * d + 3) ≤ n :=
    (Nat.le_max_right _ _).trans hThreshold
  rcases bin_large_block_conditions hdelta hdeltaOne hd hBase i with
    ⟨hdK, hAgreement, hBudget, hContact⟩
  have hLargeOrder :=
    (bin_large_block_conditions hdelta hdeltaOne (d := 2 * d + 3)
      (by omega) hLarge i).1
  exact ⟨by omega, hdK, hAgreement, hBudget, hContact⟩

/-- At the strengthened block threshold, the exact cap-free interpolation space has every jet
degree strictly below the block length.  This is a separate bound from the rectangular
degree budget `B < n`. -/
theorem exactInterpolationJetDegreeFloor_lt_blockLength {delta : ℝ} {d n : ℕ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hd : 2 ≤ d)
    (hThreshold : finiteCertificateBlockLengthThreshold delta d ≤ n)
    (i : Fin (binCount delta)) :
    exactInterpolationJetDegreeFloor
        (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1)
        (agreementThreshold (binAgreement delta i) n) d (d ^ 3) < n := by
  let e := 2 * d + 3
  have haZero : 0 < endpoint delta 0 := endpoint_pos hdelta hdeltaOne 0
  have haMono : endpoint delta 0 ≤ endpoint delta i :=
    endpoint_zero_le_endpoint hdelta i
  have hLarge : binBlockLengthThreshold delta e ≤ n :=
    (Nat.le_max_right _ _).trans hThreshold
  have hBudgetCeil :
      ⌈(2 * (HiddenDerivative.multiplicity e : ℝ)) / endpoint delta 0⌉₊ + 1 ≤ n :=
    (show ⌈(2 * (HiddenDerivative.multiplicity e : ℝ)) / endpoint delta 0⌉₊ + 1 ≤
        binBlockLengthThreshold delta e by simp [binBlockLengthThreshold]).trans hLarge
  have hCeilLt :
      ⌈(2 * (HiddenDerivative.multiplicity e : ℝ)) / endpoint delta 0⌉₊ < n := by
    omega
  have hScaleZero :
      2 * (HiddenDerivative.multiplicity e : ℝ) < endpoint delta 0 * (n : ℝ) := by
    have hRatio :
        (2 * (HiddenDerivative.multiplicity e : ℝ)) / endpoint delta 0 < (n : ℝ) :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast hCeilLt)
    exact (div_lt_iff₀ haZero).mp hRatio |>.trans_eq (mul_comm _ _)
  have hScale :
      ((d ^ 3 + d + 2 : ℕ) : ℝ) < endpoint delta i * (n : ℝ) := by
    calc
      ((d ^ 3 + d + 2 : ℕ) : ℝ) ≤
          2 * (HiddenDerivative.multiplicity e : ℝ) := by
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        simp only [HiddenDerivative.multiplicity, e]
        push_cast
        have hdNonneg : (0 : ℝ) ≤ d := by positivity
        nlinarith [sq_nonneg (d : ℝ),
          mul_nonneg (sq_nonneg (d : ℝ)) hdNonneg]
      _ < endpoint delta 0 * (n : ℝ) := hScaleZero
      _ ≤ endpoint delta i * (n : ℝ) := by gcongr
  have hKLarge :
      d ^ 3 + d + 2 ≤
        ambientDimension (binAgreement delta i) (binSlack delta i) n := by
    rw [ambientDimension_eq_endpoint_floor hdelta hdeltaOne]
    exact Nat.le_floor hScale.le
  have hDenominator :
      d ^ 3 <
        (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1) - d := by
    omega
  have hAgreement := bin_agreementThreshold_le_blockLength hdelta hdeltaOne i n
  have hn : 0 < n := by omega
  rw [exactInterpolationJetDegreeFloor,
    Nat.div_lt_iff_lt_mul (by omega :
      0 < (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1) - d)]
  have hNumerator :
      d ^ 3 * agreementThreshold (binAgreement delta i) n - 1 < d ^ 3 * n := by
    have hMul := Nat.mul_le_mul_left (d ^ 3) hAgreement
    have hPos : 0 < d ^ 3 * n := Nat.mul_pos (by positivity) hn
    omega
  have hDenominatorMul :
      d ^ 3 * n <
        n * ((ambientDimension (binAgreement delta i) (binSlack delta i) n - 1) - d) := by
    simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hDenominator hn
  exact hNumerator.trans hDenominatorMul

/-- A covered rate bin carrying the exact finite rank comparison and both characteristic-sized
degree bounds needed by later interpolation and root-counting consumers. -/
structure CoveringInterpolationDimensionBound (F : Type*) [Field F]
    (delta : ℝ) (d n q k : ℕ) (i : Fin (binCount delta)) : Prop
    extends CoveringInterpolationParameterBounds delta d n q k i where
  order_succ_lt_ambient :
    d + 1 < ambientDimension (binAgreement delta i) (binSlack delta i) n
  ambientDegree_lt_fieldSize :
    ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 < q
  exactJetDegreeBudget_lt_fieldSize :
    exactInterpolationJetDegreeFloor
      (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1)
      (agreementThreshold (binAgreement delta i) n) d (d ^ 3) < q
  finiteRankComparison :
    n * certifiedEnlargedRankBound d (d ^ 3) (d ^ 3)
        (interpolationWeightBudget (binSlack delta i) d) <
      Module.finrank F
        (exactInterpolationSpace F
          (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1)
          (agreementThreshold (binAgreement delta i) n) d (d ^ 3) (d ^ 3)
          (interpolationWeightBudget (binSlack delta i) d) (by omega))

/-- Forget the field presentation of the dimension and expose the canonical executable finite
count certificate from `Counting`. -/
theorem CoveringInterpolationDimensionBound.toExactFiniteCertificate
    {F : Type*} [Field F] {delta : ℝ} {d n q k : ℕ}
    {i : Fin (binCount delta)}
    (certificate : CoveringInterpolationDimensionBound F delta d n q k i) :
    ExactFiniteCertificate n
      (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1)
      (agreementThreshold (binAgreement delta i) n) d (d ^ 3) (d ^ 3)
      (interpolationWeightBudget (binSlack delta i) d) := by
  unfold ExactFiniteCertificate
  have hdPos : 0 < d := by
    have := certificate.orderAtLeastTwo
    omega
  have hdD :
      d < ambientDimension (binAgreement delta i) (binSlack delta i) n - 1 := by
    have := certificate.order_succ_lt_ambient
    omega
  rw [← finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount
    (F := F) hdPos hdD]
  exact certificate.finiteRankComparison

/-- One order and one block threshold, both depending only on `delta`, produce a genuine exact
finite interpolation certificate in a covering bin.  The bin is chosen before the coefficient
field, and the same numerical certificate works over every field in the selected universe. -/
theorem exists_uniform_finite_covered_bin_certificates.{u} {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ d N : ℕ, 2 ≤ d ∧ ∀ n q k : ℕ, N ≤ n → n ≤ q →
      (k : ℝ) / n ≤ 1 - delta →
      ∃ i : Fin (binCount delta), ∀ (F : Type u) [Field F],
        CoveringInterpolationDimensionBound F delta d n q k i := by
  obtain ⟨d, hd, hOrder⟩ := exists_uniform_bin_order_with_shell hdelta hdeltaOne
  refine ⟨d, finiteCertificateBlockLengthThreshold delta d, hd,
    fun n q k hn hnq hRate ↦ ?_⟩
  let i₀ : Fin (binCount delta) := ⟨0, binCount_pos hdelta hdeltaOne⟩
  have hnPos : 0 < n := by
    have h := finite_certificate_large_block_conditions hdelta hdeltaOne hd hn i₀
    exact blockLength_pos_of_order_lt_ambientDimension h.2.1
  obtain ⟨i, hepsilon, htheta, hIdentity, hMessage, hAgreementRequested⟩ :=
    exists_covering_bin_parameters hdelta hdeltaOne hnPos hRate
  rcases hOrder i with ⟨hWidth, hShellScaled, hFactor, hLarge⟩
  rcases finite_certificate_large_block_conditions hdelta hdeltaOne hd hn i with
    ⟨hdSuccK, hdK, hAgreement, hBudget, hContact⟩
  have hSlacks := freeGlobalDimensionSlacks hepsilon.1 htheta.1 htheta.2
    (by omega : 0 < d) hnPos hdK
  let certificate : InterpolationParameterBounds delta d n q i := {
    orderAtLeastTwo := hd
    order_lt_ambient := hdK
    agreement_le_blockLength := hAgreement
    degreeBudget_lt_fieldSize := hBudget.trans_le hnq
    contactBudget_le_fieldSize_sq :=
      hContact.trans (Nat.pow_le_pow_left hnq 2)
    boxWidthTargetAtLeastTwo := hWidth
    boxWidth_le_multiplicity := hSlacks.1
    higherJets_fit_degreeBudget := hSlacks.2.1
    boxFamily_fits_contactBudget := hSlacks.2.2
    rankComparison := freeOrder_rank_comparison htheta.1 hd hdK hLarge
  }
  have hShell :
      weightedHigherJetCount d
          (interpolationWeightBudget (binSlack delta i) d + d ^ 3) ≤
        scaledShellFactor (binSlack delta i) d *
          (goodHigherExponents d (interpolationWeightBudget (binSlack delta i) d)
            (higherJetDegreeBudget (binSlack delta i) d)).card := by
    simpa only [scaledExponentCount_eq_weightedHigherJetCount,
      goodScaledExponentCount_eq_card_goodHigherExponents] using hShellScaled
  have hArithmetic :
      n * (4 * d ^ 8 * scaledShellFactor (binSlack delta i) d) <
        (ambientDimension (binAgreement delta i) (binSlack delta i) n - 1) *
          interpolationBoxWidth (binSlack delta i) d ^ 3 := by
    apply rankShellBound_lt_interpolationBox htheta.1 (by omega : 0 < d) hnPos
      (half_interpolationBoxWidthTarget_le_cast hWidth)
    · simpa [shellExponent] using hFactor
    · exact certificate.rankComparison
  have hExactFloor :=
    exactInterpolationJetDegreeFloor_lt_blockLength hdelta hdeltaOne hd hn i
  have hAmbientLt :
      ambientDimension (binAgreement delta i) (binSlack delta i) n < n :=
    ambientDimension_lt_blockLength hepsilon.1 hepsilon.2 htheta.1 htheta.2 hnPos
  refine ⟨i, fun F _ ↦ {
    toCoveringInterpolationParameterBounds := {
      toInterpolationParameterBounds := certificate
      agreement_mem := hepsilon
      slack_mem := htheta
      rateIdentity := hIdentity
      messageDim_le_ambient := hMessage
      binAgreement_le_requested := hAgreementRequested
    }
    order_succ_lt_ambient := hdSuccK
    ambientDegree_lt_fieldSize := by omega
    exactJetDegreeBudget_lt_fieldSize := hExactFloor.trans_le hnq
    finiteRankComparison := by
      apply n_mul_certifiedEnlargedRankBound_lt_finrank_exactInterpolationSpace
        (d := d)
        (A := agreementThreshold (binAgreement delta i) n)
        (K := ambientDimension (binAgreement delta i) (binSlack delta i) n)
        (B := interpolationDegreeBudget d (binAgreement delta i) (binSlack delta i) n)
        (W := interpolationWeightBudget (binSlack delta i) d)
        (C := higherJetDegreeBudget (binSlack delta i) d)
        (H := interpolationBoxWidth (binSlack delta i) d)
        (R := scaledShellFactor (binSlack delta i) d)
        (n := n)
        (by omega : 0 < d) (by omega)
        (by simpa only [HiddenDerivative.multiplicity] using
          certificate.boxWidth_le_multiplicity)
        certificate.higherJets_fit_degreeBudget
        (by simpa only [HiddenDerivative.multiplicity] using
          certificate.boxFamily_fits_contactBudget)
        hShell hArithmetic
  }⟩

end
end RateBinDimensionBound
end ReedSolomon
