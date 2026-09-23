/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Acceptance cases for weighted-support capacity interpolation

The examples exercise a concrete fixed-margin interpolant, the prescribed construction over a
large prime field, and the resulting agreement-list bound.
-/

open Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative
  ReedSolomon.ListDecoding
open ReedSolomon.HiddenDerivativeInterpolationCertificate

namespace WeightedSupportInterpolantTest

noncomputable section

private def singletonDomain : Fin 1 ↪ ℚ where
  toFun _ := 0
  inj' i j _ := by
    apply Fin.ext
    omega

private def singletonCutoff : ℝ :=
  ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (1 : ℝ))

private theorem singletonLocalRank_le_two :
    Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) ≤ 2 := by
  calc
    _ ≤ localResidualCoordinateBudget 1 1 0 ⌈singletonCutoff / 1⌉₊ := by
      simpa using (finrank_weightedSupportLocalConstraint_le (F := ℚ) (d := 1) (D := 1)
        (W := 0) (L := singletonCutoff) (m := 1) (by norm_num) Nat.one_pos (0 : ℚ) 0)
    _ ≤ 2 := by
      norm_num [singletonCutoff, localResidualCoordinateBudget, contactThreshold,
        Finset.natWeightedSimplex]

private theorem singletonWeightedSupportDimension_ge_four :
    4 ≤ Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 singletonCutoff Nat.one_pos) := by
  have h := sum_count_le_finrank_weightedSupportSpace ℚ (d := 1) (D := 1) (W := 0)
    (L := singletonCutoff) (by decide) Nat.one_pos
  have hs : natWeightedSimplex (fun i : Fin (1 - 1) => i.val + 1) 0 = {fun _ => 0} := by
    decide
  have h1 : ⌈(1 : ℝ)⌉₊ = 1 := by exact_mod_cast Nat.ceil_natCast 1
  have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by exact_mod_cast Nat.ceil_natCast 2
  rw [hs, sum_singleton] at h
  norm_num [singletonCutoff, CubicStaircase.count, h1, h2] at h
  exact h

/-- A concrete numerical bound for the dimension margin at cutoff two. -/
private theorem singletonFixedMarginAtTwo :
    (543 / 500 : ℝ) * ((1 : ℕ) : ℝ) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) < Module.finrank ℚ (weightedSupportSpace ℚ 1 1 0 singletonCutoff
          Nat.one_pos) := by
  have hrank : (Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) : ℝ) ≤ 2 := by
    exact_mod_cast singletonLocalRank_le_two
  have hdim : (4 : ℝ) ≤ Module.finrank ℚ
      (weightedSupportSpace ℚ 1 1 0 singletonCutoff Nat.one_pos) := by
    exact_mod_cast singletonWeightedSupportDimension_ge_four
  nlinarith

/-- The dimension margin holds for one rational evaluation point. -/
private theorem singletonFixedMargin :
    (543 / 500 : ℝ) * ((1 : ℕ) : ℝ) * Module.finrank ℚ (LinearMap.range
      (weightedSupportLocalConstraint (R := ℚ) (d := 1) (W := 0) (L := singletonCutoff) 1
        Nat.one_pos 0 0)) < Module.finrank ℚ
          (weightedSupportSpace ℚ 1 1 0 singletonCutoff Nat.one_pos) := by
  exact singletonFixedMarginAtTwo

/-- One evaluation constraint admits a nonzero interpolant under the fixed dimension margin. -/
example : ∃ Q : DifferentialPolynomial ℚ 1,
    Q ≠ 0 := by
  have hD : 0 < (1 : ℕ) := by decide
  have hm : 0 < (1 : ℕ) := by decide
  have hA : 0 < (2 : ℕ) := by decide
  have hg : (1 : ℝ) ≤ 1 := by norm_num
  have hcut : ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (1 : ℝ)) ≤
      ((1 * 2 : ℕ) : ℝ) := by norm_num
  have hresult := @ReedSolomon.exists_weightedSupport_interpolant_of_fixed_margin
    ℚ (inferInstance : Field ℚ) 1 1 1 1 0 2 (1 : ℝ) singletonDomain (fun _ => 0)
    hD hm hA hg hcut singletonFixedMargin
  obtain ⟨Q, hQ, _, _, _, _⟩ := hresult
  exact ⟨Q, hQ⟩

private def sampleDelta : ℝ := 1 / 8
private def sampleN : ℕ :=
  8 * weightedSupportMultiplicity (capacityDerivativeOrder sampleDelta)
private def sampleD : ℕ := capacityDerivativeOrder sampleDelta
private def sampleM : ℕ := weightedSupportMultiplicity sampleD
private def sampleA : ℕ := agreementThreshold sampleDelta sampleN 1
private def sampleK : ℕ := weightedSupportAmbientDimension sampleDelta sampleN 1
private def sampleFieldLower : ℕ := max sampleN (2 * (sampleM * sampleA + sampleD))

/-- The prescribed parameters have a concrete finite block and prime field. -/
private theorem prescribedSampleSetup :
    ∃ q : ℕ, q.Prime ∧ sampleN ≤ q ∧
      2 * (sampleM * sampleA + sampleD - sampleK) ≤ q ∧
      ∃ domain : Fin sampleN ↪ ZMod q,
        ∃ construction : HiddenDerivativeInterpolationCertificate
          (k := 1) (A := sampleA) sampleD sampleM domain (fun _ => 0),
          construction.ambientDim = sampleK ∧
            jetTotalDegree construction.interpolant < 2 * sampleM := by
  obtain ⟨q, hqLower, hqPrime⟩ := Nat.exists_infinite_primes sampleFieldLower
  have hqLower' : max sampleN (2 * (sampleM * sampleA + sampleD)) ≤ q := by
    simpa only [sampleFieldLower] using hqLower
  have hnq : sampleN ≤ q := (le_max_left _ _).trans hqLower'
  have hlarge : 2 * (sampleM * sampleA + sampleD - sampleK) ≤ q := by
    have hfield : 2 * (sampleM * sampleA + sampleD) ≤ q :=
      (le_max_right _ _).trans hqLower'
    exact (Nat.mul_le_mul_left 2 (Nat.sub_le _ _)).trans hfield
  let domain : Fin sampleN ↪ ZMod q := {
    toFun i := (i.val : ZMod q)
    inj' i j hij := by
      apply Fin.ext
      have hi : i.val < q := i.isLt.trans_le hnq
      have hj : j.val < q := j.isLt.trans_le hnq
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
        using congrArg ZMod.val hij
  }
  have hDge2 : 2 ≤ sampleD := by
    have hd := capacityDerivativeOrder_lower (δ := sampleDelta) (by norm_num [sampleDelta])
      (by norm_num [sampleDelta])
    dsimp [sampleD]
    omega
  have hm : 1 ≤ sampleM := by
    dsimp [sampleM]
    exact Nat.succ_le_of_lt (weightedSupportMultiplicity_pos_iff.mpr hDge2)
  have hn : 2 ≤ sampleN := by
    change 2 ≤ 8 * sampleM
    omega
  have hceil : ⌈sampleDelta * sampleN⌉₊ ≤ sampleN - 1 := by
    rw [Nat.ceil_le]
    have hnR : (2 : ℝ) ≤ sampleN := by exact_mod_cast hn
    have hcastSub : ((sampleN - 1 : ℕ) : ℝ) = (sampleN : ℝ) - 1 := by
      exact_mod_cast Nat.cast_sub (by omega : 1 ≤ sampleN)
    rw [hcastSub]
    dsimp [sampleDelta]
    nlinarith
  have hA : agreementThreshold sampleDelta sampleN 1 ≤ sampleN := by
    rw [agreementThreshold]
    omega
  obtain ⟨construction, hK, htotal⟩ :=
    @ReedSolomon.exists_prescribed_weightedSupport_construction
    sampleDelta sampleN 1 q ⟨hqPrime⟩ domain (fun _ => 0)
    (by norm_num [sampleDelta]) (by norm_num [sampleDelta]) (by decide)
    (by rfl) hnq hA
  exact ⟨q, hqPrime, hnq, hlarge, domain, construction, hK, htotal⟩

/-- At the prescribed parameters, interpolation yields a certificate with the stated degree bound.
-/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := 1) (A := sampleA) sampleD sampleM domain (fun _ => 0),
        construction.ambientDim = sampleK ∧
          jetTotalDegree construction.interpolant < 2 * sampleM := by
  obtain ⟨q, hq, -, -, domain, construction, hK, htotal⟩ := prescribedSampleSetup
  exact ⟨q, hq, domain, construction, hK, htotal⟩

/-- The prescribed interpolant bounds the agreement list over its concrete prime field. -/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      (agreeingPolynomials domain 1 sampleA (fun _ => 0)).encard ≤
        (4 * sampleM * q ^ sampleD : ℕ∞) := by
  obtain ⟨q, hq, -, hlarge, domain, construction, hK, htotal⟩ := prescribedSampleSetup
  refine ⟨q, hq, domain, ?_⟩
  have hbound := @agreeingPolynomials_encard_le_totalJetDegree
      sampleN q 1 sampleA sampleD sampleM sampleK 1 ⟨hq⟩ domain (fun _ => 0)
      construction hK (by decide) htotal (by simpa only [pow_one] using hlarge)
  simpa only [one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    hbound

end
end WeightedSupportInterpolantTest
