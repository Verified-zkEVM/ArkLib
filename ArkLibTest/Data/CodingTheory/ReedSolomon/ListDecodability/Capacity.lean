/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Acceptance cases for weighted-support capacity interpolation

The examples exercise the prescribed construction over a large prime field and the resulting
agreement-list bound.
-/

open Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative
  ReedSolomon.ListDecoding
open ReedSolomon.HiddenDerivativeInterpolationCertificate

namespace WeightedSupportInterpolantTest

noncomputable section

private def sampleDelta : ℝ := 1 / 8
private def sampleN : ℕ :=
  8 * weightedSupportMultiplicity (capacityDerivativeOrder sampleDelta)
private def sampleD : ℕ := capacityDerivativeOrder sampleDelta
private def sampleM : ℕ := weightedSupportMultiplicity sampleD
private def sampleMessageDim : ℕ := sampleD + 1
private def sampleA : ℕ := agreementThreshold sampleDelta sampleN sampleMessageDim
private def sampleK : ℕ :=
  weightedSupportAmbientDimension sampleDelta sampleN sampleMessageDim
private def sampleFieldLower : ℕ := max sampleN (2 * (sampleM * sampleA + sampleD))

private def onePointDomain : Fin 1 ↪ ZMod 2 where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _

private theorem onePointThreshold :
    agreementThreshold 1 (Fintype.card (Fin 1)) 1 = 2 := by
  simp [agreementThreshold]

/-- The prescribed parameters have a concrete finite block and prime field. -/
private theorem prescribedSampleSetup :
    ∃ q : ℕ, q.Prime ∧ sampleN ≤ q ∧
      2 * (sampleM * sampleA + sampleD) ≤ q ∧
      2 * (sampleM * sampleA + sampleD - sampleK) ≤ q ∧
      ∃ domain : Fin sampleN ↪ ZMod q,
        ∃ construction : HiddenDerivativeInterpolationCertificate
          (k := sampleMessageDim) (A := sampleA) sampleD sampleM domain (fun _ => 0),
          construction.ambientDim = sampleK ∧
            jetTotalDegree construction.interpolant < 2 * sampleM := by
  obtain ⟨q, hqLower, hqPrime⟩ := Nat.exists_infinite_primes sampleFieldLower
  have hqLower' : max sampleN (2 * (sampleM * sampleA + sampleD)) ≤ q := by
    simpa only [sampleFieldLower] using hqLower
  have hnq : sampleN ≤ q := (le_max_left _ _).trans hqLower'
  have hfield : 2 * (sampleM * sampleA + sampleD) ≤ q :=
    (le_max_right _ _).trans hqLower'
  have hlarge : 2 * (sampleM * sampleA + sampleD - sampleK) ≤ q := by
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
  have hHlower : (108 / 5 : ℝ) ≤ harmonic (sampleD - 1) := by
    have h := (capacityDerivativeOrder_lower (δ := sampleDelta)
      (by norm_num [sampleDelta]) (by norm_num [sampleDelta])).2.2
    change ReedSolomon.HiddenDerivative.WeightedSupportParameters.xi / sampleDelta ≤
      harmonic (sampleD - 1) at h
    norm_num [ReedSolomon.HiddenDerivative.WeightedSupportParameters.xi, sampleDelta] at h
    exact h
  have hHge1 : (1 : ℝ) ≤ harmonic (sampleD - 1) := by linarith
  have hmLower : 100 * (sampleD : ℝ) ^ 2 * harmonic (sampleD - 1) ≤ sampleM := by
    exact_mod_cast le_weightedSupportMultiplicity sampleD
  have hDreal : (1 : ℝ) ≤ sampleD := by
    exact_mod_cast (show 1 ≤ sampleD by omega)
  have hMsquare : 100 * (sampleD : ℝ) ^ 2 ≤ sampleM := by
    have hnonneg := mul_nonneg
      (show (0 : ℝ) ≤ 100 * (sampleD : ℝ) ^ 2 by positivity)
      (sub_nonneg.mpr hHge1)
    nlinarith
  have hmessageDim_le_m : sampleD + 1 ≤ sampleM := by
    have hreal : (sampleMessageDim : ℝ) ≤ sampleM := by
      dsimp [sampleMessageDim]
      push_cast
      nlinarith [sq_nonneg ((sampleD : ℝ) - 1)]
    exact_mod_cast hreal
  have hn : 2 ≤ sampleN := by
    change 2 ≤ 8 * sampleM
    omega
  have hceil : ⌈sampleDelta * sampleN⌉₊ = sampleM := by
    have hreal : sampleDelta * sampleN = (sampleM : ℝ) := by
      dsimp [sampleDelta, sampleN, sampleM, sampleD]
      push_cast
      ring
    rw [hreal, Nat.ceil_natCast]
  have hA : agreementThreshold sampleDelta sampleN sampleMessageDim ≤ sampleN := by
    rw [agreementThreshold, hceil]
    change sampleMessageDim + sampleM ≤ 8 * sampleM
    dsimp [sampleMessageDim]
    omega
  obtain ⟨construction, hK, htotal⟩ :=
    @ReedSolomon.exists_prescribed_weightedSupport_construction
    sampleDelta sampleN sampleMessageDim q ⟨hqPrime⟩ domain (fun _ => 0)
    (by norm_num [sampleDelta]) (by norm_num [sampleDelta])
    (by dsimp [sampleMessageDim]; omega)
    (by rfl) hnq hA
  exact ⟨q, hqPrime, hnq, hfield, hlarge, domain, construction, hK, htotal⟩

/-- At the prescribed parameters, interpolation yields a certificate with the stated degree bound.
-/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := sampleMessageDim) (A := sampleA) sampleD sampleM domain (fun _ => 0),
        construction.ambientDim = sampleK ∧
          jetTotalDegree construction.interpolant < 2 * sampleM := by
  obtain ⟨q, hq, -, -, -, domain, construction, hK, htotal⟩ := prescribedSampleSetup
  exact ⟨q, hq, domain, construction, hK, htotal⟩

/-- The prescribed interpolant bounds the agreement list over its concrete prime field. -/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      (agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0)).encard ≤
        (4 * sampleM * q ^ sampleD : ℕ∞) ∧
      (4 * sampleM * q ^ sampleD : ℕ) <
        Nat.card (Polynomial.degreeLT (ZMod q) sampleMessageDim) := by
  obtain ⟨q, hq, -, hfield, hlarge, domain, construction, hK, htotal⟩ :=
    prescribedSampleSetup
  have hbound := @agreeingPolynomials_encard_le_totalJetDegree
      sampleN q sampleMessageDim sampleA sampleD sampleM sampleK 1 ⟨hq⟩ domain (fun _ => 0)
      construction hK (by decide) htotal (by simpa only [pow_one] using hlarge)
  have hbound' :
      (agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0)).encard ≤
        (4 * sampleM * q ^ sampleD : ℕ∞) := by
    simpa only [one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound
  have hdge2 : 2 ≤ sampleD := by
    have h := (capacityDerivativeOrder_lower (δ := sampleDelta)
      (by norm_num [sampleDelta]) (by norm_num [sampleDelta])).1
    dsimp [sampleD]
    omega
  have hA : 2 ≤ sampleA := by
    dsimp [sampleA, agreementThreshold, sampleMessageDim]
    omega
  have hfour : 4 * sampleM < q := by
    have hstrict : 4 * sampleM < 2 * (sampleM * sampleA + sampleD) := by
      have hmul : 2 * sampleM ≤ sampleM * sampleA :=
        calc
          2 * sampleM = sampleM * 2 := Nat.mul_comm _ _
          _ ≤ sampleM * sampleA := Nat.mul_le_mul_left sampleM hA
      omega
    exact hstrict.trans_le hfield
  have hpow : 4 * sampleM * q ^ sampleD < q ^ (sampleD + 1) := by
    calc
      4 * sampleM * q ^ sampleD < q * q ^ sampleD :=
        Nat.mul_lt_mul_of_pos_right hfour (Nat.pow_pos hq.pos)
      _ = q ^ (sampleD + 1) := by rw [Nat.pow_succ]; ring
  have hcard : Nat.card (Polynomial.degreeLT (ZMod q) sampleMessageDim) =
      q ^ sampleMessageDim := by
    calc
      Nat.card (Polynomial.degreeLT (ZMod q) sampleMessageDim) =
          Nat.card (Fin sampleMessageDim → ZMod q) :=
        Nat.card_congr (Polynomial.degreeLTEquiv (ZMod q) sampleMessageDim).toEquiv
      _ = Nat.card (ZMod q) ^ sampleMessageDim := by
        rw [Nat.card_fun, Nat.card_fin]
      _ = q ^ sampleMessageDim := by simp only [Nat.card_zmod]
  refine ⟨q, hq, domain, hbound', ?_⟩
  calc
    (4 * sampleM * q ^ sampleD : ℕ) < q ^ sampleMessageDim := by
      simpa only [sampleMessageDim] using hpow
    _ = Nat.card (Polynomial.degreeLT (ZMod q) sampleMessageDim) := hcard.symm

/-- The prescribed weighted-support instance has a certified capacity-gap list bound. -/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      Nonempty (CapacityGapCertificate sampleDelta domain 1
        (4 * sampleM * q ^ (2 * sampleD))) := by
  obtain ⟨q, hq, hnq, -, -, domain, -, -, -⟩ := prescribedSampleSetup
  have hdge2 : 2 ≤ capacityDerivativeOrder sampleDelta := by
    have h := (capacityDerivativeOrder_lower (δ := sampleDelta)
      (by norm_num [sampleDelta]) (by norm_num [sampleDelta])).1
    omega
  have hm : 0 < weightedSupportMultiplicity (capacityDerivativeOrder sampleDelta) :=
    weightedSupportMultiplicity_pos_iff.mpr hdge2
  have hblock :
      8 * weightedSupportMultiplicity (capacityDerivativeOrder sampleDelta) ≤ sampleN := by
    exact le_rfl
  have hkn : 1 ≤ sampleN := by
    dsimp only [sampleN]
    omega
  obtain ⟨hbound, _hlarge⟩ := weightedSupport_capacity_list_bound_four_mul sampleDelta
    (by norm_num [sampleDelta]) (by norm_num [sampleDelta]) sampleN 1 q hblock
    (by decide) hkn hq hnq domain
  exact ⟨q, hq, domain, by simpa only [sampleM, sampleD] using hbound⟩

/-- A pointwise agreement bound constructs a certificate on the singleton code. -/
example : Nonempty (CapacityGapCertificate 1 onePointDomain 1 0) := by
  refine ⟨CapacityGapCertificate.ofPointwiseBound (by norm_num) (by decide)
    (domain := onePointDomain) (messageDim := 1) (listBound := 0) ?_⟩
  intro received
  have hEmpty : agreeingPolynomials onePointDomain 1
      (agreementThreshold 1 (Fintype.card (Fin 1)) 1) received = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hAgreementLe : Code.agree
        (ReedSolomon.evalOnPoints onePointDomain p) received ≤ 1 := by
      simpa using (Code.agree_le_card
        (u := ReedSolomon.evalOnPoints onePointDomain p) (v := received))
    have hAgreementLt : Code.agree
        (ReedSolomon.evalOnPoints onePointDomain p) received < 2 :=
      hAgreementLe.trans_lt (by decide)
    change agreementThreshold 1 (Fintype.card (Fin 1)) 1 ≤
      Code.agree (ReedSolomon.evalOnPoints onePointDomain p) received at hp
    rw [onePointThreshold] at hp
    exact (Nat.not_le_of_gt hAgreementLt) hp
  rw [hEmpty]
  simp

end
end WeightedSupportInterpolantTest
