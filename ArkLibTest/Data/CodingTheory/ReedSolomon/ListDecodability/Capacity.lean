/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CodewordBound
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.CurveCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FiniteField
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FixedRateExplicitGate
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.CurveCertificate
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Acceptance cases for Reed–Solomon capacity list bounds

The examples cover weighted-support interpolation, finite-field capacity bounds, transfer from
close-polynomial counts to codeword-list bounds, actual-stage and gap bounds from concrete
received-curve certificates, and fixed-rate and uniform rate-partition bounds.
-/

open Finset PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative
  ReedSolomon.HiddenDerivative.WeightedSupportParameters
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

/-- The prescribed parameters have a concrete finite block and prime field. -/
private theorem prescribedSampleSetup :
    ∃ q : ℕ, q.Prime ∧ sampleN ≤ q ∧
      2 * (sampleM * sampleA + sampleD) ≤ q ∧
      2 * (sampleM * sampleA + sampleD - sampleK) ≤ q ∧
      ∃ domain : Fin sampleN ↪ ZMod q,
        ∃ construction : HiddenDerivativeInterpolationCertificate
          (k := sampleMessageDim) (A := sampleA) sampleD sampleM domain (fun _ => 0),
          construction.ambientDim = sampleK ∧
            jetTotalDegree construction.interpolant < 2 * sampleM ∧
            8 * sampleM ≤ sampleN ∧ 0 < sampleMessageDim ∧
            sampleMessageDim ≤ sampleN ∧ sampleA ≤ sampleN ∧ 1 ≤ sampleM := by
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
  have hblock : 8 * sampleM ≤ sampleN := by
    change 8 * sampleM ≤ 8 * sampleM
    exact le_rfl
  have hmessageDim_pos : 0 < sampleMessageDim := by
    dsimp [sampleMessageDim]
    omega
  have hmessageDim_le_n : sampleMessageDim ≤ sampleN := by
    calc
      sampleMessageDim ≤ sampleM := hmessageDim_le_m
      _ ≤ 8 * sampleM := by omega
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
  exact ⟨q, hqPrime, hnq, hfield, hlarge, domain, construction, hK, htotal,
    hblock, hmessageDim_pos, hmessageDim_le_n, hA, hm⟩

private theorem sampleZeroInList {q : ℕ} (domain : Fin sampleN ↪ ZMod q)
    (hA : sampleA ≤ sampleN) :
    (0 : MessagePolynomial (ZMod q) sampleMessageDim) ∈
      agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0) := by
  have hEval : ReedSolomon.evalOnPoints domain
      (0 : MessagePolynomial (ZMod q) sampleMessageDim) = fun _ => 0 := by
    ext i
    simp [ReedSolomon.evalOnPoints]
  change sampleA ≤ Code.agree
    (ReedSolomon.evalOnPoints domain (0 : MessagePolynomial (ZMod q) sampleMessageDim))
    (fun _ => 0)
  rw [hEval, Code.agree_self]
  simpa only [Fintype.card_fin] using hA

/-- At the prescribed parameters, interpolation yields a certificate with the stated degree bound.
-/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := sampleMessageDim) (A := sampleA) sampleD sampleM domain (fun _ => 0),
        construction.ambientDim = sampleK ∧
          jetTotalDegree construction.interpolant < 2 * sampleM := by
  obtain ⟨q, hq, -, -, -, domain, construction, hK, htotal, -, -, -, -, -⟩ :=
    prescribedSampleSetup
  exact ⟨q, hq, domain, construction, hK, htotal⟩

/-- The prescribed interpolant bounds the agreement list over its concrete prime field. -/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      (agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0)).encard ≤
        (4 * sampleM * q ^ sampleD : ℕ∞) ∧
      (4 * sampleM * q ^ sampleD : ℕ) <
        Nat.card (Polynomial.degreeLT (ZMod q) sampleMessageDim) := by
  obtain ⟨q, hq, -, hfield, hlarge, domain, construction, hK, htotal, -, -, -, -, -⟩ :=
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
      0 < 4 * sampleM * q ^ (2 * sampleD) ∧
      Nonempty (CapacityGapCertificate sampleDelta domain sampleMessageDim
        (4 * sampleM * q ^ (2 * sampleD))) ∧
      (0 : MessagePolynomial (ZMod q) sampleMessageDim) ∈
        agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0) := by
  obtain ⟨q, hq, hnq, -, -, domain, -, -, -, hblock, hk, hkn, hA, hm⟩ :=
    prescribedSampleSetup
  obtain ⟨hbound, _hlarge⟩ := weightedSupport_capacity_list_bound_four_mul sampleDelta
    (by norm_num [sampleDelta]) (by norm_num [sampleDelta]) sampleN sampleMessageDim q
    (by simpa only [sampleM, sampleD] using hblock) hk hkn hq hnq domain
  obtain ⟨certificate⟩ := hbound
  have hpositive : 0 < 4 * sampleM * q ^ (2 * sampleD) := by
    have hmpos : 0 < sampleM := by omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) hmpos) (Nat.pow_pos hq.pos)
  have hpointwise : ∀ received : Fin sampleN → ZMod q,
      (agreeingPolynomials domain sampleMessageDim
        (agreementThreshold sampleDelta (Fintype.card (Fin sampleN)) sampleMessageDim)
        received).encard ≤
          ((4 * sampleM * q ^ (2 * sampleD) : ℕ) : ℕ∞) := by
    intro received
    simpa only [sampleM, sampleD, Fintype.card_fin] using
      (certificate.pointwiseListBound received).1
  have hNpos : 0 < Fintype.card (Fin sampleN) := by
    simpa only [Fintype.card_fin] using hk.trans_le hkn
  have hhelper : CapacityGapCertificate sampleDelta domain sampleMessageDim
      (4 * sampleM * q ^ (2 * sampleD)) := CapacityGapCertificate.ofPointwiseBound
    (by norm_num [sampleDelta]) hNpos (domain := domain)
    (messageDim := sampleMessageDim)
    (listBound := 4 * sampleM * q ^ (2 * sampleD)) hpointwise
  exact ⟨q, hq, domain, hpositive, ⟨hhelper⟩, sampleZeroInList domain hA⟩

/-- The public construction contract supplies the sample certificate at an attainable threshold.
-/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      ∃ construction : HiddenDerivativeInterpolationCertificate
        (k := sampleMessageDim) (A := sampleA) sampleD sampleM domain (fun _ => 0),
        construction.ambientDim = sampleK ∧
          (0 : MessagePolynomial (ZMod q) sampleMessageDim) ∈
            agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0) := by
  obtain ⟨q, hq, hnq, -, -, domain, -, -, -, hblock, hk, hkn, hA, -⟩ :=
    prescribedSampleSetup
  have hconstruct := exists_weightedSupport_hiddenDerivativeConstruction sampleDelta
    (by norm_num [sampleDelta]) (by norm_num [sampleDelta]) sampleN sampleMessageDim q
    (by simpa only [sampleM, sampleD] using hblock) hk hkn hq hnq hA
  obtain ⟨construction, hK⟩ := hconstruct domain (fun _ => 0)
  exact ⟨q, hq, domain, construction, hK, sampleZeroInList domain hA⟩

/-- The packaged weighted-support bound gives a positive-factor certificate for the sample.
-/
example :
    ∃ q : ℕ, q.Prime ∧ ∃ domain : Fin sampleN ↪ ZMod q,
      ∃ listFactor : ℕ, 0 < listFactor ∧
        Nonempty (CapacityGapCertificate sampleDelta domain sampleMessageDim
          (listFactor * q ^ (2 * sampleD))) ∧
        (0 : MessagePolynomial (ZMod q) sampleMessageDim) ∈
          agreeingPolynomials domain sampleMessageDim sampleA (fun _ => 0) := by
  obtain ⟨q, hq, hnq, -, -, domain, -, -, -, hblock, hk, hkn, hA, -⟩ :=
    prescribedSampleSetup
  obtain ⟨_, listFactor, hfactor, hBound⟩ :=
    weightedSupport_capacity_list_bound sampleDelta
      (by norm_num [sampleDelta]) (by norm_num [sampleDelta])
  have hcertificate := hBound sampleN sampleMessageDim q
    (by simpa only [sampleM, sampleD] using hblock) hk hkn hq hnq domain
  exact ⟨q, hq, domain, listFactor, hfactor,
    by simpa only [sampleD] using hcertificate.1,
    sampleZeroInList domain hA⟩

private def geometricSampleDomain : Fin sampleN ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

local instance : DecidableEq ℚ := Classical.decEq _

private theorem prescribedGeometricSampleData :
    0 < sampleMessageDim ∧ sampleA ≤ sampleN ∧
      let d := Nat.ceil (Real.exp (xi / sampleDelta))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ sampleN := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hblock, hk, _, hA, _⟩ := prescribedSampleSetup
  have hδmax : sampleDelta < 1 / 4 := by norm_num [sampleDelta]
  have hblock' :
      let d := Nat.ceil (Real.exp (xi / sampleDelta))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      8 * m ≤ sampleN := by
    simpa only [sampleN, sampleM, sampleD,
      capacityDerivativeOrder_eq_ceil hδmax, weightedSupportMultiplicity] using hblock
  exact ⟨hk, hA, hblock'⟩

private theorem geometricSampleZero_mem :
    (0 : Polynomial ℚ) ∈ closePolynomialSet geometricSampleDomain (fun _ ↦ 0)
      sampleMessageDim (agreementThreshold sampleDelta sampleN sampleMessageDim) := by
  obtain ⟨_, hA, _⟩ := prescribedGeometricSampleData
  rw [closePolynomialSet]
  refine ⟨by simp, ?_⟩
  have hset : polynomialAgreementSet geometricSampleDomain (fun _ ↦ 0)
      (0 : Polynomial ℚ) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet]
  rw [hset]
  simpa [sampleA, Fintype.card_fin] using hA

/-- A concrete zero polynomial belongs to a singleton finite sublist with the prescribed bound. -/
example :
    let d := Nat.ceil (Real.exp (xi / sampleDelta))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    (({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ)).card : ℝ) ≤
        4 * (m : ℝ) ^ 2 * (4 * m / sampleDelta) ^ d * sampleN ^ d ∧
      (0 : Polynomial ℚ) ∈ closePolynomialSet geometricSampleDomain (fun _ ↦ 0)
        sampleMessageDim (agreementThreshold sampleDelta sampleN sampleMessageDim) := by
  obtain ⟨hk, hA, hblock⟩ := prescribedGeometricSampleData
  have hbound := prescribed_geometric_finite_list_bound sampleDelta sampleN sampleMessageDim
    geometricSampleDomain (fun _ ↦ 0) (by norm_num [sampleDelta])
    (by norm_num [sampleDelta]) hk hblock hA
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
    ({(0 : Polynomial ℚ)} : Finset (Polynomial ℚ))
    (by
      intro P hP
      simp only [Finset.mem_singleton] at hP
      subst P
      exact geometricSampleZero_mem)
  exact ⟨by simpa using hbound, geometricSampleZero_mem⟩

/-- The complete prescribed agreement list is nonempty, finite, and geometrically bounded. -/
example :
    let d := Nat.ceil (Real.exp (xi / sampleDelta))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    (0 : Polynomial ℚ) ∈ closePolynomialSet geometricSampleDomain (fun _ ↦ 0)
        sampleMessageDim (agreementThreshold sampleDelta sampleN sampleMessageDim) ∧
      (closePolynomialSet geometricSampleDomain (fun _ ↦ 0) sampleMessageDim
        (agreementThreshold sampleDelta sampleN sampleMessageDim)).Finite ∧
        ((closePolynomialSet geometricSampleDomain (fun _ ↦ 0) sampleMessageDim
          (agreementThreshold sampleDelta sampleN sampleMessageDim)).ncard : ℝ) ≤
          4 * (m : ℝ) ^ 2 * (4 * m / sampleDelta) ^ d * sampleN ^ d := by
  obtain ⟨hk, hA, hblock⟩ := prescribedGeometricSampleData
  have hbound := prescribed_geometric_close_list_bound sampleDelta sampleN sampleMessageDim
    geometricSampleDomain (fun _ ↦ 0) (by norm_num [sampleDelta])
    (by norm_num [sampleDelta]) hk hblock hA
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  exact ⟨geometricSampleZero_mem, hbound.1, hbound.2⟩

private def singletonAgreementDomain : Fin 1 ↪ ℚ where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _

example :
    (agreeingPolynomials singletonAgreementDomain 1 1 (fun _ ↦ 0)).encard ≤
      (closePolynomialSet singletonAgreementDomain (fun _ ↦ 0) 1 1).encard := by
  exact agreeingPolynomials_encard_le_closePolynomialSet
    singletonAgreementDomain (fun _ ↦ 0)

example :
    Code.Lambda (ReedSolomon.code singletonAgreementDomain 1 : Set (Fin 1 → ℚ))
        (capacityRadius 0 1 1) ≤ 1 := by
  have hthreshold : agreementThreshold 0 1 1 = 1 := by
    norm_num [agreementThreshold]
  have hB : ∀ received : Fin 1 → ℚ,
      (closePolynomialSet singletonAgreementDomain received 1
        (agreementThreshold 0 1 1)).Finite ∧
        ((closePolynomialSet singletonAgreementDomain received 1
          (agreementThreshold 0 1 1)).ncard : ℝ) ≤ 1 := by
    intro received
    rw [hthreshold]
    refine ⟨closePolynomialSet_finite singletonAgreementDomain received (by norm_num), ?_⟩
    simpa using closePolynomialSet_one_ncard_le_div singletonAgreementDomain received
      (by norm_num)
  have hbound := lambda_le_ceil_of_closePolynomialSet_bound
    (δ := 0) (n := 1) (k := 1) (by norm_num) (by norm_num)
    singletonAgreementDomain 1 hB
  simpa using hbound

/-- The prescribed close-list bound transfers to the codeword-list function. -/
example :
    let d := Nat.ceil (Real.exp (xi / sampleDelta))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    Code.Lambda (ReedSolomon.code geometricSampleDomain sampleMessageDim :
      Set (Fin sampleN → ℚ)) (capacityRadius sampleDelta sampleN sampleMessageDim) ≤
      (Nat.ceil (4 * (m : ℝ) ^ 2 * (4 * m / sampleDelta) ^ d * sampleN ^ d) : ℕ∞) := by
  obtain ⟨hk, hA, hblock⟩ := prescribedGeometricSampleData
  exact prescribed_geometric_lambda_bound sampleDelta sampleN sampleMessageDim
    geometricSampleDomain (by norm_num [sampleDelta]) (by norm_num [sampleDelta])
    hk hblock hA (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private def curveCertificateCenters : Fin 2 ↪ ℚ where
  toFun i := i.val
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private def curveCertificateReceived : Fin 2 → ℚ := fun _ ↦ 0

private noncomputable def curveCertificateWord : Fin 2 → Polynomial ℚ :=
  fun i ↦ Polynomial.C (curveCertificateReceived i)

private noncomputable def curveCertificate :
    SymbolicReceivedCurve.Certificate 2 2 0 1 0 0
      curveCertificateCenters curveCertificateWord :=
  Classical.choice (by
    simpa [curveCertificateWord] using
      exists_partitionSupport_curve_certificate
        (D := 1) (d := 0) (m := 1) (W := 0) (n := 2) (A := 2) (k := 2) (ℓ := 0)
        (ν := 1) (L := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        curveCertificateCenters curveCertificateWord
        (by intro i; simp [curveCertificateWord])
        (by
          intro u hu
          have h : u none + 1 * totalJetDegree u < 2 := by
            exact_mod_cast hu.2
          omega)
        (by
          have hcard : (partitionSupportExponents 1 0 0 (2 : ℝ) (by norm_num)).card =
              partitionSourceCount 1 0 0 2 := by
            simpa using
              (card_partitionSupportExponents (D := 1) (d := 0) (W := 0) (by norm_num) 2)
          rw [hcard]
          norm_num [partitionSourceCount, localDerivativeCoordinateBudget, contactThreshold,
            weightedHigherJetCount, Finset.natWeightedSimplex, Finset.sum_range_succ]))

example :
    let Q : DifferentialPolynomial ℚ 0 :=
      MvPolynomial.map (Polynomial.eval₂RingHom (RingHom.id ℚ) 0) curveCertificate.Q
    ∃ stages terminal, ∃ list : Finset (Polynomial ℚ),
      SeparantChain Q stages terminal ∧
        (list : Set (Polynomial ℚ)) =
          closePolynomialSet curveCertificateCenters curveCertificateReceived 2 2 ∧
        (list.card : ℚ) ≤ (stages.map (directJetStageCharge 2 2 2 2)).sum := by
  dsimp only
  obtain ⟨stages, terminal, list, hchain, hlist, _, hbound⟩ :=
    exists_closePolynomial_list_of_curve_certificate_actualStages
      curveCertificateCenters curveCertificateReceived curveCertificate
      (by norm_num) (by norm_num)
      (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  exact ⟨stages, terminal, list, hchain, hlist, hbound⟩

example :
    (closePolynomialSet curveCertificateCenters curveCertificateReceived 2 2).Finite ∧
      ((closePolynomialSet curveCertificateCenters curveCertificateReceived 2 2).ncard : ℚ) ≤
        1 := by
  simpa using close_list_bound_of_curve_certificate_directJetCoarse
    curveCertificateCenters curveCertificateReceived curveCertificate
    (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private noncomputable def curveCertificateDegreeOne :
    SymbolicReceivedCurve.Certificate 2 1 0 1 0 0
      curveCertificateCenters curveCertificateWord := by
  let cert := curveCertificate
  refine
    { Q := cert.Q
      challengeDegree_le := cert.challengeDegree_le
      totalJetDegree_le := cert.totalJetDegree_le
      specialization_sound := ?_ }
  intro E hE ρ z
  obtain ⟨hQ, hdegree, hsound⟩ := cert.specialization_sound ρ z
  refine ⟨hQ, hdegree, ?_⟩
  intro indices P hP hA heval
  apply hsound indices P ?_ hA heval
  exact lt_trans hP (by norm_num)

example :
    (closePolynomialSet curveCertificateCenters curveCertificateReceived 1 2).Finite ∧
      ((closePolynomialSet curveCertificateCenters curveCertificateReceived 1 2).ncard :
        ℝ) ≤ 1 := by
  simpa using close_list_bound_of_curve_certificate_of_jetCharacteristic
    (δ := 1 / 2) (K := 1) (d := 0) (ν := 1) (H := 0)
    curveCertificateCenters curveCertificateReceived curveCertificateDegreeOne
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

end
end WeightedSupportInterpolantTest

private def finiteFieldCapacityDomain : Fin 2 ↪ ZMod 3 where
  toFun i := (i.val : ZMod 3)
  inj' i j hij := by
    apply Fin.ext
    have hi : i.val < 3 := i.isLt.trans_le (by decide)
    have hj : j.val < 3 := j.isLt.trans_le (by decide)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      using congrArg ZMod.val hij

/-- At gap one half, the exact list contains the zero polynomial and has size at most one. -/
example :
    ∃ list : Finset (Polynomial (ZMod 3)),
      (0 : Polynomial (ZMod 3)) ∈ list ∧ list.card ≤ 1 := by
  have h := exists_field_bounded_capacity_list (1 / 2 : ℝ) (by norm_num)
  have hinstance := h 2 1 3 2 (by norm_num) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)
    finiteFieldCapacityDomain (fun _ => 0)
  obtain ⟨list, hexact, -, hhalf, -, -⟩ := hinstance
  have hagreement :
      Code.agree (fun i => (0 : Polynomial (ZMod 3)).eval (finiteFieldCapacityDomain i))
        (fun _ => 0) = 2 := by
    have heval :
        (fun i => (0 : Polynomial (ZMod 3)).eval (finiteFieldCapacityDomain i)) =
          (fun _ => 0) := by
      ext i
      simp
    rw [heval, Code.agree_self]
    simp
  refine ⟨list, (hexact 0).2 ⟨by simp, ?_⟩, hhalf (by norm_num)⟩
  rw [hagreement]

open ReedSolomon.HiddenDerivative.RatePartition

section RatePartitionAcceptance

noncomputable local instance : DecidableEq ℚ := Classical.decEq _

private def ratePartitionSampleDomain (n : ℕ) : Fin n ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' i j hij := by
    change (i.val : ℚ) = (j.val : ℚ) at hij
    apply Fin.ext
    exact_mod_cast hij

private noncomputable def sampleRate : ℝ := 1 / 2
private noncomputable def sampleGap : ℝ := 1 / 4
private noncomputable def sampleAgreement : ℝ := sampleRate + sampleGap
private noncomputable def sampleOrder : ℕ := fixedRatePartitionOrder sampleRate sampleGap

private theorem sampleRateGate :
    0 < sampleRate ∧ sampleRate < sampleAgreement ∧ sampleAgreement < 1 ∧
      500 ≤ sampleOrder ∧ 1 < rateGamma sampleRate sampleAgreement sampleOrder := by
  refine ⟨by norm_num [sampleRate], ?_, ?_, ?_, ?_⟩
  · norm_num [sampleRate, sampleAgreement, sampleGap]
  · norm_num [sampleRate, sampleAgreement, sampleGap]
  · simpa only [sampleOrder] using fixedRatePartitionOrder_ge_500 sampleRate sampleGap
  · simpa only [sampleOrder, sampleAgreement] using
      fixedRateGamma_gt_one (by norm_num [sampleRate]) (by norm_num [sampleGap])

open Classical in
/-- The explicit fixed-rate gate gives its complete-list bound at the selected block length. -/
example :
    ∃ p : PartitionFiniteParameters sampleRate sampleAgreement sampleOrder,
      ∃ n : ℕ,
        n = rateBlockThreshold sampleRate sampleOrder p.multiplicity ∧
        (closePolynomialSet (ratePartitionSampleDomain n) (fun _ => (0 : ℚ)) 1 n).Finite ∧
          ((closePolynomialSet (ratePartitionSampleDomain n) (fun _ => (0 : ℚ)) 1 n).ncard :
            ℝ) ≤
            (rateJetCap sampleRate p.multiplicity : ℝ) ^ 2 *
            (2 * rateJetCap sampleRate p.multiplicity / (sampleAgreement - sampleRate)) ^
                sampleOrder * n ^ sampleOrder := by
  obtain ⟨hR, hRa, haone, hd, hgate⟩ := sampleRateGate
  have hδ : 0 < sampleGap := by norm_num [sampleGap]
  obtain ⟨p, hbound⟩ :=
    ReedSolomon.fixedRatePartitionOrder_list_bound hR hδ haone
  let n := rateBlockThreshold sampleRate sampleOrder p.multiplicity
  have hn : rateBlockThreshold sampleRate sampleOrder p.multiplicity ≤ n := by rfl
  have hAn : sampleAgreement * n ≤ n := by
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have hguards := rateBlockThreshold_guards (rate := sampleRate)
    (agreement := sampleAgreement) (order := sampleOrder) (multiplicity := p.multiplicity)
    (n := n) (k := 0) (A := n) hR (hRa.trans haone) hn
    (by simpa using mul_nonneg hR.le (Nat.cast_nonneg n)) hAn
  have hfloor : 1 ≤ ⌊sampleRate * n⌋₊ := by
    have := hguards.1
    omega
  have hkR : ((1 : ℕ) : ℝ) ≤ sampleRate * n := by
    calc
      ((1 : ℕ) : ℝ) ≤ (⌊sampleRate * n⌋₊ : ℝ) := by exact_mod_cast hfloor
      _ ≤ sampleRate * n := Nat.floor_le (by positivity)
  refine ⟨p, n, rfl, ?_⟩
  have hSelector := hbound ℚ n 1 n hn (by norm_num) (by simpa using hkR) hAn (by rfl)
    (ratePartitionSampleDomain n) (fun _ => 0)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hDirect := ReedSolomon.ratePartition_close_list_bound (F := ℚ) (p := p) (n := n)
    (k := 1) (A := n) hR hRa haone hd hn (by norm_num) (by simpa using hkR) hAn (by rfl)
    (ratePartitionSampleDomain n) (fun _ => 0)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  simpa only [sampleAgreement, add_sub_cancel_left] using ⟨hDirect.1, hSelector.2⟩

private noncomputable def fixedRateSampleParameters :
    PartitionFiniteParameters sampleRate sampleAgreement sampleOrder :=
  fixedRatePartitionFiniteParameters (by norm_num [sampleRate]) (by norm_num [sampleGap])

private noncomputable def fixedRateSampleLength : ℕ :=
  rateBlockThreshold sampleRate sampleOrder fixedRateSampleParameters.multiplicity

open Classical in
/-- The selected fixed-rate parameters bound the complete list over the rationals. -/
example :
    (closePolynomialSet (ratePartitionSampleDomain fixedRateSampleLength)
      (fun _ => (0 : ℚ)) 1 fixedRateSampleLength).Finite ∧
      ((closePolynomialSet (ratePartitionSampleDomain fixedRateSampleLength)
        (fun _ => (0 : ℚ)) 1 fixedRateSampleLength).ncard : ℝ) ≤
        (rateJetCap sampleRate fixedRateSampleParameters.multiplicity : ℝ) ^ 2 *
          (2 * rateJetCap sampleRate fixedRateSampleParameters.multiplicity / sampleGap) ^
            sampleOrder * fixedRateSampleLength ^ sampleOrder := by
  have hR : 0 < sampleRate := by norm_num [sampleRate]
  have hδ : 0 < sampleGap := by norm_num [sampleGap]
  have haone : sampleRate + sampleGap < 1 := by norm_num [sampleRate, sampleGap]
  have hn : rateBlockThreshold sampleRate sampleOrder
      fixedRateSampleParameters.multiplicity ≤ fixedRateSampleLength := by rfl
  have hAn : sampleAgreement * (fixedRateSampleLength : ℝ) ≤ fixedRateSampleLength := by
    have hagreement : sampleAgreement ≤ 1 := by
      norm_num [sampleAgreement, sampleRate, sampleGap]
    have hn_nonneg : (0 : ℝ) ≤ fixedRateSampleLength := Nat.cast_nonneg _
    calc
      sampleAgreement * fixedRateSampleLength ≤ 1 * fixedRateSampleLength :=
        mul_le_mul_of_nonneg_right hagreement hn_nonneg
      _ = fixedRateSampleLength := by ring
  have hk0 : (0 : ℝ) ≤ sampleRate * (fixedRateSampleLength : ℝ) :=
    mul_nonneg (by norm_num [sampleRate]) (Nat.cast_nonneg _)
  have hguards := rateBlockThreshold_guards (rate := sampleRate)
    (agreement := sampleAgreement) (order := sampleOrder)
    (multiplicity := fixedRateSampleParameters.multiplicity)
    (n := fixedRateSampleLength) (k := 0) (A := fixedRateSampleLength) hR
    (by norm_num [sampleRate]) hn (by simpa using hk0) hAn
  have hfloor : 1 ≤ ⌊sampleRate * fixedRateSampleLength⌋₊ := by omega
  have hkR : (1 : ℝ) ≤ sampleRate * fixedRateSampleLength := by
    have hfloorReal : (1 : ℝ) ≤ (⌊sampleRate * fixedRateSampleLength⌋₊ : ℝ) := by
      exact_mod_cast hfloor
    exact hfloorReal.trans (Nat.floor_le (by positivity))
  have hbound := ReedSolomon.fixedRatePartitionOrder_list_bound_selected
    hR hδ haone
  dsimp only at hbound
  exact hbound ℚ fixedRateSampleLength 1 fixedRateSampleLength hn (by norm_num)
    (by simpa using hkR) hAn (by rfl) (ratePartitionSampleDomain fixedRateSampleLength)
    (fun _ => 0) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))

private noncomputable def uniformSampleDelta : ℝ := 1 / 5
private noncomputable def uniformSampleLength : ℕ := uniformBlockThreshold uniformSampleDelta

private theorem uniformSampleGap :
    ((1 : ℕ) : ℝ) + uniformSampleDelta * uniformSampleLength ≤ uniformSampleLength := by
  have hm : 1 ≤ uniformMultiplicity uniformSampleDelta := by
    have := add_two_le_uniformMultiplicity uniformSampleDelta
    omega
  have hm' : 1 ≤ uniformMultiplicity (1 / 5 : ℝ) := by
    simpa [uniformSampleDelta] using hm
  have hm_real : (1 : ℝ) ≤ (uniformMultiplicity (1 / 5 : ℝ) : ℝ) := by
    exact_mod_cast hm'
  have hsize := (uniformBlockThreshold_guards (δ := uniformSampleDelta)
    (n := uniformSampleLength) (by norm_num [uniformSampleDelta])
    (by norm_num [uniformSampleDelta]) (by rfl)).1
  norm_num [uniformSampleDelta] at hsize
  have hn50 : (50 : ℝ) ≤ uniformSampleLength := by
    have hmult : (2 : ℝ) ≤ 2 * (uniformMultiplicity (1 / 5) : ℝ) := by
      nlinarith [hm_real]
    have hle := hmult.trans hsize
    norm_num at hle
    linarith
  norm_num [uniformSampleDelta]
  nlinarith [hn50]

open Classical in
/-- The uniform small-gap bound holds at the selected block length over the rationals. -/
example :
    (closePolynomialSet (ratePartitionSampleDomain uniformSampleLength)
      (fun _ => (0 : ℚ)) 1 uniformSampleLength).Finite ∧
      ((closePolynomialSet (ratePartitionSampleDomain uniformSampleLength)
        (fun _ => (0 : ℚ)) 1 uniformSampleLength).ncard : ℝ) ≤
        (uniformJetCap uniformSampleDelta : ℝ) ^ 2 *
          (2 * uniformJetCap uniformSampleDelta / uniformSampleDelta) ^
            uniformDerivativeOrder uniformSampleDelta * uniformSampleLength ^
              uniformDerivativeOrder uniformSampleDelta ∧
      (let d := uniformDerivativeOrder uniformSampleDelta
       let ν := uniformJetCap uniformSampleDelta
       let C : ℝ := (ν : ℝ) ^ 2 * (2 * ν / uniformSampleDelta) ^ d
      (closePolynomialSet (ratePartitionSampleDomain uniformSampleLength) (fun _ => (0 : ℚ)) 1
        uniformSampleLength).Finite ∧
         ((closePolynomialSet (ratePartitionSampleDomain uniformSampleLength) (fun _ => (0 : ℚ))
           1 uniformSampleLength).ncard : ℝ) ≤ C * uniformSampleLength ^ d) := by
  have hchar : ringChar ℚ = 0 ∨ uniformSampleLength ≤ ringChar ℚ :=
    Or.inl (ringChar.eq_zero : ringChar ℚ = 0)
  have hExpanded := uniformRatePartition_close_list_bound
    (δ := uniformSampleDelta) (n := uniformSampleLength) (k := 1) (A := uniformSampleLength)
    (by norm_num [uniformSampleDelta]) (by norm_num [uniformSampleDelta]) (by rfl)
    (by norm_num) uniformSampleGap (by rfl) (ratePartitionSampleDomain uniformSampleLength)
    (fun _ => 0) hchar
  exact ⟨hExpanded.1, hExpanded.2, uniform_capacity_list_bound uniformSampleDelta
    (by norm_num [uniformSampleDelta]) (by norm_num [uniformSampleDelta])
    uniformSampleLength 1 uniformSampleLength (by rfl) (by norm_num) uniformSampleGap
    (by rfl) (ratePartitionSampleDomain uniformSampleLength) (fun _ => 0) hchar⟩

end RatePartitionAcceptance
