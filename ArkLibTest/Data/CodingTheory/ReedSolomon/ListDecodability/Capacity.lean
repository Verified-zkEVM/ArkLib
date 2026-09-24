/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupportInterpolant
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.WeightedSupport
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FiniteField
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
