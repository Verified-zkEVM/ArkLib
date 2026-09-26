/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Midpoint
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.SharpCountingBound
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.CertificateBound
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedCurve
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedLine
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.RatePartition
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.FixedRateExplicitGate
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformRate
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.MathematicalUniformRate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.FixedRateGate
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
import ArkLib.Data.Polynomial.Differential.Basic
import ArkLib.Data.Polynomial.Differential.JetDegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Acceptance case for correlated-agreement capacity bounds -/

open Polynomial ReedSolomon
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.WeightedSupportParameters
open PolynomialDifferential

noncomputable section

private theorem algebraicClosureInfinite : Infinite (AlgebraicClosure ℚ) := by
  exact Infinite.of_injective (algebraMap ℚ (AlgebraicClosure ℚ))
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective

local instance : Infinite (AlgebraicClosure ℚ) := algebraicClosureInfinite
local instance : DecidableEq ℚ := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- At gap `1 / 5`, the order-one agreement threshold of a block of length `8 m` fits in the
block. -/
private theorem agreementThreshold_one_fifth_le (m : ℕ) (hm : 0 < m) :
    agreementThreshold (1 / 5 : ℝ) (8 * m) 1 ≤ 8 * m := by
  apply (agreementThreshold_le_iff_real (by norm_num) (8 * m) 1 (8 * m)).mpr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  linarith

example : correlatedMidpoint (1 / 2) 10 2 ≤ 8 ∧
    (1 / 2 : ℝ) * (10 : ℕ) / 2 ≤ ((8 - correlatedMidpoint (1 / 2) 10 2 + 1 : ℕ) : ℝ) := by
  obtain ⟨-, h, -, h', -⟩ := correlatedMidpoint_bounds (1 / 2) 10 2 8 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩

open Classical in
example :
    let δ : ℝ := 1 / 5
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let n := 8 * m
    let ν := 2 * m - 1
    let centers : Fin n ↪ ℚ :=
      ⟨fun i => (i : ℚ), fun a b h => by
        apply Fin.ext
        change (a.val : ℚ) = (b.val : ℚ) at h
        exact_mod_cast h⟩
    let f : Fin n → ℚ := fun i => (i : ℚ)
    let g : Fin n → ℚ := fun _ => 0
    Nonempty (SymbolicReceivedCurve.Certificate (agreementThreshold δ n 1) 1 1 ν d
      (12 * ν - 1) centers (fun i => receivedLine (f i) (g i))) := by
  let δ : ℝ := 1 / 5
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let n := 8 * m
  let ν := 2 * m - 1
  let centers : Fin n ↪ ℚ :=
    ⟨fun i => (i : ℚ), fun a b h => by
      apply Fin.ext
      change (a.val : ℚ) = (b.val : ℚ) at h
      exact_mod_cast h⟩
  let f : Fin n → ℚ := fun i => (i : ℚ)
  let g : Fin n → ℚ := fun _ => 0
  let values : Fin 2 → Fin n → ℚ := fun t i => if t = 0 then f i else g i
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hδ : 0 < δ := by norm_num [δ]
  have hδmax : δ < 1 / 4 := by norm_num [δ]
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hH : (0 : ℝ) < (harmonic (d - 1) : ℝ) := by
    have hxi : 0 < xi := by norm_num [xi]
    simpa only [d] using (div_pos hxi hδ).trans_le ho.2.2
  have hdlower : 48000 ≤ d := by simpa only [d] using ho.1
  have hd : 0 < d := by omega
  have hm : 0 < m := by
    dsimp only [m]
    apply Nat.ceil_pos.mpr
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n := by
    dsimp only
    exact Nat.le_refl _
  have hA : agreementThreshold δ n 1 ≤ n := agreementThreshold_one_fifth_le m hm
  have hparams := exists_prescribed_correlated_parameters (F := ℚ) δ n 1 centers f g
    hδ hδmax hblock hA (Or.inl (by simp))
  have _hprescribed := exists_exceptional_exactPowerAgreement_of_prescribedCurve
    (F := ℚ) (E := AlgebraicClosure ℚ) δ n 1 1 centers values iota
    hδ hδmax (by norm_num) (by norm_num) hblock hA (Or.inl (by simp))
  have _hprescribedStages :=
    exists_exceptional_exactPowerAgreement_with_prescribed_stageBounds
    (F := ℚ) (E := AlgebraicClosure ℚ) δ n 1 1 centers values iota
    hδ hδmax (by norm_num) (by norm_num) hblock hA (Or.inl (by simp))
  exact hparams.1

open Classical in
/-- The prescribed-line bound supplies exact witnesses for a zero candidate on a zero line. -/
example :
    let δ : ℝ := 1 / 5
    let d := Nat.ceil (Real.exp (xi / δ))
    let H : ℝ := harmonic (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let n := 8 * m
    let centers : Fin n ↪ ℚ :=
      ⟨fun i => (i : ℚ), fun a b h => by
        apply Fin.ext
        change (a.val : ℚ) = (b.val : ℚ) at h
        exact_mod_cast h⟩
    ∃ exceptional : Finset (AlgebraicClosure ℚ),
      (exceptional.card : ℝ) ≤ prescribedProductAgreementConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp (xi / δ)) + 1) ∧
      ∃ z ∉ exceptional, HasExactCorrelatedPair
        centers (fun _ ↦ 0) (fun _ ↦ 0)
        (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z (0 : (AlgebraicClosure ℚ)[X]) := by
  let δ : ℝ := 1 / 5
  let d := Nat.ceil (Real.exp (xi / δ))
  let H : ℝ := harmonic (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let n := 8 * m
  let centers : Fin n ↪ ℚ :=
    ⟨fun i => (i : ℚ), fun a b h => by
      apply Fin.ext
      change (a.val : ℚ) = (b.val : ℚ) at h
      exact_mod_cast h⟩
  let f : Fin n → ℚ := fun _ => 0
  let g : Fin n → ℚ := fun _ => 0
  let iota : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hδ : 0 < δ := by norm_num [δ]
  have hδmax : δ < 1 / 4 := by norm_num [δ]
  have ho := prescribed_order_lower δ hδ hδmax.le
  have hH : (0 : ℝ) < (harmonic (d - 1) : ℝ) := by
    have hxi : 0 < xi := by norm_num [xi]
    simpa only [d] using (div_pos hxi hδ).trans_le ho.2.2
  have hdlower : 48000 ≤ d := by simpa only [d] using ho.1
  have hd : 0 < d := by omega
  have hm : 0 < m := by
    dsimp only [m]
    apply Nat.ceil_pos.mpr
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hblock :
      let d := Nat.ceil (Real.exp (xi / δ))
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      8 * m ≤ n := by
    dsimp only
    exact Nat.le_refl _
  have hA : agreementThreshold δ n 1 ≤ n := agreementThreshold_one_fifth_le m hm
  obtain ⟨exceptional, hbound, hgood⟩ := exists_prescribedLine_exactCorrelatedPair
    (F := ℚ) (E := AlgebraicClosure ℚ) δ n 1 centers f g iota hδ hδmax (by norm_num)
    (by simpa [xi] using hblock) hA
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : AlgebraicClosure ℚ) :
      polynomialAgreementSet (centers.trans ⟨iota, iota.injective⟩)
        (fun i ↦ iota (f i) + z * iota (g i)) (0 : (AlgebraicClosure ℚ)[X]) =
        Finset.univ := by
    refine Finset.eq_univ_of_forall fun i ↦ (mem_polynomialAgreementSet _ _ _ i).2 ?_
    simp only [f, g, eval_zero, map_zero, mul_zero, add_zero]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z, Finset.card_univ, Fintype.card_fin]; exact hA)

example :
    let L := correlatedMidpoint (1 / 2) 8 1
    (((8 - L + 1 : ℕ) : ℝ) / ((6 - L + 1 : ℕ) : ℝ) ≤ 2 / (1 / 2 : ℝ)) ∧
      (((8 - 1 + 1 : ℕ) : ℝ) / ((L - 1 + 1 : ℕ) : ℝ) ≤ 2 / (1 / 2 : ℝ)) := by
  simpa [correlatedMidpoint] using
    correlatedMidpoint_ratios_le_two_div (δ := 1 / 2) (n := 8) (k := 1) (A := 6)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The midpoint budget bounds a concrete order-one agreement stage. -/
example :
    (regularPowerBatchedAgreementSharpBound 1 8 1 4 1
      (correlatedMidpoint (1 / 2) 8 1) 6 1 1 : ℝ) ≤
      polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 1 := by
  simpa [correlatedMidpoint] using
    regularPowerBatchedAgreementSharpBound_midpoint_le_stageBound
      (δ := 1 / 2) (r := 1) (n := 8) (K := 4) (k := 1) (A := 6)
      (ℓ := 1) (j := 1) (H := 1) (v := 1) (h := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Increasing an order-one stage to its cap preserves the concrete scalar bound. -/
example : polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 1 ≤
    polynomialCurveSharpStageBound (1 / 2) 8 1 1 1 2 := by
  exact polynomialCurveSharpStageBound_le_uniform
    (δ := 1 / 2) (n := 8) (ℓ := 1) (v := 1) (h := 1) (r := 1) (d := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The product cutoff bounds both contributions for a concrete stage. -/
example :
    let L := correlatedProductCutoff 2 1 6
    (1 : ℝ) * (((8 - L + 1 : ℕ) : ℝ) / ((6 - L + 1 : ℕ) : ℝ)) *
        (dimensionSensitiveIncidenceProduct 8 6 1 1 1 : ℝ) +
      (1 : ℝ) * ((8 - L : ℕ) : ℝ) * 1 * ((1 : ℕ) ^ 1 : ℝ) *
        (dimensionSensitiveIncidenceProduct 8 L 1 1 1 : ℝ) ≤
      polynomialCurveProductStageBound (1 / 2) 8 1 1 1 2 1 := by
  simpa using product_stage_bound (1 / 2) 8 1 6 2 1 1 1 1 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Increasing a product stage from order one to its cap preserves the scalar bound. -/
example : polynomialCurveProductStageBound (1 / 2) 8 1 1 1 2 1 ≤
    polynomialCurveProductStageBound (1 / 2) 8 1 1 1 2 2 := by
  exact polynomialCurveProductStageBound_le_uniform
    (δ := 1 / 2) (n := 8) (ℓ := 1) (v := 1) (h := 1) (d := 2) (r := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The scalar aggregate bounds one concrete family of product stages. -/
example :
    ((1 * 1 : ℕ) : ℝ) +
      ∑ _i ∈ (Finset.univ : Finset (Fin 1)), (1 : ℝ) ≤
        (1 : ℝ) * polynomialCurveProductAgreementConstant (1 / 2) 1 1 1 * (8 : ℝ) ^ 2 := by
  simpa using product_stages_aggregate
    (S := (Finset.univ : Finset (Fin 1))) (cost := fun _ ↦ (1 : ℝ))
    (δ := 1 / 2) (n := 8) (ℓ := 1) (v := 1) (h := 1) (d := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i hi; norm_num [polynomialCurveProductStageBound])

/-- The product scalar bounds a concrete regular agreement stage. -/
example :
    let L := correlatedProductCutoff 1 1 6
    (regularPowerBatchedAgreementSharpBound 1 8 1 4 1 L 6 1 1 (τ := 0) : ℝ) ≤
      polynomialCurveProductStageBound (1 / 2) 8 1 1 1 1 1 := by
  simpa using regularPowerBatchedAgreementSharpBound_product_le_stage
    (δ := 1 / 2) (r := 1) (n := 8) (K := 4) (k := 1) (A := 6)
    (ℓ := 1) (j := 1) (H := 1) (v := 1) (h := 1) (d := 1) (τ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example :
    let L := correlatedMidpoint (1 / 2) 8 1
    (1 : ℝ) + ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
      (regularPowerBatchedAgreementSharpBound 1 8 1 4 1 L 6 1 1 : ℝ) ≤
      polynomialCurveSharpAgreementConstant (1 / 2) 1 1 1 * (8 : ℝ) ^ (1 + 1) := by
  simpa using regularPowerBatchedAgreementSharp_finiteStage_uniform_le
    (S := (Finset.univ : Finset (Fin 1))) (order := fun _ ↦ 1)
    (jetDegree := fun _ ↦ 1) (height := fun _ ↦ 1)
    (δ := 1 / 2) (n := 8) (K := 4) (k := 1) (A := 6) (ℓ := 1) (v := 1) (h := 1) (d := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i hi; norm_num) (by intro i hi; norm_num) (by intro i hi; norm_num)
    (by intro i hi; norm_num)

/-- The product cutoff bounds a concrete one-stage regular agreement family. -/
example :
    let L := correlatedProductCutoff 1 1 6
    (1 : ℝ) + ∑ _i ∈ (Finset.univ : Finset (Fin 1)),
      (regularPowerBatchedAgreementSharpBound 1 8 1 4 1 L 6 1 1 (τ := 0) : ℝ) ≤
      polynomialCurveProductAgreementConstant (1 / 2) 1 1 1 * (8 : ℝ) ^ (1 + 1) := by
  simpa using regularPowerBatchedAgreementSharp_product_finiteStage_le
    (S := (Finset.univ : Finset (Fin 1))) (order := fun _ ↦ 1)
    (jetDegree := fun _ ↦ 1) (height := fun _ ↦ 1)
    (δ := 1 / 2) (n := 8) (K := 4) (k := 1) (A := 6) (ℓ := 1) (v := 1) (h := 1)
    (d := 1) (τ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i hi; norm_num) (by intro i hi; norm_num) (by intro i hi; norm_num)
    (by intro i hi; norm_num)

/-- The prescribed product-based coefficient is positive at a concrete small gap. -/
example : 0 < prescribedProductAgreementConstant (1 / 5) :=
  prescribedProductAgreementConstant_pos (by norm_num) (by norm_num)

private def tinyCertificateDomain : Fin 3 ↪ ℚ :=
  ⟨fun i => (i : ℚ), fun i j h => by
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at h
    exact_mod_cast h⟩

private def tinyCertificateValues : Fin 2 → Fin 3 → ℚ := fun _ _ => 0

private noncomputable def tinyCurveCertificate :
    SymbolicReceivedCurve.Certificate 2 1 1 1 1 1 tinyCertificateDomain
      (fun i => powerBatchedCoordinate fun t => tinyCertificateValues t i) := by
  classical
  let Q : DifferentialPolynomial ℚ[X] 1 := MvPolynomial.X (some (0 : Fin 2))
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : Finsupp.single (some (0 : Fin 2)) 1 = u
    · simp [Q, MvPolynomial.coeff_X, hu]
    · simp [Q, MvPolynomial.coeff_X, hu]
  · intro u hu
    change u ∈ (MvPolynomial.X (some (0 : Fin 2))).support at hu
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hu
    rw [hu]
    simp [totalJetDegree, Finsupp.weight_single, jetDegreeWeight]
  · intro E _ ρ z
    have hmap :
        MvPolynomial.map (Polynomial.eval₂RingHom ρ z) Q =
          MvPolynomial.X (some (0 : Fin 2)) := by
      simp [Q]
    have hdegree :
        jetTotalDegree (MvPolynomial.X (some (0 : Fin 2)) : DifferentialPolynomial E 1) ≤ 1 := by
      apply (jetTotalDegree_le_iff _ 1).2
      intro u hu
      rw [MvPolynomial.support_X, Finset.mem_singleton] at hu
      rw [hu]
      simp [totalJetDegree, Finsupp.weight_single, jetDegreeWeight]
    refine ⟨by rw [hmap]; exact MvPolynomial.X_ne_zero _, ?_, ?_⟩
    · rw [hmap]
      exact hdegree
    · intro indices P hP hcard hagree
      rw [hmap, differentialSpecialization_jet]
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < indices.card)
      have hroot : P.eval (ρ (tinyCertificateDomain i)) = 0 := by
        simpa [tinyCertificateValues, powerBatchedCoordinate] using hagree i hi
      by_cases hzero : P = 0
      · simp [hzero]
      · have hnat : P.natDegree < 1 := (natDegree_lt_iff_degree_lt hzero).mpr hP
        have hnatZero : P.natDegree = 0 := by omega
        have hcoeff : P.coeff 0 = 0 := by
          rw [eq_C_of_natDegree_eq_zero hnatZero, Polynomial.eval_C] at hroot
          exact hroot
        have hpoly : P = 0 := by
          rw [eq_C_of_natDegree_eq_zero hnatZero]
          simp [hcoeff]
        simp [hpoly]

example :
    ∃ bad : Finset (AlgebraicClosure ℚ),
      (bad.card : ℝ) ≤
        polynomialCurveProductAgreementConstant (1 / 3) 1 1 1 * (3 : ℝ) ^ 2 := by
  obtain ⟨bad, hbound, _⟩ := exists_exceptional_exactPowerAgreement_of_certificate
    (F := ℚ) (E := AlgebraicClosure ℚ) (n := 3) (k := 1) (A := 2) (K := 2)
    (ℓ := 1) (ν := 1) (d := 1) (height := 1) (h := 1) (δ := 1 / 3)
    tinyCertificateDomain tinyCertificateValues (algebraMap ℚ (AlgebraicClosure ℚ))
    tinyCurveCertificate
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨bad, by simpa using hbound⟩

open ReedSolomon.HiddenDerivative.RatePartition

private noncomputable def mcaRate : ℝ := 1 / 2
private noncomputable def mcaGap : ℝ := 1 / 4
private noncomputable def mcaAgreement : ℝ := mcaRate + mcaGap
private noncomputable def mcaOrder : ℕ := fixedRatePartitionOrder mcaRate mcaGap

private theorem mcaRateGate :
    0 < mcaRate ∧ mcaRate < mcaAgreement ∧ mcaAgreement < 1 ∧ 500 ≤ mcaOrder ∧
      1 < rateGamma mcaRate mcaAgreement mcaOrder := by
  refine ⟨by norm_num [mcaRate], ?_, ?_, ?_, ?_⟩
  · norm_num [mcaRate, mcaAgreement, mcaGap]
  · norm_num [mcaRate, mcaAgreement, mcaGap]
  · simpa only [mcaOrder] using fixedRatePartitionOrder_ge_500 mcaRate mcaGap
  · simpa only [mcaOrder, mcaAgreement] using
      fixedRateGamma_gt_one (by norm_num [mcaRate]) (by norm_num [mcaGap])

private noncomputable def mcaParameters :
    PartitionFiniteParameters mcaRate mcaAgreement mcaOrder :=
  fixedRatePartitionFiniteParameters (by norm_num [mcaRate]) (by norm_num [mcaGap])

private noncomputable def mcaLength : ℕ :=
  rateBlockThreshold mcaRate mcaOrder mcaParameters.multiplicity

private theorem fixedRateThresholdRate
    (p : PartitionFiniteParameters mcaRate mcaAgreement mcaOrder) :
    ((1 : ℕ) : ℝ) ≤ mcaRate * rateBlockThreshold mcaRate mcaOrder p.multiplicity := by
  obtain ⟨hR, hRa, haone, _, _⟩ := mcaRateGate
  let n := rateBlockThreshold mcaRate mcaOrder p.multiplicity
  have hn : rateBlockThreshold mcaRate mcaOrder p.multiplicity ≤ n := Nat.le_refl _
  have hAn : mcaAgreement * n ≤ n := by
    have ha : mcaAgreement ≤ 1 := by norm_num [mcaRate, mcaAgreement, mcaGap]
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hk0 : ((0 : ℕ) : ℝ) ≤ mcaRate * n := by
    simpa only [Nat.cast_zero] using mul_nonneg hR.le hn0
  have hfloorLower : mcaOrder + 1 ≤ ⌊mcaRate * n⌋₊ :=
    (rateBlockThreshold_guards hR (hRa.trans haone) hn hk0 hAn).1
  have hfloor : 1 ≤ ⌊mcaRate * n⌋₊ := by omega
  calc
    ((1 : ℕ) : ℝ) ≤ (⌊mcaRate * n⌋₊ : ℝ) := by exact_mod_cast hfloor
    _ ≤ mcaRate * n := Nat.floor_le (by positivity)

private def mcaDomain (n : ℕ) : Fin n ↪ ℚ where
  toFun i := (i.val : ℚ)
  inj' i j hij := by
    change (i.val : ℚ) = (j.val : ℚ) at hij
    apply Fin.ext
    exact_mod_cast hij

private def mcaValues (n : ℕ) : Fin 2 → Fin n → ℚ := fun _ _ => 0

private theorem mcaLengthAgreement : mcaAgreement * mcaLength ≤ mcaLength := by
  have ha : mcaAgreement ≤ 1 := by norm_num [mcaRate, mcaAgreement, mcaGap]
  nlinarith [Nat.cast_nonneg mcaLength (α := ℝ)]

open Classical in
/-- The fixed-rate parameters give an extension-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset (AlgebraicClosure ℚ),
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant
        (mcaAgreement - mcaRate) (rateJetCap mcaRate mcaParameters.multiplicity)
        (marginHeight (rateJetCap mcaRate mcaParameters.multiplicity)
          (partitionFiniteRatio mcaRate mcaAgreement mcaOrder mcaParameters.multiplicity))
        mcaOrder * (mcaLength : ℝ) ^ (mcaOrder + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain mcaLength) (mcaValues mcaLength)
        (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z (0 : (AlgebraicClosure ℚ)[X]) := by
  obtain ⟨hR, hRa, haone, hd, _⟩ := mcaRateGate
  have hn : rateBlockThreshold mcaRate mcaOrder mcaParameters.multiplicity ≤ mcaLength :=
    Nat.le_refl _
  obtain ⟨exceptional, hbound, hgood⟩ := exists_ratePartition_curve_exactPowerAgreement
    (F := ℚ) (E := AlgebraicClosure ℚ) (n := mcaLength) (k := 1) (A := mcaLength)
    (ℓ := 1) mcaParameters hR hRa haone hd hn (by norm_num)
    (fixedRateThresholdRate mcaParameters) mcaLengthAgreement
    le_rfl (by norm_num) (mcaDomain mcaLength) (mcaValues mcaLength)
    (algebraMap ℚ (AlgebraicClosure ℚ)) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : AlgebraicClosure ℚ) :
      polynomialAgreementSet
        ((mcaDomain mcaLength).trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
          (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
        (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
          (mcaValues mcaLength t i)) z) (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The fixed-rate parameters give a base-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant
        (mcaAgreement - mcaRate) (rateJetCap mcaRate mcaParameters.multiplicity)
        (marginHeight (rateJetCap mcaRate mcaParameters.multiplicity)
          (partitionFiniteRatio mcaRate mcaAgreement mcaOrder mcaParameters.multiplicity))
        mcaOrder * (mcaLength : ℝ) ^ (mcaOrder + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain mcaLength) (mcaValues mcaLength)
        (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨hR, hRa, haone, hd, _⟩ := mcaRateGate
  have hn : rateBlockThreshold mcaRate mcaOrder mcaParameters.multiplicity ≤ mcaLength :=
    Nat.le_refl _
  obtain ⟨exceptional, hbound, hgood⟩ := exists_ratePartition_baseCurve_exactPowerAgreement
    (F := ℚ) (n := mcaLength) (k := 1) (A := mcaLength) (ℓ := 1) mcaParameters
    hR hRa haone hd hn (by norm_num) (fixedRateThresholdRate mcaParameters)
    mcaLengthAgreement le_rfl (by norm_num)
    (mcaDomain mcaLength) (mcaValues mcaLength)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) :
      polynomialAgreementSet (mcaDomain mcaLength)
        (powerBatchedWord (mcaValues mcaLength) z) (0 : ℚ[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The fixed-rate parameters give an affine-line agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ polynomialCurveProductAgreementConstant
        (mcaAgreement - mcaRate) (rateJetCap mcaRate mcaParameters.multiplicity)
        (marginHeight (rateJetCap mcaRate mcaParameters.multiplicity)
          (partitionFiniteRatio mcaRate mcaAgreement mcaOrder mcaParameters.multiplicity))
        mcaOrder * (mcaLength : ℝ) ^ (mcaOrder + 1) ∧
      ∃ z ∉ exceptional,
        HasExactCorrelatedPair (mcaDomain mcaLength) (fun _ ↦ 0) (fun _ ↦ 0) (RingHom.id ℚ)
          1 z (0 : ℚ[X]) := by
  obtain ⟨hR, _, haone, _, _⟩ := mcaRateGate
  have hgap : 0 < mcaGap := by norm_num [mcaGap]
  have hn : rateBlockThreshold mcaRate mcaOrder mcaParameters.multiplicity ≤ mcaLength :=
    Nat.le_refl _
  obtain ⟨exceptional, hbound, hgood⟩ := fixedRatePartitionOrder_line_exactCorrelatedPair
    (R := mcaRate) (δ := mcaGap) hR hgap haone
    (F := ℚ) (n := mcaLength) (k := 1) (A := mcaLength) hn
    (by norm_num) (fixedRateThresholdRate mcaParameters) mcaLengthAgreement le_rfl
    (mcaDomain mcaLength)
    (fun _ => 0) (fun _ => 0) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) :
      polynomialAgreementSet (mcaDomain mcaLength) (fun i ↦ 0 + z * 0) (0 : ℚ[X]) =
        Finset.univ := by
    ext i
    simp [polynomialAgreementSet]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, ?_, z, hz, ?_⟩
  · simpa [mcaAgreement, mcaGap, mcaOrder, mcaParameters] using hbound
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The strict fixed-rate gate selects parameters that yield a concrete line bound over `ℚ`. -/
example :
    ∃ p : PartitionFiniteParameters mcaRate mcaAgreement mcaOrder,
      ∃ exceptional : Finset ℚ,
        (exceptional.card : ℝ) ≤ polynomialCurveProductAgreementConstant
          (mcaAgreement - mcaRate) (rateJetCap mcaRate p.multiplicity)
          (marginHeight (rateJetCap mcaRate p.multiplicity)
            (partitionFiniteRatio mcaRate mcaAgreement mcaOrder p.multiplicity)) mcaOrder *
          (rateBlockThreshold mcaRate mcaOrder p.multiplicity : ℝ) ^ (mcaOrder + 1) ∧
        ∃ z ∉ exceptional, HasExactCorrelatedPair
          (mcaDomain (rateBlockThreshold mcaRate mcaOrder p.multiplicity)) (fun _ ↦ 0)
          (fun _ ↦ 0) (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨hR, hRa, haone, hd, hgate⟩ := mcaRateGate
  obtain ⟨p, hline⟩ := exists_ratePartition_line_exactCorrelatedPair_parameters hR hRa haone hd
    hgate
  let n := rateBlockThreshold mcaRate mcaOrder p.multiplicity
  have hn : rateBlockThreshold mcaRate mcaOrder p.multiplicity ≤ n := Nat.le_refl _
  have hkR : ((1 : ℕ) : ℝ) ≤ mcaRate * n := by
    simpa [n] using fixedRateThresholdRate p
  have haA : mcaAgreement * n ≤ n := by
    have ha : mcaAgreement ≤ 1 := by norm_num [mcaRate, mcaAgreement, mcaGap]
    nlinarith [Nat.cast_nonneg n (α := ℝ)]
  obtain ⟨exceptional, hbound, hgood⟩ := hline ℚ n 1 n hn (by norm_num) hkR haA le_rfl
    (mcaDomain n) (fun _ => 0) (fun _ => 0)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) : polynomialAgreementSet (mcaDomain n) (fun i ↦ 0 + z * 0)
      (0 : ℚ[X]) =
      Finset.univ := by
    ext i
    simp [polynomialAgreementSet]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨p, exceptional, by simpa [n] using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

private noncomputable def uniformMcaGap : ℝ := 1 / 5
private noncomputable def uniformMcaLength : ℕ := uniformBlockThreshold uniformMcaGap

private theorem uniformMcaAgreementGap :
    ((1 : ℕ) : ℝ) + uniformMcaGap * uniformMcaLength ≤ uniformMcaLength := by
  have hm : 1 ≤ uniformMultiplicity uniformMcaGap := by
    have := add_two_le_uniformMultiplicity uniformMcaGap
    omega
  have hm' : (1 : ℝ) ≤ uniformMultiplicity uniformMcaGap := by exact_mod_cast hm
  have hsize := (uniformBlockThreshold_guards (δ := uniformMcaGap)
    (n := uniformMcaLength) (by norm_num [uniformMcaGap]) (by norm_num [uniformMcaGap])
    (Nat.le_refl _)).1
  have hmult : (2 : ℝ) ≤ 2 * (uniformMultiplicity uniformMcaGap : ℝ) := by nlinarith
  have hn50 : (50 : ℝ) ≤ uniformMcaLength := by
    have hle := hmult.trans hsize
    norm_num [uniformMcaGap] at hle
    linarith
  norm_num [uniformMcaGap]
  nlinarith [hn50]

private theorem uniformMcaBlockLength : uniformBlockThreshold uniformMcaGap ≤ uniformMcaLength :=
  Nat.le_refl _

open Classical in
/-- The uniform parameters give an extension-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset (AlgebraicClosure ℚ),
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant uniformMcaGap
        (uniformJetCap uniformMcaGap) (150 * uniformJetCap uniformMcaGap)
        (uniformDerivativeOrder uniformMcaGap) *
        (uniformMcaLength : ℝ) ^ (uniformDerivativeOrder uniformMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain uniformMcaLength)
        (mcaValues uniformMcaLength) (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z
        (0 : (AlgebraicClosure ℚ)[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ := exists_uniformRatePartition_curve_exactPowerAgreement
    (F := ℚ) (E := AlgebraicClosure ℚ) (δ := uniformMcaGap) (n := uniformMcaLength)
    (k := 1) (A := uniformMcaLength) (ℓ := 1)
    (by norm_num [uniformMcaGap]) (by norm_num [uniformMcaGap]) uniformMcaBlockLength
    (by norm_num) uniformMcaAgreementGap le_rfl (by norm_num)
    (mcaDomain uniformMcaLength) (mcaValues uniformMcaLength)
    (algebraMap ℚ (AlgebraicClosure ℚ)) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : AlgebraicClosure ℚ) :
      polynomialAgreementSet
        ((mcaDomain uniformMcaLength).trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
          (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
        (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
          (mcaValues uniformMcaLength t i)) z) (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The uniform parameters give a base-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant uniformMcaGap
        (uniformJetCap uniformMcaGap) (150 * uniformJetCap uniformMcaGap)
        (uniformDerivativeOrder uniformMcaGap) *
        (uniformMcaLength : ℝ) ^ (uniformDerivativeOrder uniformMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain uniformMcaLength)
        (mcaValues uniformMcaLength) (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_uniformRatePartition_baseCurve_exactPowerAgreement
    (δ := uniformMcaGap) (n := uniformMcaLength) (k := 1) (A := uniformMcaLength)
    (ℓ := 1) (by norm_num [uniformMcaGap]) (by norm_num [uniformMcaGap])
    uniformMcaBlockLength (by norm_num) uniformMcaAgreementGap le_rfl (by norm_num)
    (mcaDomain uniformMcaLength) (mcaValues uniformMcaLength)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) : polynomialAgreementSet (mcaDomain uniformMcaLength)
      (powerBatchedWord (mcaValues uniformMcaLength) z) (0 : ℚ[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The uniform parameters give an affine-line agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ polynomialCurveProductAgreementConstant uniformMcaGap
        (uniformJetCap uniformMcaGap) (150 * uniformJetCap uniformMcaGap)
        (uniformDerivativeOrder uniformMcaGap) *
        (uniformMcaLength : ℝ) ^ (uniformDerivativeOrder uniformMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactCorrelatedPair (mcaDomain uniformMcaLength) (fun _ ↦ 0)
        (fun _ ↦ 0) (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ := exists_uniformRatePartition_line_exactCorrelatedPair
    (δ := uniformMcaGap) (n := uniformMcaLength) (k := 1) (A := uniformMcaLength)
    (by norm_num [uniformMcaGap]) (by norm_num [uniformMcaGap]) uniformMcaBlockLength
    (by norm_num) uniformMcaAgreementGap le_rfl (mcaDomain uniformMcaLength)
    (fun _ => 0) (fun _ => 0) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) : polynomialAgreementSet (mcaDomain uniformMcaLength)
      (fun i ↦ 0 + z * 0) (0 : ℚ[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

example :
    ∃ bad : Finset (AlgebraicClosure ℚ),
      (bad.card : ℝ) ≤
        polynomialCurveProductAgreementConstant (1 / 3) 1 1 1 * (3 : ℝ) ^ 2 := by
  obtain ⟨bad, hbound, _⟩ :=
    exists_exceptional_exactPowerAgreement_of_certificate_of_jetCharacteristic
    (F := ℚ) (E := AlgebraicClosure ℚ) (n := 3) (k := 1) (A := 2) (K := 2)
    (d := 1) (ν := 1) (H := 1) (h := 1) (ℓ := 1) (δ := 1 / 3)
    tinyCertificateDomain tinyCertificateValues (algebraMap ℚ (AlgebraicClosure ℚ))
    tinyCurveCertificate
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num))
  exact ⟨bad, by simpa using hbound⟩

private noncomputable def mathMcaGap : ℝ := 1 / 5
private noncomputable def mathMcaLength : ℕ := uniformMathematicalCapacityLength mathMcaGap

private theorem mathMcaBaseLength : uniformMathematicalLength mathMcaGap ≤ mathMcaLength :=
  le_max_left _ _

private theorem mathMcaAgreementGap :
    ((1 : ℕ) : ℝ) + mathMcaGap * mathMcaLength ≤ mathMcaLength := by
  have hm : 0 < uniformMathematicalMultiplicity mathMcaGap :=
    lt_of_lt_of_le (by omega) (add_two_le_closedMultiplicity (by norm_num)
      (by have := uniformDerivativeOrder_pos mathMcaGap; omega))
  obtain ⟨-, -, hν, hνn⟩ := uniformMathematical_integer_guards (n := mathMcaLength)
    (by norm_num [mathMcaGap]) (by norm_num [mathMcaGap]) hm mathMcaBaseLength
  have hn : (2 : ℝ) ≤ mathMcaLength := by exact_mod_cast (show 2 ≤ mathMcaLength by omega)
  norm_num [mathMcaGap]
  linarith

open Classical in
/-- The mathematical uniform parameters give an extension-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset (AlgebraicClosure ℚ),
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant mathMcaGap
        (uniformMathematicalJetBound mathMcaGap) (150 * uniformMathematicalJetBound mathMcaGap)
        (uniformDerivativeOrder mathMcaGap) *
        (mathMcaLength : ℝ) ^ (uniformDerivativeOrder mathMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain mathMcaLength)
        (mcaValues mathMcaLength) (algebraMap ℚ (AlgebraicClosure ℚ)) 1 z
        (0 : (AlgebraicClosure ℚ)[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_mathematicalUniformRatePartition_curve_exactPowerAgreement
    (F := ℚ) (E := AlgebraicClosure ℚ) (δ := mathMcaGap) (n := mathMcaLength)
    (k := 1) (A := mathMcaLength) (ℓ := 1)
    (by norm_num [mathMcaGap]) (by norm_num [mathMcaGap]) mathMcaBaseLength
    (by norm_num) mathMcaAgreementGap le_rfl (by norm_num)
    (mcaDomain mathMcaLength) (mcaValues mathMcaLength)
    (algebraMap ℚ (AlgebraicClosure ℚ)) (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : AlgebraicClosure ℚ) :
      polynomialAgreementSet
        ((mcaDomain mathMcaLength).trans ⟨algebraMap ℚ (AlgebraicClosure ℚ),
          (algebraMap ℚ (AlgebraicClosure ℚ)).injective⟩)
        (powerBatchedWord (fun t i ↦ algebraMap ℚ (AlgebraicClosure ℚ)
          (mcaValues mathMcaLength t i)) z) (0 : (AlgebraicClosure ℚ)[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The mathematical uniform parameters give a base-field curve agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ (1 : ℝ) * polynomialCurveProductAgreementConstant mathMcaGap
        (uniformMathematicalJetBound mathMcaGap) (150 * uniformMathematicalJetBound mathMcaGap)
        (uniformDerivativeOrder mathMcaGap) *
        (mathMcaLength : ℝ) ^ (uniformDerivativeOrder mathMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactPowerAgreement (mcaDomain mathMcaLength)
        (mcaValues mathMcaLength) (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement
    (δ := mathMcaGap) (n := mathMcaLength) (k := 1) (A := mathMcaLength) (ℓ := 1)
    (by norm_num [mathMcaGap]) (by norm_num [mathMcaGap]) mathMcaBaseLength
    (by norm_num) mathMcaAgreementGap le_rfl (by norm_num)
    (mcaDomain mathMcaLength) (mcaValues mathMcaLength)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) : polynomialAgreementSet (mcaDomain mathMcaLength)
      (powerBatchedWord (mcaValues mathMcaLength) z) (0 : ℚ[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet, powerBatchedWord, mcaValues]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)

open Classical in
/-- The mathematical uniform parameters give an affine-line agreement bound over `ℚ`. -/
example :
    ∃ exceptional : Finset ℚ,
      (exceptional.card : ℝ) ≤ mathematicalUniformLineAgreementConstant mathMcaGap *
        (mathMcaLength : ℝ) ^ (uniformDerivativeOrder mathMcaGap + 1) ∧
      ∃ z ∉ exceptional, HasExactCorrelatedPair (mcaDomain mathMcaLength) (fun _ ↦ 0)
        (fun _ ↦ 0) (RingHom.id ℚ) 1 z (0 : ℚ[X]) := by
  obtain ⟨exceptional, hbound, hgood⟩ :=
    exists_mathematicalUniformRatePartition_line_exactCorrelatedPair
    (δ := mathMcaGap) (n := mathMcaLength) (k := 1) (A := mathMcaLength)
    (by norm_num [mathMcaGap]) (by norm_num [mathMcaGap]) le_rfl (by norm_num)
    mathMcaAgreementGap le_rfl (mcaDomain mathMcaLength) (fun _ => 0) (fun _ => 0)
    (Or.inl (ringChar.eq_zero : ringChar ℚ = 0))
  have hset (z : ℚ) : polynomialAgreementSet (mcaDomain mathMcaLength)
      (fun i ↦ 0 + z * 0) (0 : ℚ[X]) = Finset.univ := by
    ext i
    simp [polynomialAgreementSet]
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hbound, z, hz, ?_⟩
  exact hgood z hz 0 (by simp) (by rw [hset z]; simp)
