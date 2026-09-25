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
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.WeightedSupport.ScalarParameters
import ArkLib.Data.Polynomial.Differential.Basic
import ArkLib.Data.Polynomial.Differential.JetDegree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Acceptance case for correlated-agreement capacity bounds -/

open Polynomial ReedSolomon
open ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.WeightedSupportParameters
open PolynomialDifferential

example : correlatedMidpoint (1 / 2) 10 2 ≤ 8 ∧
    (1 / 2 : ℝ) * (10 : ℕ) / 2 ≤ ((8 - correlatedMidpoint (1 / 2) 10 2 + 1 : ℕ) : ℝ) := by
  obtain ⟨-, h, -, h', -⟩ := correlatedMidpoint_bounds (1 / 2) 10 2 8 (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h, h'⟩

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
  have hA : agreementThreshold δ n 1 ≤ n := by
    apply (agreementThreshold_le_iff_real hδ.le n 1 n).mpr
    have hnR : (n : ℝ) = 8 * m := by norm_num [n]
    rw [hnR]
    dsimp [δ]
    push_cast
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm.ne'
    nlinarith
  have hparams := exists_prescribed_correlated_parameters (F := ℚ) δ n 1 centers f g
    hδ hδmax hblock hA (Or.inl (by simp))
  exact hparams.1

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
  obtain ⟨bad, hbound, _⟩ := exists_curveMCA_of_certificate
    (F := ℚ) (E := AlgebraicClosure ℚ) (n := 3) (k := 1) (A := 2) (K := 2)
    (ℓ := 1) (ν := 1) (d := 1) (height := 1) (h := 1) (δ := 1 / 3)
    tinyCertificateDomain tinyCertificateValues (algebraMap ℚ (AlgebraicClosure ℚ))
    tinyCurveCertificate
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨bad, by simpa using hbound⟩

example :
    ∃ bad : Finset (AlgebraicClosure ℚ),
      (bad.card : ℝ) ≤
        polynomialCurveProductAgreementConstant (1 / 3) 1 1 1 * (3 : ℝ) ^ 2 := by
  obtain ⟨bad, hbound, _⟩ := exists_curveMCA_of_certificate_of_jetCharacteristic
    (F := ℚ) (E := AlgebraicClosure ℚ) (n := 3) (k := 1) (A := 2) (K := 2)
    (d := 1) (ν := 1) (H := 1) (h := 1) (ℓ := 1) (δ := 1 / 3)
    tinyCertificateDomain tinyCertificateValues (algebraMap ℚ (AlgebraicClosure ℚ))
    tinyCurveCertificate
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl (by norm_num))
  exact ⟨bad, by simpa using hbound⟩
