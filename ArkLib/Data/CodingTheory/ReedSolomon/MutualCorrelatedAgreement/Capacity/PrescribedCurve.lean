/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.Parameters
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.ProductCounting
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveSupportCertificate
import ArkLib.Data.Polynomial.Differential.WitnessCount
import ArkLib.Data.Polynomial.Differential.DerivativeDescent
/-!
# Prescribed power-batched agreement on polynomial curves

The prescribed interpolation parameters produce a symbolic curve certificate for arbitrary
power-batched received words. Its separant stages give a finite exceptional challenge set, and
product-based incidence estimates yield a scalar bound linear in the batching length.

## Main statements

* `exists_prescribedCurveMCA_exact`: an exact exceptional-set bound using actual separant stages.
* `exists_prescribedCurveMCA`: the corresponding explicit scalar bound.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative.WeightedSupportParameters
open scoped BigOperators

universe u

open Classical in
/-- The prescribed certificate yields an exceptional-set bound using each actual separant stage. -/
theorem exists_prescribedCurveMCA_exact {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E]
    (δ : ℝ) (n k ℓ : ℕ) (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp (xi / δ)) : ℝ) ^ 2 *
        harmonic (Nat.ceil (Real.exp (xi / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      let ν := 2 * m - 1
      let K := max k (Nat.floor (δ * n / 2))
      ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    let A := agreementThreshold δ n k
    let d := Nat.ceil (Real.exp (xi / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
    let ν := 2 * m - 1
    let K := max k (Nat.floor (δ * n / 2))
    let L := correlatedProductCutoff d k A
    let H := 12 * (ℓ * ν) - 1
    ∃ stages : List (SeparantStage F[X] d), ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ (H : ℚ) +
        ∑ stage ∈ stages.toFinset,
          regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
            (jetTotalDegree stage.1) H (τ := 2 * K - 3) ∧
      stages.toFinset.card ≤ ν ∧
      (∀ stage ∈ stages, stage.2.val ≤ d) ∧
      (∀ stage ∈ stages, 0 < jetTotalDegree stage.1 ∧ jetTotalDegree stage.1 ≤ ν) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  dsimp only
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let ν := 2 * m - 1
  let K := max k (Nat.floor (δ * n / 2))
  let L := correlatedProductCutoff d k A
  let H := 12 * (ℓ * ν) - 1
  obtain ⟨hn, _hm, hν, _hνm, _hνn, hdK, hkK, hKn, _hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hblock hA
  obtain ⟨hcharWeight, hcharK⟩ := characteristic_bounds_of_max (F := F) hchar
  have hcharCut : ringChar F = 0 ∨ K - 1 < ringChar F :=
    hcharK.imp_right (by omega)
  obtain ⟨cert⟩ :=
    HiddenDerivative.SymbolicReceivedCurve.exists_prescribed_certificate δ n k ℓ domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
      (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i)
      hℓ hδ hδ' hblock hA
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    cert.exists_exceptional_powerBatchedAgreement_sharp_of_exponent iota K L (2 * K - 3)
      (fun r _ ↦ taylorExponentSufficient_two_mul_sub_three r K) (by
        have hdpos : 0 < d := Nat.ceil_pos.mpr (Real.exp_pos _)
        omega) hdK hkK
      (correlatedProductCutoff_bounds d k A _hkA).1
      (correlatedProductCutoff_bounds d k A _hkA).2 hA hℓ
      hcharWeight (by
        intro r hr i hri hiK
        have hchoose := PolynomialDifferential.natCast_choose_ne_zero_of_ringChar
          (F := F) (D := K - 1) (s := r) hcharCut (i - r) (by omega) (by omega)
        simpa only [Nat.sub_add_cancel hri.le] using hchoose)
  refine ⟨stages, exceptional, hcard, ?_, (fun stage _ ↦ Fin.is_le stage.2), ?_, hexact⟩
  · exact (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetTotalDegree_le)
  · intro stage hs
    refine ⟨?_, (hc.jetTotalDegree_le_of_mem hs).trans cert.jetTotalDegree_le⟩
    have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
      (hc.highestActiveJet_eq_of_mem hs)).1
    exact hactive.trans_le (jetDegree_le_total stage.1 stage.2)

open Classical in
/-- One finite exceptional set bounds exact agreement for every prescribed power-batched curve. -/
theorem exists_prescribedCurveMCA {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E]
    (δ : ℝ) (n k ℓ : ℕ) (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp (xi / δ)) : ℝ) ^ 2 *
        harmonic (Nat.ceil (Real.exp (xi / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar :
      let d := Nat.ceil (Real.exp (xi / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      let ν := 2 * m - 1
      let K := max k (Nat.floor (δ * n / 2))
      ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * prescribedProductAgreementConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp (xi / δ)) + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        agreementThreshold δ n k ≤
          (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp (xi / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
  let ν := 2 * m - 1
  let K := max k (Nat.floor (δ * n / 2))
  let L := correlatedProductCutoff d k A
  let H := 12 * (ℓ * ν) - 1
  obtain ⟨hn, _hm, hν, _hνm, _hνn, _hdK, _hkK, hKn, _hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hblock hA
  obtain ⟨stages, exceptional, hcard, hstages, horders, hweights, hexact⟩ :=
    exists_prescribedCurveMCA_exact δ n k ℓ domain values iota hδ hδ' hk hℓ
      hblock hA hchar
  refine ⟨exceptional, ?_, hexact⟩
  have hcardR : (exceptional.card : ℝ) ≤ (H : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
          (jetTotalDegree stage.1) H (τ := 2 * K - 3) : ℝ) := by
    change (exceptional.card : ℚ) ≤ (H : ℚ) +
      ∑ stage ∈ stages.toFinset,
        regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
          (jetTotalDegree stage.1) H (τ := 2 * K - 3) at hcard
    exact_mod_cast hcard
  apply hcardR.trans
  have hδone : δ ≤ 1 := by linarith
  have hh : 0 < 12 * ν := Nat.mul_pos (by omega) hν
  have hH : H ≤ ℓ * (12 * ν) := by
    dsimp only [H]
    calc
      12 * (ℓ * ν) - 1 ≤ 12 * (ℓ * ν) := Nat.sub_le _ _
      _ = ℓ * (12 * ν) := by ring
  have hterminal : (H : ℝ) ≤ ((ℓ * (12 * ν) : ℕ) : ℝ) := by exact_mod_cast hH
  calc
    (H : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
          (jetTotalDegree stage.1) H (τ := 2 * K - 3) : ℝ) ≤
      ((ℓ * (12 * ν) : ℕ) : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularPowerBatchedAgreementSharpBound stage.2.val n ℓ K k L A
          (jetTotalDegree stage.1) H (τ := 2 * K - 3) : ℝ) := add_le_add hterminal le_rfl
    _ ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ ν (12 * ν) d *
        (n : ℝ) ^ (d + 1) := by
      simpa only using
        (regularPowerBatchedAgreementSharp_product_finiteStage_le stages.toFinset
          (fun stage ↦ stage.2.val) (fun stage ↦ jetTotalDegree stage.1) (fun _ ↦ H)
          δ n K k A ℓ ν (12 * ν) d (2 * K - 3) hδ hδone
          (Nat.ceil_pos.mpr (Real.exp_pos _)) hn hk hν hh hKn hgap hA
          (Nat.sub_le _ _) hstages
          (fun stage hs ↦ horders stage (List.mem_toFinset.mp hs))
          (fun stage hs ↦ (hweights stage (List.mem_toFinset.mp hs)).1)
          (fun stage hs ↦ (hweights stage (List.mem_toFinset.mp hs)).2)
          (fun _ _ ↦ hH))
    _ = (ℓ : ℝ) * prescribedProductAgreementConstant δ * (n : ℝ) ^ (d + 1) := by
      simp only [prescribedProductAgreementConstant, d, m, ν]

end ReedSolomon
