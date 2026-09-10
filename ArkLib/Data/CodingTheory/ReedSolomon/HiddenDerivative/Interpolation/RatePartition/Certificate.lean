/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.RatePartitionMatrix

/-!
# Finite rate-partition interpolation certificates

The derivative-order support and its integer local rank budget construct a
symbolic equation whenever the source count exceeds `n*r₀`. Its challenge height
is `n*r₀*(ℓ*ν)/(N-n*r₀)`, with natural division. The finite ratio estimates choose
parameters satisfying this test before the field and received curve are supplied.
No characteristic assumption is needed for interpolation itself.
-/

@[expose] public section

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

/-- The canonical selected monomials in the existing symbolic column representation. -/
def ratePartitionColumns {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    Fin (Fintype.card ↥(ratePartitionExponents D d W L hD)) → SourceColumn d :=
  fun j ↦ SourceColumn.ofExponent
    (((Fintype.equivFin ↥(ratePartitionExponents D d W L hD)).symm j).1)

@[simp]
theorem ratePartitionColumns_exponent {D d W : ℕ} {L : ℝ} (hD : 0 < D)
    (j : Fin (Fintype.card ↥(ratePartitionExponents D d W L hD))) :
    (ratePartitionColumns hD j).exponent =
      ((Fintype.equivFin ↥(ratePartitionExponents D d W L hD)).symm j).1 := by
  simp [ratePartitionColumns]

/-- Every source monomial is used once. -/
theorem ratePartitionColumns_injective {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    Function.Injective (ratePartitionColumns (d := d) (W := W) (L := L) hD) := by
  intro i j hij
  apply (Fintype.equivFin ↥(ratePartitionExponents D d W L hD)).symm.injective
  apply Subtype.ext
  rw [← ratePartitionColumns_exponent hD i, ← ratePartitionColumns_exponent hD j, hij]

/-- Canonical columns satisfy precisely the rate-partition support restrictions. -/
theorem ratePartitionColumns_eligible {D d W : ℕ} {L : ℝ} (hD : 0 < D)
    (j : Fin (Fintype.card ↥(ratePartitionExponents D d W L hD))) :
    RatePartitionEligible D d W L (ratePartitionColumns hD j).exponent := by
  rw [ratePartitionColumns_exponent]
  exact mem_ratePartitionExponents.mp
    ((Fintype.equivFin ↥(ratePartitionExponents D d W L hD)).symm j).2

/-- The finite partition source/rank test yields a universally nonvanishing curve certificate.
Its jet cap is supplied independently of multiplicity and its height retains the exact surplus. -/
theorem exists_ratePartition_certificate {F : Type*} [Field F]
    {D d m W n A k ℓ ν : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hdegree : ∀ u, RatePartitionEligible D d W L u → totalJetDegree u ≤ ν)
    (hsurplus : n * ratePartitionRankBound d m W <
      (ratePartitionExponents D d W L hD).card) :
    let N := (ratePartitionExponents D d W L hD).card
    let r := n * ratePartitionRankBound d m W
    Nonempty (Certificate F A k ℓ ν d (r * (ℓ * ν) / (N - r)) centers w) := by
  classical
  let columns := ratePartitionColumns (d := d) (W := W) (L := L) hD
  have hN : Fintype.card ↥(ratePartitionExponents D d W L hD) =
      (ratePartitionExponents D d W L hD).card := Fintype.card_coe _
  have hband := ratePartitionColumns_eligible (d := d) (W := W) (L := L) hD
  have htotal : ∀ j, totalJetDegree (columns j).exponent ≤ ν :=
    fun j ↦ hdegree _ (hband j)
  have hy₀ : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    have hc : (columns j).exponent (some 0) ≤ totalJetDegree (columns j).exponent :=
      Finsupp.le_degree 0 (columns j).exponent.some
    have hc' : (columns j).y₀ ≤ totalJetDegree (columns j).exponent := by
      simpa only [SourceColumn.exponent_zero] using hc
    exact hc'.trans (htotal j)
  have hcert := exists_certificate_of_rank_bound hL hbudget hkD centers w hw columns
    (ratePartitionColumns_injective hD) hy₀ htotal (fun j ↦ (hband j).weightedSupport)
    (finiteConstraintMatrix_rank_le_partition (fun i ↦ centers i) w columns
      (fun j ↦ (hband j).1)) (by simpa only [hN] using hsurplus)
  simpa only [hN] using hcert

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
