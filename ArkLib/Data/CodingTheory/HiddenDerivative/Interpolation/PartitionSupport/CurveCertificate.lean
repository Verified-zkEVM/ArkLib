/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.PartitionRank

/-!
# Symbolic certificates from the partition support

The finite set of partition-support exponents indexes distinct source columns. When its size
exceeds the number of received points times the local derivative budget, these columns produce a
uniformly nonvanishing polynomial-curve certificate. The challenge height retains the exact
rank surplus and uses natural-number division.

## Main statements

* `partitionSupportColumns` and its exponent, injectivity and eligibility lemmas.
* `exists_partitionSupport_curve_certificate`: the symbolic curve certificate from a strict
  dimension surplus.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

private def sourceColumnOfExponent {d : ℕ} (u : JetVariable d →₀ ℕ) : SourceColumn d :=
  ⟨u none, u (some 0), fun j ↦ u (some j.succ)⟩

private theorem sourceColumnOfExponent_exponent {d : ℕ} (u : JetVariable d →₀ ℕ) :
    (sourceColumnOfExponent u).exponent = u := by
  ext v
  rcases v with _ | j
  · simp [sourceColumnOfExponent, SourceColumn.exponent]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [sourceColumnOfExponent, SourceColumn.exponent]
    · simp [sourceColumnOfExponent, SourceColumn.exponent, Finsupp.single_apply]

/-- The source column indexed by a partition-support exponent. -/
def partitionSupportColumns {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    Fin (Fintype.card ↥(partitionSupportExponents D d W L hD)) → SourceColumn d :=
  fun j ↦
    let u := ((Fintype.equivFin ↥(partitionSupportExponents D d W L hD)).symm j).1
    ⟨u none, u (some 0), fun i ↦ u (some i.succ)⟩

/-- The exponent of a selected source column is its partition-support index. -/
@[simp]
theorem partitionSupportColumns_exponent {D d W : ℕ} {L : ℝ} (hD : 0 < D)
    (j : Fin (Fintype.card ↥(partitionSupportExponents D d W L hD))) :
    (partitionSupportColumns (d := d) (W := W) (L := L) hD j).exponent =
      ((Fintype.equivFin ↥(partitionSupportExponents D d W L hD)).symm j).1 :=
  by
    change (sourceColumnOfExponent _).exponent = _
    exact sourceColumnOfExponent_exponent _

/-- The selected source columns are pairwise distinct. -/
theorem partitionSupportColumns_injective {D d W : ℕ} {L : ℝ} (hD : 0 < D) :
    Function.Injective (partitionSupportColumns (d := d) (W := W) (L := L) hD) := by
  intro i j hij
  apply (Fintype.equivFin ↥(partitionSupportExponents D d W L hD)).symm.injective
  apply Subtype.ext
  rw [← partitionSupportColumns_exponent hD i, ← partitionSupportColumns_exponent hD j]
  exact congrArg SourceColumn.exponent hij

/-- Every selected source column satisfies the partition-support restrictions. -/
theorem partitionSupportColumns_eligible {D d W : ℕ} {L : ℝ} (hD : 0 < D)
    (j : Fin (Fintype.card ↥(partitionSupportExponents D d W L hD))) :
    PartitionSupportEligible D d W L
      (partitionSupportColumns (d := d) (W := W) (L := L) hD j).exponent := by
  rw [partitionSupportColumns_exponent]
  exact mem_partitionSupportExponents.mp
    ((Fintype.equivFin ↥(partitionSupportExponents D d W L hD)).symm j).2

/-- A strict surplus of partition-support exponents over the total local derivative budget gives a
uniformly nonvanishing symbolic curve certificate. Its challenge height is
`r * (ℓ * ν) / (N - r)`, where `N` is the number of eligible exponents and
`r = n * localDerivativeCoordinateBudget d m W`. -/
theorem exists_partitionSupport_curve_certificate {F : Type*} [Field F]
    {D d m W n A k ℓ ν : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hbudget : 0 < m * A)
    (hkD : k ≤ D + 1) (centers : Fin n ↪ F) (received : Fin n → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (hdegree : ∀ u, PartitionSupportEligible D d W L u → totalJetDegree u ≤ ν)
    (hsurplus : n * localDerivativeCoordinateBudget d m W <
      (partitionSupportExponents D d W L hD).card) :
    let N := (partitionSupportExponents D d W L hD).card
    let r := n * localDerivativeCoordinateBudget d m W
    Nonempty (SymbolicReceivedCurve.CurveCertificate F A k ℓ ν d
      (r * (ℓ * ν) / (N - r)) centers received) := by
  classical
  let N := Fintype.card ↥(partitionSupportExponents D d W L hD)
  let r := n * localDerivativeCoordinateBudget d m W
  let columns := partitionSupportColumns (d := d) (W := W) (L := L) hD
  have hN : N = (partitionSupportExponents D d W L hD).card := Fintype.card_coe _
  have hband := partitionSupportColumns_eligible (d := d) (W := W) (L := L) hD
  have htotal : ∀ j, totalJetDegree (columns j).exponent ≤ ν :=
    fun j ↦ hdegree _ (hband j)
  have hy₀ : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    have hc : (columns j).y₀ ≤ totalJetDegree (columns j).exponent := by
      have hc := Finsupp.le_degree 0 (columns j).exponent.some
      have hy₀ : (columns j).exponent.some 0 = (columns j).y₀ := by
        simp [SourceColumn.exponent]
      calc
        (columns j).y₀ = (columns j).exponent.some 0 := hy₀.symm
        _ ≤ Finsupp.degree (columns j).exponent.some := hc
        _ = totalJetDegree (columns j).exponent :=
          (totalJetDegree_eq_degree_some _).symm
    exact hc.trans (htotal j)
  have hweight : ∀ j, (columns j).exponent.weight (differentialWeight D) < m * A := by
    intro j
    have hcoarse :
        (columns j).exponent none + D * totalJetDegree (columns j).exponent < m * A := by
      exact_mod_cast ((hband j).2.trans_le hL)
    exact (weight_le_add_mul_totalJetDegree D (columns j).exponent).trans_lt hcoarse
  have hrank :
      ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) received columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ r := by
    change ((localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) received columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * localDerivativeCoordinateBudget d m W
    exact symbolicLocalConstraintMatrix_rank_le_partition centers received columns
      (fun j ↦ (hband j).1)
  have hrN : r < N := by
    dsimp only [r]
    rw [hN]
    exact hsurplus
  have hcert := SymbolicReceivedCurve.exists_curveCertificate_of_rank_bound
    hbudget hkD centers received hreceived columns (partitionSupportColumns_injective
      (d := d) (W := W) (L := L) hD) hy₀ htotal hweight hrank hrN
  simpa only [Fintype.card_coe] using hcert

end ReedSolomon.HiddenDerivative
