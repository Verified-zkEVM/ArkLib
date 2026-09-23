/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.LocalRank
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBlocks
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Primitive interpolation from weighted support

The weighted-support constraint matrix at one received point is a column restriction of the
coordinate matrix on the full weighted-support space. The coordinate-matrix rank over a rational
function field is bounded by the corresponding polynomial-valued constraint map over the base
field. Summing these local bounds gives a primitive interpolant for received curves whenever the
weighted-support space has a strict dimension surplus.

## Main statements

* `weightedSupportColumnIndex` and `localConstraintBlock_eq_weightedSupportSubmatrix`: the
  eligible support index and the local matrix restriction.
* `localConstraintMatrix_rank_le_weightedSupport`: the global rank bound over the rational
  function field.
* `exists_primitive_weightedSupport_interpolant`: a primitive interpolant from a strict
  weighted-support dimension surplus.
* `interpolant_mem_weightedSupportSpace` and its degree bounds: support and total jet degree of an
  assembled interpolant and its challenge specializations.
* `totalJetDegree_interpolant_le_two_mul_sub_one` and
  `jetTotalDegree_map_interpolant_le_two_mul_sub_one`: the prescribed cutoff bounds.

## References

* [DKT26]
* [BCPZZ26]
-/

@[expose] public section

open Polynomial PolynomialDifferential
open scoped BigOperators

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ}
variable {ι κ : Type*}

/-- The weighted-support exponent indexing a source column. -/
def weightedSupportColumnIndex (hD : 0 < D) {κ : Type*}
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    κ → ↥(weightedSupportExponents D d W L hD) := fun j =>
  ⟨(columns j).exponent, (mem_weightedSupportExponents).mpr (hband j)⟩

/-- A local block of the symbolic curve matrix is the weighted-support coordinate matrix restricted
to the exponents of the selected source columns. -/
theorem localConstraintBlock_eq_weightedSupportSubmatrix
    (hD : 0 < D) (centers : ι → F) (received : ι → F[X])
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (i : ι) :
    (fun row j => algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns
        (i, row) j) : Matrix (LowContactIndex d m) κ (RatFunc F)) =
      (weightedSupportLocalCoordinateMatrix (R := RatFunc F) (d := d) (m := m) (W := W)
        (L := L) hD
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (received i))).submatrix id
          (weightedSupportColumnIndex hD columns hband) := by
  ext row j
  simp only [Matrix.submatrix_apply, id_eq, localConstraintMatrix,
    weightedSupportLocalCoordinateMatrix_apply, weightedSupportColumnIndex,
    localConstraintCoordinatesAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    lowContactCoefficients, LinearMap.pi_apply, MvPolynomial.lcoeff_apply,
    SourceColumn.polynomial]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp

/-- The symbolic curve matrix has rank at most the number of received points times the rank of
the weighted-support local constraint map over the base field. -/
theorem localConstraintMatrix_rank_le_weightedSupport [Fintype ι] [Fintype κ]
    (hD : 0 < D) (centers : ι → F) (received : ι → F[X])
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤
      Fintype.card ι * Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) := by
  let A := (localConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns).map
    (algebraMap F[X] (RatFunc F))
  change A.rank ≤ _
  calc
    A.rank ≤ ∑ i, (A.submatrix (fun row => (i, row)) id).rank :=
      Matrix.rank_prod_rows_le_sum A
    _ ≤ ∑ _i : ι, Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
          (R := F)
          (L := L) m hD 0 0)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [show A.submatrix (fun row => (i, row)) id =
        (fun row j => algebraMap F[X] (RatFunc F)
          (localConstraintMatrix m (fun j => Polynomial.C (centers j)) received columns
            (i, row) j) : Matrix (LowContactIndex d m) κ (RatFunc F)) by
              ext row j; rfl]
      rw [localConstraintBlock_eq_weightedSupportSubmatrix hD centers received columns hband i]
      exact (Matrix.rank_submatrix_le _ id
        (weightedSupportColumnIndex hD columns hband)).trans
        (rank_weightedSupportLocalCoordinateMatrix_le_base_actual (F := F) m hD
          (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
          (algebraMap F[X] (RatFunc F) (received i)))
    _ = _ := by simp

/-- A weighted-support dimension surplus gives a primitive interpolant for a received curve. Its
coefficients have challenge degree at most `r * (ℓ * ν) / (card κ - r)`, where `r` is the global
rank bound. Every challenge specialization remains nonzero. -/
theorem exists_primitive_weightedSupport_interpolant [Fintype ι] [Fintype κ]
    (hD : 0 < D) (m ℓ ν : ℕ) (centers : ι → F) (received : ι → F[X])
    (hreceived : ∀ i, (received i).natDegree ≤ ℓ) (columns : κ → SourceColumn d)
    (hcolumns : Function.Injective columns) (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (hmargin : Fintype.card ι * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) <
        Fintype.card κ) :
    let r := Fintype.card ι * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0))
    ∃ v : κ → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ r * (ℓ * ν) / (Fintype.card κ - r)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [CommSemiring E] [Nontrivial E] (ψ : F[X] →+* E),
        MvPolynomial.map ψ (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (received i)
        (SourceColumn.interpolant columns v) := by
  intro r
  apply exists_primitive_interpolant_of_rank_le m ℓ ν centers received hreceived columns
    hcolumns hy₀ (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F))
  · exact localConstraintMatrix_rank_le_weightedSupport hD centers received columns hband
  · exact hmargin

variable {R : Type*} [CommSemiring R] {κ : Type*} [Fintype κ]

/-- An interpolant of eligible source columns lies in the weighted-support space. -/
theorem interpolant_mem_weightedSupportSpace (hD : 0 < D) (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (v : κ → R) :
    SourceColumn.interpolant columns v ∈ weightedSupportSpace R D d W L hD := by
  rw [SourceColumn.interpolant]
  apply Submodule.sum_mem
  intro j _
  rw [mem_weightedSupportSpace_iff]
  intro u hu
  have heq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  simpa only [heq] using hband j

/-- Mapping the challenge coefficients of an interpolant preserves its weighted-support bounds. -/
theorem map_interpolant_mem_weightedSupportSpace {E : Type*} [CommSemiring E]
    (hD : 0 < D) (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : κ → R[X]) (φ : R[X] →+* E) :
    MvPolynomial.map φ (SourceColumn.interpolant columns v) ∈
      weightedSupportSpace E D d W L hD := by
  rw [SourceColumn.map_interpolant]
  exact interpolant_mem_weightedSupportSpace hD columns hband (fun j => φ (v j))

/-- Every monomial of an interpolant in weighted support has total jet degree below `t` when the
support cutoff is at most `D * t`. -/
theorem totalJetDegree_interpolant_le_pred (hD : 0 < D) {t : ℕ}
    (hL : L ≤ (D : ℝ) * t) (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (v : κ → R) :
    ∀ u ∈ (SourceColumn.interpolant columns v).support, totalJetDegree u ≤ t - 1 := by
  have hQ := interpolant_mem_weightedSupportSpace hD columns hband v
  intro u hu
  exact totalJetDegree_le_pred_of_weightedSupportEligible hD hL
    (mem_weightedSupportSpace_iff.mp hQ u hu)

/-- A challenge specialization of an interpolant in weighted support has jet degree below `t`
when the support cutoff is at most `D * t`. -/
theorem jetTotalDegree_map_interpolant_lt {E : Type*} [Field E]
    (hD : 0 < D) {t : ℕ} (ht : 0 < t) (hL : L ≤ (D : ℝ) * t)
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (v : κ → R[X]) (φ : R →+* E) (z : E) :
    jetTotalDegree
      (MvPolynomial.map (Polynomial.eval₂RingHom φ z)
        (SourceColumn.interpolant columns v)) < t :=
  jetTotalDegree_lt_of_mem_weightedSupportSpace ht (by exact_mod_cast hL)
    (map_interpolant_mem_weightedSupportSpace hD columns hband v
      (Polynomial.eval₂RingHom φ z))

/-- The prescribed cutoff `(D : ℝ) * m * (1 + g)` with `g ≤ 1` gives total jet degree at most
`2 * m - 1` for every monomial of the interpolant. -/
theorem totalJetDegree_interpolant_le_two_mul_sub_one {F : Type*} [Field F]
    {d D m W : ℕ} {κ : Type*} [Fintype κ] {g : ℝ} (hD : 0 < D) (hg : g ≤ 1)
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W ((D : ℝ) * m * (1 + g))
      (columns j).exponent) (v : κ → F[X]) :
    ∀ u ∈ (SourceColumn.interpolant columns v).support, totalJetDegree u ≤ 2 * m - 1 := by
  have hDm : 0 ≤ (D : ℝ) * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcut : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m) := by
    calc
      (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hg]) hDm
      _ = (D : ℝ) * (2 * m) := by norm_cast; ring
  exact totalJetDegree_interpolant_le_pred hD (by exact_mod_cast hcut) columns hband v

/-- Every challenge specialization of an interpolant under the prescribed cutoff has total jet
degree at most `2 * m - 1`. -/
theorem jetTotalDegree_map_interpolant_le_two_mul_sub_one {F E : Type*} [Field F] [Field E]
    {d D m W : ℕ} {κ : Type*} [Fintype κ] {g : ℝ} (hD : 0 < D) (hg : g ≤ 1)
    (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W ((D : ℝ) * m * (1 + g))
      (columns j).exponent) (v : κ → F[X]) (ι : F →+* E) (z : E) :
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z)
      (SourceColumn.interpolant columns v)) ≤ 2 * m - 1 := by
  have hDm : 0 ≤ (D : ℝ) * m := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcut : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m) := by
    calc
      (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hg]) hDm
      _ = (D : ℝ) * (2 * m) := by norm_cast; ring
  by_cases hm : m = 0
  · subst m
    have hκ : IsEmpty κ := ⟨fun j => by
      have hlt : (((columns j).exponent none + D *
          totalJetDegree (columns j).exponent : ℕ) : ℝ) < 0 := by
        simpa using (hband j).2
      exact (not_lt_of_ge (Nat.cast_nonneg _) hlt)⟩
    have hzero : SourceColumn.interpolant columns v = 0 := by
      rw [SourceColumn.interpolant]
      apply Finset.sum_eq_zero
      intro j hj
      exact (hκ.false j).elim
    rw [hzero]
    simp [jetTotalDegree, MvPolynomial.weightedTotalDegree]
  · have hlt := jetTotalDegree_map_interpolant_lt (t := 2 * m) hD (by omega)
      (by exact_mod_cast hcut) columns hband v ι z
    exact Nat.le_sub_one_of_lt hlt

end ReedSolomon.HiddenDerivative
