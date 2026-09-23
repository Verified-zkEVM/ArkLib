/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.LocalRank
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Symbolic interpolation on weighted support

A strict surplus between the weighted-support dimension and the total rank of local constraints
produces a primitive symbolic interpolant. Its coefficients generate the unit ideal, so every
challenge specialization remains nonzero. The source monomials lie in the canonical weighted
support, and the interpolant satisfies the received-line constraints as polynomials.

## Main statements

* `WeightedSupportIndex` and `weightedSupportColumns`: the finite set of eligible support
  exponents and its enumeration by symbolic columns.
* `weightedSupportColumns_exponent`: each column has the exponent of its enumerated index.
* `y₀_le_two_mul_sub_one_of_eligible`: the prescribed cutoff bounds the first jet exponent.
* `exists_symbolic_weightedSupport_interpolant_of_fixed_margin`: a primitive interpolant from a
  strict dimension margin, with kernel, degree, height, and specialization guarantees.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]
variable {d D m W : ℕ} {L : ℝ}

/-- The finite type of exponents in the weighted-support space. -/
abbrev WeightedSupportIndex (D d W : ℕ) (L : ℝ) (hD : 0 < D) :=
  ↥(weightedSupportExponents D d W L hD)

namespace SymbolicWeightedSupportInterpolation

/-- One block of a matrix whose rows are indexed by a product. -/
private def Matrix.rowBlock {K : Type*} {ι ρ κ : Type*}
    (A : Matrix (ι × ρ) κ K) (i : ι) : Matrix ρ κ K :=
  fun row column => A (i, row) column

/-- A matrix with a finite product row type has rank at most the sum of its block ranks. -/
private theorem Matrix.rank_prod_rows_le_sum
    {K : Type*} [Field K] {ι ρ κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix (ι × ρ) κ K) :
    A.rank ≤ ∑ i, (Matrix.rowBlock A i).rank := by
  let Φ := A.mulVecLin
  let block : ι → Matrix ρ κ K := Matrix.rowBlock A
  let φ := fun i => (block i).mulVecLin
  let includeRange : Φ.range →ₗ[K] (∀ i, (φ i).range) := {
    toFun y i := ⟨(fun row => y.1 (i, row)), by
      rcases y.2 with ⟨v, hv⟩
      refine ⟨v, ?_⟩
      ext row
      simpa [Φ, φ, block, Matrix.rowBlock, Matrix.mulVecLin_apply, Matrix.mulVec] using
        congrFun hv (i, row)⟩
    map_add' x y := by
      ext i row
      rfl
    map_smul' a x := by
      ext i row
      rfl
  }
  have hinjective : Function.Injective includeRange := by
    intro x y hxy
    apply Subtype.ext
    funext row
    have hi := congrArg Subtype.val (congrFun hxy row.1)
    exact congrFun hi row.2
  change Module.finrank K A.mulVecLin.range ≤ _
  calc
    Module.finrank K Φ.range ≤ Module.finrank K (∀ i, (φ i).range) :=
      LinearMap.finrank_le_finrank_of_injective hinjective
    _ = ∑ i, Module.finrank K (φ i).range := Module.finrank_pi_fintype K
    _ = ∑ i, (Matrix.rowBlock A i).rank := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show φ i = (Matrix.rowBlock A i).mulVecLin by rfl]
      rfl

/-- Interpret an eligible symbolic column as an index of the canonical support matrix. -/
private def weightedSupportColumnIndex {N : ℕ} (hD : 0 < D)
    (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (j : Fin N) : WeightedSupportIndex D d W L hD :=
  ⟨(columns j).exponent, mem_weightedSupportExponents.mpr (hband j)⟩

private theorem localConstraintCoordinatesAt_monomial_map
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E)
    (center received : R) (u : JetVariable d →₀ ℕ) (row : LowContactIndex d m) :
    φ (localConstraintCoordinatesAt m center received (MvPolynomial.monomial u 1) row) =
      localConstraintCoordinatesAt m (φ center) (φ received)
        (MvPolynomial.monomial u 1) row := by
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map]
  simpa only [MvPolynomial.map_monomial, map_one] using
    congrArg (fun P : LocalPolynomial E d => P.coeff row.1)
      (ReedSolomon.HiddenDerivative.map_unscaledLocalSubstitution φ center received
        (MvPolynomial.monomial u 1))

/-- One mapped received-line point block is a column submatrix of the canonical support matrix
over the rational-function field. -/
private theorem receivedLine_block_eq_canonical_submatrix {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (i : Fin n) :
    (fun row j => algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns (i, row) j) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) =
      (weightedSupportLocalCoordinateMatrix (R := RatFunc F) (d := d) (m := m)
        (W := W) (L := L) hD
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i)))).submatrix
          id (weightedSupportColumnIndex hD columns hband) := by
  ext row j
  rw [Matrix.submatrix_apply, id_eq]
  simp only [localConstraintMatrix, weightedSupportLocalCoordinateMatrix_apply,
    weightedSupportColumnIndex, SourceColumn.polynomial]
  exact localConstraintCoordinatesAt_monomial_map
    (algebraMap F[X] (RatFunc F)) (Polynomial.C (centers i))
      (receivedLine (f i) (g i)) (columns j).exponent row

/-- Every mapped received-line point block has rank at most the source-field actual local rank. -/
private theorem receivedLine_block_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent)
    (i : Fin n) :
    Matrix.rank ((fun row j => algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns (i, row) j)) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  rw [receivedLine_block_eq_canonical_submatrix hD centers f g columns hband i]
  exact (Matrix.rank_submatrix_le _ id (weightedSupportColumnIndex hD columns hband)).trans
    (rank_weightedSupportLocalCoordinateMatrix_le_base_actual
      (F := F) m hD
      (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
      (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i))))

/-- The complete mapped symbolic matrix has rank at most `n` times the source-field actual local
rank. -/
private theorem receivedLine_matrix_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤
      n * Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  let A := (localConstraintMatrix m (fun i => Polynomial.C (centers i))
    (fun i => receivedLine (f i) (g i)) columns).map (algebraMap F[X] (RatFunc F))
  calc
    A.rank ≤ ∑ i, (Matrix.rowBlock A i).rank :=
      Matrix.rank_prod_rows_le_sum A
    _ ≤ ∑ _ : Fin n, Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
      apply Finset.sum_le_sum
      intro i _
      exact receivedLine_block_rank_le_base_actual hD centers f g columns hband i
    _ = _ := by simp

/-- Recover symbolic source coordinates from an exponent of the differential polynomial. -/
def SourceColumn.ofExponent (u : JetVariable d →₀ ℕ) : SourceColumn d where
  x := u none
  y₀ := u (some 0)
  higher j := u (some j.succ)

/-- The exponent of the source column reconstructed from `u` is `u`. -/
@[simp]
private theorem SourceColumn.exponent_ofExponent (u : JetVariable d →₀ ℕ) :
    (SourceColumn.ofExponent u).exponent = u := by
  ext v
  rcases v with _ | j
  · simp [SourceColumn.ofExponent, SourceColumn.exponent]
  · induction j using Fin.cases with
    | zero => simp [SourceColumn.ofExponent, SourceColumn.exponent]
    | succ j =>
      rw [SourceColumn.exponent_succ]
      simp [SourceColumn.ofExponent]

/-- Enumerate every weighted-support exponent as a symbolic source column. -/
def weightedSupportColumns (hD : 0 < D) :
    Fin (Fintype.card (WeightedSupportIndex D d W L hD)) → SourceColumn d :=
  fun j => SourceColumn.ofExponent
    (((Fintype.equivFin (WeightedSupportIndex D d W L hD)).symm j).1)

/-- The exponent of each enumerated column is its weighted-support index. -/
@[simp]
theorem weightedSupportColumns_exponent (hD : 0 < D)
    (j : Fin (Fintype.card (WeightedSupportIndex D d W L hD))) :
    (weightedSupportColumns (d := d) (W := W) (L := L) hD j).exponent =
      ((Fintype.equivFin (WeightedSupportIndex D d W L hD)).symm j).1 := by
  simp [weightedSupportColumns]

private theorem weightedSupportColumns_injective (hD : 0 < D) :
    Function.Injective (weightedSupportColumns (d := d) (W := W) (L := L) hD) := by
  intro i j hij
  apply (Fintype.equivFin (WeightedSupportIndex D d W L hD)).symm.injective
  apply Subtype.ext
  rw [← weightedSupportColumns_exponent hD i,
    ← weightedSupportColumns_exponent hD j, hij]

private theorem weightedSupportColumns_eligible (hD : 0 < D)
    (j : Fin (Fintype.card (WeightedSupportIndex D d W L hD))) :
    WeightedSupportEligible D d W L
      (weightedSupportColumns (d := d) (W := W) (L := L) hD j).exponent := by
  rw [weightedSupportColumns_exponent]
  exact mem_weightedSupportExponents.mp
    ((Fintype.equivFin (WeightedSupportIndex D d W L hD)).symm j).2

/-- Under the prescribed cutoff, eligibility bounds the exponent of `Y₀` by `2 * m - 1`. -/
theorem y₀_le_two_mul_sub_one_of_eligible {g : ℝ}
    (hD : 0 < D) (hg : g ≤ 1) (hm : 0 < m)
    {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W ((D : ℝ) * m * (1 + g)) u) :
    u (some 0) ≤ 2 * m - 1 := by
  have hcoord : u (some 0) ≤ totalJetDegree u := by
    rw [totalJetDegree_eq_degree_some]
    exact Finsupp.le_degree 0 u.some
  have hDReal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcut := hu.2
  push_cast at hcut
  have hL : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m) := by
    have hnonneg : (0 : ℝ) ≤ (D : ℝ) * m := by positivity
    calc
      (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) hnonneg
      _ = (D : ℝ) * (2 * m) := by ring
  have htotalReal : (totalJetDegree u : ℝ) < 2 * m := by
    have hx : (0 : ℝ) ≤ u none := Nat.cast_nonneg _
    have hmul : (D : ℝ) * totalJetDegree u < (D : ℝ) * (2 * m) :=
      (le_add_of_nonneg_left hx).trans_lt (hcut.trans_le hL)
    exact lt_of_mul_lt_mul_left hmul hDReal.le
  have htotal : totalJetDegree u < 2 * m := by exact_mod_cast htotalReal
  omega

/-- The fixed dimension margin bounds the polynomial height in the primitive kernel construction.
-/
private theorem noBand_kernel_height_lt (N q ν : ℕ) (hν : 0 < ν)
    (hmargin : (543 / 500 : ℝ) * q < N) :
    ((q * ν / (N - q) : ℕ) : ℝ) < 12 * ν := by
  have hqN : q < N := by
    have hq : (q : ℝ) < N := by nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
    exact_mod_cast hq
  have hden : (0 : ℝ) < (N - q : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hqN
  have hcast : ((N - q : ℕ) : ℝ) = (N : ℝ) - q := Nat.cast_sub hqN.le
  have hr : (q : ℝ) / ((N - q : ℕ) : ℝ) < 500 / 43 := by
    rw [div_lt_iff₀ hden, hcast]
    linarith
  have h := mul_lt_mul_of_pos_right hr (Nat.cast_pos.mpr hν)
  have hf : (((q * ν) / (N - q) : ℕ) : ℝ) ≤ ((q * ν : ℕ) : ℝ) / (N - q : ℕ) :=
    Nat.cast_div_le
  push_cast at hf
  have he : (q : ℝ) * ν / (N - q : ℕ) = ((q : ℝ) / (N - q : ℕ)) * ν := by ring
  rw [he] at hf
  have hv : (0 : ℝ) < ν := Nat.cast_pos.mpr hν
  exact (hf.trans_lt h).trans (by nlinarith)

/-- A strict dimension margin produces a primitive symbolic interpolant supported on the weighted
support space. Its coefficient degrees satisfy the rank bound and are below `12 * ν`; every
challenge specialization is nonzero, and the interpolant satisfies all received-line constraints.
-/
theorem exists_symbolic_weightedSupport_interpolant_of_fixed_margin {n ν : ℕ}
    (hD : 0 < D) (hν : 0 < ν) (centers f g : Fin n → F)
    (hy₀ : ∀ u, WeightedSupportEligible D d W L u → u (some 0) ≤ ν)
    (hmargin : (543 / 500 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W L hD)) :
    let N := Fintype.card (WeightedSupportIndex D d W L hD)
    let r₀ := Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := L) m hD 0 0))
    let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
        Matrix.mulVec
            (localConstraintMatrix m (fun i => Polynomial.C (centers i))
              (fun i => receivedLine (f i) (g i)) columns) v = 0 ∧
          (∀ j, (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀)) ∧
            (∀ j, ((v j).natDegree : ℝ) < 12 * ν) ∧
              Ideal.span (Set.range v) = ⊤ ∧
                (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
                  MvPolynomial.map (Polynomial.eval₂RingHom ι z)
                    (SourceColumn.interpolant columns v) ≠ 0) ∧
                  (∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
                    (receivedLine (f i) (g i)) (SourceColumn.interpolant columns v)) ∧
                    ∀ j, WeightedSupportEligible D d W L
                      (columns j).exponent := by
  dsimp only
  let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
  let r₀ := Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
      (L := L) m hD 0 0))
  let N := Fintype.card (WeightedSupportIndex D d W L hD)
  have hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent :=
    weightedSupportColumns_eligible hD
  have hcolumns : Function.Injective columns := weightedSupportColumns_injective hD
  have hy₀' : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    simpa [SourceColumn.exponent] using hy₀ (columns j).exponent (hband j)
  have hdim : Module.finrank F (weightedSupportSpace F D d W L hD) = N := by
    rw [finrank_weightedSupportSpace_eq_card hD, ← Fintype.card_coe]
  have hmargin' : (543 / 500 : ℝ) * ((n * r₀ : ℕ) : ℝ) < N := by
    rw [← hdim]
    simpa only [r₀, Nat.cast_mul, mul_assoc] using hmargin
  have hN : n * r₀ < N := by
    have hscale : ((n * r₀ : ℕ) : ℝ) ≤
        (543 / 500 : ℝ) * ((n * r₀ : ℕ) : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ ((n * r₀ : ℕ) : ℝ) := by positivity
      nlinarith
    have hltReal : ((n * r₀ : ℕ) : ℝ) < (N : ℝ) := hscale.trans_lt hmargin'
    exact_mod_cast hltReal
  have hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * r₀ :=
    receivedLine_matrix_rank_le_base_actual hD centers f g columns hband
  have hN' : n * r₀ < Fintype.card (Fin N) := by simpa using hN
  obtain ⟨v, hv, hdegree, hprimitive, hnozero, hconstraints⟩ :=
    ReedSolomon.HiddenDerivative.exists_primitive_receivedLine_interpolant_of_rank_le
      m ν centers f g columns hcolumns hy₀' (algebraMap F[X] (RatFunc F))
      (RatFunc.algebraMap_injective F) (s := n * r₀) hrank hN'
  have hkernel : Matrix.mulVec
      (localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns) v = 0 :=
    (localConstraintMatrix_mulVec_eq_zero_iff m _ _ columns v).mpr hconstraints
  have hdegree' : ∀ j, (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀) := by
    simpa only [Fintype.card_fin] using hdegree
  have hheight : ∀ j, ((v j).natDegree : ℝ) < 12 * ν := by
    intro j
    have hdegreeReal : ((v j).natDegree : ℝ) ≤
        ((n * r₀ * ν / (N - n * r₀) : ℕ) : ℝ) := by
      exact_mod_cast hdegree' j
    exact hdegreeReal.trans_lt (noBand_kernel_height_lt N (n * r₀) ν hν hmargin')
  have hdegree'' : ∀ j, (v j).natDegree ≤
      n * Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) * ν /
      (Fintype.card (WeightedSupportIndex D d W L hD) - n *
        Module.finrank F (LinearMap.range
          (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
            (L := L) m hD 0 0))) := by
    simpa only [r₀, N] using hdegree'
  refine ⟨v, hv, hkernel, hdegree'', hheight, hprimitive,
    fun {E} [Field E] ι z => ?_, hconstraints, hband⟩
  simpa only [columns] using
    hnozero (S := E) (show F[X] →+* E from Polynomial.eval₂RingHom ι z)

end SymbolicWeightedSupportInterpolation

end ReedSolomon.HiddenDerivative
