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
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBlocks
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Symbolic interpolation on weighted support and received curves

Every eligible exponent is represented by a source column, so the full weighted support can be
used as the column family of a symbolic interpolant. The local-coordinate matrix of each received
line or polynomial curve is a column submatrix of the canonical weighted-support matrix. Pointwise
rank bounds give a rank bound for the full matrix, and a dimension margin yields a primitive
interpolant with explicit challenge-degree and height bounds.

## Main statements

* `weightedSupportColumns`: a finite enumeration of the weighted-support exponents as source
  columns.
* `localConstraintBlock_eq_weightedSupportSubmatrix` and
  `localConstraintMatrix_rank_le_weightedSupport`: block identification and a rank bound for
  arbitrary received polynomial curves.
* `exists_primitive_weightedSupport_interpolant`: primitive interpolation from a strict dimension
  surplus for arbitrary finite point and column types.
* `interpolant_mem_weightedSupportSpace` and the degree-bound theorems: support and total jet
  degree of an assembled interpolant and its specializations.
* `receivedLine_matrix_rank_le_base_actual`: the full symbolic matrix has rank at most the number
  of points times the actual local rank.
* `exists_symbolic_weightedSupport_interpolant_of_fixed_margin`: a dimension margin yields a
  primitive interpolant on the full support with degree and height bounds.
* `exists_constant_interpolant_of_zero_rank`: zero local rank yields a primitive interpolant with
  constant coefficients.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential
open scoped BigOperators Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ}
variable {ι κ : Type*}

/-- Interpret eligible source columns as indices of the canonical weighted-support matrix. -/
def weightedSupportColumnIndex (hD : 0 < D) {κ : Type*} (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    κ → ↥(weightedSupportExponents D d W L hD) := fun j =>
  ⟨(columns j).exponent, mem_weightedSupportExponents.mpr (hband j)⟩

/-- Enumerate the weighted-support exponents as source columns. -/
def weightedSupportColumns (hD : 0 < D) :
    Fin (Fintype.card (↥(weightedSupportExponents D d W L hD))) → SourceColumn d :=
  fun j => SourceColumn.ofExponent
    (((Fintype.equivFin (↥(weightedSupportExponents D d W L hD))).symm j).1)

/-- The exponent of an enumerated weighted-support column is its enumerated exponent. -/
@[simp]
theorem weightedSupportColumns_exponent (hD : 0 < D)
    (j : Fin (Fintype.card (↥(weightedSupportExponents D d W L hD)))) :
    (weightedSupportColumns (d := d) (W := W) (L := L) hD j).exponent =
      ((Fintype.equivFin (↥(weightedSupportExponents D d W L hD))).symm j).1 := by
  simp [weightedSupportColumns]

/-- Different indices enumerate different weighted-support columns. -/
theorem weightedSupportColumns_injective (hD : 0 < D) :
    Function.Injective (weightedSupportColumns (d := d) (W := W) (L := L) hD) := by
  intro i j hij
  apply (Fintype.equivFin (↥(weightedSupportExponents D d W L hD))).symm.injective
  apply Subtype.ext
  rw [← weightedSupportColumns_exponent hD i, ← weightedSupportColumns_exponent hD j, hij]

/-- Every enumerated weighted-support column is eligible. -/
theorem weightedSupportColumns_eligible (hD : 0 < D)
    (j : Fin (Fintype.card (↥(weightedSupportExponents D d W L hD)))) :
    WeightedSupportEligible D d W L
      (weightedSupportColumns (d := d) (W := W) (L := L) hD j).exponent := by
  rw [weightedSupportColumns_exponent]
  exact mem_weightedSupportExponents.mp
    ((Fintype.equivFin (↥(weightedSupportExponents D d W L hD))).symm j).2

private theorem map_localConstraintCoordinatesAt
    {R E : Type*} [CommRing R] [CommRing E] (φ : R →+* E) (d m : ℕ)
    (center received : R) (Q : DifferentialPolynomial R d) (row : LowContactIndex d m) :
    φ (localConstraintCoordinatesAt m center received Q row) =
      localConstraintCoordinatesAt m (φ center) (φ received) (MvPolynomial.map φ Q) row := by
  unfold localConstraintCoordinatesAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lowContactCoefficients,
    LinearMap.pi_apply, MvPolynomial.lcoeff_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]

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

/-- A mapped received-line point block is a column submatrix of the canonical support matrix over
the rational-function field. -/
theorem receivedLine_block_eq_canonical_submatrix {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (i : Fin n) :
    (fun row j => algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns (i, row) j) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) =
      (weightedSupportLocalCoordinateMatrix (R := RatFunc F) (d := d) (m := m)
        (W := W) (L := L) hD
        (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
        (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i)))).submatrix
          id (weightedSupportColumnIndex hD columns hband) := by
  exact localConstraintBlock_eq_weightedSupportSubmatrix hD centers
    (fun i => receivedLine (f i) (g i)) columns hband i

/-- Every mapped received-line point block has rank at most the source-field actual local rank. -/
theorem receivedLine_block_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (i : Fin n) :
    Matrix.rank (fun row j => algebraMap F[X] (RatFunc F)
      (localConstraintMatrix m (fun i => Polynomial.C (centers i))
        (fun i => receivedLine (f i) (g i)) columns (i, row) j) :
        Matrix (LowContactIndex d m) (Fin N) (RatFunc F)) ≤
      Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  rw [receivedLine_block_eq_canonical_submatrix hD centers f g columns hband i]
  exact (Matrix.rank_submatrix_le _ id (weightedSupportColumnIndex hD columns hband)).trans
    (rank_weightedSupportLocalCoordinateMatrix_le_base_actual (F := F) (d := d) (W := W)
      (L := L) m hD
      (algebraMap F[X] (RatFunc F) (Polynomial.C (centers i)))
      (algebraMap F[X] (RatFunc F) (receivedLine (f i) (g i))))

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
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
      apply Finset.sum_le_sum
      intro i _
      change Matrix.rank (fun row j => algebraMap F[X] (RatFunc F)
        (localConstraintMatrix m (fun j => Polynomial.C (centers j)) received columns
          (i, row) j)) ≤ _
      rw [localConstraintBlock_eq_weightedSupportSubmatrix hD centers received columns hband i]
      exact (Matrix.rank_submatrix_le _ id (weightedSupportColumnIndex hD columns hband)).trans
        (rank_weightedSupportLocalCoordinateMatrix_le_base_actual (F := F) (d := d) (W := W)
          (L := L) m hD
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

/-- The complete mapped symbolic matrix has rank at most `n` times the source-field actual local
rank. -/
theorem receivedLine_matrix_rank_le_base_actual {n N : ℕ}
    (hD : 0 < D) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) :
    ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤
      n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := L) m hD 0 0)) := by
  simpa only [Fintype.card_fin] using
    (localConstraintMatrix_rank_le_weightedSupport (F := F) (d := d) (D := D) (m := m)
      (W := W) (L := L) hD centers (fun i => receivedLine (f i) (g i)) columns hband)

/-- Under the prescribed slack bound, the strict band cutoff gives `Y₀ ≤ 2m - 1`. -/
theorem y₀_le_two_mul_sub_one_of_eligible {g : ℝ} (hD : 0 < D) (hg : g ≤ 1)
    (hm : 0 < m) {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W ((D : ℝ) * m * (1 + g)) u) :
    u (some 0) ≤ 2 * m - 1 := by
  have hcut : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m : ℕ) := by
    have hnonneg : (0 : ℝ) ≤ (D : ℝ) * m := by positivity
    calc
      (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * m * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hnonneg
      _ = (D : ℝ) * (2 * m : ℕ) := by push_cast; ring
  have htotal := totalJetDegree_le_pred_of_weightedSupportEligible
    (D := D) (d := d) (W := W) (L := (D : ℝ) * m * (1 + g)) (t := 2 * m) hD hcut hu
  have hcoord : u (some 0) ≤ totalJetDegree u := by
    rw [totalJetDegree_eq_sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (u (some j))) (Finset.mem_univ 0)
  exact hcoord.trans (by omega)

/-- The strict multiplicative margin bounds the integer kernel height by twelve times the
column-degree bound. -/
theorem kernel_height_lt_twelve_mul_of_margin (N q ν : ℕ) (hν : 0 < ν)
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
  have hf : (((q * ν) / (N - q) : ℕ) : ℝ) ≤
      ((q * ν : ℕ) : ℝ) / (N - q : ℕ) := Nat.cast_div_le
  push_cast at hf
  have he : (q : ℝ) * ν / (N - q : ℕ) = ((q : ℝ) / (N - q : ℕ)) * ν := by ring
  rw [he] at hf
  have hv : (0 : ℝ) < ν := Nat.cast_pos.mpr hν
  exact (hf.trans_lt h).trans (by nlinarith)

/-- A fixed dimension margin yields a primitive symbolic interpolant on the full weighted
support, with an explicit challenge-degree bound, strict height bound, and nonvanishing after every
specialization. -/
theorem exists_symbolic_weightedSupport_interpolant_of_fixed_margin {n ν : ℕ}
    (hD : 0 < D) (hν : 0 < ν) (centers f g : Fin n → F)
    (hy₀ : ∀ u, WeightedSupportEligible D d W L u → u (some 0) ≤ ν)
    (hmargin : (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) <
        Module.finrank F (weightedSupportSpace F D d W L hD)) :
    let N := Fintype.card (↥(weightedSupportExponents D d W L hD))
    let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
        localConstraintMatrix m (fun i => Polynomial.C (centers i))
          (fun i => receivedLine (f i) (g i)) columns *ᵥ v = 0 ∧
          (∀ j, (v j).natDegree ≤ n * Module.finrank F (LinearMap.range
            (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) * ν /
            (N - n * Module.finrank F (LinearMap.range
              (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L)
                m hD 0 0)))) ∧
          (∀ j, ((v j).natDegree : ℝ) < 12 * ν) ∧
          Ideal.span (Set.range v) = ⊤ ∧
          (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
            MvPolynomial.map (Polynomial.eval₂RingHom ι z)
              (SourceColumn.interpolant columns v) ≠ 0) ∧
          (∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
            (receivedLine (f i) (g i)) (SourceColumn.interpolant columns v)) ∧
          ∀ j, WeightedSupportEligible D d W L (columns j).exponent := by
  dsimp only
  let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
  let r₀ := Module.finrank F (LinearMap.range
    (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0))
  let N := Fintype.card (↥(weightedSupportExponents D d W L hD))
  have hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent :=
    weightedSupportColumns_eligible hD
  have hcolumns : Function.Injective columns := weightedSupportColumns_injective hD
  have hy₀' : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    simpa [SourceColumn.exponent_zero] using hy₀ (columns j).exponent (hband j)
  have hdim : Module.finrank F (weightedSupportSpace F D d W L hD) = N := by
    rw [finrank_weightedSupportSpace_eq_card, ← Fintype.card_coe]
  have hmargin' : (543 / 500 : ℝ) * ((n * r₀ : ℕ) : ℝ) < N := by
    rw [← hdim]
    simpa only [r₀, Nat.cast_mul, mul_assoc] using hmargin
  have hN : n * r₀ < N := by
    have hscale : ((n * r₀ : ℕ) : ℝ) ≤
        (543 / 500 : ℝ) * ((n * r₀ : ℕ) : ℝ) := by
      have hnonneg : (0 : ℝ) ≤ ((n * r₀ : ℕ) : ℝ) := by positivity
      nlinarith
    have hltReal : ((n * r₀ : ℕ) : ℝ) < N := hscale.trans_lt hmargin'
    exact_mod_cast hltReal
  have hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map
        (algebraMap F[X] (RatFunc F))).rank ≤ n * r₀ :=
    receivedLine_matrix_rank_le_base_actual hD centers f g columns hband
  obtain ⟨v, hv, hdegree, hprimitive, hnozero, hconstraints⟩ :=
    exists_primitive_receivedLine_interpolant_of_rank_le m ν centers f g columns hcolumns hy₀'
      (algebraMap F[X] (RatFunc F)) (IsFractionRing.injective F[X] (RatFunc F)) hrank
      (by simpa [N] using hN)
  have hdegree' : ∀ j, (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀) := by
    intro j
    simpa [N] using hdegree j
  have hkernel : localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns *ᵥ v = 0 :=
    (localConstraintMatrix_mulVec_eq_zero_iff m _ _ columns v).mpr hconstraints
  have hheight : ∀ j, ((v j).natDegree : ℝ) < 12 * ν := by
    intro j
    have hdegreeReal : ((v j).natDegree : ℝ) ≤
        ((n * r₀ * ν / (N - n * r₀) : ℕ) : ℝ) := by
      exact_mod_cast hdegree' j
    exact hdegreeReal.trans_lt (kernel_height_lt_twelve_mul_of_margin N (n * r₀) ν hν hmargin')
  exact ⟨v, hv, hkernel, hdegree', hheight, hprimitive, fun ι z => hnozero _, hconstraints,
    hband⟩

/-- Zero local rank yields a primitive interpolant whose coefficients are constant polynomials. -/
theorem exists_constant_interpolant_of_zero_rank {n ν : ℕ} (hD : 0 < D) (hν : 0 < ν)
    (centers f g : Fin n → F)
    (hy₀ : ∀ u, WeightedSupportEligible D d W L u → u (some 0) ≤ ν)
    (hrank : Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) = 0)
    (hdim : 0 < Module.finrank F (weightedSupportSpace F D d W L hD)) :
    let N := Fintype.card (↥(weightedSupportExponents D d W L hD))
    let columns := weightedSupportColumns (d := d) (W := W) (L := L) hD
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
        (∀ j, (v j).natDegree = 0) ∧
        Ideal.span (Set.range v) = ⊤ ∧
        (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
          MvPolynomial.map (Polynomial.eval₂RingHom ι z)
            (SourceColumn.interpolant columns v) ≠ 0) ∧
        ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
          (receivedLine (f i) (g i)) (SourceColumn.interpolant columns v) := by
  have hmargin : (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W) (L := L) m hD 0 0)) <
        Module.finrank F (weightedSupportSpace F D d W L hD) := by
    rw [hrank]
    simpa using (show (0 : ℝ) < Module.finrank F (weightedSupportSpace F D d W L hD) by
      exact_mod_cast hdim)
  obtain ⟨v, hv, _, hdegree, _, hprimitive, hnozero, hconstraints, _⟩ :=
    exists_symbolic_weightedSupport_interpolant_of_fixed_margin hD hν centers f g hy₀ hmargin
  refine ⟨v, hv, ?_, hprimitive, hnozero, hconstraints⟩
  intro j
  have h := hdegree j
  simpa [hrank] using h

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
