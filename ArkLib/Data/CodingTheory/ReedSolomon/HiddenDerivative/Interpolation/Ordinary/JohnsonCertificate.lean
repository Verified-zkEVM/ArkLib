/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Johnson.InterpolationBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.LocalImage
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveColumnHeight
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorHeight
/-!
# The finite ordinary Johnson interpolation certificate

This module realizes the exact BCHKS source and row counts as one primitive order-zero equation
for a symbolic received line. Its source support is the strict lattice
`x + D*y < ceil(t*n*sqrt(D/n))`, and its coefficient degree is bounded by the printed `h`.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve

noncomputable section

/-- Exact strict source columns at the Johnson cutoffs. -/
abbrev JohnsonColumnIndex (X D μ : ℕ) :=
  Σ j : Fin (μ + 1), Fin (X - D * j.val)

/-- Triangular local rows, indexed first by error degree and then by the remaining T degree. -/
abbrev JohnsonLocalRowIndex (m : ℕ) :=
  Σ e : Fin m, Fin (m - e.val)

abbrev JohnsonRowIndex (n m : ℕ) := Fin n × JohnsonLocalRowIndex m

/-- Enumerate all strict source columns as the generic symbolic-column type. -/
def johnsonColumns (X D μ : ℕ) :
    Fin (Fintype.card (JohnsonColumnIndex X D μ)) → SourceColumn 0 := fun j ↦
  let q := (Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j
  ⟨q.2.val, q.1.val, Fin.elim0⟩

@[simp] theorem johnsonColumns_y₀ (X D μ : ℕ)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonColumns X D μ j).y₀ =
      ((Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j).1.val := rfl

@[simp] theorem johnsonColumns_x (X D μ : ℕ)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonColumns X D μ j).x =
      ((Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j).2.val := rfl

@[simp] theorem johnsonColumns_totalJetDegree (X D μ : ℕ)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    totalJetDegree (johnsonColumns X D μ j).exponent = (johnsonColumns X D μ j).y₀ := by
  simp

/-- The canonical columns are distinct. -/
theorem johnsonColumns_injective (X D μ : ℕ) : Function.Injective (johnsonColumns X D μ) := by
  intro i j hij
  let e := Fintype.equivFin (JohnsonColumnIndex X D μ)
  have hy : (e.symm i).1 = (e.symm j).1 := by
    apply Fin.ext
    simpa only [e, johnsonColumns_y₀] using congrArg SourceColumn.y₀ hij
  apply e.symm.injective
  apply Sigma.ext hy
  have hbound : X - D * (e.symm i).1.val = X - D * (e.symm j).1.val := by rw [hy]
  apply (Fin.heq_ext_iff hbound).2
  simpa only [e, johnsonColumns_x] using congrArg SourceColumn.x hij

/-- Convert the triangular coordinates into the literal low-contact local exponent. -/
def johnsonLocalRow (m : ℕ) (row : JohnsonLocalRowIndex m) : LowContactIndex 0 m :=
  ⟨zeroLocalExponent (row.1.val + row.2.val) row.1.val, by
    rw [localContactOrder_zero]
    simp [zeroLocalExponent, localT, localE, localAux]
    have := row.2.isLt
    omega⟩

@[simp] theorem johnsonLocalRow_localJetDegree (m : ℕ) (row : JohnsonLocalRowIndex m) :
    localJetDegree (johnsonLocalRow m row).1 = row.1.val := by
  change Finsupp.weight (localJetDegreeWeight (d := 0))
    (zeroLocalExponent (row.1.val + row.2.val) row.1.val) = row.1.val
  rw [zeroLocalExponent, map_add]
  simp [Finsupp.weight_single, localJetDegreeWeight, localT, localE, localAux]

/-- The exact triangular matrix of symbolic local constraints. -/
def johnsonConstraintMatrix {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (JohnsonRowIndex n m) (Fin (Fintype.card (JohnsonColumnIndex X D μ))) F[X] :=
  fun row j ↦ constraintMatrix m centers w (johnsonColumns X D μ)
    (row.1, johnsonLocalRow m row.2) j

/-- Reindex the literal triangular matrix for the polynomial-kernel constructor. -/
def johnsonFinMatrix {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (Fin (Fintype.card (JohnsonRowIndex n m)))
      (Fin (Fintype.card (JohnsonColumnIndex X D μ))) F[X] :=
  (johnsonConstraintMatrix X D μ m centers w).submatrix
    (Fintype.equivFin (JohnsonRowIndex n m)).symm id

/-- Flattened row weight is the local error degree. -/
def johnsonFinRowWeight {n : ℕ} (m : ℕ)
    (i : Fin (Fintype.card (JohnsonRowIndex n m))) : ℕ :=
  ((Fintype.equivFin (JohnsonRowIndex n m)).symm i).2.1.val

/-- The dependent source index has the exact staircase cardinality. -/
theorem card_johnsonColumnIndex (X D μ : ℕ) :
    Fintype.card (JohnsonColumnIndex X D μ) =
      ∑ j ∈ Finset.range (μ + 1), (X - D * j) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j ↦ X - D * j) (μ + 1)

/-- Enumerating the columns preserves their exact shifted scalar-slot count. -/
theorem sum_johnsonColumns_slots (X D μ h : ℕ) :
    Finset.univ.sum (fun j : Fin (Fintype.card (JohnsonColumnIndex X D μ)) ↦
      h + 1 - (johnsonColumns X D μ j).y₀) = johnsonSourceSlotCount X D μ h := by
  let e := Fintype.equivFin (JohnsonColumnIndex X D μ)
  calc
    _ = Finset.univ.sum (fun q : JohnsonColumnIndex X D μ ↦ h + 1 - q.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro q _
      simp [e, johnsonColumns]
    _ = Finset.univ.sum (fun j : Fin (μ + 1) ↦
        (X - D * j.val) * (h + 1 - j.val)) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      simp
    _ = johnsonSourceSlotCount X D μ h := by
      rw [johnsonSourceSlotCount, ← Fin.sum_univ_eq_sum_range]

/-- Enumerating the triangular rows preserves the exact multiplicity-row slot count. -/
theorem sum_johnsonFinRowWeight_slots {n : ℕ} (m h : ℕ) :
    Finset.univ.sum (fun i : Fin (Fintype.card (JohnsonRowIndex n m)) ↦
      h + 1 - johnsonFinRowWeight m i) = johnsonRowSlotCount n m h := by
  let e := Fintype.equivFin (JohnsonRowIndex n m)
  calc
    _ = Finset.univ.sum (fun row : JohnsonRowIndex n m ↦ h + 1 - row.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro row _
      simp [e, johnsonFinRowWeight]
    _ = n * Finset.univ.sum (fun q : JohnsonLocalRowIndex m ↦ h + 1 - q.1.val) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = n * Finset.univ.sum (fun q : Fin m ↦
        (m - q.val) * (h + 1 - q.val)) := by
      congr 1
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      simp
    _ = johnsonRowSlotCount n m h := by
      rw [johnsonRowSlotCount, ← Fin.sum_univ_eq_sum_range]

private theorem exists_johnsonLocalRow_of_triangular {m : ℕ} (row : LowContactIndex 0 m)
    (htri : row.1 (localE 0) ≤ row.1 (localT 0)) :
    ∃ q : JohnsonLocalRowIndex m, johnsonLocalRow m q = row := by
  have hT : row.1 (localT 0) < m := by
    simpa only [localContactOrder_zero] using row.2
  have hE : row.1 (localE 0) < m := htri.trans_lt hT
  have hrem : row.1 (localT 0) - row.1 (localE 0) <
      m - row.1 (localE 0) := by
    apply Nat.lt_sub_iff_add_lt.mpr
    omega
  let q : JohnsonLocalRowIndex m :=
    ⟨⟨row.1 (localE 0), hE⟩,
      ⟨row.1 (localT 0) - row.1 (localE 0), hrem⟩⟩
  refine ⟨q, Subtype.ext ?_⟩
  change zeroLocalExponent
      (row.1 (localE 0) + (row.1 (localT 0) - row.1 (localE 0)))
      (row.1 (localE 0)) = row.1
  rw [Nat.add_sub_of_le htri, zeroLocalExponent_reconstruct]

/-- The triangular rows detect exactly the complete order-zero local constraint system. -/
theorem johnsonConstraintMatrix_kernel_iff {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card (JohnsonColumnIndex X D μ)) → F[X]) :
    johnsonConstraintMatrix X D μ m centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i)
        (interpolant (johnsonColumns X D μ) v) := by
  classical
  rw [← constraintMatrix_kernel_iff m centers w (johnsonColumns X D μ) v]
  constructor
  · intro hselected
    funext row
    by_cases htri : row.2.1 (localE 0) ≤ row.2.1 (localT 0)
    · obtain ⟨q, hq⟩ := exists_johnsonLocalRow_of_triangular row.2 htri
      have hrow := congrFun hselected (row.1, q)
      simpa [johnsonConstraintMatrix, Matrix.mulVec, dotProduct, hq] using hrow
    · rw [Matrix.mulVec]
      apply Finset.sum_eq_zero
      intro j _
      have hz : constraintMatrix m centers w (johnsonColumns X D μ) row j = 0 := by
        by_contra hne
        have hsupp : row.2.1 ∈
            (unscaledLocalSubstitution 0 (C (centers row.1)) (w row.1)
              (johnsonColumns X D μ j).polynomial).support := by
          rw [MvPolynomial.mem_support_iff]
          simpa [constraintMatrix, localConstraintCoordinatesAt, lowContactCoefficients] using hne
        exact htri (unscaled_zero_support (C (centers row.1)) (w row.1)
          (johnsonColumns X D μ j).polynomial row.2.1 hsupp)
      simp [hz]
  · intro hfull
    have hmatrix := (constraintMatrix_kernel_iff m centers w
      (johnsonColumns X D μ) v).mpr
      ((constraintMatrix_kernel_iff m centers w (johnsonColumns X D μ) v).mp hfull)
    funext row
    have hrow := congrFun hmatrix (row.1, johnsonLocalRow m row.2)
    simpa [johnsonConstraintMatrix, Matrix.mulVec, dotProduct] using hrow

/-- Flattening the triangular rows preserves the exact kernel. -/
theorem johnsonFinMatrix_kernel_iff {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card (JohnsonColumnIndex X D μ)) → F[X]) :
    johnsonFinMatrix X D μ m centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i)
        (interpolant (johnsonColumns X D μ) v) := by
  rw [← johnsonConstraintMatrix_kernel_iff X D μ m centers w v]
  constructor
  · intro h
    funext row
    have hi := congrFun h ((Fintype.equivFin (JohnsonRowIndex n m)) row)
    simpa [johnsonFinMatrix, Matrix.mulVec, dotProduct] using hi
  · intro h
    funext i
    exact congrFun h ((Fintype.equivFin (JohnsonRowIndex n m)).symm i)

/-- Every triangular matrix entry has the exact shifted challenge-degree bound. -/
theorem johnsonConstraintMatrix_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1) (row : JohnsonRowIndex n m)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonConstraintMatrix X D μ m centers w row j).natDegree ≤
      (johnsonColumns X D μ j).y₀ - row.2.1.val := by
  have h := constraintMatrix_degree_le_grade_shift m 1 centers w hw
    (johnsonColumns X D μ) (row.1, johnsonLocalRow m row.2) j
  simpa [johnsonConstraintMatrix, johnsonLocalRow_localJetDegree] using h

/-- Rows above a source column's jet grade vanish identically. -/
theorem johnsonConstraintMatrix_eq_zero_of_grade_lt {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1) (row : JohnsonRowIndex n m)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (hgrade : (johnsonColumns X D μ j).y₀ < row.2.1.val) :
    johnsonConstraintMatrix X D μ m centers w row j = 0 := by
  apply constraintMatrix_eq_zero_of_source_grade_lt_row_grade m 1 centers w hw
  simpa [johnsonLocalRow_localJetDegree] using hgrade

/-- Flattened entries satisfy the shifted degree premise. -/
theorem johnsonFinMatrix_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (_hweight : johnsonFinRowWeight m i ≤ (johnsonColumns X D μ j).y₀) :
    (johnsonFinMatrix X D μ m centers w i j).natDegree ≤
      (johnsonColumns X D μ j).y₀ - johnsonFinRowWeight m i := by
  exact johnsonConstraintMatrix_degree_le X D μ m centers w hw _ j

/-- Flattened rows above the source grade vanish. -/
theorem johnsonFinMatrix_eq_zero_of_grade_lt {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (hgrade : (johnsonColumns X D μ j).y₀ < johnsonFinRowWeight m i) :
    johnsonFinMatrix X D μ m centers w i j = 0 := by
  exact johnsonConstraintMatrix_eq_zero_of_grade_lt X D μ m centers w hw _ j hgrade

/-! ### The packaged ordinary Johnson certificate -/

variable {F : Type*} [Field F]

/-- A primitive order-zero equation with the literal BCHKS strict support and its
extension-field agreement implication. -/
structure JohnsonSymbolicCertificate {n : ℕ} (D A m μ k h Xc : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) where
  coefficients : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]
  Q : DifferentialPolynomial F[X] 0
  eq_interpolant : Q = interpolant (johnsonColumns Xc D μ) coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
  support : ∀ u ∈ Q.support, WeightedSupportEligible D 0 0 (Xc : ℝ) u
  jetDegree_le : jetDegree Q (0 : Fin 1) ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
    (receivedLine (f i) (g i)) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Uniform coefficient bounds on the canonical Johnson interpolant. -/
theorem coeff_johnsonInterpolant_natDegree_le {Xc D μ h : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X])
    (hv : ∀ j, (v j).natDegree ≤ h) :
    ∀ u, (MvPolynomial.coeff u (interpolant (johnsonColumns Xc D μ) v)).natDegree ≤ h := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (johnsonColumns Xc D μ j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [coeff_interpolant _ (johnsonColumns_injective Xc D μ) v j]
    exact hv j
  · have hcoeff : MvPolynomial.coeff u (interpolant (johnsonColumns Xc D μ) v) = 0 := by
      rw [interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    simp [hcoeff]

/-- Every supported exponent of the canonical interpolant comes from a source column. -/
theorem support_johnsonInterpolant_subset_range {Xc D μ : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X])
    {u : JetVariable 0 →₀ ℕ}
    (hu : u ∈ (interpolant (johnsonColumns Xc D μ) v).support) :
    u ∈ Set.range (fun j ↦ (johnsonColumns Xc D μ j).exponent) := by
  classical
  by_contra hn
  have hcoeff : MvPolynomial.coeff u (interpolant (johnsonColumns Xc D μ) v) = 0 := by
    rw [interpolant, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [MvPolynomial.coeff_monomial]
    split
    · rename_i heq
      exact (hn ⟨j, heq⟩).elim
    · rfl
  exact MvPolynomial.mem_support_iff.mp hu hcoeff

/-- Every strict Johnson source column satisfies the weighted-support predicate. -/
theorem johnsonColumns_weightedSupportEligible {Xc D μ : ℕ}
    (j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ))) :
    WeightedSupportEligible D 0 0 (Xc : ℝ) (johnsonColumns Xc D μ j).exponent := by
  let q := (Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j
  have hq := q.2.isLt
  have hstrict : q.2.val + D * q.1.val < Xc := by omega
  constructor
  · simp [fullHigherJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype]
  · norm_cast
    simpa [q, johnsonColumns, SourceColumn.totalJetDegree_exponent] using hstrict

/-- A canonical Johnson interpolant belongs to its strict weighted-support space. -/
theorem interpolant_mem_johnsonWeightedSupport {Xc D μ : ℕ} (hD : 0 < D)
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]) :
    interpolant (johnsonColumns Xc D μ) v ∈
      weightedSupportSpace F[X] D 0 0 (Xc : ℝ) hD := by
  rw [interpolant]
  apply Submodule.sum_mem
  intro j _
  rw [mem_weightedSupportSpace_iff]
  intro u hu
  have hueq : u = (johnsonColumns Xc D μ j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  subst u
  exact johnsonColumns_weightedSupportEligible j

/-- The canonical Johnson interpolant has jet degree at most its slice cutoff. -/
theorem johnsonInterpolant_jetDegree_le {Xc D μ : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]) :
    jetDegree (interpolant (johnsonColumns Xc D μ) v) (0 : Fin 1) ≤ μ := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro u hu
  obtain ⟨j, rfl⟩ := support_johnsonInterpolant_subset_range v hu
  have hj := ((Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j).1.isLt
  simpa [SourceColumn.exponent] using Nat.le_of_lt_succ hj

/-- The literal Johnson recipe constructs the primitive ordinary symbolic certificate.
The assumptions are precisely its physical rate, agreement, and code-degree guards; no
dimension, rank, kernel, or desired interpolation conclusion is supplied by the caller. -/
theorem exists_johnson_symbolic_certificate
    {n D A k : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (_hagreement : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (_hAn : A ≤ n)
    (hkD : k ≤ D + 1) (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (JohnsonSymbolicCertificate (F := F) D A (johnsonM n D eta)
      (johnsonMu n D eta) k (johnsonH n D eta) (johnsonXCutoff n D eta)
      centers f g) := by
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let Xc := johnsonXCutoff n D eta
  let columns := johnsonColumns Xc D μ
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  have hcut : Xc ≤ m * A := by
    simpa only [Xc, m] using johnsonXCutoff_le_mul_agreement hD hDn heta hthreshold
  have hbudget : 0 < m * A := by
    have hDA := johnson_degree_succ_le_agreement hD hDn heta hthreshold
    have hm := johnsonM_ge_three n D eta
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    SymbolicReceivedCurve.exists_primitive_interpolant_of_shifted_height
      m 1 h (fun i ↦ centers i) w columns (johnsonColumns_injective Xc D μ)
      (johnsonFinMatrix Xc D μ m (fun i ↦ centers i) w)
      (johnsonFinRowWeight m)
      (johnsonFinMatrix_kernel_iff Xc D μ m (fun i ↦ centers i) w)
      (by
        intro i j hweight
        have hh := johnsonFinMatrix_degree_le Xc D μ m (fun i ↦ centers i) w
          (fun i ↦ receivedLine_natDegree_le (f i) (g i)) i j (by
            simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hweight)
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hh)
      (by
        intro i j hweight
        apply johnsonFinMatrix_eq_zero_of_grade_lt Xc D μ m (fun i ↦ centers i) w
          (fun i ↦ receivedLine_natDegree_le (f i) (g i)) i j
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hweight) (by
          rw [sum_johnsonFinRowWeight_slots]
          simpa only [columns, one_mul, johnsonColumns_totalJetDegree,
            sum_johnsonColumns_slots, m, μ, h, Xc] using
              johnson_interpolation_slot_surplus hD hDn)
  let Q : DifferentialPolynomial F[X] 0 := interpolant columns v
  have hvheight : ∀ j, (v j).natDegree ≤ h := by
    intro j
    by_cases hz : v j = 0
    · simp [hz]
    · have hlt : (v j).natDegree < h + 1 - (columns j).y₀ := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using
          Polynomial.mem_degreeLT.mp (hvdegree j)
      omega
  have hQsupport : Q ∈ weightedSupportSpace F[X] D 0 0 (Xc : ℝ) hDpos := by
    exact interpolant_mem_johnsonWeightedSupport hDpos v
  refine ⟨{
    coefficients := v
    Q := Q
    eq_interpolant := rfl
    primitiveCoefficients := hprimitive
    challengeDegree_le := coeff_johnsonInterpolant_natDegree_le v hvheight
    support := fun u hu ↦ mem_weightedSupportSpace_iff.mp hQsupport u hu
    jetDegree_le := johnsonInterpolant_jetDegree_le v
    localConstraints := hconstraints
    specialization_sound := ?_ }⟩
  intro E _ ι z
  refine ⟨hnonzero ι z, ?_⟩
  intro indices P hPdegree hcard hagreements
  apply differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
    hDpos (by exact_mod_cast hcut) hbudget hkD (fun i ↦ centers i) f g columns
    (fun j ↦ johnsonColumns_weightedSupportEligible j) v hconstraints ι z indices P
    hPdegree centers.injective.injOn hcard hagreements

end
end ReedSolomon.HiddenDerivative
