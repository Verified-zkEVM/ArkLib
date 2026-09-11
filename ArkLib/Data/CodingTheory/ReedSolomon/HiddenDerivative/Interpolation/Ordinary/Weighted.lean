/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Ordinary.JohnsonCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.Johnson.WeightedCertificate

/-!
# The optimized finite ordinary Johnson interpolation certificate

The printed Johnson certificate uses the exact source staircase
`i + D * j < m * A`, with `0 ≤ j ≤ B`. A local row of error grade `b > B`
is identically zero on this source. We therefore retain only the grades
`0 ≤ b ≤ min B (m - 1)`. This is the finite row truncation responsible for the
optimized table constants; it changes neither the complete multiplicity system nor
the resulting extension-field recovery statement.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve

noncomputable section

/-- The nonzero triangular local rows after deleting error grades above `B`. -/
abbrev WeightedJohnsonLocalRowIndex (m B : ℕ) :=
  Σ b : Fin (min B (m - 1) + 1), Fin (m - b.val)

abbrev WeightedJohnsonRowIndex (n m B : ℕ) := Fin n × WeightedJohnsonLocalRowIndex m B

/-- Forget that a retained row has error grade at most `B`. -/
def weightedJohnsonLocalRowIndexToJohnson {m B : ℕ}
    (row : WeightedJohnsonLocalRowIndex m B) : JohnsonLocalRowIndex m :=
  ⟨⟨row.1.val, by
      have hpos : 0 < m - row.1.val :=
        lt_of_le_of_lt (Nat.zero_le row.2.val) row.2.isLt
      omega⟩, row.2⟩

@[simp] theorem weightedJohnsonLocalRowIndexToJohnson_errorGrade {m B : ℕ}
    (row : WeightedJohnsonLocalRowIndex m B) :
    (weightedJohnsonLocalRowIndexToJohnson row).1.val = row.1.val := rfl

/-- The exact constraint matrix after removing rows which vanish on every source column. -/
def weightedJohnsonConstraintMatrix {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (WeightedJohnsonRowIndex n m B)
      (Fin (Fintype.card (JohnsonColumnIndex X D B))) F[X] :=
  fun row j ↦ johnsonConstraintMatrix X D B m centers w
    (row.1, weightedJohnsonLocalRowIndexToJohnson row.2) j

/-- Reindex the optimized matrix for the shifted polynomial-kernel constructor. -/
def weightedJohnsonFinMatrix {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
    Matrix (Fin (Fintype.card (WeightedJohnsonRowIndex n m B)))
      (Fin (Fintype.card (JohnsonColumnIndex X D B))) F[X] :=
  (weightedJohnsonConstraintMatrix X D B m centers w).submatrix
    (Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm id

/-- A retained row is weighted by its local error grade. -/
def weightedJohnsonFinRowWeight {n : ℕ} (m B : ℕ)
    (i : Fin (Fintype.card (WeightedJohnsonRowIndex n m B))) : ℕ :=
  ((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i).2.1.val

/-- The optimized rows have the exact scalar-slot count printed in the paper. -/
theorem sum_weightedJohnsonFinRowWeight_slots {n : ℕ} (m B h : ℕ) :
    Finset.univ.sum
        (fun i : Fin (Fintype.card (WeightedJohnsonRowIndex n m B)) ↦
          h + 1 - weightedJohnsonFinRowWeight m B i) =
      n * ∑ b ∈ Finset.range (min B (m - 1) + 1),
        (m - b) * (h + 1 - b) := by
  let e := Fintype.equivFin (WeightedJohnsonRowIndex n m B)
  calc
    _ = Finset.univ.sum
        (fun row : WeightedJohnsonRowIndex n m B ↦ h + 1 - row.2.1.val) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro row _
      simp [e, weightedJohnsonFinRowWeight]
    _ = n * Finset.univ.sum
        (fun q : WeightedJohnsonLocalRowIndex m B ↦ h + 1 - q.1.val) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = n * Finset.univ.sum
        (fun b : Fin (min B (m - 1) + 1) ↦
          (m - b.val) * (h + 1 - b.val)) := by
      congr 1
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro b _
      simp
    _ = _ := by rw [← Fin.sum_univ_eq_sum_range]

private theorem exists_weightedJohnsonLocalRowIndex_of_le
    {m B : ℕ} (row : JohnsonLocalRowIndex m) (hgrade : row.1.val ≤ B) :
    ∃ q : WeightedJohnsonLocalRowIndex m B,
      weightedJohnsonLocalRowIndexToJohnson q = row := by
  have hm : row.1.val ≤ m - 1 := by omega
  have hbound : row.1.val < min B (m - 1) + 1 := by omega
  let q : WeightedJohnsonLocalRowIndex m B :=
    ⟨⟨row.1.val, hbound⟩, row.2⟩
  refine ⟨q, Sigma.ext (Fin.ext rfl) ?_⟩
  apply (Fin.heq_ext_iff ?_).2
  · rfl
  · rfl

/-- Deleting rows above `B` preserves the full local-constraint kernel. -/
theorem weightedJohnsonConstraintMatrix_kernel_iff {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (v : Fin (Fintype.card (JohnsonColumnIndex X D B)) → F[X]) :
    weightedJohnsonConstraintMatrix X D B m centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i)
        (interpolant (johnsonColumns X D B) v) := by
  rw [← johnsonConstraintMatrix_kernel_iff X D B m centers w v]
  constructor
  · intro hselected
    funext row
    by_cases hgrade : row.2.1.val ≤ B
    · obtain ⟨q, hq⟩ :=
        exists_weightedJohnsonLocalRowIndex_of_le row.2 hgrade
      have hrow := congrFun hselected (row.1, q)
      simpa [weightedJohnsonConstraintMatrix, Matrix.mulVec, dotProduct, hq] using hrow
    · rw [Matrix.mulVec]
      apply Finset.sum_eq_zero
      intro j _
      have hjB : (johnsonColumns X D B j).y₀ ≤ B := by
        have hj := ((Fintype.equivFin (JohnsonColumnIndex X D B)).symm j).1.isLt
        simpa only [johnsonColumns_y₀] using Nat.le_of_lt_succ hj
      have hz := johnsonConstraintMatrix_eq_zero_of_grade_lt X D B m centers w hw row j
        (lt_of_le_of_lt hjB (Nat.lt_of_not_ge hgrade))
      simp [hz]
  · intro hfull
    funext row
    have hrow := congrFun hfull
      (row.1, weightedJohnsonLocalRowIndexToJohnson row.2)
    simpa [weightedJohnsonConstraintMatrix, Matrix.mulVec, dotProduct] using hrow

/-- Flattening the optimized rows preserves the complete local-constraint kernel. -/
theorem weightedJohnsonFinMatrix_kernel_iff {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (v : Fin (Fintype.card (JohnsonColumnIndex X D B)) → F[X]) :
    weightedJohnsonFinMatrix X D B m centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i)
        (interpolant (johnsonColumns X D B) v) := by
  rw [← weightedJohnsonConstraintMatrix_kernel_iff X D B m centers w hw v]
  constructor
  · intro h
    funext row
    have hi := congrFun h ((Fintype.equivFin (WeightedJohnsonRowIndex n m B)) row)
    simpa [weightedJohnsonFinMatrix, Matrix.mulVec, dotProduct] using hi
  · intro h
    funext i
    exact congrFun h ((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i)

/-- Optimized flattened entries satisfy the shifted challenge-degree premise. -/
theorem weightedJohnsonFinMatrix_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (i : Fin (Fintype.card (WeightedJohnsonRowIndex n m B)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D B)))
    (_hweight : weightedJohnsonFinRowWeight m B i ≤ (johnsonColumns X D B j).y₀) :
    (weightedJohnsonFinMatrix X D B m centers w i j).natDegree ≤
      (johnsonColumns X D B j).y₀ - weightedJohnsonFinRowWeight m B i := by
  simpa [weightedJohnsonFinMatrix, weightedJohnsonConstraintMatrix,
    weightedJohnsonFinRowWeight] using
    johnsonConstraintMatrix_degree_le X D B m centers w hw
      (((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i).1,
        weightedJohnsonLocalRowIndexToJohnson
          ((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i).2) j

/-- Optimized flattened rows above the source grade vanish. -/
theorem weightedJohnsonFinMatrix_eq_zero_of_grade_lt {F : Type*} [Field F] {n : ℕ}
    (X D B m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (i : Fin (Fintype.card (WeightedJohnsonRowIndex n m B)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D B)))
    (hgrade : (johnsonColumns X D B j).y₀ < weightedJohnsonFinRowWeight m B i) :
    weightedJohnsonFinMatrix X D B m centers w i j = 0 := by
  apply johnsonConstraintMatrix_eq_zero_of_grade_lt X D B m centers w hw
    (((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i).1,
      weightedJohnsonLocalRowIndexToJohnson
        ((Fintype.equivFin (WeightedJohnsonRowIndex n m B)).symm i).2) j
  simpa [weightedJohnsonFinRowWeight] using hgrade

/-- Exact finite source/row surplus constructs the complete primitive ordinary certificate.

The caller supplies only the explicit finite count inequality. The conclusion keeps every
agreement subset of size at least `A`, remains nonzero after every field extension and
challenge specialization, and has the full agreement-set recovery shape packaged by
`JohnsonSymbolicCertificate`. -/
theorem exists_weighted_johnson_symbolic_certificate
    {F : Type*} [Field F] {n D A m B k h : ℕ}
    (hD : 1 ≤ D) (hcut : D * B < m * A) (hkD : k ≤ D + 1)
    (hsurplus :
      n * ∑ b ∈ Finset.range (min B (m - 1) + 1),
          (m - b) * (h + 1 - b) <
        johnsonSourceSlotCount (m * A) D B h)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (JohnsonSymbolicCertificate (F := F) D A m B k h (m * A)
      centers f g) := by
  let columns := johnsonColumns (m * A) D B
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  have hbudget : 0 < m * A := lt_of_le_of_lt (Nat.zero_le (D * B)) hcut
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    SymbolicReceivedCurve.exists_primitive_interpolant_of_shifted_height
      m 1 h (fun i ↦ centers i) w columns
      (johnsonColumns_injective (m * A) D B)
      (weightedJohnsonFinMatrix (m * A) D B m (fun i ↦ centers i) w)
      (weightedJohnsonFinRowWeight m B)
      (weightedJohnsonFinMatrix_kernel_iff (m * A) D B m (fun i ↦ centers i) w
        (fun i ↦ receivedLine_natDegree_le (f i) (g i)))
      (by
        intro i j hweight
        have hh := weightedJohnsonFinMatrix_degree_le (m * A) D B m
          (fun i ↦ centers i) w (fun i ↦ receivedLine_natDegree_le (f i) (g i))
          i j (by
            simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hweight)
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hh)
      (by
        intro i j hweight
        apply weightedJohnsonFinMatrix_eq_zero_of_grade_lt (m * A) D B m
          (fun i ↦ centers i) w (fun i ↦ receivedLine_natDegree_le (f i) (g i))
          i j
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hweight)
      (by
        rw [sum_weightedJohnsonFinRowWeight_slots]
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree,
          sum_johnsonColumns_slots] using hsurplus)
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
  have hQsupport : Q ∈
      weightedSupportSpace F[X] D 0 0 (((m * A : ℕ) : ℝ)) hDpos := by
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
    hDpos (by exact_mod_cast (Nat.le_refl (m * A))) hbudget hkD
    (fun i ↦ centers i) f g columns
    (fun j ↦ johnsonColumns_weightedSupportEligible j) v hconstraints ι z indices P
    hPdegree centers.injective.injOn hcard hagreements

/-- A checked arithmetic certificate instantiates the complete symbolic interpolation theorem.

This is the downstream bridge from the finite `N,W,R,T,H` certificate to the primitive
interpolant. It keeps the public arithmetic record independent of the field and received words. -/
theorem IsJohnsonWeightedCertificate.exists_symbolic
    {F : Type*} [Field F] {n D A m B k H : ℕ}
    (hcert : IsJohnsonWeightedCertificate n D A m B H)
    (hD : 1 ≤ D) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (JohnsonSymbolicCertificate (F := F) D A m B k H (m * A)
      centers f g) := by
  apply exists_weighted_johnson_symbolic_certificate hD hcert.2.2.1 hkD
  simpa only [johnsonWeightedRowSlots, johnsonWeightedU,
    johnsonWeightedSourceSlots, johnsonSourceSlotCount] using
      hcert.rowSlots_lt_sourceSlots

end
end ReedSolomon.HiddenDerivative
