/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ZeroOrder
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.SourceColumn
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Soundness
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.WeightedSupport
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.InterpolationBounds
/-!
# Finite ordinary Johnson interpolation certificates

This module indexes the strict Johnson source columns, packages their order-zero local constraint
matrix, and constructs a primitive symbolic certificate for received lines. The certificate has
the prescribed weighted support, bounded challenge degree, and soundness under field extension.

## Main statements

* `JohnsonColumnIndex` and `johnsonColumns`: the finite strict staircase of source monomials.
* `johnsonConstraintMatrix_kernel_iff`: the finite triangular matrix captures every local
  constraint.
* `JohnsonSymbolicCertificate` and `exists_johnson_symbolic_certificate`: the primitive
  interpolation certificate and its construction from the Johnson slot surplus.

## References

* [BCHKS25]
* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation
open SourceColumn

noncomputable section

/-- Exact strict source columns at the Johnson cutoffs. -/
abbrev JohnsonColumnIndex (X D μ : ℕ) :=
  Σ j : Fin (μ + 1), Fin (X - D * j.val)

/-- Triangular local rows, indexed first by error degree and then by the remaining T degree. -/
abbrev JohnsonLocalRowIndex (m : ℕ) :=
  Σ e : Fin m, Fin (m - e.val)

/-- The evaluation point and triangular local coordinate of a finite matrix row. -/
abbrev JohnsonRowIndex (n m : ℕ) := Fin n × JohnsonLocalRowIndex m

/-- Enumerate all strict source columns as the generic symbolic-column type. -/
def johnsonColumns (X D μ : ℕ) :
    Fin (Fintype.card (JohnsonColumnIndex X D μ)) → SourceColumn 0 := fun j ↦
  let q := (Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j
  ⟨q.2.val, q.1.val, Fin.elim0⟩

/-- The `y` exponent of an enumerated source column is its first staircase coordinate. -/
@[simp] theorem johnsonColumns_y₀ (X D μ : ℕ)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonColumns X D μ j).y₀ =
      ((Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j).1.val := rfl

/-- The `x` exponent of an enumerated source column is its second staircase coordinate. -/
@[simp] theorem johnsonColumns_x (X D μ : ℕ)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonColumns X D μ j).x =
      ((Fintype.equivFin (JohnsonColumnIndex X D μ)).symm j).2.val := rfl

/-- The total jet degree of an enumerated source column is its `y` exponent. -/
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
  ⟨zeroOrderLocalExponent (row.1.val + row.2.val) row.1.val, by
    rw [localContactOrder_eq]
    simp [zeroOrderLocalExponent, localT, localE, localAux]
    have := row.2.isLt
    omega⟩

/-- A triangular row's local jet degree is its first coordinate. -/
@[simp] theorem johnsonLocalRow_localJetDegree (m : ℕ) (row : JohnsonLocalRowIndex m) :
    (johnsonLocalRow m row).1.weight (localJetDegreeWeight 0) = row.1.val := by
  change Finsupp.weight (localJetDegreeWeight (d := 0))
    (zeroOrderLocalExponent (row.1.val + row.2.val) row.1.val) = row.1.val
  simp [zeroOrderLocalExponent, Finsupp.weight_single, localJetDegreeWeight, localT, localE,
    localAux]

/-- The exact triangular matrix of symbolic local constraints. -/
def johnsonConstraintMatrix {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X]) :
  Matrix (JohnsonRowIndex n m) (Fin (Fintype.card (JohnsonColumnIndex X D μ))) F[X] :=
  fun row j ↦ localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w
    (johnsonColumns X D μ) (row.1, johnsonLocalRow m row.2) j

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
    have hcontact := row.2
    rw [localContactOrder_eq] at hcontact
    simpa [Nat.zero_mul, Nat.add_zero] using hcontact
  have hE : row.1 (localE 0) < m := htri.trans_lt hT
  have hrem : row.1 (localT 0) - row.1 (localE 0) <
      m - row.1 (localE 0) := by
    apply Nat.lt_sub_iff_add_lt.mpr
    omega
  let q : JohnsonLocalRowIndex m :=
    ⟨⟨row.1 (localE 0), hE⟩,
      ⟨row.1 (localT 0) - row.1 (localE 0), hrem⟩⟩
  refine ⟨q, Subtype.ext ?_⟩
  change zeroOrderLocalExponent
      (row.1 (localE 0) + (row.1 (localT 0) - row.1 (localE 0)))
      (row.1 (localE 0)) = row.1
  rw [Nat.add_sub_of_le htri, zeroOrderLocalExponent_reconstruct]

/-- The triangular rows detect exactly the complete order-zero local constraint system. -/
theorem johnsonConstraintMatrix_kernel_iff {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card (JohnsonColumnIndex X D μ)) → F[X]) :
    johnsonConstraintMatrix X D μ m centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (C (centers i)) (w i)
        (interpolant (johnsonColumns X D μ) v) := by
  classical
  rw [← localConstraintMatrix_mulVec_eq_zero_iff m (fun i ↦ Polynomial.C (centers i)) w
    (johnsonColumns X D μ) v]
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
      have hz : localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w
          (johnsonColumns X D μ) row j = 0 := by
        by_contra hne
        have hcoeff :
            (localConstraintAt m (Polynomial.C (centers row.1)) (w row.1)
              (johnsonColumns X D μ j).polynomial).coeff row.2.1 ≠ 0 := by
          simpa only [localConstraintMatrix_apply_eq_localConstraintAt_coeff] using hne
        exact htri ((localConstraintAt_zeroOrder_support m (Polynomial.C (centers row.1))
          (w row.1) (johnsonColumns X D μ j).polynomial row.2.1
          (MvPolynomial.mem_support_iff.mpr hcoeff)).1)
      change localConstraintMatrix m (fun i ↦ Polynomial.C (centers i)) w
        (johnsonColumns X D μ) row j * v j = 0
      rw [hz]
      simp
  · intro hfull
    have hmatrix := (localConstraintMatrix_mulVec_eq_zero_iff m
      (fun i ↦ Polynomial.C (centers i)) w (johnsonColumns X D μ) v).mpr
      ((localConstraintMatrix_mulVec_eq_zero_iff m (fun i ↦ Polynomial.C (centers i)) w
        (johnsonColumns X D μ) v).mp hfull)
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
  have h := natDegree_localConstraintMatrix_le_sub m 1
    centers w hw (johnsonColumns X D μ)
    (row.1, johnsonLocalRow m row.2) j
  simpa [johnsonConstraintMatrix, johnsonLocalRow_localJetDegree] using h

/-- Rows above a source column's jet grade vanish identically. -/
theorem johnsonConstraintMatrix_eq_zero_of_grade_lt {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (row : JohnsonRowIndex n m)
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (hgrade : (johnsonColumns X D μ j).y₀ < row.2.1.val) :
    johnsonConstraintMatrix X D μ m centers w row j = 0 := by
  apply localConstraintMatrix_eq_zero_of_lt m
    (fun i ↦ Polynomial.C (centers i)) w (johnsonColumns X D μ)
  simpa [johnsonColumns_totalJetDegree, johnsonLocalRow_localJetDegree] using hgrade

/-- Flattened entries satisfy the shifted degree premise. -/
theorem johnsonFinMatrix_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 1)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonFinMatrix X D μ m centers w i j).natDegree ≤
      (johnsonColumns X D μ j).y₀ - johnsonFinRowWeight m i := by
  simpa [johnsonFinMatrix, johnsonFinRowWeight] using
    johnsonConstraintMatrix_degree_le X D μ m centers w hw
      ((Fintype.equivFin (JohnsonRowIndex n m)).symm i) j

/-- Flattened rows above the source grade vanish. -/
theorem johnsonFinMatrix_eq_zero_of_grade_lt {F : Type*} [Field F] {n : ℕ}
    (X D μ m : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (hgrade : (johnsonColumns X D μ j).y₀ < johnsonFinRowWeight m i) :
    johnsonFinMatrix X D μ m centers w i j = 0 := by
  exact johnsonConstraintMatrix_eq_zero_of_grade_lt X D μ m centers w _ j hgrade

/-! ### The packaged ordinary Johnson certificate -/

variable {F : Type*} [Field F]

/-- A primitive order-zero equation with strict weighted support and an extension-field agreement
implication. -/
structure JohnsonSymbolicCertificate {n : ℕ} (D A m μ k h Xc : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) where
  /-- Coefficients indexed by the strict Johnson source staircase. -/
  coefficients : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]
  /-- The order-zero differential polynomial in the certificate. -/
  Q : DifferentialPolynomial F[X] 0
  /-- The certificate polynomial is its source-column interpolant. -/
  eq_interpolant : Q = interpolant (johnsonColumns Xc D μ) coefficients
  /-- The coefficient polynomials generate the unit ideal. -/
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  /-- Every coefficient of `Q` has challenge-variable degree at most `h`. -/
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  /-- Every exponent in the support of `Q` satisfies the weighted cutoff. -/
  support : ∀ u ∈ Q.support, WeightedSupportEligible D 0 0 (Xc : ℝ) u
  /-- The jet degree of `Q` is at most `μ`. -/
  jetDegree_le : jetDegree Q (0 : Fin 1) ≤ μ
  /-- The polynomial `Q` satisfies the order-`m` constraints at every received point. -/
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
    (receivedLine (f i) (g i)) Q
  /-- Every coefficient specialization is nonzero and vanishes under differential
  specialization for each degree-`< k` polynomial agreeing at at least `A` indexed points. -/
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Every strict Johnson source column satisfies the weighted-support predicate. -/
theorem johnsonColumns_weightedSupportEligible {Xc D μ : ℕ}
    (j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ))) :
    WeightedSupportEligible D 0 0 (Xc : ℝ) (johnsonColumns Xc D μ j).exponent := by
  let q := (Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j
  have hq := q.2.isLt
  have hstrict : q.2.val + D * q.1.val < Xc := by omega
  constructor
  · simp [fullHigherJetWeight, jetHigherWeight, johnsonColumns, SourceColumn.exponent,
      Finsupp.weight_single]
  · norm_cast
    simpa [q, johnsonColumns, SourceColumn.totalJetDegree_exponent] using hstrict

/-- The canonical Johnson interpolant has jet degree at most its slice cutoff. -/
theorem johnsonInterpolant_jetDegree_le {Xc D μ : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]) :
    jetDegree (interpolant (johnsonColumns Xc D μ) v) (0 : Fin 1) ≤ μ := by
  have hcolumns : ∀ j, totalJetDegree (johnsonColumns Xc D μ j).exponent ≤ μ := by
    intro j
    rw [johnsonColumns_totalJetDegree]
    have hj := ((Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j).1.isLt
    simpa only [johnsonColumns_y₀] using Nat.le_of_lt_succ hj
  calc
    jetDegree (interpolant (johnsonColumns Xc D μ) v) (0 : Fin 1) ≤
        jetTotalDegree (interpolant (johnsonColumns Xc D μ) v) :=
      jetDegree_le_total _ _
    _ ≤ μ := by
      rw [jetTotalDegree_le_iff]
      intro u hu
      exact SourceColumn.interpolant_totalJetDegree_le (johnsonColumns Xc D μ)
        hcolumns v u hu

/-- The Johnson slot surplus constructs a primitive ordinary symbolic certificate from the rate
and degree bounds. -/
theorem exists_johnson_symbolic_certificate
    {n D A k : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A)
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
    simpa only [Xc, m] using johnsonXCutoff_le_mul_agreement heta hthreshold
  have hbudget : 0 < m * A := by
    have hDlt : D < n := by omega
    have hDA := johnson_degree_succ_le_agreement hD hDlt heta hthreshold
    have hm := johnsonM_ge_three n D eta
    exact Nat.mul_pos (by omega) (by omega)
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_shifted_height
      m 1 h (fun i ↦ centers i) w columns (johnsonColumns_injective Xc D μ)
      (johnsonFinMatrix Xc D μ m (fun i ↦ centers i) w)
      (johnsonFinRowWeight m)
      (johnsonFinMatrix_kernel_iff Xc D μ m (fun i ↦ centers i) w)
      (by
        intro i j hweight
        have hh := johnsonFinMatrix_degree_le Xc D μ m (fun i ↦ centers i) w
          (fun i ↦ natDegree_receivedLine_le (f i) (g i)) i j
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hh)
      (by
        intro i j hweight
        apply johnsonFinMatrix_eq_zero_of_grade_lt Xc D μ m (fun i ↦ centers i) w
          i j
        simpa only [columns, one_mul, johnsonColumns_totalJetDegree] using hweight) (by
          rw [sum_johnsonFinRowWeight_slots]
          simpa only [columns, one_mul, johnsonColumns_totalJetDegree,
            sum_johnsonColumns_slots, m, μ, h, Xc] using
              johnson_interpolation_slot_surplus hD (by omega))
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
    exact interpolant_mem_weightedSupportSpace hDpos (johnsonColumns Xc D μ)
      (fun j ↦ johnsonColumns_weightedSupportEligible j) v
  refine ⟨{
    coefficients := v
    Q := Q
    eq_interpolant := rfl
    primitiveCoefficients := hprimitive
    challengeDegree_le := SourceColumn.coeff_interpolant_natDegree_le
      (johnsonColumns Xc D μ) (johnsonColumns_injective Xc D μ) v hvheight
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
