/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Ordinary.JohnsonCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.BaseEquation
/-! # Johnson interpolation certificate for polynomial received curves -/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve ReedSolomon

noncomputable section

/-- The exact height that scales every shifted Johnson coefficient slot by `ℓ`. -/
def johnsonPowerHeight (ℓ h : ℕ) : ℕ := ℓ * (h + 1) - 1

/-- The exact shifted-slot height stays within the linear `ℓ`-scaled height budget. -/
theorem johnsonPowerHeight_le (ℓ h : ℕ) : johnsonPowerHeight ℓ h ≤ ℓ * (h + 1) := by
  exact Nat.sub_le _ _

variable {F : Type*} [Field F]

/-- A primitive order-zero Johnson equation for an arbitrary polynomial received curve. -/
structure JohnsonPowerSymbolicCertificate {n ℓ : ℕ} (D A m μ k h Xc : ℕ)
    (centers : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) where
  coefficients : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]
  Q : DifferentialPolynomial F[X] 0
  eq_interpolant : Q = interpolant (johnsonColumns Xc D μ) coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ johnsonPowerHeight ℓ h
  support : ∀ u ∈ Q.support, WeightedSupportEligible D 0 0 (Xc : ℝ) u
  jetDegree_le : jetDegree Q (0 : Fin 1) ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
    (powerBatchedCoordinate fun t ↦ values t i) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) =
          powerBatchedWord (fun t j ↦ ι (values t j)) z i) →
        differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

private theorem coeff_johnsonPowerInterpolant_natDegree_le {Xc D μ H : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X])
    (hv : ∀ j, (v j).natDegree ≤ H) :
    ∀ u, (MvPolynomial.coeff u (interpolant (johnsonColumns Xc D μ) v)).natDegree ≤ H := by
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

private theorem support_johnsonPowerInterpolant_subset_range {Xc D μ : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X])
    {u : JetVariable 0 →₀ ℕ} (hu : u ∈ (interpolant (johnsonColumns Xc D μ) v).support) :
    u ∈ Set.range (fun j ↦ (johnsonColumns Xc D μ j).exponent) := by
  classical
  by_contra hn
  apply MvPolynomial.mem_support_iff.mp hu
  rw [interpolant, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [MvPolynomial.coeff_monomial]
  split
  · rename_i heq
    exact (hn ⟨j, heq⟩).elim
  · rfl

private theorem johnsonPowerColumns_weightedSupportEligible {Xc D μ : ℕ}
    (j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ))) :
    WeightedSupportEligible D 0 0 (Xc : ℝ) (johnsonColumns Xc D μ j).exponent := by
  let q := (Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j
  have hq := q.2.isLt
  have hstrict : q.2.val + D * q.1.val < Xc := by omega
  constructor
  · simp [fullHigherJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype]
  · norm_cast
    simpa [q, johnsonColumns, SourceColumn.totalJetDegree_exponent] using hstrict

private theorem johnsonPowerInterpolant_jetDegree_le {Xc D μ : ℕ}
    (v : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) → F[X]) :
    jetDegree (interpolant (johnsonColumns Xc D μ) v) (0 : Fin 1) ≤ μ := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro u hu
  obtain ⟨j, rfl⟩ := support_johnsonPowerInterpolant_subset_range v hu
  have hj := ((Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j).1.isLt
  simpa [SourceColumn.exponent] using Nat.le_of_lt_succ hj

/-- The Johnson matrix has the shifted degree bound for a degree-`ℓ` received curve. -/
theorem johnsonPowerFinMatrix_degree_le {n : ℕ}
    (X D μ m ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (_hweight : ℓ * johnsonFinRowWeight m i ≤
      ℓ * (johnsonColumns X D μ j).y₀) :
    (johnsonFinMatrix X D μ m centers w i j).natDegree ≤
      ℓ * (johnsonColumns X D μ j).y₀ - ℓ * johnsonFinRowWeight m i := by
  have h := constraintMatrix_degree_le_grade_shift m ℓ centers w hw
    (johnsonColumns X D μ)
    (((Fintype.equivFin (JohnsonRowIndex n m)).symm i).1,
      johnsonLocalRow m ((Fintype.equivFin (JohnsonRowIndex n m)).symm i).2) j
  simpa only [johnsonFinMatrix, johnsonConstraintMatrix, Matrix.submatrix_apply,
    johnsonFinRowWeight, johnsonLocalRow_localJetDegree, SourceColumn.totalJetDegree_exponent,
    Fin.sum_univ_zero, add_zero, Nat.mul_sub_left_distrib, id_eq] using h

/-- Johnson matrix entries above the scaled source grade vanish. -/
theorem johnsonPowerFinMatrix_eq_zero_of_weight_lt {n : ℕ}
    (X D μ m ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (_hℓ : 0 < ℓ)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ)))
    (hweight : ℓ * (johnsonColumns X D μ j).y₀ < ℓ * johnsonFinRowWeight m i) :
    johnsonFinMatrix X D μ m centers w i j = 0 := by
  apply constraintMatrix_eq_zero_of_source_grade_lt_row_grade m ℓ centers w hw
  simpa only [johnsonFinMatrix, johnsonConstraintMatrix, Matrix.submatrix_apply,
    johnsonFinRowWeight, johnsonLocalRow_localJetDegree,
    SourceColumn.totalJetDegree_exponent, Fin.sum_univ_zero, add_zero, id_eq] using
      Nat.lt_of_mul_lt_mul_left hweight

/-- The literal Johnson recipe constructs a primitive equation for every positive-degree
polynomial received curve. Its challenge height is `ℓ * (johnsonH + 1) - 1`. -/
theorem exists_johnsonPower_symbolic_certificate
    {n D A k ℓ : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (_hagreement : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (_hAn : A ≤ n)
    (hkD : k ≤ D + 1) (hℓ : 0 < ℓ) (centers : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F) :
    Nonempty (JohnsonPowerSymbolicCertificate (F := F) D A (johnsonM n D eta)
      (johnsonMu n D eta) k (johnsonH n D eta) (johnsonXCutoff n D eta)
      centers values) := by
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let H := johnsonPowerHeight ℓ h
  let Xc := johnsonXCutoff n D eta
  let columns := johnsonColumns Xc D μ
  let w : Fin n → F[X] := fun i ↦ powerBatchedCoordinate fun t ↦ values t i
  have hDpos : 0 < D := Nat.zero_lt_of_lt hD
  have hcut : Xc ≤ m * A := by
    simpa only [Xc, m] using johnsonXCutoff_le_mul_agreement hD hDn heta hthreshold
  have hbudget : 0 < m * A := by
    have hDA := johnson_degree_succ_le_agreement hD hDn heta hthreshold
    have hm := johnsonM_ge_three n D eta
    exact Nat.mul_pos (by omega) (by omega)
  have hw : ∀ i, (w i).natDegree ≤ ℓ := fun i ↦ powerBatchedCoordinate_natDegree_le _
  have hH : H + 1 = ℓ * (h + 1) := by
    dsimp only [H, johnsonPowerHeight]
    have : 0 < ℓ * (h + 1) := Nat.mul_pos hℓ (by omega)
    omega
  have hscaledSurplus :
      Finset.univ.sum (fun i : Fin (Fintype.card (JohnsonRowIndex n m)) ↦
        H + 1 - ℓ * johnsonFinRowWeight m i) <
      Finset.univ.sum (fun j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) ↦
        H + 1 - ℓ * totalJetDegree (columns j).exponent) := by
    have hline := johnson_interpolation_slot_surplus (eta := eta) hD hDn
    rw [← sum_johnsonFinRowWeight_slots (n := n) m h,
      ← sum_johnsonColumns_slots Xc D μ h] at hline
    have hscale : ℓ *
        Finset.univ.sum (fun i : Fin (Fintype.card (JohnsonRowIndex n m)) ↦
          h + 1 - johnsonFinRowWeight m i) <
        ℓ * Finset.univ.sum
          (fun j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)) ↦
            h + 1 - (johnsonColumns Xc D μ j).y₀) :=
      (Nat.mul_lt_mul_left hℓ).mpr hline
    rw [Finset.mul_sum, Finset.mul_sum] at hscale
    simpa only [hH, columns, johnsonColumns_totalJetDegree,
      ← Nat.mul_sub_left_distrib] using hscale
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    SymbolicReceivedCurve.exists_primitive_interpolant_of_shifted_height
      m ℓ H (fun i ↦ centers i) w columns (johnsonColumns_injective Xc D μ)
      (johnsonFinMatrix Xc D μ m (fun i ↦ centers i) w)
      (fun i ↦ ℓ * johnsonFinRowWeight m i)
      (johnsonFinMatrix_kernel_iff Xc D μ m (fun i ↦ centers i) w)
      (by
        intro i j hweight
        have hweight' : ℓ * johnsonFinRowWeight m i ≤
            ℓ * (johnsonColumns Xc D μ j).y₀ := by
          simpa only [columns, johnsonColumns_totalJetDegree] using hweight
        simpa only [columns, johnsonColumns_totalJetDegree] using
          johnsonPowerFinMatrix_degree_le Xc D μ m ℓ
            (fun i ↦ centers i) w hw i j hweight')
      (by
        intro i j hweight
        apply johnsonPowerFinMatrix_eq_zero_of_weight_lt Xc D μ m ℓ
          (fun i ↦ centers i) w hw hℓ i j
        simpa only [columns, johnsonColumns_totalJetDegree] using hweight)
      hscaledSurplus
  let Q : DifferentialPolynomial F[X] 0 := interpolant columns v
  have hvheight : ∀ j, (v j).natDegree ≤ H := by
    intro j
    by_cases hz : v j = 0
    · simp [hz]
    · have hlt : (v j).natDegree < H + 1 - ℓ * (columns j).y₀ := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        simpa only [columns, johnsonColumns_totalJetDegree] using Polynomial.mem_degreeLT.mp
          (hvdegree j)
      omega
  refine ⟨{
    coefficients := v
    Q := Q
    eq_interpolant := rfl
    primitiveCoefficients := hprimitive
    challengeDegree_le := coeff_johnsonPowerInterpolant_natDegree_le v hvheight
    support := ?_
    jetDegree_le := johnsonPowerInterpolant_jetDegree_le v
    localConstraints := hconstraints
    specialization_sound := ?_ }⟩
  · intro u hu
    obtain ⟨j, rfl⟩ := support_johnsonPowerInterpolant_subset_range v hu
    exact johnsonPowerColumns_weightedSupportEligible j
  · intro E _ ι z
    refine ⟨hnonzero ι z, ?_⟩
    intro indices P hPdegree hcard hagreements
    have hPnat : P.natDegree ≤ D := by
      by_cases hz : P = 0
      · simp [hz]
      · have : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hPdegree
        omega
    apply differentialSpecialization_curve_interpolant_eq_zero_of_agreements
      hDpos (by exact_mod_cast hcut) hbudget (fun i ↦ centers i) w columns
      (fun j ↦ johnsonPowerColumns_weightedSupportEligible j) v hconstraints
      ι z indices P hPnat centers.injective.injOn hcard
    intro i hi
    simpa only [w, powerBatchedCoordinate, powerBatchedWord,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, mul_comm] using hagreements i hi

end
end ReedSolomon.HiddenDerivative
