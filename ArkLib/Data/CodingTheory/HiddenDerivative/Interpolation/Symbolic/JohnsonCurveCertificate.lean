/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveCertificate
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.CurveHeight

/-!
# Johnson interpolation for polynomial received curves

Scaling both the row and column grades by the received degree preserves the strict Johnson
slot surplus at height `ℓ * (h + 1) - 1`. The resulting primitive interpolant is nonzero under
every field specialization and vanishes on every sufficiently agreeing low-degree candidate.
No restriction on the characteristic is needed.
-/

@[expose] public section

open Polynomial PolynomialDifferential
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative

open SourceColumn SymbolicReceivedCurve

/-- Polynomial received coordinates scale the shifted Johnson matrix degree by `ℓ`. -/
theorem johnsonFinMatrix_curve_degree_le {F : Type*} [Field F] {n : ℕ}
    (X D μ m ℓ : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (i : Fin (Fintype.card (JohnsonRowIndex n m)))
    (j : Fin (Fintype.card (JohnsonColumnIndex X D μ))) :
    (johnsonFinMatrix X D μ m centers w i j).natDegree ≤
      ℓ * (johnsonColumns X D μ j).y₀ - ℓ * johnsonFinRowWeight m i := by
  have h := natDegree_localConstraintMatrix_le_sub m ℓ centers w hw
    (johnsonColumns X D μ)
    (((Fintype.equivFin (JohnsonRowIndex n m)).symm i).1,
      johnsonLocalRow m ((Fintype.equivFin (JohnsonRowIndex n m)).symm i).2) j
  simpa [johnsonFinMatrix, johnsonConstraintMatrix, johnsonFinRowWeight,
    Nat.mul_sub_left_distrib] using h

/-- A positive curve degree gives a specialization-sound Johnson certificate at the scaled
height. The code dimension may be any `k ≤ D + 1`. -/
theorem exists_johnson_curve_symbolic_certificate
    {F : Type*} [Field F] {n D A k ℓ : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hkD : k ≤ D + 1)
    (hℓ : 0 < ℓ) (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) :
    Nonempty (Certificate A k ℓ (johnsonMu n D eta) 0
      (curveInterpolationHeight ℓ (johnsonH n D eta)) centers w) := by
  classical
  let m := johnsonM n D eta
  let μ := johnsonMu n D eta
  let h := johnsonH n D eta
  let H := curveInterpolationHeight ℓ h
  let Xc := johnsonXCutoff n D eta
  let columns := johnsonColumns Xc D μ
  have hcut : Xc ≤ m * A := johnsonXCutoff_le_mul_agreement heta hthreshold
  have hbudget : 0 < m * A := by
    have := johnson_degree_succ_le_agreement hD (show D < n by omega) heta hthreshold
    have := johnsonM_ge_three n D eta
    exact Nat.mul_pos (by omega) (by omega)
  have hslots :
      ∑ i : Fin (Fintype.card (JohnsonRowIndex n m)),
        (H + 1 - ℓ * johnsonFinRowWeight m i) <
      ∑ j : Fin (Fintype.card (JohnsonColumnIndex Xc D μ)),
        (H + 1 - ℓ * totalJetDegree (columns j).exponent) := by
    simp_rw [H, curveInterpolationHeight_column hℓ, ← Finset.mul_sum]
    apply Nat.mul_lt_mul_of_pos_left _ hℓ
    simp only [columns, johnsonColumns_totalJetDegree, sum_johnsonFinRowWeight_slots,
      sum_johnsonColumns_slots]
    exact johnson_interpolation_slot_surplus hD (by omega)
  obtain ⟨v, _, hvdegree, _, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_shifted_height m ℓ H (fun i ↦ centers i) w
      columns (johnsonColumns_injective Xc D μ)
      (johnsonFinMatrix Xc D μ m (fun i ↦ centers i) w)
      (fun i ↦ ℓ * johnsonFinRowWeight m i)
      (fun v hv ↦ (johnsonFinMatrix_kernel_iff Xc D μ m (fun i ↦ centers i) w v).mp hv)
      (by
        intro i j _
        simpa only [columns, johnsonColumns_totalJetDegree] using
          johnsonFinMatrix_curve_degree_le Xc D μ m ℓ (fun i ↦ centers i) w hw i j)
      (by
        intro i j hij
        apply johnsonFinMatrix_eq_zero_of_grade_lt
        exact Nat.lt_of_mul_lt_mul_left (by
          simpa only [columns, johnsonColumns_totalJetDegree] using hij)) hslots
  have hvheight : ∀ j, (v j).natDegree ≤ H := by
    intro j
    by_cases hz : v j = 0
    · simp [hz]
    · have hlt := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp (hvdegree j))
      omega
  have hcolumns : ∀ j, totalJetDegree (columns j).exponent ≤ μ := by
    intro j
    rw [johnsonColumns_totalJetDegree]
    exact Nat.le_of_lt_succ
      ((Fintype.equivFin (JohnsonColumnIndex Xc D μ)).symm j).1.isLt
  let Q := interpolant columns v
  refine ⟨⟨Q, coeff_interpolant_natDegree_le columns (johnsonColumns_injective Xc D μ)
    v hvheight, interpolant_totalJetDegree_le columns hcolumns v, ?_⟩⟩
  intro E _ ρ z
  let ψ := Polynomial.eval₂RingHom ρ z
  refine ⟨hnonzero ρ z, map_interpolant_jetTotalDegree_le ψ columns hcolumns v, ?_⟩
  intro indices P hP hsize hagree
  have hPdegree : P.natDegree ≤ D := by
    by_cases hz : P = 0
    · simp [hz]
    · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
      omega
  have hQweight : differentialWeightedDegree D (MvPolynomial.map ψ Q) < m * A := by
    rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
      Finset.sup_lt_iff hbudget]
    intro u hu
    have hsource := MvPolynomial.support_map_subset ψ Q hu
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hsource)
    have heq : u = (columns j).exponent := by
      simpa [Q] using MvPolynomial.support_monomial_subset hj
    rw [heq]
    exact weight_differentialWeight_lt_of_weightedSupportEligible
      (by exact_mod_cast hcut) (johnsonColumns_weightedSupportEligible j)
  have hlocal : ∀ i, SatisfiesLocalConstraints m (ρ (centers i))
      ((w i).eval₂ ρ z) (MvPolynomial.map ψ Q) := by
    intro i
    have hi := SatisfiesLocalConstraints.map ψ m (Polynomial.C (centers i))
      (w i) Q (hconstraints i)
    change SatisfiesLocalConstraints m
      (Polynomial.eval₂ ρ z (Polynomial.C (centers i))) ((w i).eval₂ ρ z)
      (MvPolynomial.map ψ Q) at hi
    simpa only [Polynomial.eval₂_C] using hi
  exact differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (fun i ↦ ρ (centers i)) (fun i ↦ (w i).eval₂ ρ z) indices hQweight
    (fun i _ ↦ hlocal i) P hPdegree (fun _ _ _ _ hij ↦ centers.injective (ρ.injective hij))
    hsize hagree

end ReedSolomon.HiddenDerivative
