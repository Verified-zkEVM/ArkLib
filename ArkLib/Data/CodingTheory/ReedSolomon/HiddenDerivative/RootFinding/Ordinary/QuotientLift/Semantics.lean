/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Series
public import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
-- The specialization homomorphism reduces the implementation of `toPoly` and `ringEquiv`.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv

/-!
# Specializing quotient-series coefficients at a geometric root

A parameter root may lie in any extension field. `specialize` evaluates each coefficient
polynomial at that root and leaves the centered series variable unchanged. This operation
commutes with the executable residual, so Newton's correctness proof can work with ordinary
field-valued polynomials while the program manipulates all roots simultaneously.

The first-order Taylor identity identifies the computed initial slope with `Q_Y(center,U)`.
`residual_congr` says that matching branch coefficients give matching residual coefficients;
Newton uses it when moving the derivative inverse to the updated branch.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

noncomputable section

open CompPoly CompPoly.CPolynomial

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

variable {L : Type*} [Field L]

/-- Interpret the coefficient parameter at a root in an arbitrary extension field. -/
def specialize (ι : E →+* L) (θ : L) : Series E →+* Polynomial L :=
  (Polynomial.mapRingHom ((Polynomial.eval₂RingHom ι θ).comp CPolynomial.toPolyRingHom)).comp
    CPolynomial.toPolyRingHom

/-- A constant series specializes its single parameter polynomial. -/
@[simp] theorem specialize_C (ι : E →+* L) (θ : L) (a : CPolynomial E) :
    specialize ι θ (CPolynomial.C a) = Polynomial.C (a.toPoly.eval₂ ι θ) := by
  simp [specialize, CPolynomial.C_toPoly]

/-- The centered series variable is unaffected by parameter specialization. -/
@[simp] theorem specialize_X (ι : E →+* L) (θ : L) :
    specialize ι θ (CPolynomial.X : Series E) = Polynomial.X := by
  simp [specialize, CPolynomial.X_toPoly]

/-- Coefficient extraction commutes with specializing the parameter. -/
@[simp] theorem coeff_specialize (ι : E →+* L) (θ : L) (series : Series E) (j : ℕ) :
    (specialize ι θ series).coeff j = (series.coeff j).toPoly.eval₂ ι θ := by
  change ((series.toPoly.map
    ((Polynomial.eval₂RingHom ι θ).comp CPolynomial.toPolyRingHom)).coeff j) = _
  rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly]
  rfl

/-- The executable residual specializes to the literal bivariate substitution. -/
theorem specialize_residual (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (series : Series E) :
    specialize ι θ (residual Q center series) =
      MvPolynomial.eval₂ (Polynomial.C.comp ι)
        ![Polynomial.X + Polynomial.C (ι center), specialize ι θ series]
        (CPoly.fromCMvPolynomial Q) := by
  rw [residual, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;> simp [CPolynomial.C_toPoly]

omit [BEq E] [LawfulBEq E] in
/-- Changing only the coefficient of positive degree `j` changes residual coefficient `j`
affinely, with slope `Q_Y(center,P(0))`. Terms quadratic in the change have degree above `j`. -/
theorem residual_coefficient_affine (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (center : L) (P : Polynomial L) (j : ℕ) (hj : 0 < j) (γ : L) :
    (MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C center, P + Polynomial.C γ * Polynomial.X ^ j] q).coeff j =
    (MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C center, P] q).coeff j +
      MvPolynomial.eval₂ ι ![center, P.coeff 0] (MvPolynomial.pderiv 1 q) * γ := by
  let values : Fin 2 → Polynomial L := ![Polynomial.X + Polynomial.C center, P]
  let increments : Fin 2 → Polynomial L := ![0, Polynomial.C γ * Polynomial.X ^ j]
  have hdiv := MvPolynomial.pow_succ_dvd_eval₂Hom_add_sub_pderiv
    (Polynomial.C.comp ι) values increments Finset.univ q (1 : Fin 2) Polynomial.X j hj
    (by simp)
    (by simp [increments])
    (by intro i _ hi; fin_cases i <;> simp_all [increments])
    (by simp)
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdiv j (by omega)
  have hvalues : values + increments =
      ![Polynomial.X + Polynomial.C center, P + Polynomial.C γ * Polynomial.X ^ j] := by
    funext i
    fin_cases i <;> simp [values, increments]
  rw [hvalues] at hcoeff
  simp only [Polynomial.coeff_sub, increments, Matrix.cons_val_one, Matrix.cons_val_zero,
    ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    Polynomial.coeff_mul_C] at hcoeff
  have hslope :
      (MvPolynomial.eval₂ (Polynomial.C.comp ι) values (MvPolynomial.pderiv 1 q)).coeff 0 =
        MvPolynomial.eval₂ ι ![center, P.coeff 0] (MvPolynomial.pderiv 1 q) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    change Polynomial.evalRingHom 0
      (MvPolynomial.eval₂ (Polynomial.C.comp ι) values (MvPolynomial.pderiv 1 q)) = _
    rw [MvPolynomial.eval₂_comp_left]
    congr 1
    · ext a
      simp
    · funext i
      fin_cases i <;> simp [values, Polynomial.coeff_zero_eq_eval_zero]
  change _ - _ -
    (MvPolynomial.eval₂ (Polynomial.C.comp ι) values (MvPolynomial.pderiv 1 q)).coeff 0 * γ = 0
    at hcoeff
  rw [hslope] at hcoeff
  rw [sub_eq_zero, sub_eq_iff_eq_add] at hcoeff
  simpa [values, add_comm] using hcoeff

omit [BEq E] [LawfulBEq E] in
/-- Series agreeing through degree `j-1` give residuals agreeing through the same degree. -/
theorem residual_congr (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (center : L) (P S : Polynomial L) (j : ℕ)
    (h : Polynomial.X ^ j ∣ P - S) :
    Polynomial.X ^ j ∣
      MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X + Polynomial.C center, P] q -
      MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X + Polynomial.C center, S] q := by
  let I : Ideal (Polynomial L) := Ideal.span {Polynomial.X ^ j}
  let π := Ideal.Quotient.mk I
  have heq : π P = π S := Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)
  apply Ideal.mem_span_singleton.mp
  change _ ∈ I
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact heq

/-- The computed two-evaluation slope is exactly the value-variable partial derivative. -/
theorem eval₂_slope (ι : E →+* L) (θ : L) (Q : CPoly.CMvPolynomial 2 E) (center : E) :
    (slope Q center).toPoly.eval₂ ι θ =
      MvPolynomial.eval₂ ι ![ι center, θ]
        (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) := by
  have h := residual_coefficient_affine ι (CPoly.fromCMvPolynomial Q) (ι center)
    (Polynomial.C θ) 1 (by decide) 1
  rw [slope, CPolynomial.toPoly_sub, Polynomial.eval₂_sub,
    ← coeff_specialize, ← coeff_specialize, specialize_residual, specialize_residual]
  simp only [map_add, specialize_C, specialize_X, CPolynomial.X_toPoly,
    Polynomial.eval₂_X]
  simpa using (sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h))


end
end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
