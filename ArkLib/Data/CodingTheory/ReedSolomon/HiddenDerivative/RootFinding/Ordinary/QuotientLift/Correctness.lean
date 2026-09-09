/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Machine
import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor

/-!
# Why simultaneous quotient lifting recovers every regular branch

The proof specializes the executable coefficient arrays at an arbitrary geometric root of `h`.
A first-order Taylor congruence identifies the next residual coefficient as an affine function.
The shared modular inverse solves that equation at every root at once. Induction then matches
all coefficients of any degree-`< k` polynomial solution, yielding equality of polynomials.

This proves the functional lifting contract. Producing a covering modulus and a regular center,
and replacing sequential coefficient steps by the paper's fast Newton implementation, are
separate constructor obligations.
-/

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

/-- A symbolic coefficient extension becomes the corresponding scalar series extension. -/
theorem specialize_appendCoefficient (ι : E →+* L) (θ : L)
    (series : Series E) (j : ℕ) (a : CPolynomial E) :
    specialize ι θ (appendCoefficient series j a) = specialize ι θ series +
      Polynomial.C (a.toPoly.eval₂ ι θ) * Polynomial.X ^ j := by
  simp [appendCoefficient]

/-- At a root of `h`, monic reduction leaves the affine coefficient solution unchanged. -/
theorem eval₂_liftCoefficient (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (modulus inverse : CPolynomial E)
    (series : Series E) (j : ℕ) (hmonic : modulus.monic)
    (hroot : modulus.toPoly.eval₂ ι θ = 0) :
    (liftCoefficient Q center modulus inverse series j).toPoly.eval₂ ι θ =
      -(specialize ι θ (residual Q center series)).coeff j * inverse.toPoly.eval₂ ι θ := by
  rw [liftCoefficient, modByMonic_toPoly_eq_modByMonic _ _ hmonic,
    Polynomial.eval₂_modByMonic_eq_self_of_root hroot]
  simp [toPoly_mul, toPoly_neg, coeff_specialize]

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

omit [BEq E] [LawfulBEq E] in
/-- The affine correction agrees with any true solution for one additional coefficient.
Invertibility of the initial slope forces the correction to equal
that solution's next coefficient. -/
theorem corrected_matches_one_more (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (center : L) (P S : Polynomial L) (j : ℕ) (hj : 0 < j)
    (hinitial : S.coeff 0 = P.coeff 0)
    (hmatch : Polynomial.X ^ j ∣ P - S)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C center, P] q = 0)
    (inverse : L)
    (hinverse : MvPolynomial.eval₂ ι ![center, P.coeff 0] (MvPolynomial.pderiv 1 q) *
      inverse = 1) :
    Polynomial.X ^ (j + 1) ∣ P -
      (S + Polynomial.C
        (-(MvPolynomial.eval₂ (Polynomial.C.comp ι)
          ![Polynomial.X + Polynomial.C center, S] q).coeff j * inverse) * Polynomial.X ^ j) := by
  let γ := (P - S).coeff j
  let corrected := S + Polynomial.C γ * Polynomial.X ^ j
  have hcorrected : Polynomial.X ^ (j + 1) ∣ P - corrected := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    by_cases hij : i < j
    · have hzero := Polynomial.X_pow_dvd_iff.mp hmatch i hij
      simpa [corrected, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt hij] using hzero
    · have hij' : i = j := by omega
      subst i
      simp only [corrected, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_C_mul_X_pow, γ]
      simp only [ite_true]
      ring
  have hres := residual_congr ι q center P corrected (j + 1) hcorrected
  have hz := Polynomial.X_pow_dvd_iff.mp hres j (by omega)
  rw [hsolution, zero_sub, Polynomial.coeff_neg, neg_eq_zero] at hz
  have haff := residual_coefficient_affine ι q center S j hj γ
  rw [hinitial] at haff
  change (MvPolynomial.eval₂ (Polynomial.C.comp ι)
    ![Polynomial.X + Polynomial.C center, corrected] q).coeff j = 0 at hz
  rw [haff] at hz
  have hγ : γ = -(MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C center, S] q).coeff j * inverse := by
    have hm := congrArg (fun a => a * inverse) hz
    rw [add_mul, mul_right_comm _ γ inverse, hinverse, one_mul, MulZeroClass.zero_mul] at hm
    simpa only [neg_mul] using (eq_neg_of_add_eq_zero_right hm)
  simpa [corrected, hγ] using hcorrected

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

/-- Each executed lift preserves all previously matching coefficients and gains one more. -/
theorem liftSteps_matches (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (modulus inverse : CPolynomial E)
    (hmonic : modulus.monic) (hroot : modulus.toPoly.eval₂ ι θ = 0)
    (hinverse : CPolynomial.inverseMod? (slope Q center) modulus = some inverse)
    (P : Polynomial L)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C (ι center), P] (CPoly.fromCMvPolynomial Q) = 0)
    (hconstant : P.coeff 0 = θ) (steps j : ℕ) (hj : 0 < j) (series : Series E)
    (hmatch : Polynomial.X ^ j ∣ P - specialize ι θ series) :
    Polynomial.X ^ (j + steps) ∣
      P - specialize ι θ (liftSteps Q center modulus inverse steps j series) := by
  induction steps generalizing j series with
  | zero => simpa [liftSteps] using hmatch
  | succ steps ih =>
    have hinit : (specialize ι θ series).coeff 0 = P.coeff 0 := by
      have hc := Polynomial.X_pow_dvd_iff.mp hmatch 0 hj
      exact (sub_eq_zero.mp (by simpa using hc)).symm
    have hi := CPolynomial.eval₂_mul_inverseMod_eq_one ι θ hroot hinverse
    have hi' : MvPolynomial.eval₂ ι ![ι center, P.coeff 0]
        (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) * inverse.toPoly.eval₂ ι θ = 1 := by
      simpa only [hconstant, eval₂_slope] using hi
    have hnext := corrected_matches_one_more ι (CPoly.fromCMvPolynomial Q) (ι center)
      P (specialize ι θ series) j hj hinit hmatch hsolution (inverse.toPoly.eval₂ ι θ) hi'
    have hnext' : Polynomial.X ^ (j + 1) ∣ P - specialize ι θ
        (appendCoefficient series j (liftCoefficient Q center modulus inverse series j)) := by
      rw [specialize_appendCoefficient, eval₂_liftCoefficient ι θ Q center modulus inverse
        series j hmonic hroot, specialize_residual]
      exact hnext
    simpa [liftSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (j + 1) (by omega) _ hnext'

/-- The computed series contains no coefficients beyond the requested lifting precision. -/
theorem degree_liftSteps_lt (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (modulus inverse : CPolynomial E)
    (steps j : ℕ) (series : Series E) (hdegree : (specialize ι θ series).degree < j) :
    (specialize ι θ (liftSteps Q center modulus inverse steps j series)).degree < j + steps := by
  induction steps generalizing j series with
  | zero => simpa [liftSteps] using hdegree
  | succ steps ih =>
    have hnext : (specialize ι θ
        (appendCoefficient series j (liftCoefficient Q center modulus inverse series j))).degree <
        j + 1 := by
      rw [specialize_appendCoefficient]
      apply (Polynomial.degree_add_le _ _).trans_lt
      apply max_lt
      · exact hdegree.trans (by exact_mod_cast Nat.lt_succ_self j)
      · exact (Polynomial.degree_C_mul_X_pow_le j _).trans_lt
          (by exact_mod_cast Nat.lt_succ_self j)
    simpa [liftSteps, add_assoc, add_comm, add_left_comm] using ih (j+1) _ hnext

/-- Coprimality of the initial slope and modulus makes the executable inverse guard succeed. -/
theorem regularLift_exists (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (modulus : CPolynomial E) (k : ℕ)
    (hcoprime : IsCoprime (slope Q center).toPoly modulus.toPoly) :
    ∃ out, regularLift? Q center modulus k = some out := by
  obtain ⟨inverse, hinverse⟩ :=
    (CPolynomial.inverseMod_exists_iff_coprime (slope Q center) modulus).mpr hcoprime
  refine ⟨liftSteps Q center modulus inverse (k - 1) 1
    (CPolynomial.C (CPolynomial.X : CPolynomial E)), ?_⟩
  unfold regularLift?
  rw [hinverse]
  rfl

/-- **Simultaneous branch correctness.** For every root `θ` of `h`, a successful lift equals
any polynomial solution of degree below `k` whose centered constant coefficient is `θ`.
The extension field appears only in this theorem; the program operates entirely on stored
polynomials over the coefficient field. -/
theorem regularLift_specializes (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (modulus : CPolynomial E)
    (hmonic : modulus.monic) (hroot : modulus.toPoly.eval₂ ι θ = 0)
    (k : ℕ) (hk : 0 < k) (out : Series E) (hrun : regularLift? Q center modulus k = some out)
    (P : Polynomial L) (hdegree : P.degree < k) (hconstant : P.coeff 0 = θ)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C (ι center), P] (CPoly.fromCMvPolynomial Q) = 0) :
    specialize ι θ out = P := by
  unfold regularLift? at hrun
  cases hinverse : CPolynomial.inverseMod? (slope Q center) modulus with
  | none => simp [hinverse] at hrun
  | some inverse =>
    rw [hinverse] at hrun
    change some (liftSteps Q center modulus inverse (k-1) 1
      (CPolynomial.C (CPolynomial.X : CPolynomial E))) = some out at hrun
    have hout := Option.some.inj hrun
    subst out
    have hstart : Polynomial.X ^ 1 ∣ P -
        specialize ι θ (CPolynomial.C (CPolynomial.X : CPolynomial E)) := by
      rw [pow_one, Polynomial.X_dvd_iff]
      rw [Polynomial.coeff_sub, specialize_C, CPolynomial.X_toPoly,
        Polynomial.eval₂_X, Polynomial.coeff_C_zero, hconstant, sub_self]
    have hmatches := liftSteps_matches ι θ Q center modulus inverse hmonic hroot hinverse P
      hsolution hconstant (k-1) 1 (by decide) _ hstart
    have houtdegree := degree_liftSteps_lt ι θ Q center modulus inverse (k-1) 1
      (CPolynomial.C (CPolynomial.X : CPolynomial E)) (by
        simp only [specialize_C, CPolynomial.X_toPoly, Polynomial.eval₂_X]
        exact Polynomial.degree_C_le.trans_lt (by decide))
    have hsum : 1 + (k - 1) = k := by omega
    rw [hsum] at hmatches
    have houtdegree' : (specialize ι θ
        (liftSteps Q center modulus inverse (k-1) 1
          (CPolynomial.C (CPolynomial.X : CPolynomial E)))).degree < k := by
      simpa only [← Nat.cast_add, hsum] using houtdegree
    ext j
    by_cases hj : j < k
    · have hcoeff := Polynomial.X_pow_dvd_iff.mp hmatches j hj
      exact (sub_eq_zero.mp (by simpa only [Polynomial.coeff_sub] using hcoeff)).symm
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (houtdegree'.trans_le (by exact_mod_cast Nat.le_of_not_gt hj)),
        Polynomial.coeff_eq_zero_of_degree_lt
          (hdegree.trans_le (by exact_mod_cast Nat.le_of_not_gt hj))]

end
end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
