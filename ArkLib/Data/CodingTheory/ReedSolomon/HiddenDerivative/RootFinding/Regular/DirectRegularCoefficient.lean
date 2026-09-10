/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.Completeness
/-!
# Direct regular coefficient solving

The next residual coefficient is affine for positive lift order. Evaluating it at zero and one
recovers its intercept and slope, so a nonzero slope gives the unique coefficient by division.
The executable solver requires no finite-field enumeration. `none` means that this nonzero-slope
method is unavailable, not that the equation has no solutions.

This is a functional optimization of the exhaustive scan. The concrete residual evaluations still
use polynomial operations whose closed operational cost adequacy is open. No runtime or total
field-operation bound is claimed here.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open CompPoly

variable {F : Type*} [Field F] [DecidableEq F] {r : ℕ}

/-- The residual coefficient at zero increment. -/
def effectiveRegularIntercept (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) : F := effectiveResidualCoeff Q center P k 0

/-- Recover the affine slope from two concrete residual evaluations. -/
def effectiveRegularSlope (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) : F :=
  effectiveResidualCoeff Q center P k 1 - effectiveRegularIntercept Q center P k

/-- Solve a nonzero-slope affine residual. The intercept is shared between the slope and quotient,
so the definition invokes exactly two residual evaluations, independently of field cardinality. -/
def effectiveDirectRegularCoefficient (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) : Option F :=
  let beta := effectiveResidualCoeff Q center P k 0
  let slope := effectiveResidualCoeff Q center P k 1 - beta
  if slope = 0 then none else some (-beta / slope)

private theorem effectiveResidualCoeff_affine_semantic
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (k : ℕ) (hk : 0 < k) (gamma : F) :
    effectiveResidualCoeff Q center P k gamma =
      (shiftedJetSubstitution center (unshift center P) (semanticEquation Q)).coeff k +
        (((k + r).choose r : F) * gamma) *
          jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
            (polynomialJet center (unshift center P)) := by
  rw [effectiveResidualCoeff, CPolynomial.coeff_toPoly, effectiveResidual_toPoly,
    unshift_effectiveRegularCandidate]
  exact coeff_shiftedJetSubstitution_regularLiftCandidate hk _ _ _ _

/-- The recovered slope is the actual binomial-times-separant coefficient. -/
theorem effectiveRegularSlope_eq (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) (hk : 0 < k) :
    effectiveRegularSlope Q center P k = ((k + r).choose r : F) *
      jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
        (polynomialJet center (unshift center P)) := by
  rw [effectiveRegularSlope, effectiveRegularIntercept,
    effectiveResidualCoeff_affine_semantic Q center P k hk 1,
    effectiveResidualCoeff_affine_semantic Q center P k hk 0]
  ring

/-- Positive residual order is the only hypothesis needed for the affine identity. -/
theorem effectiveResidualCoeff_affine (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CPolynomial F) (k : ℕ) (hk : 0 < k) (gamma : F) :
    effectiveResidualCoeff Q center P k gamma = effectiveRegularIntercept Q center P k +
      effectiveRegularSlope Q center P k * gamma := by
  rw [effectiveRegularIntercept, effectiveRegularSlope_eq Q center P k hk,
    effectiveResidualCoeff_affine_semantic Q center P k hk gamma,
    effectiveResidualCoeff_affine_semantic Q center P k hk 0]
  ring

/-- `none` reports a zero slope, including the case where every coefficient is a solution. -/
theorem effectiveDirectRegularCoefficient_eq_none_iff
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) (k : ℕ) :
    effectiveDirectRegularCoefficient Q center P k = none ↔
      effectiveRegularSlope Q center P k = 0 := by
  simp [effectiveDirectRegularCoefficient, effectiveRegularSlope, effectiveRegularIntercept]

/-- A returned value is exactly the nonzero-slope quotient. -/
theorem effectiveDirectRegularCoefficient_eq_some_iff
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F) (k : ℕ) (gamma : F) :
    effectiveDirectRegularCoefficient Q center P k = some gamma ↔
      effectiveRegularSlope Q center P k ≠ 0 ∧
        -effectiveRegularIntercept Q center P k / effectiveRegularSlope Q center P k = gamma := by
  simp [effectiveDirectRegularCoefficient, effectiveRegularSlope, effectiveRegularIntercept]

/-- Every returned coefficient annihilates the next residual coefficient, and is its unique root. -/
theorem effectiveDirectRegularCoefficient_sound_unique
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (k : ℕ) (hk : 0 < k) (gamma : F)
    (hgamma : effectiveDirectRegularCoefficient Q center P k = some gamma) :
    effectiveResidualCoeff Q center P k gamma = 0 ∧
      ∀ other : F, effectiveResidualCoeff Q center P k other = 0 → other = gamma := by
  obtain ⟨hslope, hquot⟩ :=
    (effectiveDirectRegularCoefficient_eq_some_iff Q center P k gamma).mp hgamma
  have hzero : effectiveRegularIntercept Q center P k +
      effectiveRegularSlope Q center P k * gamma = 0 := by
    rw [← hquot]
    field_simp
    ring
  constructor
  · rw [effectiveResidualCoeff_affine Q center P k hk gamma]
    exact hzero
  · intro other hother
    rw [effectiveResidualCoeff_affine Q center P k hk other] at hother
    apply (mul_left_cancel₀ hslope)
    exact add_left_cancel (hother.trans hzero.symm)

/-- Over a finite field the direct result equals the entire exhaustive coefficient scan. -/
theorem effectiveRegularCoefficients_eq_singleton_of_direct [Fintype F]
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (k : ℕ) (hk : 0 < k) (gamma : F)
    (hgamma : effectiveDirectRegularCoefficient Q center P k = some gamma) :
    effectiveRegularCoefficients Q center P k = {gamma} := by
  obtain ⟨hzero, hunique⟩ :=
    effectiveDirectRegularCoefficient_sound_unique Q center P k hk gamma hgamma
  ext other
  rw [mem_effectiveRegularCoefficients, Finset.mem_singleton]
  exact ⟨hunique other, fun h ↦ h ▸ hzero⟩

/-- A nonzero separant and a degree below the characteristic guarantee a nonzero affine slope. -/
theorem effectiveRegularSlope_ne_zero_of_regular
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (k D : ℕ) (hk : 0 < k) (hdegree : k + r ≤ D) (hD : D < ringChar F)
    (hsep : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center (unshift center P)) ≠ 0) :
    effectiveRegularSlope Q center P k ≠ 0 := by
  rw [effectiveRegularSlope_eq Q center P k hk]
  exact mul_ne_zero
    (Polynomial.natCast_choose_ne_zero_of_lt_ringChar (hdegree.trans_lt hD) (by omega)) hsep

/-- Every regular surviving prefix has an available direct solve at the next permitted degree. -/
theorem effectiveDirectRegularCoefficient_exists_of_survivor [Fintype F]
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet (semanticEquation Q) (Fin.last r) center jet)
    (D steps : ℕ) (hdegree : steps + 1 + r ≤ D) (hD : D < ringChar F)
    (P : CPolynomial F)
    (hP : P ∈ (effectiveRegularIteration Q center (effectiveInitialPrefix jet) steps).candidates) :
    ∃ gamma, effectiveDirectRegularCoefficient Q center P (steps + 1) = some gamma ∧
      effectiveRegularCoefficients Q center P (steps + 1) = {gamma} := by
  have hjet := effectiveRegularIteration_polynomialJet Q center jet steps hP
  have hslope := effectiveRegularSlope_ne_zero_of_regular Q center P (steps + 1) D
    (Nat.succ_pos steps) hdegree hD (by rw [hjet]; exact hregular.2)
  have hsome : effectiveDirectRegularCoefficient Q center P (steps + 1) =
      some (-effectiveRegularIntercept Q center P (steps + 1) /
        effectiveRegularSlope Q center P (steps + 1)) :=
    (effectiveDirectRegularCoefficient_eq_some_iff _ _ _ _ _).mpr ⟨hslope, rfl⟩
  exact ⟨_, hsome, effectiveRegularCoefficients_eq_singleton_of_direct Q center P
    (steps + 1) (Nat.succ_pos steps) _ hsome⟩

end ReedSolomon.HiddenDerivative
