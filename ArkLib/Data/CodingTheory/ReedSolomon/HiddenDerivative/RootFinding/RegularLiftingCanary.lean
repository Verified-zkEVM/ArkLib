/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.RegularLifting
import Mathlib.Algebra.Field.ZMod

/-!
# Canaries for regular coefficient lifting

These examples exercise the sharp positive-characteristic boundary in Kopparty's regular
one-step lift.  In characteristic two, the step `k = r = 1` has multiplier
`choose (k + r) r = choose 2 1 = 0`.  For the equation `Y₁ = 0`, both coefficients of the
centered quadratic lift solve the equation, so the nonresonance (or below-characteristic)
hypothesis cannot be dropped.
-/

namespace ReedSolomon.HiddenDerivative

open Polynomial

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The boundary equation asks for the first Hasse derivative to vanish. -/
private def characteristicTwoBoundaryEquation : DifferentialPolynomial (ZMod 2) 1 :=
  MvPolynomial.X (some (Fin.last 1))

/-- At the first excluded degree, the binomial slope vanishes. -/
example : (((1 + 1).choose 1 : ℕ) : ZMod 2) = 0 := by
  decide

/-- Every quadratic lift coefficient satisfies the boundary equation in characteristic two. -/
example (gamma : ZMod 2) :
    shiftedJetSubstitution 0 (regularLiftCandidate 0 gamma 1 1 0)
      characteristicTwoBoundaryEquation = 0 := by
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  simp [characteristicTwoBoundaryEquation, shiftedJetSubstitution, regularLiftCandidate,
    hassePerturbation, htwo]

/-- Consequently the two field elements give distinct candidates with the same zero residual. -/
example :
    regularLiftCandidate 0 (0 : ZMod 2) 1 1 0 ≠
      regularLiftCandidate 0 (1 : ZMod 2) 1 1 0 ∧
    shiftedJetSubstitution 0 (regularLiftCandidate 0 (0 : ZMod 2) 1 1 0)
        characteristicTwoBoundaryEquation = 0 ∧
    shiftedJetSubstitution 0 (regularLiftCandidate 0 (1 : ZMod 2) 1 1 0)
        characteristicTwoBoundaryEquation = 0 := by
  constructor
  · intro h
    have hcoeff := congrArg (fun p : (ZMod 2)[X] => p.coeff 2) h
    simp [regularLiftCandidate, hassePerturbation] at hcoeff
  · have htwo : (1 + 1 : ZMod 2) = 0 := by decide
    constructor <;>
      simp [characteristicTwoBoundaryEquation, shiftedJetSubstitution, regularLiftCandidate,
        hassePerturbation, htwo]

/-! The next example checks the sign and multiplier on a nonresonant step. -/

/-- Over `ZMod 5`, the equation `Y₁ - X = 0` forces the quadratic lift coefficient. -/
private def characteristicFiveRegularEquation : DifferentialPolynomial (ZMod 5) 1 :=
  MvPolynomial.X (some (Fin.last 1)) - MvPolynomial.X none

/-- The direct residual law is `(2 * gamma - 1) * X`. -/
private theorem characteristicFive_residual (gamma : ZMod 5) :
    shiftedJetSubstitution 0 (regularLiftCandidate 0 gamma 1 1 0)
      characteristicFiveRegularEquation = C (2 * gamma - 1) * X := by
  simp [characteristicFiveRegularEquation, shiftedJetSubstitution, regularLiftCandidate,
    hassePerturbation]
  simp only [map_ofNat]
  ring

/-- Hence `gamma = 3` is the unique lift coefficient and makes the complete residual zero. -/
example :
    shiftedJetSubstitution 0 (regularLiftCandidate 0 (3 : ZMod 5) 1 1 0)
      characteristicFiveRegularEquation = 0 ∧
    ∀ gamma : ZMod 5,
      shiftedJetSubstitution 0 (regularLiftCandidate 0 gamma 1 1 0)
        characteristicFiveRegularEquation = 0 → gamma = 3 := by
  constructor
  · rw [characteristicFive_residual]
    norm_num
    exact ZMod.natCast_self 5
  · intro gamma hgamma
    rw [characteristicFive_residual] at hgamma
    have hcoeff := congrArg (fun p : (ZMod 5)[X] => p.coeff 1) hgamma
    simp only [coeff_mul_X, coeff_C, coeff_zero] at hcoeff
    apply mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0)
    calc
      2 * gamma = 1 := sub_eq_zero.mp hcoeff
      _ = 2 * 3 := by decide

end

end ReedSolomon.HiddenDerivative
