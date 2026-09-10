/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Lifting.ExecutableRegularIteration
public import CompPoly.Univariate.ToPoly.Degree
/-!
# Executable primitives for regular differential lifting

An initial Hasse jet is stored as an explicit array of centered coefficients. Conversion to
Mathlib polynomials is used only to state its semantics. The executable constructor requires
effective equality on field elements and does not choose a polynomial from an existence proof.

The imported iteration kernel scans only next coefficients and performs a final residual and degree
filter. `RegularLiftCompleteness` proves its exact bounded-solution/initial-jet
specification and regular per-stage uniqueness by explicit representation bridges. Those results
do not yet give a closed operational implementation or a runtime bound for the lifting scan.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open Polynomial
open CompPoly

variable {F : Type*} [Field F] [DecidableEq F] {r : ℕ}

/-- Store the initial Hasse jet as a centered coefficient array, trimming trailing zeros. -/
def effectiveInitialPrefix (jet : Fin (r + 1) → F) : CPolynomial F :=
  CPolynomial.ofArray (Array.ofFn jet)

/-- Every supplied initial coefficient is preserved by the executable constructor. -/
theorem coeff_effectiveInitialPrefix (jet : Fin (r + 1) → F) (j : Fin (r + 1)) :
    CPolynomial.coeff (effectiveInitialPrefix jet) j.val = jet j := by
  rw [effectiveInitialPrefix, CPolynomial.coeff_ofArray]
  simp [Array.getD, j.isLt]

/-- The initial prefix contains no coefficients above the initial jet order. -/
theorem coeff_effectiveInitialPrefix_of_lt (jet : Fin (r + 1) → F) (i : ℕ)
    (hi : r < i) : CPolynomial.coeff (effectiveInitialPrefix jet) i = 0 := by
  rw [effectiveInitialPrefix, CPolynomial.coeff_ofArray]
  simp [Array.getD, show ¬ i < r + 1 by omega]

/-- The semantic initial prefix has degree at most the initial jet order. -/
theorem degree_effectiveInitialPrefix_toPoly_le (jet : Fin (r + 1) → F) :
    (effectiveInitialPrefix jet).toPoly.degree ≤ r := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro i hi
  rw [← CPolynomial.coeff_toPoly]
  exact coeff_effectiveInitialPrefix_of_lt jet i (by exact_mod_cast hi)

/-- Unshifting the executable initial prefix realizes the requested Hasse jet at any center. -/
theorem polynomialJet_taylor_effectiveInitialPrefix (center : F)
    (jet : Fin (r + 1) → F) :
    polynomialJet center (taylor (-center) (effectiveInitialPrefix jet).toPoly) = jet := by
  funext j
  change hasseCoeffAt center j.val
    (taylor (-center) (effectiveInitialPrefix jet).toPoly) = jet j
  rw [hasseCoeffAt_taylor, add_neg_cancel, hasseCoeffAt_zero_eq_coeff,
    ← CPolynomial.coeff_toPoly]
  exact coeff_effectiveInitialPrefix jet j

/-- A regular initial jet supplies the residual-divisibility invariant for the first lift. -/
theorem X_dvd_shiftedJetSubstitution_effectiveInitialPrefix
    (Q : DifferentialPolynomial F r) (center : F) (jet : Fin (r + 1) → F)
    (hregular : IsRegularJet Q (Fin.last r) center jet) :
    X ∣ shiftedJetSubstitution center
      (taylor (-center) (effectiveInitialPrefix jet).toPoly) Q := by
  rw [X_dvd_iff, coeff_zero_eq_eval_zero, ← taylor_differentialSpecialization,
    taylor_eval, zero_add, eval_differentialSpecialization,
    polynomialJet_taylor_effectiveInitialPrefix]
  exact hregular.1

end ReedSolomon.HiddenDerivative
