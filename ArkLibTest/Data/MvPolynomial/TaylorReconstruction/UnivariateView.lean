/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
import Mathlib.Data.ZMod.Basic

/-! Mixed coefficient variables, the final-variable convention, and exact finite-field data. -/

open CPoly CPoly.CMvPolynomial CPoly.TaylorReconstruction CompPoly

namespace UnivariateViewTests

/-- Execute both representation conversions and inspect the resulting coefficient polynomials. -/
def run : IO Unit := do
  let t₀ : CMvPolynomial 3 ℤ := X 0
  let t₁ : CMvPolynomial 3 ℤ := X 1
  let z : CMvPolynomial 3 ℤ := X 2
  let p := t₀ * t₁ * z ^ 2 + 3 * t₁ * z + 5
  let q := splitLast p
  unless q.coeff 2 == (X 0 * X 1 : CMvPolynomial 2 ℤ) &&
      q.coeff 1 == (3 * X 1 : CMvPolynomial 2 ℤ) && q.coeff 0 == 5 && q.coeff 3 == 0 do
    throw (IO.userError "last-variable split changed coefficient variables or powers")
  unless flattenLast q == p do
    throw (IO.userError "flat-to-univariate roundtrip changed stored polynomial")
  let nested : CPolynomial (CMvPolynomial 2 ℤ) :=
    CPolynomial.C (X 0) + CPolynomial.X ^ 3 * CPolynomial.C (X 1 + 1)
  unless flattenLast nested == t₀ + z ^ 3 * (t₁ + 1) do
    throw (IO.userError "univariate flattening used the wrong flat variable")
  unless splitLast (flattenLast nested) == nested do
    throw (IO.userError "univariate-to-flat roundtrip changed stored coefficients")
  let single : CMvPolynomial 1 ℤ := X 0 ^ 3 + C 2
  let singleView := splitLast single
  unless singleView.coeff 0 == (C 2 : CMvPolynomial 0 ℤ) &&
      singleView.coeff 3 == 1 && flattenLast singleView == single do
    throw (IO.userError "zero-free-variable adapter failed")
  -- This nonzero polynomial evaluates to zero at every element of its coefficient field.
  let vanishes : CMvPolynomial 1 (ZMod 2) := X 0 ^ 2 - X 0
  unless vanishes != 0 && (splitLast vanishes).coeff 2 == 1 &&
      flattenLast (splitLast vanishes) == vanishes do
    throw (IO.userError "adapter preserved finite-field values but lost polynomial data")
  unless (splitLast (0 : CMvPolynomial 3 ℤ)) == 0 do
    throw (IO.userError "zero polynomial acquired a nonzero univariate representation")

end UnivariateViewTests
