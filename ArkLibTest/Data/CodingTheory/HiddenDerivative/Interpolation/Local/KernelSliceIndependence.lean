/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.KernelSliceIndependence

/-!
# Kernel slice independence acceptance tests

The lowest `T`-coefficient of the hidden error for `d = 1` and `d = 0`, the need for the
`T`-freeness hypothesis, injectivity of the family over `ℤ` for `d = 0`, and a concrete family
dimension.
-/

open MvPolynomial ReedSolomon.HiddenDerivative

/-- For `d = 1` the constant coefficient in `T` of `U - localJetSum 1` is `U - Y₁`. -/
example : localTCoefficient (R := ℚ) 1 0 (hiddenErrorFactor 1) = X none - X (some 0) :=
  localTCoefficient_zero_hiddenErrorFactor (by norm_num)

/-- For `d = 0` the hidden error is `U`, and its constant coefficient is still nonzero. -/
example : localTCoefficient (R := ℚ) 0 0 (hiddenErrorFactor 0) ≠ 0 :=
  localTCoefficient_zero_hiddenErrorFactor_ne_zero 0

/-- `T` has zero `T^0` coefficient, so `eq_zero_of_localTCoefficient_zero_eq_zero` needs its
support hypothesis. -/
example : localTCoefficient (R := ℚ) 1 0 (X (localT 1)) = 0 ∧
    (X (localT 1) : LocalPolynomial ℚ 1) ≠ 0 :=
  ⟨by simpa using localTCoefficient_X_localT_pow_mul (R := ℚ) (d := 1) 1 0 1, X_ne_zero _⟩

/-- For `d = 0`, over `ℤ`, the family map is injective. -/
example : Function.Injective (exhibitedKernelFamilyMap (R := ℤ) (d := 0) 2 1 0) :=
  exhibitedKernelFamilyMap_injective 2 1 0

/-- For `d = 1, m = 2, M = 1, W = 0` the slice at `r = 0` (threshold `2`) is zero and the slice
at `r = 1` (threshold `1`) is spanned by `1`. -/
example : Module.finrank ℚ (ExhibitedKernelFamilySource ℚ 1 2 1 0) = 1 := by
  rw [finrank_exhibitedKernelFamilySource (by norm_num)]
  decide
