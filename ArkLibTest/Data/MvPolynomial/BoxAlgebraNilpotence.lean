/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoxAlgebraNilpotence

/-! Whole-kernel nilpotence and surviving mixed-parameter regression cases. -/

namespace BoxAlgebraNilpotenceTests

open CPoly CPoly.BoxAlgebra

private abbrev A := Carrier 2 2 ℤ
private def residual : A := eps 0 + eps 1

example : parameterIdeal (r := 2) (N := 2) (R := ℤ) ^ 3 = ⊥ :=
  parameterIdeal_pow (by decide)

example : residual ^ 3 = 0 := by
  apply pow_eq_zero_of_constantValue_eq_zero (by decide)
  change constantSpecialization (by decide) (eps 0 + eps 1 : A) = 0
  simp

example (p : A) (hp : constantSpecialization (by decide) p = 0) : p ^ 3 = 0 :=
  pow_eq_zero_of_constantValue_eq_zero (by decide) p hp

example : parameterIdeal (r := 0) (N := 2) (R := ℤ) = ⊥ := by
  simpa using (parameterIdeal_pow (r := 0) (R := ℤ) (N := 2) (by decide))

example : parameterIdeal (r := 3) (N := 1) (R := ℤ) = ⊥ := by
  simpa using (parameterIdeal_pow (r := 3) (R := ℤ) (N := 1) (by decide))

/-- Execute the residual whose square survives but whose cube vanishes. -/
def run : IO Unit := do
  unless residual ^ 2 != 0 do
    throw (IO.userError "mixed residual incorrectly annihilated at coordinate precision")
  unless (residual ^ 2).val.coeff #m[1, 1] == 2 do
    throw (IO.userError "mixed residual square lost its coefficient")
  unless residual ^ 3 == 0 do
    throw (IO.userError "mixed residual survives whole-kernel exponent")
  unless constantSpecialization (by decide) residual == 0 do
    throw (IO.userError "parameter specialization is nonzero")
  unless constantSpecialization (by decide) ((7 : A) + residual) == 7 do
    throw (IO.userError "constant specialization lost its constant")
  unless constantSpecialization (by decide) (((3 : A) + residual) * (5 + eps 0)) == 15 do
    throw (IO.userError "constant specialization failed multiplicativity")

#print axioms CPoly.BoxAlgebra.parameterIdeal_pow
#print axioms CPoly.BoxAlgebra.ker_constantSpecialization
#print axioms CPoly.BoxAlgebra.constantSpecialization_ker_pow

end BoxAlgebraNilpotenceTests
