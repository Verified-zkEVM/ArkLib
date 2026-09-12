/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.StoredField

/-!
# Executable univariate Euclid over a stored function field

These producers instantiate CompPoly's proved polynomial kernels with the
executable rational-function field. Their semantic target is `F(U)[V]`.
They do not implement multivariate gcd or polynomial-factor descent.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.FunctionFieldEuclid

open CompPoly CPolynomial StoredField

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Interpret a stored outer polynomial in the mathematical rational-function field. -/
noncomputable def value (p : CPolynomial (Carrier F)) : Polynomial (RatFunc F) :=
  p.toPoly.map valueHom

/-- The two storage layers preserve equality exactly. -/
theorem value_injective : Function.Injective (value (F := F)) := by
  intro p q h
  apply toPolyLinearEquiv.injective
  rw [toPolyLinearEquiv_apply, toPolyLinearEquiv_apply]
  exact Polynomial.map_injective _ StoredField.value_injective h

/-- Run monic Euclidean gcd with stored rational-function coefficient arithmetic. -/
def gcd (p q : CPolynomial (Carrier F)) : CPolynomial (Carrier F) := gcdMonic p q

open scoped Classical in
/-- The actual Euclidean producer computes the normalized gcd in `F(U)[V]`. -/
theorem value_gcd (p q : CPolynomial (Carrier F)) :
    value (gcd p q) = normalize (EuclideanDomain.gcd (value p) (value q)) := by
  classical
  unfold value gcd
  rw [gcdMonic_toPoly_eq_normalize_gcd, Polynomial.map_normalize, Polynomial.gcd_map]

/-- Checked exact division over stored rational-function coefficients. -/
def divide (p q : CPolynomial (Carrier F)) : Option (CPolynomial (Carrier F)) :=
  exactDivide p q

/-- Success of the executed division is equivalent to the semantic product identity
and a nonzero divisor. -/
theorem divide_eq_some_iff (p q r : CPolynomial (Carrier F)) :
    divide p q = some r ↔ q ≠ 0 ∧ value r * value q = value p := by
  rw [divide, exactDivide_eq_some_iff]
  refine and_congr_right fun _ => ?_
  have hm : value (r * q) = value r * value q := by
    simp only [value, toPoly_mul, Polynomial.map_mul]
  rw [← hm]
  exact value_injective.eq_iff.symm

end Polynomial.FunctionFieldAlgorithms.FunctionFieldEuclid
