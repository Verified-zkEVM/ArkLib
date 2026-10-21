/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluation

/-!
# Evaluation profile envelopes

The bounds apply to the explicitly instrumented coefficient power sum. Coefficient reads and
control ticks are counted separately from field additions and multiplications.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

/-- Coordinate bounds for power-sum evaluation of an array of at most `m` coefficients. -/
def evaluationProfileBound (m : ℕ) : ArithmeticCostKind → ℕ
  | .add | .coefficientRead => m
  | .mul => m ^ 2
  | .metadata => m ^ 2 + m + 1
  | _ => 0

/-- Every coordinate of coefficient evaluation obeys its explicit array-length envelope. -/
theorem profileArithmetic_evalRaw_apply_le (p : CPolynomial.Raw F) (x : F) (m : ℕ)
    (hsize : p.size ≤ m) (kind : ArithmeticCostKind) :
    (profileArithmetic (evalRaw p x)).2 kind ≤ evaluationProfileBound m kind := by
  have hmul := profileArithmetic_evalRaw_mul_le p x
  have hsq := Nat.pow_le_pow_left hsize 2
  cases kind <;> simp [profileArithmetic_evalRaw, evaluationProfileBound] at hmul ⊢ <;> omega

end CompPoly.Arithmetic
