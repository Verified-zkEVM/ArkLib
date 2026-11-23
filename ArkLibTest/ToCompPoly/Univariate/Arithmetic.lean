/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationBound
import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationCost
import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluation

/-!
# Measured polynomial arithmetic trust checks

These classic clients guard the literal arithmetic erasure and the exact or bounded profiles
of raw convolution, trimming, power-sum evaluation, and cached interpolation.
-/

/--
info: 'CompPoly.profileArithmetic_fst' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.profileArithmetic_fst

/--
info: 'CompPoly.Arithmetic.profileArithmetic_mulRaw' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_mulRaw

section Convolution
open CompPoly

variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

example (p q : CPolynomial.Raw F) (hp : p.size ≠ 0) :
    let cost := (profileArithmetic (Arithmetic.mulRaw p q)).2
    (cost .add, cost .mul, cost .coefficientRead, cost .metadata) =
      (p.size * q.size, p.size * q.size, 2 * (p.size * q.size),
        p.size * q.size + (q.size + p.size - 1) + 1) := by
  simp [Arithmetic.profileArithmetic_mulRaw, CPolynomial.Raw.size_mulRaw, hp]

end Convolution

/--
info: 'CompPoly.Arithmetic.profileArithmetic_trimRaw_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_trimRaw_le

/--
info: 'CompPoly.Arithmetic.profileArithmetic_evalRaw' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_evalRaw

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_inv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_inv

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_nodeRead' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_nodeRead

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_valueRead' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_valueRead

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_cubic_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_cubic_le

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_add_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_add_sub_le
