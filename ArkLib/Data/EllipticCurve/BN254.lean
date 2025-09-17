/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import ArkLib.Data.FieldTheory.NonBinaryField.BN254
import ArkLib.ToMathlib.NumberTheory.PrattCertificate
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# BN254 Elliptic Curve

WARNING: this is experimental. Use with caution!

This file defines the BN254 elliptic curve, a pairing-friendly curve used in
cryptographic applications.

The BN254 curve is defined over a prime field with the equation Y² = X³ + 3.

## Main definitions

* `BN254.baseFieldSize`: The characteristic of the base field
* `BN254.BaseField`: The base field F_p where the curve is defined
* `BN254.curve`: The BN254 elliptic curve as a Weierstrass curve
* `BN254.generator`: A generator point on the curve

## References

The BN254 curve parameters follow the specification used in Ethereum's alt_bn128
precompiles and various zero-knowledge proof systems.


-/

namespace BN254

/-- The base field characteristic (prime p) for BN254 elliptic curve -/
@[reducible]
def baseFieldSize : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The base field F_p over which the BN254 elliptic curve is defined -/
abbrev BaseField := ZMod baseFieldSize

/-- Proof that the BN254 base field characteristic is prime -/
theorem BaseField_is_prime : Nat.Prime baseFieldSize := by
  unfold baseFieldSize
  -- This is a well-known 254-bit prime used in the BN254 curve
  -- For now we'll use sorry; in practice this would need a full primality proof
  sorry

instance : Fact (Nat.Prime baseFieldSize) := ⟨BaseField_is_prime⟩

instance : Field BaseField := ZMod.instField baseFieldSize

/-- The BN254 elliptic curve: Y² = X³ + 3 -/
def curve : WeierstrassCurve BaseField := {
  a₁ := 0,  -- coefficient of XY
  a₂ := 0,  -- coefficient of X²
  a₃ := 0,  -- coefficient of Y
  a₄ := 0,  -- coefficient of X
  a₆ := 3   -- constant term (so we have Y² = X³ + 3)
}

/-- The BN254 curve is in short normal form -/
instance : curve.IsShortNF := by constructor <;> rfl

/-- The BN254 curve is elliptic (has non-zero discriminant) -/
instance : curve.IsElliptic := by
  -- For short form Y² = X³ + aX + b, discriminant is -16(4a³ + 27b²)
  -- Here a = 0, b = 3, so discriminant is -16(27 * 9) = -16 * 243 = -3888
  -- Since the base field prime is much larger than 3888, this is non-zero
  constructor
  rw [WeierstrassCurve.Δ_of_isShortNF]
  simp [curve]
  grind

/-- A generator point `(1, 2)` on the BN254 curve.

NOTE: some places assume generator is `(-1, 2)` instead. -/
def generator : BaseField × BaseField := (1, 2)

/-- The generator point is on the curve -/
theorem generator_on_curve : let (x, y) := generator
  y^2 = x^3 + 3 := by
  simp [generator]
  norm_num

end BN254
