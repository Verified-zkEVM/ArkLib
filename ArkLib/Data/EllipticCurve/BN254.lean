/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import CompPoly.Fields.BN254
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
  refine PrattCertificate'.out (p := baseFieldSize)
    ⟨3, by reduce_mod_char, ?_⟩
  refine .split
    [2, 3 ^ 2, 13, 29, 67, 229, 311, 983, 11003,
     405928799, 11465965001,
     13427688667394608761327070753331941386769]
    (fun r hr ↦ ?_) (by norm_num)
  simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr
    | hr | hr | hr | hr | hr | hr <;> rw [hr]
  · exact .prime 2 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 3 2 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 13 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 29 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 67 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 229 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 311 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 983 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 11003 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 405928799 1 _
      (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime 11465965001 1 _ ?_
      (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out
      ⟨3, by reduce_mod_char, ?_⟩
    refine .split [2 ^ 3, 5 ^ 4, 7, 327599]
      (fun r hr ↦ ?_) (by norm_num)
    simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr <;> rw [hr]
    · exact .prime 2 3 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 5 4 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 7 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 327599 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
  · refine .prime
      13427688667394608761327070753331941386769 1 _ ?_
      (by reduce_mod_char; decide) (by norm_num)
    refine PrattCertificate'.out
      ⟨17, by reduce_mod_char, ?_⟩
    refine .split
      [2 ^ 4, 3, 7, 11, 1853641, 4562087,
       173171039, 2480874801745591]
      (fun r hr ↦ ?_) (by norm_num)
    simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr
      | hr | hr | hr | hr <;> rw [hr]
    · exact .prime 2 4 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 3 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 7 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 11 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 1853641 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 4562087 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · exact .prime 173171039 1 _
        (by pratt) (by reduce_mod_char; decide) (by norm_num)
    · refine .prime 2480874801745591 1 _ ?_
        (by reduce_mod_char; decide) (by norm_num)
      refine PrattCertificate'.out
        ⟨11, by reduce_mod_char, ?_⟩
      refine .split
        [2, 3 ^ 2, 5, 19, 41, 35385462869]
        (fun r hr ↦ ?_) (by norm_num)
      simp only [Nat.reducePow, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with hr | hr | hr
        | hr | hr | hr <;> rw [hr]
      · exact .prime 2 1 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 3 2 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 5 1 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 19 1 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 41 1 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)
      · exact .prime 35385462869 1 _
          (by pratt) (by reduce_mod_char; decide) (by norm_num)

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
