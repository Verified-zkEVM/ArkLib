import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point@
import ArkLib.Data.FieldTheory.NonBinaryField.BN254
import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
# BN254 Elliptic Curve

This file defines the BN254 elliptic curve, a pairing-friendly curve used in
cryptographic applications.

The BN254 curve is defined over a prime field with the equation Y² = X³ + 3.

## Main definitions

* `BN254.BASE_FIELD_CARD`: The characteristic of the base field
* `BN254.BaseField`: The base field F_p where the curve is defined
* `BN254.curve`: The BN254 elliptic curve as a Weierstrass curve
* `BN254.generator`: A generator point on the curve
* `BN254.Point`: Points on the elliptic curve (finite points and point at infinity)
* `BN254.Point.add`: Point addition operation
* `BN254.Point.smul`: Scalar multiplication
* `BN254.Point.isValid`: Point validation function

## References

The BN254 curve parameters follow the specification used in Ethereum's alt_bn128
precompiles and various zero-knowledge proof systems.

-/

namespace BN254

/-- The base field characteristic (prime p) for BN254 elliptic curve -/
@[reducible]
def BASE_FIELD_CARD : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The base field F_p over which the BN254 elliptic curve is defined -/
abbrev BaseField := ZMod BASE_FIELD_CARD

/-- Proof that the BN254 base field characteristic is prime -/
theorem BaseField_is_prime : Nat.Prime BASE_FIELD_CARD := by
  unfold BASE_FIELD_CARD
  -- This is a well-known 254-bit prime used in the BN254 curve
  -- For now we'll use sorry; in practice this would need a full primality proof
  sorry

instance : Fact (Nat.Prime BASE_FIELD_CARD) := ⟨BaseField_is_prime⟩

instance : Field BaseField := ZMod.instField BASE_FIELD_CARD

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

/-- A generator point on the BN254 curve -/
def generator : BaseField × BaseField := (1, 2)

/-- The generator point is on the curve -/
theorem generator_on_curve : let (x, y) := generator
  y^2 = x^3 + 3 := by
  simp [generator]
  norm_num

/-! ## Point Arithmetic -/

/-- Points on the BN254 elliptic curve -/
inductive Point where
  /-- The point at infinity (identity element) -/
  | infinity : Point
  /-- A finite point with coordinates (x, y) -/
  | finite : BaseField → BaseField → Point

namespace Point

/-- Check if a point is the point at infinity -/
def isInfinity : Point → Bool
  | infinity => true
  | finite _ _ => false

/-- Check if coordinates are on the curve: y² = x³ + 3 -/
def onCurve (x y : BaseField) : Prop := y^2 = x^3 + 3

/-- Check if a point is valid (either infinity or on the curve) -/
def isValid : Point → Prop
  | infinity => True
  | finite x y => onCurve x y

/-- Convert the generator to a Point -/
def generatorPoint : Point := finite generator.1 generator.2

/-- The generator point is valid -/
theorem generatorPoint_valid : isValid generatorPoint := by
  simp [generatorPoint, isValid, onCurve, generator]
  norm_num

/-- Point negation -/
def neg : Point → Point
  | infinity => infinity
  | finite x y => finite x (-y)

/-- Point addition on the BN254 curve. TODO: verify for correctness and performance. -/
def add : Point → Point → Point
  | infinity, P => P
  | P, infinity => P
  | finite x₁ y₁, finite x₂ y₂ =>
    if x₁ = x₂ then
      if y₁ = y₂ then
        -- Point doubling: P + P
        if y₁ = 0 then infinity
        else
          let s := (3 * x₁^2) / (2 * y₁)  -- slope for tangent
          let x₃ := s^2 - 2 * x₁
          let y₃ := s * (x₁ - x₃) - y₁
          finite x₃ y₃
      else
        -- Points are inverses: P + (-P) = O
        infinity
    else
      -- General addition: P + Q where P ≠ Q
      let s := (y₂ - y₁) / (x₂ - x₁)  -- slope of line through P and Q
      let x₃ := s^2 - x₁ - x₂
      let y₃ := s * (x₁ - x₃) - y₁
      finite x₃ y₃

/-- Point equality is decidable -/
instance (P Q : Point) : Decidable (P = Q) := by
  cases P <;> cases Q <;> simp [Point.finite.injEq] <;> infer_instance

/-- Scalar multiplication using double-and-add algorithm.
TODO: verify for correctness and performance. -/
def nsmul : Nat → Point → Point
  | 0, _ => infinity
  | 1, P => P
  | n + 2, P =>
    if (n + 2) % 2 = 0 then
      nsmul ((n + 2) / 2) (add P P)  -- double the point, halve the scalar
    else
      add P (nsmul (n + 1) P)  -- subtract 1 from scalar, add point

/-- Scalar multiplication for integers -/
def zsmul : Int → Point → Point
  | Int.ofNat n, P => nsmul n P
  | Int.negSucc n, P => neg (nsmul (n + 1) P)

end Point

/-! ## Group Structure -/

/-- Addition operation for the group structure -/
instance : Add Point := ⟨Point.add⟩

/-- Zero element (point at infinity) -/
instance : Zero Point := ⟨Point.infinity⟩

/-- Negation operation -/
instance : Neg Point := ⟨Point.neg⟩

/-- Scalar multiplication by natural numbers -/
instance : SMul Nat Point := ⟨Point.nsmul⟩

/-- Scalar multiplication by integers -/
instance : SMul Int Point := ⟨Point.zsmul⟩

/-- The BN254 points form an additive commutive group -/
instance : AddCommGroup Point where
  add := (· + ·)
  add_assoc := by sorry  -- Elliptic curve addition is associative
  zero := 0
  zero_add := by sorry  -- 0 + P = P (point at infinity is identity)
  add_zero := by sorry  -- P + 0 = P
  neg := (- ·)
  neg_add_cancel := by sorry  -- (-P) + P = 0
  add_comm := by sorry  -- P + Q = Q + P
  nsmul := BN254.Point.nsmul
  zsmul := BN254.Point.zsmul
  nsmul_zero := by sorry
  nsmul_succ := by sorry
  zsmul_zero' := by sorry
  zsmul_succ' := by sorry

/-! ## Examples -/

example : Point.generatorPoint + Point.generatorPoint =
  Point.add Point.generatorPoint Point.generatorPoint := rfl

-- example : (2 : Nat) • Point.generatorPoint =
--   Point.generatorPoint + Point.generatorPoint := by
--   simp [HSMul.hSMul, Point.nsmul]

example : Point.isValid Point.generatorPoint = true := by
  simp [Point.generatorPoint_valid]

end BN254
