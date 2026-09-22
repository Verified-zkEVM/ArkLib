/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import CompPoly.Multivariate.Eval

/-!
# Ring-operation bridges for computable multivariate polynomials

Re-export CompPoly's bundled evaluation and finite-sum/product API and provide explicit
ring-homomorphism equations for converting ring operations to `MvPolynomial`.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `fromCMvPolynomial` commutes with addition, in `HAdd` notation. CompPoly's own `CPoly.map_add`
is stated at `Add.add`, which `rw` will not match against a `+` written by the elaborator. -/
theorem fromCMvPolynomial_add' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p + q) = fromCMvPolynomial p + fromCMvPolynomial q :=
  _root_.map_add (polyRingEquiv (n := n) (R := R)) p q

/-- `fromCMvPolynomial` commutes with multiplication, in `HMul` notation. -/
theorem fromCMvPolynomial_mul' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p * q) = fromCMvPolynomial p * fromCMvPolynomial q :=
  _root_.map_mul (polyRingEquiv (n := n) (R := R)) p q

/-- `fromCMvPolynomial` sends `1` to `1`. -/
theorem fromCMvPolynomial_one' :
    fromCMvPolynomial (1 : CMvPolynomial n R) = 1 :=
  _root_.map_one (polyRingEquiv (n := n) (R := R))

end CPoly.CMvPolynomial

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- `fromCMvPolynomial` commutes with subtraction, in `HSub` notation. -/
theorem fromCMvPolynomial_sub' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p - q) = fromCMvPolynomial p - fromCMvPolynomial q :=
  _root_.map_sub (polyRingEquiv (n := n) (R := R)) p q

end CPoly.CMvPolynomial
