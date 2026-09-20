/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import CompPoly.Multivariate.Eval
public import CompPoly.Multivariate.MvPolyEquiv.Instances
public import CompPoly.Multivariate.Operations

/-!
  # Transporting computable multivariate polynomials along ring operations

  Additions to `CompPoly.Multivariate.MvPolyEquiv`, not yet upstreamed to CompPoly.

  A statement about *degrees* is not determined by values (two distinct polynomials agree
  everywhere over a finite field), so it has to cross the representation boundary at the level of
  the polynomial itself, through `fromCMvPolynomial`. That map is the forward direction of
  `polyRingEquiv`, hence a ring homomorphism. CompPoly states its compatibility with the ring
  operations at `Add.add` / `Mul.mul`, which `rw` will not match against a `+` or `*` written by
  the elaborator; the primed forms below are stated in `HAdd` / `HMul` / `HSub` notation.

  These are the lemmas the Hachi sumcheck summands need
  (`Commitments/Functional/Hachi/ZeroCheck/Constraints.lean`).
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `fromCMvPolynomial` commutes with addition, in `HAdd` notation. -/
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
