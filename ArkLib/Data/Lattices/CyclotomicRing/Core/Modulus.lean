/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ToCompPoly.Univariate.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Cyclotomic Moduli over `CPolynomial`

This file defines the modulus data that turns a computable polynomial type
`CompPoly.CPolynomial R` into the cyclotomic ring `R[X] / (Φ_m)`.

Because Mathlib's `Polynomial.cyclotomic` is *noncomputable* (it routes through
roots of unity in `ℂ`), we cannot build the modulus by evaluating `cyclotomic`.
Instead a `CyclotomicModulus` bundles an *explicit* computable polynomial
`φ : CPolynomial R` (e.g. `X^d + 1`) together with

* a proof that `φ` is monic (needed for CompPoly's `modByMonic`-based reduction),
* its `conductor` `m`, and
* a proof linking it to the genuine cyclotomic polynomial,
  `φ.toPoly = Polynomial.cyclotomic m R`.

The canonical Hachi [NOZ26] instantiation is the power-of-two cyclotomic
`φ = X^{2^α} + 1`, of conductor `2^{α+1}`, provided as `powTwoCyclotomic`.

To keep the executable layer free of any noncomputable contamination, the data
and the proofs are kept in **separate** structures:

* `CyclotomicModulus R` is *pure computable data* (`φ`, `conductor`); reduction,
  multiplication and the vector/matrix operations depend only on it, so the
  canonical Hachi instance is fully `#eval`-able.
* `IsCyclotomic Φ` is a `Prop`-class bundling the two proof obligations
  (`monic`, `isCyclotomic`); only the (noncomputable) semantic bridge needs it.

## Main definitions

* `CyclotomicModulus R` — the computable modulus data.
* `IsCyclotomic Φ` — the cyclotomic-correctness proofs for a modulus.
* `CyclotomicModulus.powTwoCyclotomic α` — the Hachi modulus `X^{2^α} + 1`
  (computable), with its `IsCyclotomic` instance.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open Polynomial

namespace CompPoly.CPolynomial

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- `CPolynomial.X.toPoly = Polynomial.X`. -/
@[simp] theorem toPoly_X : (CPolynomial.X : CPolynomial R).toPoly = Polynomial.X := by
  unfold CPolynomial.toPoly; exact Raw.toPoly_X

end CompPoly.CPolynomial

namespace ArkLib.Lattices

open CompPoly CompPoly.CPolynomial

/-- Computable data describing a cyclotomic modulus for the polynomial ring over
`R`: an explicit, computable polynomial `φ : CPolynomial R` (e.g. `X^d + 1`)
together with its conductor `m`. This structure carries *no proofs*, so the
reduction and ring operations built on it (`reduce`, `mul`, `matVecMul`, …) stay
fully computable. The cyclotomic-correctness proofs live separately in
`IsCyclotomic`. -/
structure CyclotomicModulus (R : Type*) [Field R] [BEq R] [LawfulBEq R] where
  /-- The explicit computable modulus polynomial, e.g. `X^d + 1`. -/
  φ : CPolynomial R
  /-- The conductor `m`: `φ` is the `m`-th cyclotomic polynomial. -/
  conductor : ℕ

/-- Cyclotomic-correctness proofs for a modulus `Φ`: that `φ` is monic (so
CompPoly's `modByMonic` reduction applies) and that, as a Mathlib polynomial,
`φ` is the `conductor`-th cyclotomic polynomial (so the reduced ring really is
`R[X] / (Φ_m)`). A `Prop`-class, supplied by instance resolution to the
semantic bridge without touching the executable layer. -/
class IsCyclotomic {R : Type*} [Field R] [BEq R] [LawfulBEq R]
    (Φ : CyclotomicModulus R) : Prop where
  /-- `φ` is monic. -/
  monic : Φ.φ.toPoly.Monic
  /-- `φ` is, as a Mathlib polynomial, the `conductor`-th cyclotomic polynomial. -/
  isCyclotomic : Φ.φ.toPoly = Polynomial.cyclotomic Φ.conductor R

namespace CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-- The power-of-two cyclotomic modulus `φ = X^{2^α} + 1`, the
cyclotomic polynomial of conductor `2^{α+1}`. This is the ring of integers of
the `2^{α+1}`-th cyclotomic field, used as `R_q := Z_q[X] / (X^d + 1)` with
`d = 2^α` throughout lattice-based proof systems. Computable: the operations
built on it can be `#eval`-ed. -/
def powTwoCyclotomic (α : ℕ) : CyclotomicModulus R where
  φ := CPolynomial.X ^ (2 ^ α) + 1
  conductor := 2 ^ (α + 1)

/-- The modulus `X^{2^α} + 1` is the `2^{α+1}`-th cyclotomic polynomial. -/
instance powTwoCyclotomic_isCyclotomic (α : ℕ) :
    IsCyclotomic (powTwoCyclotomic (R := R) α) where
  monic := by
    have hX : (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly
        = Polynomial.X ^ (2 ^ α) + 1 := by
      rw [toPoly_add, toPoly_pow, toPoly_X, toPoly_one]
    change (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly.Monic
    rw [hX, ← Polynomial.C_1]
    exact monic_X_pow_add_C (1 : R) (pow_ne_zero α two_ne_zero)
  isCyclotomic := by
    have hX : (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly
        = Polynomial.X ^ (2 ^ α) + 1 := by
      rw [toPoly_add, toPoly_pow, toPoly_X, toPoly_one]
    change (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly
      = Polynomial.cyclotomic (2 ^ (α + 1)) R
    rw [hX, cyclotomic_prime_pow_eq_geom_sum (R := R) (p := 2) (n := α) Nat.prime_two]
    rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, _root_.add_comm]

/-- The power-of-two modulus, as a Mathlib polynomial, is `X^{2^α} + 1`. -/
theorem powTwoCyclotomic_toPoly (α : ℕ) :
    (powTwoCyclotomic (R := R) α).φ.toPoly = Polynomial.X ^ (2 ^ α) + 1 := by
  change (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial R).toPoly = _
  rw [toPoly_add, toPoly_pow, toPoly_X, toPoly_one]

/-- The ring dimension: `natDegree` of the power-of-two modulus is `2^α`. -/
theorem powTwoCyclotomic_natDegree (α : ℕ) :
    (powTwoCyclotomic (R := R) α).φ.natDegree = 2 ^ α := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, powTwoCyclotomic_toPoly,
    show (Polynomial.X ^ 2 ^ α + 1 : Polynomial R) = Polynomial.X ^ 2 ^ α + Polynomial.C 1 by
      rw [Polynomial.C_1], Polynomial.natDegree_X_pow_add_C]

end CyclotomicModulus

end ArkLib.Lattices
