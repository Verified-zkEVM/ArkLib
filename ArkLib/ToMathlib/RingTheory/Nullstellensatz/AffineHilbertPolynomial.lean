/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient

/-!
# Zero-dimensional point counts and the affine Hilbert polynomial

Let `k` be a field, `σ` a finite type and `I` an ideal of `MvPolynomial σ k` whose quotient is
finite-dimensional over `k`. Over every field extension `K` of `k`, the zero locus of `I` has at
most `(affineHilbertPolynomial I).coeff 0` points. The affine Hilbert polynomial of such an ideal
is the constant `Module.finrank k (MvPolynomial σ k ⧸ I)`
(`MvPolynomial.affineHilbertPolynomial_eq_C_finrank`), so the statement is
`MvPolynomial.ncard_zeroLocus_le_finrank_quotient` read through the Hilbert polynomial. The
finite-dimensional hypothesis is equivalent to Krull dimension zero of the quotient and to the
Hilbert polynomial having natural degree zero (`natDegree_affineHilbertPolynomial_eq_zero_iff`).

## Main statements

* `MvPolynomial.ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial`: the bound for a
  finite-dimensional quotient.
* `MvPolynomial.finite_zeroLocus_and_ncard_le_affineHilbertPolynomial`: finiteness and the bound
  for a quotient of Krull dimension zero.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:
`AffineHilbert.finite_zeroLocus_and_ncard_le_hilbertPolynomial` in
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/Polynomial.lean`, stated here for
`MvPolynomial.affineHilbertPolynomial`. The source assumed Krull dimension zero; the bound is
also stated under the `Module.Finite` hypothesis that its proof uses, with the source statement
as `finite_zeroLocus_and_ncard_le_affineHilbertPolynomial`.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Finite σ]

/-- For a finite-dimensional coordinate quotient, the zero locus of `I` over any field extension
`K` has at most `(affineHilbertPolynomial I).coeff 0` points.

The finite-dimensional hypothesis is needed: over `k = K = ZMod 2` in one variable, the zero
ideal has a zero locus of two points, while its affine Hilbert polynomial `X + 1` has constant
coefficient `1`. -/
theorem ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    ((zeroLocus K I).ncard : ℚ) ≤ (affineHilbertPolynomial I).coeff 0 := by
  rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero]
  exact_mod_cast ncard_zeroLocus_le_finrank_quotient I

/-- A coordinate quotient of Krull dimension zero has a finite zero locus over any field extension
`K`, with at most `(affineHilbertPolynomial I).coeff 0` points. Krull dimension zero makes the
finite-type quotient finite-dimensional (`Module.finite_iff_krullDimLE_zero`). -/
theorem finite_zeroLocus_and_ncard_le_affineHilbertPolynomial (I : Ideal (MvPolynomial σ k))
    [Ring.KrullDimLE 0 (MvPolynomial σ k ⧸ I)] :
    (zeroLocus K I).Finite ∧
      ((zeroLocus K I).ncard : ℚ) ≤ (affineHilbertPolynomial I).coeff 0 := by
  have : Module.Finite k (MvPolynomial σ k ⧸ I) :=
    (Module.finite_iff_krullDimLE_zero k _).mpr inferInstance
  exact ⟨finite_zeroLocus_of_finite_quotient I,
    ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial I⟩

end MvPolynomial
