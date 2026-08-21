/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import CompPoly.Univariate.ToPoly.Impl

/-!
# A computable `CPolynomial → Polynomial` conversion

CompPoly's `CPolynomial.toPoly` is `noncomputable`: it is defined as the `eval₂` of the
coefficient array into `Polynomial R`, and `Polynomial`'s `Semiring` instance is
noncomputable, so the folded sum `∑ᵢ C aᵢ · Xⁱ` cannot be run. That is a property of *that
definition*, not of the target type: a Mathlib `Polynomial` is a `Finsupp` under
`Polynomial.ofFinsupp`, and building one from a coefficient array needs no ring operations at
all — only a decidable zero test, which `[BEq R] [LawfulBEq R]` supplies.

`cToPoly` is that construction, and `cToPoly_eq_toPoly` proves it agrees with `toPoly` on the
nose. So a definition that must *produce* a Mathlib polynomial — an honest prover computing a
division quotient, say — can be computable after all, while every theorem stated about
`toPoly` continues to apply through the agreement lemma.

The same `ofFinsupp` idiom already appears in `Data/Polynomial/SplitFold.lean` (`splitNth`) and
`Data/CodingTheory/BerlekampWelch/Condition.lean` (`truncate`); this file is its
CompPoly-facing instance.

## Main definitions

* `CompPoly.CPolynomial.cToPoly` — the computable conversion.
* `CompPoly.CPolynomial.coeff_cToPoly` — its coefficients are `CPolynomial.coeff`, by `rfl`.
* `CompPoly.CPolynomial.cToPoly_eq_toPoly` — agreement with the noncomputable `toPoly`.
-/

namespace CompPoly.CPolynomial

variable {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

/-- **Computable `CPolynomial → Polynomial`.** The coefficient array is read directly into a
`Finsupp` supported on `Finset.range` of the array size: the support is cut down by the
decidable zero test coming from `LawfulBEq`, and no `Polynomial` ring operation is involved,
which is exactly what makes this compile where `toPoly` does not. -/
def cToPoly (p : CPolynomial R) : Polynomial R :=
  Polynomial.ofFinsupp <| AddMonoidAlgebra.ofCoeff
    { support := (Finset.range p.val.size).filter (fun i => !(p.coeff i == 0))
      toFun := fun i => p.coeff i
      mem_support_toFun := by
        intro a
        simp only [Finset.mem_filter, Finset.mem_range, Bool.not_eq_true', beq_eq_false_iff_ne,
          ne_eq, and_iff_right_iff_imp]
        intro h
        by_contra hlt
        exact h (by
          simp [CPolynomial.coeff, Raw.coeff, Array.getD,
            (by omega : ¬ a < p.val.size)]) }

/-- The coefficients of `cToPoly p` are `p`'s own, by `rfl` — the conversion is a
re-presentation of the coefficient array, not a computation on it. -/
@[simp] theorem coeff_cToPoly (p : CPolynomial R) (i : ℕ) :
    (cToPoly p).coeff i = p.coeff i := rfl

/-- **Agreement with the noncomputable `toPoly`.** Both sides have `CPolynomial.coeff` as their
coefficient function (`coeff_cToPoly` by `rfl`, `CPolynomial.coeff_toPoly` for `toPoly`), so
they are equal by `Polynomial.ext`. Every result stated about `toPoly` therefore transfers to
the computable conversion by rewriting. -/
theorem cToPoly_eq_toPoly (p : CPolynomial R) : cToPoly p = p.toPoly := by
  ext i
  rw [coeff_cToPoly, CPolynomial.coeff_toPoly]

end CompPoly.CPolynomial
