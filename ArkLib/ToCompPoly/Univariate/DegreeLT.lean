/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ToMathlib.Polynomial.DegreeLT
public import CompPoly.Univariate.ToPoly.Degree

/-!
# Bounded computable polynomials of degree at most `d`

The finite subtype `degreeLT (d + 1)` holds the computable polynomials of degree at most `d`.
Searches over it stand for searches over the Mathlib polynomials of degree at most `d`.

## Main statements

* `CompPoly.CPolynomial.degree_toPoly_le`: an element converts to a polynomial of degree at
  most `d`.
* `CompPoly.CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le`: a search over the subtype
  finds a witness exactly when some polynomial is one, for predicates that bound the degree.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]

/-- An element of `degreeLT (d + 1)` converts to a polynomial of degree at most `d`. -/
theorem degree_toPoly_le {d : ℕ} (P : ↥(degreeLT (R := R) (d + 1))) :
    P.val.toPoly.degree ≤ d :=
  Polynomial.degree_lt_succ_iff.mp <| Polynomial.mem_degreeLT.mp (degreeLT_toPoly.mp P.property)

/-- Suppose that every polynomial that satisfies `Q` has degree at most `d`.
Then some element of `degreeLT (d + 1)` satisfies `Q` after conversion
exactly when some polynomial satisfies `Q`. -/
theorem exists_degreeLT_succ_toPoly_iff_of_degree_le (d : ℕ) (Q : Polynomial R → Prop)
    (hQ : ∀ p, Q p → p.degree ≤ d) :
    (∃ p : ↥(degreeLT (R := R) (d + 1)), Q p.val.toPoly) ↔ ∃ p, Q p :=
  exists_degreeLT_toPoly_iff_of_degree_lt (d + 1) Q fun p hp ↦
    Polynomial.degree_lt_succ_iff.mpr (hQ p hp)

end CompPoly.CPolynomial
