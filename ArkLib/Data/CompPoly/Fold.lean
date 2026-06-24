/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CompPoly.Basic
import ArkLib.Data.Polynomial.SplitFold

/-!
# Computable Split/Fold for `CPolynomial`

Native computable `CPolynomial` versions of the split/fold operations used by
FRI. The definitions operate directly on CompPoly coefficients and do not route
through Mathlib polynomials.
-/

open CompPoly CPoly
open scoped BigOperators

namespace CompPoly.CPolynomial

variable {R : Type} [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-- The `i`-th component of the `n`-way split of a computable polynomial. -/
def splitNth (n : ℕ) [NeZero n] (p : CPolynomial R) : Fin n → CPolynomial R :=
  fun i => ∑ j ∈ p.support,
    if j % n = (i : ℕ) then
      monomial (j / n) (p.coeff j)
    else
      0

/-- Recombine the `n`-way split of `p` using powers of `α`. -/
def foldNth (n : ℕ) [NeZero n] (p : CPolynomial R) (α : R) :
    CPolynomial R :=
  ∑ i : Fin n, C (α ^ (i : ℕ)) * splitNth n p i

end CompPoly.CPolynomial

section ToPoly

open Polynomial

namespace CompPoly.CPolynomial

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [DecidableEq R]

theorem splitNth_toPoly (n : ℕ) [NeZero n] (p : CPolynomial R) (i : Fin n) :
    (splitNth n p i).toPoly = p.toPoly.splitNth n i := by
  sorry

theorem foldNth_toPoly (n : ℕ) [NeZero n] (p : CPolynomial R) (α : R) :
    (foldNth n p α).toPoly = p.toPoly.foldNth n α := by
  simp [CPolynomial.foldNth, Polynomial.foldNth, toPoly_sum, toPoly_mul, C_toPoly,
    splitNth_toPoly]

theorem foldNth_natDegree_le_of_le
    (n d : ℕ) [NeZero n] (p : CPolynomial R) (α : R)
    (hdeg : p.natDegree ≤ n * d) :
    (foldNth n p α).natDegree ≤ d := by
  rw [natDegree_toPoly, foldNth_toPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.splitNth_degree_le (n := n) (f := p.toPoly) (i := i)).trans ?_
  have hdegPoly : p.toPoly.natDegree ≤ n * d := by
    simpa [natDegree_toPoly] using hdeg
  exact Nat.div_le_of_le_mul hdegPoly

end CompPoly.CPolynomial

end ToPoly
