/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.LinearAlgebra.ColumnDegreeKernel
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.ReceivedLine

/-!
# Symbolic received-line interpolation with column-sensitive height

In a source monomial `X^x Y₀^a Y₁^b`, the received-line challenge enters through
translation of `Y₀`. Its column in the actual constraint matrix therefore has
challenge degree at most `a`. Giving every column the largest degree loses this
information. Instead, at a trial height `h`, allow that column `h+1-a` coefficients,
or none if `a > h`.

The strict inequality below compares these unknown scalar coefficients with the
`n*r*(h+1)` scalar equations. It yields a primitive interpolant whose challenge
height is at most `h`, satisfying all the received-line constraints identically.
Primitive normalization ensures that it stays nonzero at every challenge, including
challenges in extension fields.

## Reading the statement

* `columns` are distinct source monomials. Their `y₀` exponents provide the weights.
* `hrank` bounds the rank of the actual constraint matrix over the rational function
  field. It is a separate mathematical input, not the number of rows in its raw encoding.
* `hheight` is precisely the finite column-height test. Equal weights may be grouped
  into the manuscript's multiplicities `N_a` without changing the sum.
* `v` is the polynomial coefficient vector; `interpolant columns v` assembles `Q`.
* The last conclusion supplies the actual local constraints. To infer differential
  identities on close polynomials, also establish the support's weighted-degree cutoff.

This theorem is independent of derivative order and support shape. It therefore belongs
with symbolic interpolation, while finite first-order support counts belong in `FirstOrder`.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.3, Proposition 6.3 (finite first-order
  certificate).
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

variable {F : Type*} [Field F] {d : ℕ}

/-- The individual `Y₀` exponents certify a symbolic interpolation height without replacing
all column degrees by their maximum. Every specialization of the output is nonzero. -/
theorem exists_symbolic_received_line_interpolant_of_column_height {n N : ℕ}
    (m r h : ℕ) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns)
    (hrank : ((matrix m centers f g columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * r)
    (hheight : n * r * (h + 1) < ∑ j, (h + 1 - (columns j).y₀)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      Matrix.mulVec (matrix m centers f g columns) v = 0 ∧
      (∀ j, (v j).natDegree ≤ h) ∧ Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
        (receivedLine (f i) (g i)) (interpolant columns v) := by
  let M := finMatrix m centers f g columns
  have hs : (M.map (algebraMap F[X] (RatFunc F))).rank ≤ n * r :=
    (finMatrix_rank_le_matrix_rank m centers f g columns).trans hrank
  have hsurplus : (M.map (algebraMap F[X] (RatFunc F))).rank * (h + 1) <
      ∑ j, (h + 1 - (columns j).y₀) :=
    (Nat.mul_le_mul_right (h + 1) hs).trans_lt hheight
  obtain ⟨v, hv, hMv, hvdeg, hprimitive, hnozero⟩ :=
    Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus M (fun j ↦ (columns j).y₀) h
      (finMatrix_entry_natDegree_le_y₀ m centers f g columns) hsurplus
  have hkernel : Matrix.mulVec (matrix m centers f g columns) v = 0 :=
    (finMatrix_mulVec_eq_zero_iff m centers f g columns v).mp hMv
  refine ⟨v, hv, hkernel, hvdeg, hprimitive, ?_,
    (matrix_mulVec_eq_zero_iff m centers f g columns v).mp hkernel⟩
  intro E _ ι z
  exact map_interpolant_ne_zero columns hcolumns v ι z (hnozero ι z)

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
