/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.MvPolynomial.WeightAtMost
public import Mathlib.Algebra.CharP.Defs

/-!
# Jet-degree bounds for the exact interpolation space

A monomial `X^a Y₀^b₀ ⋯ Y_d^b_d` in the exact interpolation space has specialization weight
`a + ∑_j (D - j) b_j < m * A`, so its exponent of `Y_j` satisfies `b_j * (D - j) ≤ m * A - 1`.
For `d < D` every `D - j` is positive and

```text
b_j ≤ (m * A - 1) / (D - j) =: exactInterpolationJetDegreeFloorAt D A m j.
```

This coordinate floor is at most the global floor `exactInterpolationJetDegreeFloor D A d m`
`= (m * A - 1) / (D - d)` of `Interpolation/Index.lean`, which bounds the total jet degree. The
root-finding steps need each jet degree below the characteristic of the coefficient ring, and
`jetDegree_lt_ringChar_of_mem_exactInterpolationSpace` derives this from the global floor. No
cap on the total degree or on the exponent of `Y₁` is used, only the weight condition.

## Main statements

* `exactInterpolationSpace_le_restrictWeightAtMost`: the exact space lies in the space of
  polynomials of specialization weight at most `m * A - 1`.
* `jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace`: the
  coordinate floor, and `exactInterpolationJetDegreeFloorAt_le`: its comparison with the global
  floor.
* `jetDegree_lt_ringChar_of_mem_exactInterpolationSpace`: the characteristic bound.
* `jetDegree_exactInterpolationPolynomial_le_floorAt` and
  `jetDegree_exactInterpolationPolynomial_lt_ringChar`: the same bounds for the polynomial with
  prescribed exact interpolation coefficients.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 3.4, Definition 3.6 and (12), and Section 6.3,
  Theorem 6.3
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {d D A m M W : ℕ}

/-- Every member of the exact interpolation space has all monomials of specialization weight at
most `m * A - 1`. For `m * A = 0` the space is `{0}` and the statement holds trivially. -/
theorem exactInterpolationSpace_le_restrictWeightAtMost [CommSemiring F] (hdD : d < D) :
    exactInterpolationSpace F D A d m M W hdD ≤
      MvPolynomial.restrictWeightAtMost (R := F) (differentialWeight D) (m * A - 1) := by
  intro Q hQ
  rw [MvPolynomial.mem_restrictWeightAtMost]
  intro u hu
  have := (mem_exactInterpolationSpace_iff.mp hQ u hu).2.2
  omega

/-- The coordinate floor `(m * A - 1) / (D - j)` for the exponent of `Y_j`. Natural-number
division rounds down; for `j < D` it is the largest `b` with `b * (D - j) ≤ m * A - 1`. -/
def exactInterpolationJetDegreeFloorAt (D A m : ℕ) (j : Fin (d + 1)) : ℕ :=
  (m * A - 1) / (D - j.val)

/-- Every member of the exact interpolation space has degree in `Y_j` at most
`(m * A - 1) / (D - j)`. The hypothesis `d < D` makes the weight `D - j` of `Y_j` positive; it is
also needed to form the space. -/
theorem jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace
    [CommSemiring F] (Q : DifferentialPolynomial F d) {hdD : d < D}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD) (j : Fin (d + 1)) :
    jetDegree Q j ≤ exactInterpolationJetDegreeFloorAt D A m j :=
  MvPolynomial.degreeOf_le_div_of_mem_restrictWeightAtMost
    (exactInterpolationSpace_le_restrictWeightAtMost hdD hQ)
    (differentialWeight_some_pos_of_order_lt_degree hdD j)

/-- For `d < D` the coordinate floor at `Y_j` is at most the global floor
`(m * A - 1) / (D - d)`, since `D - d ≤ D - j` and both are positive. -/
theorem exactInterpolationJetDegreeFloorAt_le (hdD : d < D) (j : Fin (d + 1)) :
    exactInterpolationJetDegreeFloorAt D A m j ≤ exactInterpolationJetDegreeFloor D A d m := by
  rw [exactInterpolationJetDegreeFloorAt, exactInterpolationJetDegreeFloor]
  have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
  exact Nat.div_le_div_left (by omega) (by omega)

/-- If the global floor `(m * A - 1) / (D - d)` is below the characteristic of `F`, every jet
degree of a member of the exact interpolation space is below the characteristic. In
characteristic zero (`ringChar F = 0`) the hypothesis is false and the statement is vacuous;
callers in characteristic zero use `jetDegree_le_floor_of_mem_exactInterpolationSpace`
directly. -/
theorem jetDegree_lt_ringChar_of_mem_exactInterpolationSpace [CommSemiring F]
    (Q : DifferentialPolynomial F d) {hdD : d < D}
    (hQ : Q ∈ exactInterpolationSpace F D A d m M W hdD)
    (hfloor : exactInterpolationJetDegreeFloor D A d m < ringChar F) (j : Fin (d + 1)) :
    jetDegree Q j < ringChar F :=
  (jetDegree_le_floor_of_mem_exactInterpolationSpace hdD hQ j).trans_lt hfloor

/-! ### Polynomials from exact interpolation coefficients -/

/-- The polynomial with prescribed exact interpolation coefficients satisfies the coordinate
floor. -/
theorem jetDegree_exactInterpolationPolynomial_le_floorAt [CommSemiring F] {hdD : d < D}
    (c : ExactInterpolationCoefficients F D A d m M W hdD) (j : Fin (d + 1)) :
    jetDegree (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) j ≤
      exactInterpolationJetDegreeFloorAt D A m j :=
  jetDegree_le_exactInterpolationJetDegreeFloorAt_of_mem_exactInterpolationSpace _
    (exactInterpolationPolynomial hdD c).property j

/-- The polynomial with prescribed exact interpolation coefficients has every jet degree below
the characteristic once the global floor is. -/
theorem jetDegree_exactInterpolationPolynomial_lt_ringChar [CommSemiring F] {hdD : d < D}
    (c : ExactInterpolationCoefficients F D A d m M W hdD)
    (hfloor : exactInterpolationJetDegreeFloor D A d m < ringChar F) (j : Fin (d + 1)) :
    jetDegree (exactInterpolationPolynomial hdD c : DifferentialPolynomial F d) j <
      ringChar F :=
  jetDegree_lt_ringChar_of_mem_exactInterpolationSpace _
    (exactInterpolationPolynomial hdD c).property hfloor j

end

end ReedSolomon.HiddenDerivative
