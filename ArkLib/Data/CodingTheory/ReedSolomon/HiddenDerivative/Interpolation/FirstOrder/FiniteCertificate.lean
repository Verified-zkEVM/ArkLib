/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.HeightCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Symbolic
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite

/-!
# A finite first-order symbolic certificate from executable counts

This module removes the remaining choice of source columns from first-order symbolic
interpolation. It uses the canonical enumeration of every monomial

```text
X^x Y₀^a Y₁^b,  b ≤ M,  a + b ≤ μ,
                    x + D a + (D - 1) b < m A
```

and applies the degree-one specialization of the shifted graded-row engine.

## Reading the statements

The main theorem takes only the mathematical parameters, an embedding of the `n`
evaluation centers, the two received words defining `f + Zg`, and the strict numeric
inequality

```text
firstOrderCurveShiftedRowSlotBound D A m M μ n 1 h
  < firstOrderCurveShiftedHeightSlotCount D A m M μ 1 h.
```

There is no caller-supplied matrix rank, column family, or support-membership proof.
The result contains one primitive polynomial `Q` over `F[Z]`, chosen before any extension
field, challenge, agreement set, or candidate polynomial. Every candidate of degree below
`k` that agrees with `f + zg` at at least `A` positions satisfies the specialized
differential identity.

## Proof route and scope

The received line is viewed as a degree-one polynomial curve. The curve constructor supplies the
compressed graded matrix, primitive kernel, finite-support bounds, local constraints, and
extension-field soundness, and this module packages the result in the line certificate structure.

These theorems construct the interpolation equation and prove its agreement implication.
They do not count solutions of that equation or establish a final list-size or
correlated-agreement bound.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.3, Proposition 6.3 (finite first-order
  certificate).
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicWeightedSupportInterpolation

noncomputable section

variable {F : Type*} [Field F]

/-- The line case (`ℓ = 1`) of the shifted graded engine constructs the complete finite
first-order symbolic certificate. All matrix and rank facts are discharged internally. -/
theorem exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
    {D A m M μ k h n : ℕ}
    (hD : 0 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (f g : Fin n → F)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M μ n 1 h <
      firstOrderCurveShiftedHeightSlotCount D A m M μ 1 h) :
    Nonempty (FirstOrderSymbolicCertificate (F := F) D A m M μ k h centers f g
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) := by
  let w : Fin n → F[X] := fun i ↦ receivedLine (f i) (g i)
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    1 (Nat.zero_lt_of_lt hD) hbudget hkD centers w
      (fun i ↦ receivedLine_natDegree_le (f i) (g i)) hheight
  refine ⟨{
    coefficients := cert.coefficients
    Q := cert.Q
    eq_interpolant := cert.eq_interpolant
    primitiveCoefficients := cert.primitiveCoefficients
    challengeDegree_le := cert.challengeDegree_le
    support := cert.support
    firstJetDegree_le := cert.firstJetDegree_le
    totalJetDegree_le := cert.totalJetDegree_le
    localConstraints := cert.localConstraints
    specialization_sound := ?_ }⟩
  intro E _ ι z
  obtain ⟨hnonzero, hsound⟩ := cert.specialization_sound ι z
  refine ⟨hnonzero, ?_⟩
  intro indices P hPdegree hcard hagreements
  apply hsound indices P hPdegree hcard
  intro i hi
  rw [hagreements i hi]
  change ι (f i) + z * ι (g i) =
    Polynomial.eval₂ ι z (receivedLine (f i) (g i))
  simp only [receivedLine, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_X]

end

end ReedSolomon.HiddenDerivative
