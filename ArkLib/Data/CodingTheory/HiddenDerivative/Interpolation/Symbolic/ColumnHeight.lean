/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
public import ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight

/-!
# Symbolic interpolation with column-dependent challenge degrees

With constant centers and received values of challenge degree at most `ℓ`, the column of a source
column with `Y₀` exponent `y₀` has challenge degree at most `ℓ * y₀`
(`natDegree_localConstraintMatrix_le`). At a target height `h`, that column can therefore carry a
coefficient of challenge degree below `h + 1 - ℓ * y₀`, which is none when `ℓ * y₀ > h`. If a rank
bound `s` for the local constraint matrix satisfies

```text
s * (h + 1) < ∑_j (h + 1 - ℓ * y₀(j)),
```

then there is a primitive interpolant whose coefficient in column `j` has degree below
`h + 1 - ℓ * y₀(j)`, in particular at most `h`. It satisfies the local constraints at every point
and stays nonzero under every ring homomorphism from `F[X]` into a nontrivial semiring.

## Main statements

* `exists_primitive_interpolant_of_column_height`: the construction for received curves.
* `exists_primitive_receivedLine_interpolant_of_column_height`: the case of received lines.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

@[expose] public section

open PolynomialDifferential
open scoped Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {d : ℕ} {ι κ : Type*} [Finite ι] [Fintype κ]

/-- For received values of challenge degree at most `ℓ`, a rank bound `s` with
`s * (h + 1) < ∑_j (h + 1 - ℓ * y₀(j))` gives a primitive interpolant whose coefficient in column
`j` has degree below `h + 1 - ℓ * y₀(j)`, that satisfies all the local constraints and stays
nonzero under every ring homomorphism from `F[X]` into a nontrivial semiring. -/
theorem exists_primitive_interpolant_of_column_height (m ℓ h : ℕ) (centers : ι → F)
    (received : ι → F[X]) (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    {K : Type*} [Field K] (φ : F[X] →+* K) (hφ : Function.Injective φ) {s : ℕ}
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) received
      columns).map φ).rank ≤ s)
    (hsurplus : s * (h + 1) < ∑ j, (h + 1 - ℓ * (columns j).y₀)) :
    ∃ v : κ → F[X], v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - ℓ * (columns j).y₀)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : F[X] →+* S),
        MvPolynomial.map ψ (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (received i)
        (SourceColumn.interpolant columns v) := by
  have := Fintype.ofFinite ι
  set M := supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns
  have hrankM : (M.map φ).rank ≤ s :=
    (rank_map_supportedLocalConstraintMatrix φ m _ _ _).le.trans hrank
  obtain ⟨v, hv, hMv, hvdeg, hspan⟩ :=
    Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le M
      (fun j => ℓ * (columns j).y₀) h
      (fun i j => natDegree_localConstraintMatrix_le m ℓ centers received hreceived columns i.1 j)
      φ hφ hrankM hsurplus
  refine ⟨v, hv, hvdeg, hspan,
    fun ψ => SourceColumn.map_interpolant_ne_zero hcolumns ψ
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan ψ), ?_⟩
  exact (localConstraintMatrix_mulVec_eq_zero_iff m _ received columns v).mp
    ((supportedLocalConstraintMatrix_mulVec_eq_zero_iff m _ received columns v).mp hMv)

/-- The case of a received line `f i + Z g i`: a rank bound `s` with
`s * (h + 1) < ∑_j (h + 1 - y₀(j))` gives a primitive interpolant whose coefficient in column `j`
has degree below `h + 1 - y₀(j)`. -/
theorem exists_primitive_receivedLine_interpolant_of_column_height (m h : ℕ)
    (centers f g : ι → F) (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    {K : Type*} [Field K] (φ : F[X] →+* K) (hφ : Function.Injective φ) {s : ℕ}
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map φ).rank ≤ s)
    (hsurplus : s * (h + 1) < ∑ j, (h + 1 - (columns j).y₀)) :
    ∃ v : κ → F[X], v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F (h + 1 - (columns j).y₀)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : F[X] →+* S),
        MvPolynomial.map ψ (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (receivedLine (f i) (g i))
        (SourceColumn.interpolant columns v) := by
  simpa using exists_primitive_interpolant_of_column_height m 1 h centers _
    (fun i => natDegree_receivedLine_le (f i) (g i)) columns hcolumns φ hφ hrank
    (by simpa using hsurplus)

end ReedSolomon.HiddenDerivative
