/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel
public import ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight
public import ArkLib.ToMathlib.Polynomial.DegreeLT

/-!
# Symbolic interpolation for received polynomial curves

The received value at each point is a polynomial `received i` of degree at most `ℓ` in a symbolic
challenge, and the centers are constants. A rank bound `s` for the local constraint matrix, after
an injective ring homomorphism from `F[X]` into a field, with `s` below the number of source
columns, gives a coefficient vector `v` over `F[X]` such that the interpolant
`SourceColumn.interpolant columns v`

* satisfies the local constraints at every point, as polynomials in the challenge;
* has coefficients of challenge degree at most `s * (ℓ * ν) / (card κ - s)`, where `ν` bounds the
  `Y₀` exponents of the columns;
* has coefficients that generate the unit ideal of `F[X]`, so its image under every ring
  homomorphism from `F[X]` into a nontrivial semiring is nonzero. In particular it stays nonzero
  after every specialization of the challenge, in `F` or in an extension field.

The rank bound is a hypothesis. The received line `f + Z g` is the case `ℓ = 1`.

## Main statements

* `exists_primitive_interpolant_of_rank_le`: the construction for received curves.
* `exists_primitive_receivedLine_interpolant_of_rank_le`: the case of received lines.

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

/-- The received value `f + Z g` of a line, as a polynomial in the challenge `Z`. -/
def receivedLine (f g : F) : F[X] :=
  Polynomial.C f + Polynomial.X * Polynomial.C g

/-- A received line has challenge degree at most `1`. -/
theorem natDegree_receivedLine_le (f g : F) : (receivedLine f g).natDegree ≤ 1 := by
  rw [receivedLine]
  compute_degree

/-- A received curve of challenge degree at most `ℓ`, with a rank bound `s` below the number of
source columns, has a primitive interpolant of challenge degree at most
`s * (ℓ * ν) / (card κ - s)` that satisfies all the local constraints and stays nonzero under
every ring homomorphism from `F[X]` into a nontrivial semiring. -/
theorem exists_primitive_interpolant_of_rank_le (m ℓ ν : ℕ) (centers : ι → F)
    (received : ι → F[X]) (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν) {K : Type*} [Field K] (φ : F[X] →+* K)
    (hφ : Function.Injective φ) {s : ℕ}
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i)) received
      columns).map φ).rank ≤ s)
    (hs : s < Fintype.card κ) :
    ∃ v : κ → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ s * (ℓ * ν) / (Fintype.card κ - s)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : F[X] →+* S),
        MvPolynomial.map ψ (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (received i)
        (SourceColumn.interpolant columns v) := by
  have := Fintype.ofFinite ι
  set M := supportedLocalConstraintMatrix m (fun i => Polynomial.C (centers i)) received columns
  have hrankM : (M.map φ).rank ≤ s :=
    (rank_map_supportedLocalConstraintMatrix φ m _ _ _).le.trans hrank
  have hdeg : ∀ i j, (M i j).natDegree ≤ ℓ * ν := fun i j =>
    (natDegree_localConstraintMatrix_le m ℓ centers received hreceived columns i.1 j).trans
      (Nat.mul_le_mul_left ℓ (hy₀ j))
  obtain ⟨v, hv, hMv, hvdeg, hspan⟩ :=
    Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le M hdeg φ hφ hrankM hs
  refine ⟨v, hv, fun j => Polynomial.natDegree_le_of_mem_degreeLT_succ (hvdeg j), hspan,
    fun ψ => SourceColumn.map_interpolant_ne_zero hcolumns ψ
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan ψ), ?_⟩
  exact (localConstraintMatrix_mulVec_eq_zero_iff m _ received columns v).mp
    ((supportedLocalConstraintMatrix_mulVec_eq_zero_iff m _ received columns v).mp hMv)

/-- The case of a received line `f i + Z g i`: a rank bound `s` below the number of source columns
gives a primitive interpolant of challenge degree at most `s * ν / (card κ - s)`. -/
theorem exists_primitive_receivedLine_interpolant_of_rank_le (m ν : ℕ) (centers f g : ι → F)
    (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    (hy₀ : ∀ j, (columns j).y₀ ≤ ν) {K : Type*} [Field K] (φ : F[X] →+* K)
    (hφ : Function.Injective φ) {s : ℕ}
    (hrank : ((localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => receivedLine (f i) (g i)) columns).map φ).rank ≤ s)
    (hs : s < Fintype.card κ) :
    ∃ v : κ → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ s * ν / (Fintype.card κ - s)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {S : Type*} [CommSemiring S] [Nontrivial S] (ψ : F[X] →+* S),
        MvPolynomial.map ψ (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (receivedLine (f i) (g i))
        (SourceColumn.interpolant columns v) := by
  simpa using exists_primitive_interpolant_of_rank_le m 1 ν centers _
    (fun i => natDegree_receivedLine_le (f i) (g i)) columns hcolumns hy₀ φ hφ hrank hs

end ReedSolomon.HiddenDerivative
