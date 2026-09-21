/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.RowBasis
public import ArkLib.ToMathlib.Polynomial.DegreeLT
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Polynomial kernel vectors of uniformly bounded degree

For a polynomial matrix with `r` rows and `c` columns, suppose every entry has natural degree at
most `b` and `r < c`. This file constructs a nonzero vector in the right kernel whose coordinates
have degree strictly less than

`r * b / (c - r) + 1`.

The row count `r` may be replaced by any upper bound `s` on the rank of the matrix over a field
into which `F[X]` embeds, for example the rational function field, and the kernel vector may be
chosen primitive: its coordinates generate the unit ideal of `F[X]`.

## Main statements

* `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` uses arbitrary finite row and column index
  types and records the bound as membership in `Polynomial.degreeLT`, including for zero
  coordinates. `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` is the exact natural-degree
  interface of the source theorem.
* `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` replaces the row count by an upper
  bound `s` on the rank of `M.map φ`, for any injective ring homomorphism `φ` from `F[X]` to a
  field. `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le` is its natural-degree
  form.
* `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` adds to the rank form the
  conclusion that the coordinates of the kernel vector generate the unit ideal.

## Proof outline

The row-count theorem treats the bounded coefficients of the kernel vector as scalar unknowns.
Multiplication by the matrix followed by coefficient extraction is a linear map between
finite-dimensional spaces; the displayed bound makes its source dimension larger than its target
dimension, so rank-nullity supplies a nonzero vector in its kernel.

For the rank form, `Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` selects `rank (M.map φ)`
rows of `M` with the same right kernel as `M`. The row-count theorem applies to this submatrix,
and the resulting bound is at most the bound for `s` because `r * b / (c - r)` is monotone in
`r` for `r < c`. For the primitive form, `Matrix.exists_primitive_kernel_vector_eq_smul` writes
the kernel vector as `g • u` with `g ≠ 0` and `u` primitive, and
`Polynomial.mem_degreeLT_of_mul_left` (in `ArkLib.ToMathlib.Polynomial.DegreeLT`) transfers the
degree bound from `g * u j` to `u j`. The natural-degree forms follow from the `degreeLT` forms
by `Polynomial.natDegree_le_of_mem_degreeLT_succ`.

## References

The theorem family is extracted and generalized from `ArkLib.ToMathlib.LinearAlgebra` at
immutable source revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The row-count theorem
generalizes `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` in
`PolynomialKernelHeight.lean`. The rank forms generalize
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in the same file and
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` in
`PrimitivePolynomialKernel.lean`. Those source theorems fix the rank to be exactly `s`, measure it
over `RatFunc F`, and use `Fin` indices, so a caller with only `rank ≤ r` had to prove the
monotonicity of the bound itself. The source's row-count primitive theorem
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le` is the primitive rank form with
`s := Fintype.card rows` and the rank bound `Matrix.rank_le_card_height`.

The shifted and column families of the same revision remain to be ported:
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT` and
`Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus` in `ShiftedDegreeKernel.lean`, and
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`,
`Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank`, and
`Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus` in `ColumnDegreeKernel.lean`.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {F : Type*} [Field F]

/-- A wide polynomial matrix has a nonzero right-kernel vector with uniformly bounded degree.

If `M` has `r` rows and `c` columns, all entries have natural degree at most `b`, and `r < c`, the
resulting coordinate `v j` belongs to `Polynomial.degreeLT F (r * b / (c - r) + 1)`. Thus the
strict degree bound also records zero coordinates without relying on the convention
`Polynomial.natDegree 0 = 0`. The construction is uniform over arbitrary finite index types and
requires no characteristic assumption beyond `F` being a field. -/
theorem exists_ne_zero_mulVec_eq_zero_degreeLT {rows cols : Type*}
    [Fintype rows] [Fintype cols] {b : ℕ}
    (M : Matrix rows cols F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hwide : Fintype.card rows < Fintype.card cols) :
    ∃ v : cols → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        ∀ j, v j ∈ Polynomial.degreeLT F
          (Fintype.card rows * b / (Fintype.card cols - Fintype.card rows) + 1) := by
  let h := Fintype.card rows * b / (Fintype.card cols - Fintype.card rows)
  let decode : (Fin (h + 1) → F) →ₗ[F] F[X] :=
    (Polynomial.degreeLT F (h + 1)).subtype ∘ₗ
      (Polynomial.degreeLTEquiv F (h + 1)).symm.toLinearMap
  let decodeVec : (cols → Fin (h + 1) → F) →ₗ[F] (cols → F[X]) :=
    LinearMap.pi fun j ↦ decode ∘ₗ LinearMap.proj j
  let takeCoeffs : (rows → F[X]) →ₗ[F] (rows → Fin (h + b + 1) → F) :=
    LinearMap.pi fun i ↦ LinearMap.pi fun k ↦
      Polynomial.lcoeff F k ∘ₗ LinearMap.proj i
  let coefficientMap :
      (cols → Fin (h + 1) → F) →ₗ[F] (rows → Fin (h + b + 1) → F) :=
    takeCoeffs ∘ₗ (M.mulVecLin.restrictScalars F) ∘ₗ decodeVec
  have hden : 0 < Fintype.card cols - Fintype.card rows := Nat.sub_pos_of_lt hwide
  have hcoeff :
      Fintype.card rows * b <
        (h + 1) * (Fintype.card cols - Fintype.card rows) := by
    apply (Nat.div_lt_iff_lt_mul hden).mp
    exact Nat.lt_succ_self _
  have hdim :
      Module.finrank F (rows → Fin (h + b + 1) → F) <
        Module.finrank F (cols → Fin (h + 1) → F) := by
    simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      Module.finrank_self, mul_one]
    change Fintype.card rows * (h + b + 1) < Fintype.card cols * (h + 1)
    have hsplit :
        Fintype.card rows + (Fintype.card cols - Fintype.card rows) = Fintype.card cols :=
      Nat.add_sub_of_le hwide.le
    nlinarith
  have hker : LinearMap.ker coefficientMap ≠ ⊥ :=
    coefficientMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hc, hcne⟩ := (LinearMap.ker coefficientMap).ne_bot_iff.mp hker
  let v : cols → F[X] := fun j ↦ decode (c j)
  have hvdegree (j : cols) : v j ∈ Polynomial.degreeLT F (h + 1) :=
    ((Polynomial.degreeLTEquiv F (h + 1)).symm (c j)).property
  have hvnatDegree (j : cols) : (v j).natDegree ≤ h := by
    apply Polynomial.natDegree_le_of_degree_le
    rw [Polynomial.degreeLT_succ_eq_degreeLE] at hvdegree
    exact Polynomial.mem_degreeLE.mp (hvdegree j)
  have hproduct (i : rows) (j : cols) : (M i j * v j).natDegree ≤ h + b := by
    exact (Polynomial.natDegree_mul_le_of_le (hdeg i j) (hvnatDegree j)).trans_eq
      (Nat.add_comm b h)
  have hmulVec_degree (i : rows) : ((M *ᵥ v) i).natDegree ≤ h + b := by
    change (∑ j, M i j * v j).natDegree ≤ h + b
    exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun j _ ↦ hproduct i j
  have hmulVec : M *ᵥ v = 0 := by
    funext i
    apply Polynomial.ext
    intro k
    by_cases hk : k < h + b + 1
    · let k' : Fin (h + b + 1) := ⟨k, hk⟩
      have hzero := congrFun (congrFun (LinearMap.mem_ker.mp hc) i) k'
      have hdecodeVec : decodeVec c = v := by
        ext j
        rfl
      simp only [coefficientMap, LinearMap.comp_apply] at hzero
      rw [hdecodeVec] at hzero
      simpa [takeCoeffs, k'] using hzero
    · simp only [Pi.zero_apply, coeff_zero]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hk' : h + b < k := by omega
      exact lt_of_le_of_lt (hmulVec_degree i) hk'
  have hvne : v ≠ 0 := by
    intro hv
    apply hcne
    have hdecode : Function.Injective decode := by
      intro x y hxy
      apply (Polynomial.degreeLTEquiv F (h + 1)).symm.injective
      apply Subtype.ext
      exact hxy
    funext j
    apply hdecode
    simpa [v] using congrFun hv j
  exact ⟨v, hvne, hmulVec, hvdegree⟩

/-- Natural-degree form of the uniform polynomial kernel-height theorem.

For `r = Fintype.card rows` and `c = Fintype.card cols`, every coordinate of the nonzero kernel
vector has natural degree at most `r * b / (c - r)`. On `rows = Fin n` and `cols = Fin N`, this
is exactly `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` from the immutable source. -/
theorem exists_ne_zero_mulVec_eq_zero_natDegree_le {rows cols : Type*}
    [Fintype rows] [Fintype cols] {b : ℕ}
    (M : Matrix rows cols F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (hwide : Fintype.card rows < Fintype.card cols) :
    ∃ v : cols → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        ∀ j, (v j).natDegree ≤
          Fintype.card rows * b / (Fintype.card cols - Fintype.card rows) := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_degreeLT M hdeg hwide
  exact ⟨v, hv, hMv, fun j ↦ Polynomial.natDegree_le_of_mem_degreeLT_succ (hvdegree j)⟩

/-- A polynomial matrix whose rank is below its column count has a nonzero right-kernel vector of
uniformly bounded degree.

Let `φ : F[X] →+* K` be an injective ring homomorphism into a field, such as
`algebraMap F[X] (RatFunc F)`. If every entry of `M` has natural degree at most `b`, the rank of
`M.map φ` is at most `s`, and `s < c` for `c = Fintype.card cols`, then some nonzero `v` with
`M *ᵥ v = 0` has every coordinate in `Polynomial.degreeLT F (s * b / (c - s) + 1)`.

The rank is measured over a field because `F[X]` is not one, and the injectivity of `φ` makes the
kernel over `F[X]` agree with the kernel over `K` on vectors with polynomial entries. The
hypothesis is an upper bound rather than the exact rank, and the bound `s * b / (c - s)` is
monotone in `s`, so a caller with an estimate `rank ≤ s` can use it directly. The hypothesis
`s < c` is what guarantees a nonzero kernel vector.

Edge cases: when `s = 0` the budget is `degreeLT F 1`, so the coordinates are constants; an
injective `φ` gives rank zero only for the zero matrix, which annihilates every constant vector.
The row type may be empty, and it may be much larger than `s`: only `rank (M.map φ)` rows enter
the bound. The bound is stated with `degreeLT`, so it does not rely on the convention
`Polynomial.natDegree 0 = 0`; `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le` is
the natural-degree form. -/
theorem exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le {rows cols K : Type*}
    [Finite rows] [Fintype cols] [Field K] {b s : ℕ}
    (M : Matrix rows cols F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (φ : F[X] →+* K) (hφ : Function.Injective φ) (hrank : (M.map φ).rank ≤ s)
    (hs : s < Fintype.card cols) :
    ∃ v : cols → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        ∀ j, v j ∈ Polynomial.degreeLT F (s * b / (Fintype.card cols - s) + 1) := by
  obtain ⟨selected, hselected⟩ := M.exists_rows_submatrix_mulVec_eq_zero_iff φ hφ
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_degreeLT (M.submatrix selected id)
      (fun i j ↦ hdeg (selected i) j) (by simpa using hrank.trans_lt hs)
  refine ⟨v, hv, (hselected v).mp hMv, fun j ↦ Polynomial.degreeLT_mono ?_ (hvdegree j)⟩
  rw [Fintype.card_fin]
  exact Nat.add_le_add_right (Nat.div_le_div (Nat.mul_le_mul_right b hrank)
    (Nat.sub_le_sub_left hrank _) (Nat.sub_ne_zero_of_lt hs)) 1

/-- Natural-degree form of the rank-bounded polynomial kernel-height theorem.

Under the hypotheses of `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`, every
coordinate of the nonzero kernel vector has natural degree at most `s * b / (c - s)`, where
`c = Fintype.card cols`. This form does not distinguish a zero coordinate from a nonzero constant.
With `φ := algebraMap F[X] (RatFunc F)` and `Fin` indices, it recovers
`Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq` from the immutable source, whose
exact-rank hypothesis `hrank : rank = s` is passed as `hrank.le`. -/
theorem exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le {rows cols K : Type*}
    [Finite rows] [Fintype cols] [Field K] {b s : ℕ}
    (M : Matrix rows cols F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (φ : F[X] →+* K) (hφ : Function.Injective φ) (hrank : (M.map φ).rank ≤ s)
    (hs : s < Fintype.card cols) :
    ∃ v : cols → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        ∀ j, (v j).natDegree ≤ s * b / (Fintype.card cols - s) := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le M hdeg φ hφ hrank hs
  exact ⟨v, hv, hMv, fun j ↦ Polynomial.natDegree_le_of_mem_degreeLT_succ (hvdegree j)⟩

/-- A polynomial matrix whose rank is below its column count has a primitive right-kernel vector
of uniformly bounded degree.

Under the hypotheses of `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le`, the kernel
vector can also be chosen with `Ideal.span (Set.range v) = ⊤`: its coordinates have no common
factor of positive degree. The degree budget is the same `degreeLT` bound, so zero coordinates
and the case `s = 0` behave as in that theorem.

The immutable source states primitivity together with the specialization clause
`∀ {E} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0`. That clause follows from
the unit-ideal conclusion: apply `Ideal.comp_ne_zero_of_span_range_eq_top` with
`φ := Polynomial.eval₂RingHom ι z`, whose target `E` is nontrivial.

The row-count primitive form of the source,
`Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le`, is the case
`s := Fintype.card rows` with `hrank := Matrix.rank_le_card_height (M.map φ)`, which needs a
`Fintype` instance on the rows. -/
theorem exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le {rows cols K : Type*}
    [Finite rows] [Fintype cols] [Field K] {b s : ℕ}
    (M : Matrix rows cols F[X]) (hdeg : ∀ i j, (M i j).natDegree ≤ b)
    (φ : F[X] →+* K) (hφ : Function.Injective φ) (hrank : (M.map φ).rank ≤ s)
    (hs : s < Fintype.card cols) :
    ∃ v : cols → F[X],
      v ≠ 0 ∧ M *ᵥ v = 0 ∧
        (∀ j, v j ∈ Polynomial.degreeLT F (s * b / (Fintype.card cols - s) + 1)) ∧
          Ideal.span (Set.range v) = ⊤ := by
  classical
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le M hdeg φ hφ hrank hs
  obtain ⟨g, u, hg, rfl, hu, hMu, hspan⟩ := M.exists_primitive_kernel_vector_eq_smul hv hMv
  exact ⟨u, hu, hMu, fun j ↦ Polynomial.mem_degreeLT_of_mul_left hg (hvdegree j), hspan⟩

end Matrix
