/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Polynomial kernel vectors of uniformly bounded degree

For a polynomial matrix with `r` rows and `c` columns, suppose every entry has natural degree at
most `b` and `r < c`. This file constructs a nonzero vector in the right kernel whose coordinates
have degree strictly less than

`r * b / (c - r) + 1`.

The principal theorem `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` uses arbitrary finite row
and column index types and records the bound as membership in `Polynomial.degreeLT`, including for
zero coordinates. `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` is the exact natural-degree
interface of the source theorem.

The proof treats the bounded coefficients of the kernel vector as scalar unknowns. Multiplication
by the matrix followed by coefficient extraction is a linear map between finite-dimensional
spaces; the displayed bound makes its source dimension larger than its target dimension, so
rank-nullity supplies a nonzero vector in its kernel.

The theorem family is extracted and generalized from
`ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight` at immutable source revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. It is the row-count form of the polynomial
kernel-height lemma in [DKTZ26, Section 5.1, Lemma 5.1]. The intrinsic rank, primitive,
column-budget, and shifted-budget forms are intentionally deferred to later polynomial-kernel
slices.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26]
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
  refine ⟨v, hv, hMv, fun j ↦ ?_⟩
  apply Polynomial.natDegree_le_of_degree_le
  rw [Polynomial.degreeLT_succ_eq_degreeLE] at hvdegree
  exact Polynomial.mem_degreeLE.mp (hvdegree j)

end Matrix
