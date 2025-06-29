/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.Data.FieldTheory.BinaryTowerField.Prelude
import ArkLib.Data.FieldTheory.BinaryTowerField.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finsupp.Basic -- For Finsupp, often used in basis representations
/-!
# Generalized Tensor Algebra and Dual View

This file develops the algebraic theory of the tensor product algebra `A := L ⊗[K] R` for arbitrary field extensions `L/K` and `R/K` and its restriction to binary tower fields called tower algebra.

## Main Definitions

- `TensorAlgebra K L R` : the tensor product of the field L and R over their common subfield K, which forms a K-algebra: A := L ⊗[K] R
- `TowerAlgebra K L R` : the tower algebra is a special case of `TensorAlgebra` where K, L, R are binary tower fields

## TODOs
-- some theorems about subring embeddings (φ0, φ1) and subring operations for tensor algebra (e.g. columns and rows decomposition)
-- multilinear bases of tower algebra over subfields
-- packed polynomial f(μ_₁, ..., μ_ℓ) over K into f'(μ_₁, ..., μ_ℓ') over L, where dim(L/K) = 2^(ℓ - ℓ') => intantiate into binary tower fields

## References

- [Lan02] Serge Lang. "Algebra". Revised Third Edition. Vol. 211. Graduate Texts in Mathematics. Springer, 2002.

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).

- [DP23] Diamond, Benjamin E., and Jim Posen. "Succinct arguments over towers of binary fields."
  Cryptology ePrint Archive (2023).
-/

noncomputable section

open Polynomial
open AdjoinRoot
open TensorProduct
open Module
open Finsupp
open BinaryTower

namespace TensorAlgebra

/-!
### Definition of the Tensor Algebra `A := L ⊗[K] R`
Formalize `A` as `TensorProduct K L R`, which is a `K`-algebra by mathlib's built-in structure.
Require `[L:K] = 2^κ` and `[R:K] = 2^λ`.
-/

variable (K L R : Type*) (lκ rκ: ℕ) [Field K] [Field L] [Field R] [Algebra K L] [Algebra K R] [Fact (finrank K L = lκ)] [Fact (finrank K R = rκ)] [SMulCommClass K L L] [SMulCommClass K R R]

abbrev TA := L ⊗[K] R

instance addCommGroup : AddCommGroup (TA K L R) := inferInstance

-- multiplication for pure tensors
@[simp]
lemma tmul_mul_tmul (a₁ a₂ b₁ b₂ : L) :
  (a₁ ⊗ₜ[K] b₁) * (a₂ ⊗ₜ[K] b₂) = (a₁ * a₂) ⊗ₜ[K] (b₁ * b₂) :=
  Algebra.TensorProduct.tmul_mul_tmul a₁ a₂ b₁ b₂

@[simp]
lemma one_is_one_tmul_one : (1 : TA K L R) = (1 : L) ⊗ₜ[K] (1 : R) :=
  Algebra.TensorProduct.one_def

@[simp]
lemma zero_is_zero_tmul_zero : (0 : TA K L R) = (0 : L) ⊗ₜ[K] (0 : R) :=
  (TensorProduct.zero_tmul (R := K) (M := L) (N := R) 0).symm

-- lift from K to TA K L R
@[simp]
lemma algebraMap_apply (r : K) :
  (algebraMap K (TA K L R)) r = (algebraMap K L r) ⊗ₜ[K] (1 : R) :=
  Algebra.TensorProduct.algebraMap_apply r

-- left tmul l ↦ l ⊗ₜ 1
@[simp]
lemma includeLeft_apply (l : L) :
  (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := L) (B := R)) l = l ⊗ₜ[K] 1 :=
  rfl

-- right tmul r ↦ 1 ⊗ₜ r
@[simp]
lemma includeRight_apply (r : R) :
  (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)) r = 1 ⊗ₜ[K] r :=
  rfl

/-!
### Basis decomposition
-/

lemma basis_decomposition {ιL ιR : Type*} [Fintype ιL] [Fintype ιR] (bL : Basis ιL K L) (bR : Basis ιR K R) (x : L ⊗[K] R) :
  x = ∑ (i : ιL × ιR), (bL.tensorProduct bR).repr x i • (bL i.1 ⊗ₜ[K] bR i.2) :=
by
  have sum_repr_of_x: ∑ (i : ιL × ιR), ((bL.tensorProduct bR).repr x) i • (bL.tensorProduct bR) i = x := (bL.tensorProduct bR).sum_repr x
  rw [←sum_repr_of_x]
  congr
  funext i
  rw [Basis.tensorProduct_apply']
  simp only [map_sum, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.univ_sum_single]

/-!
### Zero and pure tensor lemmas
-/

/-- For fields K ⊆ L, x ⊗ₜ[K] c = 0 ↔ x = 0 or c = 0. -/
theorem tmul_eq_zero_iff (x : L) (c : R) :
    (x ⊗ₜ[K] c : L ⊗[K] R) = 0 ↔ x = 0 ∨ c = 0 := by
  constructor
  · intro h_tmul_eq_zero -- Assume x ⊗ c = 0
    by_cases hc_is_zero : c = 0
    · exact Or.inr hc_is_zero -- If c = 0, we're done
    · -- Case: c ≠ 0. We need to show x = 0.
      -- Obtain a basis for L over K. All vector spaces over a field have a basis.
      obtain ⟨basis_L, h_basis⟩ := Module.Free.exists_basis (R := K) (M := L)
      obtain ⟨basis_R, h_basis_R⟩ := Module.Free.exists_basis (R := K) (M := R)
      let bL : Basis basis_L K L := h_basis
      let bR : Basis basis_R K R := h_basis_R
      -- The set {bL i ⊗ bR j} forms a basis for L ⊗[K] R.
      let basis_tensor : Basis (basis_L × basis_R) K (L ⊗[K] R) :=
        Basis.tensorProduct bL bR
      -- If x ⊗ c = 0, then its coordinates in basis_tensor are all zero.
      have coeffs_prod_zero : ∀ (i : basis_L) (j : basis_R), (bL.repr x i) * (bR.repr c j) = 0 := by
        intro i j
        let coord_val := basis_tensor.repr (x ⊗ₜ[K] c) (i, j)
        have coord_def : coord_val = (bR.repr c j) • (bL.repr x i) := Basis.tensorProduct_repr_tmul_apply bL bR x c i j
        rw [smul_eq_mul] at coord_def
        rw [mul_comm, ←coord_def]
        have : coord_val = (basis_tensor.repr 0) (i, j) := by
          rw [←h_tmul_eq_zero]
        rw [this]
        -- ⊢ (basis_tensor.repr 0) (i, j) = 0
        rfl
      have repr_c_ne_zero : bR.repr c ≠ 0 := by
        intro h
        apply hc_is_zero
        apply bR.repr.injective
        apply Finsupp.ext
        intro i
        rw [h]
        rw [Finsupp.zero_apply]
        simp
      have h_support : (bR.repr c).support.Nonempty := Finsupp.support_nonempty_iff.mpr repr_c_ne_zero
      obtain ⟨k, hk⟩ := h_support
      have all_x_coeffs_zero : ∀ (i : basis_L), bL.repr x i = 0 := by
        intro i
        have prod_is_zero := coeffs_prod_zero i k
        exact (mul_eq_zero.mp prod_is_zero).resolve_right (Finsupp.mem_support_iff.mp hk)
      have repr_x_is_zero : bL.repr x = 0 := Finsupp.ext (fun i => all_x_coeffs_zero i)
      exact Or.inl (bL.repr.injective (Finsupp.ext (fun i => by rw [all_x_coeffs_zero]; norm_num)))
  · -- Backward direction is the same as before
    rintro (rfl | rfl)
    · exact TensorProduct.zero_tmul (R := K) (M := L) (N := R) c
    · exact TensorProduct.tmul_zero (R := K) (M := L) (N := R) x

lemma ta_one_ne_zero : (1 : TA K L R) ≠ 0 := by
  intro h
  have := tmul_eq_zero_iff K L R 1 1
  rw [←h] at this
  have contra := (this.mp rfl)
  cases contra
  case inl h1 => exact one_ne_zero h1
  case inr h2 => exact one_ne_zero h2

lemma pure_tensor_right_cancel (a b : L) (c : R) (hc : c ≠ 0) : (a ⊗ₜ[K] c) = (b ⊗ₜ[K] c) → a = b := by
  intro h
  have sub_eq_zero: (a - b) ⊗ₜ[K] c = 0 := by
    calc
      (a - b) ⊗ₜ[K] c = a ⊗ₜ[K] c - b ⊗ₜ[K] c := by rw [TensorProduct.sub_tmul]
      _ = 0 := by simp only [h]; norm_num
  have h_zero := (tmul_eq_zero_iff K L R (a - b) c).mp sub_eq_zero
  cases h_zero with
  | inl h1 => exact eq_of_sub_eq_zero h1
  | inr h2 => exact (hc h2).elim

lemma pure_tensor_left_cancel (c : L) (a b : R) (hc : c ≠ 0) : (c ⊗ₜ[K] a) = (c ⊗ₜ[K] b) → a = b := by
  intro h
  have sub_eq_zero: c ⊗ₜ[K] (a - b) = 0 := by
    calc
      c ⊗ₜ[K] (a - b) = c ⊗ₜ[K] a - c ⊗ₜ[K] b := by rw [TensorProduct.tmul_sub]
      _ = 0 := by simp only [h]; norm_num
  have h_zero := (tmul_eq_zero_iff K L R c (a - b)).mp sub_eq_zero
  cases h_zero with
  | inl h1 => exact (hc h1).elim
  | inr h2 => exact eq_of_sub_eq_zero h2

lemma pure_tensor_eq_iff_eq_mul_one (α₁ β₁: L) (α₂ β₂: R) : (α₁ ⊗ₜ[K] α₂) = (β₁ ⊗ₜ[K] β₂) ↔ (α₁ ⊗ₜ[K] α₂) * (1 : TA K L R) = (β₁ ⊗ₜ[K] β₂) * (1 : TA K L R) := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [mul_one (a := β₁ ⊗ₜ[K] β₂)] at h
    rw [mul_one (a := α₁ ⊗ₜ[K] α₂)] at h
    exact h

/-!
### Subring Embeddings φ0 and φ1
Define the maps φ0 : l ↦ l ⊗ 1 and φ1 : r ↦ 1 ⊗ r.
Prove they are ring embeddings.
-/

-- φ0: left inclusion as ring hom
abbrev φ0 : L →+* TA K L R := Algebra.TensorProduct.includeLeftRingHom (R := K) (A := L) (B := R)
-- φ0_alg: left inclusion as algebra hom
abbrev φ0_alg : L →ₐ[K] TA K L R := Algebra.TensorProduct.includeLeft (R := K) (A := L) (B := R)
-- φ1_alg: right inclusion as algebra hom (no standard ring hom version)
abbrev φ1_alg : R →ₐ[K] TA K L R := Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)

def scalarMul0 (α : L) : TA K L R →ₗ[K] TA K L R :=
  LinearMap.mulLeft (TA K L R) (φ0 (K := K) (L := L) (R := R) α)

def scalarMul1 (α : R) : TA K L R →ₗ[K] TA K L R :=
  LinearMap.mulLeft (TA K L R) (φ1_alg (K := K) (L := L) (R := R) α)

@[simp]
theorem φ0_apply (α : L) : φ0 (K := K) (L := L) (R := R) α = α ⊗ₜ[K] 1 := rfl

@[simp]
theorem φ1_apply (α : R) : φ1_alg (K := K) (L := L) (R := R) α = 1 ⊗ₜ[K] α := rfl

/-!
### A is K-algebra
-/
instance A_is_K_algebra : Algebra K (TA K L R) := Algebra.TensorProduct.instAlgebra
instance A_is_L_algebra : Algebra L (TA K L R) := Algebra.TensorProduct.leftAlgebra
instance A_is_R_algebra : Algebra R (TA K L R) := Algebra.TensorProduct.rightAlgebra

-- Define tower algebra where K, L, and R are binary tower fields

/--
Given bases `bL : ιL → L` and `bR : ιR → R` of `L` and `R` over `K`,
the set `{bL i ⊗ₜ[K] bR j | i ∈ ιL, j ∈ ιR}` is a basis of `L ⊗[K] R` over `K`.
-/
def tensorAlgebra_basis {K L R : Type*} [Field K] [Field L] [Field R]
  [Algebra K L] [Algebra K R]
  {ιL ιR : Type*} (bL : Basis ιL K L) (bR : Basis ιR K R) :
  Basis (ιL × ιR) K (L ⊗[K] R) :=
  bL.tensorProduct bR

/--
The value of the tensor algebra basis at (i, j) is `bL i ⊗ₜ[K] bR j`.
-/
theorem tensorAlgebra_basis_apply {K L R : Type*} [Field K] [Field L] [Field R]
  [Algebra K L] [Algebra K R]
  {ιL ιR : Type*} (bL : Basis ιL K L) (bR : Basis ιR K R) (i : ιL) (j : ιR) :
  tensorAlgebra_basis bL bR (i, j) = bL i ⊗ₜ[K] bR j :=
  Basis.tensorProduct_apply bL bR i j

universe u v w

-- basis of A (L ⊗[K] R) over L is equivalent to basis of R over K
noncomputable def tensorAlgebra_basis_over_L
  {K : Type u} {L : Type v} {R : Type w} [Field K] [Field L] [Field R]
  [Module K L] [Module K R] [Semiring (L ⊗[K] R)] [Module L (L ⊗[K] R)] [Algebra K R] [Algebra K L] [Algebra R (L ⊗[K] R)] [IsScalarTower K R (L ⊗[K] R)]
  {ιR : Type*} [Fintype ιR] (bR : Basis ιR K R) :
  Basis ιR L (L ⊗[K] R) :=
  letI : Module L (L ⊗[K] R) := inferInstance
  let basis_vectors : ιR → L ⊗[K] R :=
    fun i => 1 ⊗ₜ[K] bR i
  have hli: LinearIndependent L basis_vectors := by sorry
  have hsp: ⊤ ≤ Submodule.span L (Set.range basis_vectors) := by sorry
  Basis.mk (R:=L) (M:=(L ⊗[K] R)) (ι:=ιR) (hli := hli) (hsp := hsp) (v := basis_vectors)

-- basis of A (L ⊗[K] R) over R is equivalent to basis of L over K
noncomputable def tensorAlgebra_basis_over_R
  {K : Type u} {L : Type v} {R : Type w} [Field K] [Field R] [Field L]
  [Module K L] [Module K R] [Semiring (L ⊗[K] R)] [Module R (L ⊗[K] R)] [Algebra K R] [Algebra K L] [Algebra R (L ⊗[K] R)] [IsScalarTower K R (L ⊗[K] R)]
  {ιL : Type*} (bL : Basis ιL K L) :
  Basis ιL R (L ⊗[K] R) :=
  letI : Module R (L ⊗[K] R) := inferInstance
  let basis_vectors : ιL → L ⊗[K] R :=
    fun i => bL i ⊗ₜ[K] 1
  have hli: LinearIndependent R basis_vectors := by sorry
  have hsp: ⊤ ≤ Submodule.span R (Set.range basis_vectors) := by sorry
  Basis.mk (R:=R) (M:=(L ⊗[K] R)) (ι:=ιL) (hli := hli) (hsp := hsp) (v := basis_vectors)

theorem tensor_algebra_basis_over_L_apply
  {K L R : Type*} [Field K] [Field L] [Field R] [Algebra K L] [Algebra K R]
  {ιR : Type*} [Fintype ιR]
  (bR : Basis ιR K R) (i : ιR) :
  (tensorAlgebra_basis_over_L bR) i = φ1_alg (K := K) (L := L) (R := R) (bR i) :=
by
  -- Unfold the definition to see that this is true by construction
  unfold tensorAlgebra_basis_over_L
  simp only [Basis.mk_apply]
  rfl

theorem tensor_algebra_basis_over_R_apply
  {K L R : Type*} [Field K] [Field L] [Field R] [Algebra K L] [Algebra K R]
  {ιL : Type*} [Fintype ιL]
  (bL : Basis ιL K L) (i : ιL) :
  (tensorAlgebra_basis_over_R bL) i = φ0_alg (K := K) (L := L) (R := R) (bL i) :=
by
  unfold tensorAlgebra_basis_over_R
  simp only [Basis.mk_apply]
  rfl

variable (K L R : Type*) [Field K] [Field L] [Field R]
variable [Algebra K L] [Algebra K R] [IsScalarTower K L (L ⊗[K] R)] [IsScalarTower K R (L ⊗[K] R)]
variable (ιL ιR : Type*) [Fintype ιL] [Fintype ιR]

class TensorAlgebra
  (K : Type*) (L : Type*) (R : Type*) (A : Type*) (ιL ιR : Type*)
  [Field K] [Field L] [Field R]
  [Fintype ιL] [Fintype ιR] where
  A_is_semiring : Semiring A
  -- eq: A = B
  L_is_K_algebra : Algebra K L
  R_is_K_algebra : Algebra K R
  A_is_K_algebra : Algebra K A
  A_is_L_algebra : Algebra L A
  A_is_R_algebra : Algebra R A
  A_is_tensor_product : Nonempty (A ≃ₐ[K] L ⊗[K] R)
  basis_over_L : Basis ιR L A
  basis_over_R : Basis ιL R A

-- [@reducible]
-- def TowerAlgebra (κ τ ι : ℕ) [Fact (κ < τ)] [Fact (ι < τ)] := BTField τ ⊗[BTField κ] BTField ι

-- TowerAlgebra is a special case of TensorAlgebra where K, L, R are binary tower fields
instance TowerAlgebra (κ τ ι : ℕ) [Fact (κ < τ)] [Fact (ι < τ)]
  [Module (BTField κ) (BTField τ)] [Module (BTField κ) (BTField ι)]
  [Algebra (BTField κ) (BTField τ)] [Algebra (BTField κ) (BTField ι)] :
  TensorAlgebra (BTField κ) (BTField τ) (BTField ι) (x: BTField τ ⊗[BTField κ] BTField ι) (BTField ι) (BTField ι) where
  A_is_semiring := sorry
  L_is_K_algebra := inferInstance
  R_is_K_algebra := inferInstance
  A_is_K_algebra := sorry
  A_is_L_algebra := sorry
  A_is_R_algebra := sorry
  A_is_tensor_product := sorry
  basis_over_L := sorry
  basis_over_R := sorry

instance SquareTowerAlgebra (κ τ : ℕ) [Fact (κ < τ)]
  [Module (BTField κ) (BTField τ)] [Algebra (BTField κ) (BTField τ)] :
  TensorAlgebra (BTField κ) (BTField τ) (BTField τ) (BTField τ ⊗[BTField κ] BTField τ) (BTField τ) (BTField τ) where
  A_is_semiring := sorry
  L_is_K_algebra := inferInstance
  R_is_K_algebra := inferInstance
  A_is_K_algebra := sorry
  A_is_L_algebra := sorry
  A_is_R_algebra := sorry
  A_is_tensor_product := sorry
  basis_over_L := sorry
  basis_over_R := sorry

end TensorAlgebra
end

#check LawfulMonad -- ⊢ (m : Type u → Type v) → [inst : Monad m] → Prop
