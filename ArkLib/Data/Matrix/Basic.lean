/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova
-/

import Mathlib.LinearAlgebra.Matrix.Hadamard
import ArkLib.Data.Fin.Tuple.Defs
import ArkLib.Data.MvPolynomial.Multilinear

/-!
  # Auxiliary definitions and lemmas for matrices
-/

namespace Matrix

variable {α : Type*}
         {F : Type} [Field F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ'] [DecidableEq ℓ']

def rightpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.rightpad m₂ (fun _ => a) (Fin.rightpad n₂ a ∘ M)

def leftpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.leftpad m₂ (fun _ => a) (Fin.leftpad n₂ a ∘ M)

lemma dotProduct_rightpad {R} [CommSemiring R]
    {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (f g : Fin n₁ → R) :
    (∑ j : Fin n₂, Fin.rightpad n₂ (0 : R) f j * Fin.rightpad n₂ (0 : R) g j) =
    ∑ j : Fin n₁, f j * g j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn; simp only [Fin.sum_univ_add]
  have h1 : ∀ i : Fin n₁, Fin.rightpad (n₁ + k) (0 : R) f (Fin.castAdd k i) *
      Fin.rightpad (n₁ + k) (0 : R) g (Fin.castAdd k i) = f i * g i :=
    fun i ↦ by simp [Fin.rightpad, i.isLt]
  have h2 : ∀ j : Fin k, Fin.rightpad (n₁ + k) (0 : R) f (Fin.natAdd n₁ j) *
      Fin.rightpad (n₁ + k) (0 : R) g (Fin.natAdd n₁ j) = 0 :=
    fun j ↦ by simp [Fin.rightpad]
  simp_rw [h1, h2, Finset.sum_const_zero, add_zero]

/-- A rectangular matrix `A` has a left pseudoinverse, if there exists a matrix `B` such that
`B * A = 1`. -/
def HasLeftPseudoInverse (A : Matrix ℓ ℓ' F) : Prop := ∃ B : Matrix ℓ' ℓ F, B * A = 1

/-- A matrix `B` is a left pseudoinverse of a matrix `A` if `B * A = 1`. -/
def IsLeftPseudoInverse (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) : Prop := B * A = 1

/-- For a matrix `A`, if the determinant of `A^T * A` is a unit, then `A^T * A * A^T` is a left
pseudoinverse of `A`. Here `A^T` denotes the transpose of `A`. -/
lemma leftPseudoInverse_transpose_mul_self (A : Matrix ℓ ℓ' F) (hA : IsUnit (A.transpose * A).det) :
    IsLeftPseudoInverse A ((A.transpose * A)⁻¹ * A.transpose) := by
  unfold IsLeftPseudoInverse
  simp only [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ hA

end Matrix

namespace Matrix

open MvPolynomial

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- Convert a matrix of dimensions `2^m × 2^n` to a nested multilinear polynomial
  `R[X Fin n][X Fin m]`. Note the order of nesting (i.e. `m` is on the outside). -/
noncomputable def toMLE (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) : R[X Fin n][X Fin m] :=
  MLE' (MLE' ∘ A)

end Matrix
