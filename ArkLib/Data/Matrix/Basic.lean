/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import ArkLib.Data.Fin.Tuple.Defs
public import ArkLib.Data.MvPolynomial.Multilinear

/-!
  # Auxiliary definitions and lemmas for matrices
-/

@[expose] public section

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

/-- Zero-padding the left vector restricts a dot product to its original coordinates. -/
lemma dotProduct_rightpad_left {R : Type*} [CommSemiring R]
    {m n : ℕ} (h : m ≤ n) (f : Fin m → R) (g : Fin n → R) :
    (∑ j, Fin.rightpad n (0 : R) f j * g j) =
      ∑ j, f j * g (Fin.castLE h j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_univ_add]
  simp only [Fin.rightpad]
  simp
  rfl

/-- A rectangular matrix `A` has a left pseudoinverse, if there exists a matrix `B` such that
`B * A = 1`. -/
def HasLeftPseudoInverse (A : Matrix ℓ ℓ' F) : Prop := ∃ B : Matrix ℓ' ℓ F, B * A = 1

/-- A matrix `B` is a left pseudoinverse of a matrix `A` if `B * A = 1`. -/
def IsLeftPseudoInverse (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) : Prop := B * A = 1

/-- For a matrix `A`, if the determinant of `A^T * A` is a unit, then `(A^T * A)⁻¹ * A^T` is a left
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

/-- Fixing the row point leaves the multilinear extension of the evaluated columns. -/
theorem toMLE_rowSlice (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (x : Fin m → R) :
    eval (C ∘ x) M.toMLE = MLE' (fun b => eval x (MLE' (fun a => M a b))) := by
  change eval (C ∘ x) (MLE (fun a => MLE' (M (finFunctionFinEquiv a)))) = _
  rw [MLE_eval]
  simp only [MLE', MLE, Function.comp_apply, map_sum, map_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  have hk : eqTilde (a : Fin m → MvPolynomial (Fin n) R) (C ∘ x) =
      C (eqTilde (a : Fin m → R) x) := by
    rw [map_eqTilde]
    rfl
  rw [hk]
  simp only [eqTilde, eval_C]
  ring

/-- A matrix slice has individual degree at most one in each column coordinate. -/
theorem toMLE_rowSlice_degreeOf (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (x : Fin m → R) (i : Fin n) :
    degreeOf i (eval (C ∘ x) M.toMLE) ≤ 1 := by
  rw [toMLE_rowSlice]
  exact MLE_degreeOf _ i

/-- Evaluating a matrix slice at a Boolean column selects its column multilinear extension. -/
theorem toMLE_rowSlice_eval_zeroOne (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (x : Fin m → R) (b : Fin n → Fin 2) :
    eval (b : Fin n → R) (eval (C ∘ x) M.toMLE) =
      eval x (MLE' (fun a => M a (finFunctionFinEquiv b))) := by
  rw [toMLE_rowSlice]
  exact MLE_eval_zeroOne _ _

end Matrix
