/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.LinearAlgebra.Matrix.Hadamard
import ArkLib.Data.Fin.Tuple.Defs
import ArkLib.Data.MvPolynomial.Multilinear

/-!
  # Auxiliary definitions and lemmas for matrices
-/

namespace Matrix

variable {α : Type*}

def rightpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.rightpad m₂ (fun _ => a) (Fin.rightpad n₂ a ∘ M)

def leftpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.leftpad m₂ (fun _ => a) (Fin.leftpad n₂ a ∘ M)

end Matrix

namespace Matrix

open MvPolynomial

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- Convert a matrix of dimensions `2^m × 2^n` to a nested multilinear polynomial
  `R[X Fin n][X Fin m]`. Note the order of nesting (i.e. `m` is on the outside). -/
noncomputable def toMLE (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) : R[X Fin n][X Fin m] :=
  MLE' (MLE' ∘ A)

end Matrix
