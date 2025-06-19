/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.Hadamard

/-!
# Rank-1 Constraint System (R1CS)

This file defines the R1CS (Rank-1 Constraint System) relation
- The definition is in terms of `Fin` vectors and matrices. In the future, we may consider more
  efficient representations such as `Vector` and `Vector m (Vector n α)`.
- We define padding (on the right) for R1CS instances, and show that padding preserves the R1CS
  relation.
- We define the sparse representation of a matrix (ideally, moved to another file).

-/


-- Padding for `Fin` vectors

section find_home

namespace Fin

variable {α : Sort*}

/-- Pad a `Fin`-indexed vector on the right with an element `a`.

This becomes truncation if `n < m`. -/
def rightpad (n : ℕ) (a : α) {m : ℕ} (v : Fin m → α) : Fin n → α :=
  fun i => if h : i < m then v ⟨i, h⟩ else a

/-- Pad a `Fin`-indexed vector on the left with an element `a`.

This becomes truncation if `n < m`. -/
def leftpad (n : ℕ) (a : α) {m : ℕ} (v : Fin m → α) : Fin n → α :=
  fun i => if h : n - m ≤ i then v ⟨i - (n - m), by omega⟩ else a

end Fin

namespace Matrix

variable {α : Type*}

def rightpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.rightpad m₂ (fun _ => a) (Fin.rightpad n₂ a ∘ M)

def leftpad (m₂ n₂ : ℕ) (a : α) {m₁ n₁ : ℕ} (M : Matrix (Fin m₁) (Fin n₁) α) :
    Matrix (Fin m₂) (Fin n₂) α :=
  Fin.leftpad m₂ (fun _ => a) (Fin.leftpad n₂ a ∘ M)

end Matrix

/-- The sparse representation of a matrix `m → n → α` consists of:
- The number of non-zero entries `k : ℕ`
- The row indices `row : Fin k → m`
- The column indices `col : Fin k → n`
- The values `val : Fin k → α`

This representation is **not** unique. In particular, we may have duplicate `(row, col)` pairs, and
some `val` may be zero.
-/
structure SparseMatrix (m n α : Type*) where
  numEntries : ℕ
  row : Fin numEntries → m
  col : Fin numEntries → n
  val : Fin numEntries → α
deriving Inhabited, DecidableEq

/-- Convert a sparse matrix to a regular (dense) matrix. For each entry `(i, j)` of the matrix, we
  simply sum over all `k` such that `(row k, col k) = (i, j)`.
-/
def SparseMatrix.toMatrix {m n α : Type*} [DecidableEq m] [DecidableEq n] [AddCommMonoid α]
    (A : SparseMatrix m n α) : Matrix m n α :=
  fun i j => ∑ k : Fin A.numEntries, if A.row k = i ∧ A.col k = j then A.val k else 0

end find_home

namespace R1CS

open Matrix

variable (R : Type*) [CommSemiring R]

inductive MatrixIdx where | A | B | C deriving Inhabited, DecidableEq

structure Size where
  m : ℕ -- number of columns
  n_x : ℕ -- number of public variables
  n_w : ℕ -- number of witness variables

abbrev Size.n (sz : Size) : ℕ := sz.n_x + sz.n_w

@[reducible]
def Statement (sz : Size) := Fin sz.n_x → R

@[reducible]
def OracleStatement (sz : Size) := fun _ : MatrixIdx => Matrix (Fin sz.m) (Fin sz.n) R

@[reducible]
def Witness (sz : Size) := Fin sz.n_w → R

@[reducible]
-- The R1CS relation
def relation (sz : Size) :
    (Fin sz.n_x → R) → -- public input `x`
    (MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R) → -- matrices `A`, `B`, `C` as oracle inputs
    (Fin sz.n_w → R) → -- witness input `w`
    Prop :=
  fun stmt matrices wit =>
    let z : Fin (sz.n_x + sz.n_w) → R := Fin.append stmt wit
    (matrices .A *ᵥ z) * (matrices .B *ᵥ z) = (matrices .C *ᵥ z)

/-- Pad an R1CS instance (on the right) from `sz₁` to `sz₂` with zeros.

Note that this results in truncation if the second size is smaller than the first one. -/
def pad (sz₁ sz₂ : Size)
    (stmt : Statement R sz₁)
    (matrices : MatrixIdx → Matrix (Fin sz₁.m) (Fin sz₁.n) R)
    (wit : Witness R sz₁) :
    Statement R sz₂ × (MatrixIdx → Matrix (Fin sz₂.m) (Fin sz₂.n) R) × Witness R sz₂ :=
  (Fin.rightpad sz₂.n_x 0 stmt,
    fun idx => Matrix.rightpad sz₂.m sz₂.n 0 (matrices idx),
    Fin.rightpad sz₂.n_w 0 wit)

-- TODO: should we decompose this function into `padStatement`, `padMatrices`, and `padWitness`?

end R1CS
