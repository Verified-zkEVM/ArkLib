/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Matrix.Basic

/-!
  # Sparse representation of matrices
-/

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
