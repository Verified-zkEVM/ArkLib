/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Matrix.Basic

/-!
# Rank-1 Constraint System (R1CS)

This file defines the R1CS (Rank-1 Constraint System) relation
- The definition is in terms of `Fin` vectors and matrices. In the future, we may consider more
  efficient representations such as `Vector` and `Vector m (Vector n α)`.
- We define padding (on the right) for R1CS instances, and show that padding preserves the R1CS
  relation.
-/

namespace R1CS

open Matrix

variable (R : Type*) [CommSemiring R]

inductive MatrixIdx where | A | B | C deriving Inhabited, DecidableEq

structure Size where
  m : ℕ -- number of columns
  n : ℕ -- number of rows
  n_w : ℕ -- number of witness variables
  n_w_le_n : n_w ≤ n := by omega -- Number of witness variables must be at most the number of rows

attribute [simp] Size.n_w_le_n

variable (sz : Size)

/-- Number of public `𝕩` variables -/
abbrev Size.n_x : ℕ := sz.n - sz.n_w

lemma Size.n_eq_n_x_add_n_w : sz.n = sz.n_x + sz.n_w := by
  simp [Size.n_x]

@[reducible]
def Statement := Fin sz.n_x → R

@[reducible]
def OracleStatement := fun _ : MatrixIdx => Matrix (Fin sz.m) (Fin sz.n) R

@[reducible]
def Witness := Fin sz.n_w → R

/-- The vector `𝕫` is the concatenation of the public input and witness variables -/
@[reducible, inline]
def 𝕫 {R} {sz} (stmt : Statement R sz) (wit : Witness R sz) : Fin sz.n → R :=
  Fin.append stmt wit ∘ Fin.cast (by simp)

/-- The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean
  component-wise (Hadamard) vector multiplication. -/
@[reducible]
def relation :
    (Fin sz.n_x → R) → -- public input `x`
    (MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R) → -- matrices `A`, `B`, `C` as oracle inputs
    (Fin sz.n_w → R) → -- witness input `w`
    Prop :=
  fun stmt matrix wit =>
    letI 𝕫 := 𝕫 stmt wit
    (matrix .A *ᵥ 𝕫) * (matrix .B *ᵥ 𝕫) = (matrix .C *ᵥ 𝕫)

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

-- padding preserves the R1CS relation
theorem pad_preserves_relation (sz₁ sz₂ : Size)
    (stmt : Statement R sz₁)
    (matrices : MatrixIdx → Matrix (Fin sz₁.m) (Fin sz₁.n) R)
    (wit : Witness R sz₁) :
    relation R sz₁ stmt matrices wit =
      let (stmt', matrices', wit') := pad R sz₁ sz₂ stmt matrices wit
      relation R sz₂ stmt' matrices' wit' := by
  simp [pad, relation, rightpad]
  sorry

end R1CS
