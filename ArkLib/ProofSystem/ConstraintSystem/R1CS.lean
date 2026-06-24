/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Matrix.Basic
import ArkLib.Data.Fin.Tuple.Lemmas

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

instance : Fintype MatrixIdx where
  elems := { val := [MatrixIdx.A, MatrixIdx.B, MatrixIdx.C], nodup := by decide }
  complete := by
    intro idx
    cases idx <;> simp

@[simp]
theorem MatrixIdx.sum_univ {α : Type*} [AddCommMonoid α] (f : MatrixIdx → α) :
    (∑ idx : MatrixIdx, f idx) = f .A + f .B + f .C := by
  simp [Finset.univ, Fintype.elems, add_assoc]

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

/-- Padding preserves the R1CS relation when `sz₁.m ≤ sz₂.m` (no row truncation),
    `sz₁.n_w ≤ sz₂.n_w` (no witness truncation), and `sz₁.n_x = sz₂.n_x` (same number of
    public variables). The last condition is essential: padding `stmt` and `wit` independently
    can misalign the combined vector `𝕫` if `n_x` changes. -/
theorem pad_preserves_relation (sz₁ sz₂ : Size)
    (h : sz₁.m ≤ sz₂.m ∧ sz₁.n_w ≤ sz₂.n_w ∧ sz₁.n_x = sz₂.n_x)
    (stmt : Statement R sz₁)
    (matrices : MatrixIdx → Matrix (Fin sz₁.m) (Fin sz₁.n) R)
    (wit : Witness R sz₁) :
    relation R sz₁ stmt matrices wit =
      let (stmt', matrices', wit') := pad R sz₁ sz₂ stmt matrices wit
      relation R sz₂ stmt' matrices' wit' := by
  obtain ⟨hm, hnw, hnx⟩ := h
  have hnx1 : sz₁.n_x = sz₁.n - sz₁.n_w := rfl; have hnx2 : sz₂.n_x = sz₂.n - sz₂.n_w := rfl
  have hn_w1 := sz₁.n_w_le_n; have hn_w2 := sz₂.n_w_le_n
  have hn : sz₁.n ≤ sz₂.n := by omega
  have z_eq : 𝕫 (Fin.rightpad sz₂.n_x 0 stmt) (Fin.rightpad sz₂.n_w 0 wit) =
      Fin.rightpad sz₂.n 0 (𝕫 stmt wit) := by
    ext ⟨j, hj⟩; by_cases hlt : j < sz₁.n
    · conv_rhs => rw [Fin.rightpad_apply_lt _ _ _ _ hlt]
      simp only [𝕫, Function.comp, Fin.cast_mk]; by_cases hx : j < sz₁.n_x
      · rw [Fin.append_left_of_lt j _ (by omega), Fin.rightpad_apply_lt _ _ _ _ hx,
            Fin.append_left_of_lt j _ hx]
      · rw [Fin.append_right_of_not_lt j _ (by omega),
            Fin.rightpad_apply_lt _ _ _ _ (show j - sz₂.n_x < sz₁.n_w by omega),
            Fin.append_right_of_not_lt j _ hx]
        exact congrArg wit (Fin.ext (show j - sz₂.n_x = j - sz₁.n_x by omega))
    · push_neg at hlt; conv_rhs => rw [Fin.rightpad_apply_ge _ _ _ _ hlt]
      simp only [𝕫, Function.comp, Fin.cast_mk]
      rw [Fin.append_right_of_not_lt j _ (by omega : ¬ j < sz₂.n_x),
          Fin.rightpad_apply_ge _ _ _ _ (show sz₁.n_w ≤ j - sz₂.n_x by omega)]
  have mv_eq : ∀ (M : Matrix (Fin sz₁.m) (Fin sz₁.n) R),
      Matrix.rightpad sz₂.m sz₂.n 0 M *ᵥ Fin.rightpad sz₂.n 0 (𝕫 stmt wit) =
      Fin.rightpad sz₂.m 0 (M *ᵥ 𝕫 stmt wit) := fun M => funext fun ⟨i, hi⟩ => by
    simp only [mulVec, dotProduct, Matrix.rightpad, Fin.rightpad, Function.comp]
    split_ifs with him
    · exact dotProduct_rightpad hn (M ⟨i, him⟩) (𝕫 stmt wit)
    · exact Finset.sum_eq_zero fun ⟨j, _⟩ _ => by ring
  simp only [relation, pad, z_eq]; simp only [mv_eq]; apply propext
  constructor <;> intro heq <;> funext ⟨i, hi⟩ <;> simp only [Pi.mul_apply, Fin.rightpad]
  · split_ifs with him <;> [exact congr_fun heq ⟨i, him⟩; ring]
  · simpa [show i < sz₁.m from hi] using congr_fun heq ⟨i, by omega⟩

end R1CS
