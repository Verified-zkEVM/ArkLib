/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Matrix.Basic
public import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# Rank-1 Constraint System (R1CS)

This file defines the R1CS (Rank-1 Constraint System) relation
- The definition is in terms of `Fin` vectors and matrices. In the future, we may consider more
  efficient representations such as `Vector` and `Vector m (Vector n α)`.
- Enlarging an instance pads its public and witness column blocks separately, preserving and
  reflecting the relation with an explicit witness pullback.
-/

@[expose] public section

namespace R1CS

open Matrix

variable (R : Type*) [CommSemiring R]

inductive MatrixIdx where | A | B | C deriving Inhabited, DecidableEq

structure Size where
  m : ℕ -- number of rows
  n : ℕ -- number of columns
  n_w : ℕ -- number of witness variables
  -- The witness dimension is at most the column dimension.
  n_w_le_n : n_w ≤ n := by omega

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

/-- Pad the public coordinates independently of the witness coordinates. -/
def embedStatement (sz₁ sz₂ : Size) (stmt : Statement R sz₁) : Statement R sz₂ :=
  Fin.rightpad sz₂.n_x 0 stmt

/-- Pad the witness coordinates independently of the public coordinates. -/
def embedWitness (sz₁ sz₂ : Size) (wit : Witness R sz₁) : Witness R sz₂ :=
  Fin.rightpad sz₂.n_w 0 wit

/-- Recover the original witness coordinates from a witness for the enlarged instance. -/
def pullbackWitness (sz₁ sz₂ : Size) (hw : sz₁.n_w ≤ sz₂.n_w)
    (wit : Witness R sz₂) : Witness R sz₁ :=
  fun j => wit (Fin.castLE hw j)

/-- Enlarge a constraint matrix by padding its public and witness column blocks separately.
The witness block starts after the enlarged public block. Extra rows and columns are zero. -/
def embedMatrix (sz₁ sz₂ : Size) (M : Matrix (Fin sz₁.m) (Fin sz₁.n) R) :
    Matrix (Fin sz₂.m) (Fin sz₂.n) R :=
  fun i => if hi : i.val < sz₁.m then
    Fin.append
      (Fin.rightpad sz₂.n_x 0
        (fun j : Fin sz₁.n_x => M ⟨i.val, hi⟩
          (Fin.cast sz₁.n_eq_n_x_add_n_w.symm (Fin.castAdd sz₁.n_w j))))
      (Fin.rightpad sz₂.n_w 0
        (fun j : Fin sz₁.n_w => M ⟨i.val, hi⟩
          (Fin.cast sz₁.n_eq_n_x_add_n_w.symm (Fin.natAdd sz₁.n_x j)))) ∘
      Fin.cast sz₂.n_eq_n_x_add_n_w
    else 0

/-- Enlarge each of the three constraint matrices using the same column layout. -/
def embedMatrices (sz₁ sz₂ : Size) (matrices : ∀ idx, OracleStatement R sz₁ idx) :
    (∀ idx, OracleStatement R sz₂ idx) :=
  fun idx => embedMatrix R sz₁ sz₂ (matrices idx)

private theorem sum_mul_𝕫 (sz : Size) (v : Fin sz.n → R)
    (stmt : Statement R sz) (wit : Witness R sz) :
    (∑ j, v j * 𝕫 stmt wit j) =
      (∑ j : Fin sz.n_x,
        v (Fin.cast sz.n_eq_n_x_add_n_w.symm (Fin.castAdd sz.n_w j)) * stmt j) +
      ∑ j : Fin sz.n_w,
        v (Fin.cast sz.n_eq_n_x_add_n_w.symm (Fin.natAdd sz.n_x j)) * wit j := by
  rw [← (finCongr sz.n_eq_n_x_add_n_w.symm).sum_comp]
  simp [𝕫, Fin.sum_univ_add]

/-- Matrix multiplication for the enlarged instance recovers the original multiplication on
its original rows, including for arbitrary values of the unused witness coordinates. -/
theorem embedMatrix_mulVec (sz₁ sz₂ : Size)
    (hx : sz₁.n_x ≤ sz₂.n_x) (hw : sz₁.n_w ≤ sz₂.n_w)
    (M : Matrix (Fin sz₁.m) (Fin sz₁.n) R)
    (stmt : Statement R sz₁) (wit : Witness R sz₂) :
    embedMatrix R sz₁ sz₂ M *ᵥ 𝕫 (embedStatement R sz₁ sz₂ stmt) wit =
      Fin.rightpad sz₂.m 0 (M *ᵥ 𝕫 stmt (pullbackWitness R sz₁ sz₂ hw wit)) := by
  ext i
  simp only [mulVec, dotProduct]
  rw [sum_mul_𝕫]
  by_cases hi : i.val < sz₁.m
  · simp only [embedMatrix, hi, ↓reduceDIte, Function.comp_apply, Fin.cast_cast,
      Fin.cast_eq_self, Fin.append_left, Fin.append_right]
    rw [Matrix.dotProduct_rightpad_left hw]
    simp only [embedStatement]
    rw [Matrix.dotProduct_rightpad hx]
    rw [Fin.rightpad_apply_lt _ _ _ _ hi]
    simp only [mulVec, dotProduct]
    rw [sum_mul_𝕫]
    rfl
  · simp [embedMatrix, hi, Fin.rightpad]

/-- Enlarging the public and witness blocks preserves and reflects satisfaction. Reflection
uses the explicit witness pullback and holds for every witness of the enlarged instance. -/
theorem relation_embed_iff (sz₁ sz₂ : Size) (hm : sz₁.m ≤ sz₂.m)
    (hx : sz₁.n_x ≤ sz₂.n_x) (hw : sz₁.n_w ≤ sz₂.n_w)
    (stmt : Statement R sz₁) (matrices : ∀ idx, OracleStatement R sz₁ idx)
    (wit : Witness R sz₂) :
    relation R sz₂ (embedStatement R sz₁ sz₂ stmt)
      (embedMatrices R sz₁ sz₂ matrices) wit ↔
      relation R sz₁ stmt matrices (pullbackWitness R sz₁ sz₂ hw wit) := by
  simp only [relation, embedMatrices, embedMatrix_mulVec R sz₁ sz₂ hx hw]
  constructor <;> intro h <;> funext i
  · have hi := congr_fun h (Fin.castLE hm i)
    simpa [Fin.rightpad, i.isLt, Pi.mul_apply] using hi
  · by_cases hi : i.val < sz₁.m
    · simpa [Fin.rightpad, hi, Pi.mul_apply] using congr_fun h ⟨i.val, hi⟩
    · simp [Fin.rightpad, hi, Pi.mul_apply]

/-- Pulling back a zero-padded witness recovers the original witness. -/
@[simp]
theorem pullbackWitness_embedWitness (sz₁ sz₂ : Size) (hw : sz₁.n_w ≤ sz₂.n_w)
    (wit : Witness R sz₁) :
    pullbackWitness R sz₁ sz₂ hw (embedWitness R sz₁ sz₂ wit) = wit := by
  funext i
  simp [pullbackWitness, embedWitness, Fin.rightpad, i.isLt]

/-- The zero-padded original witness satisfies the enlarged instance exactly when it satisfied
its original instance. -/
theorem embed_preserves_relation (sz₁ sz₂ : Size) (hm : sz₁.m ≤ sz₂.m)
    (hx : sz₁.n_x ≤ sz₂.n_x) (hw : sz₁.n_w ≤ sz₂.n_w)
    (stmt : Statement R sz₁) (matrices : ∀ idx, OracleStatement R sz₁ idx)
    (wit : Witness R sz₁) :
    relation R sz₂ (embedStatement R sz₁ sz₂ stmt) (embedMatrices R sz₁ sz₂ matrices)
      (embedWitness R sz₁ sz₂ wit) ↔ relation R sz₁ stmt matrices wit := by
  rw [relation_embed_iff R sz₁ sz₂ hm hx hw, pullbackWitness_embedWitness]

end R1CS
