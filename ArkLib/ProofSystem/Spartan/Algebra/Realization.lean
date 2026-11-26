/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Identities
public import ArkLib.ProofSystem.Spartan.Context

/-!
# Executable Spartan polynomial evaluations

Finite table evaluations realize the semantic multilinear extensions. The terminal equation
reconstructs the assignment from the public prefix and a single witness evaluation.
-/

@[expose] public section

namespace Spartan.Realization

open MvPolynomial Matrix
open scoped BigOperators

variable {R : Type} [CommRing R] {m n : ℕ}

/-- The executable equality kernel. -/
def eqWeight (x y : Fin n → R) : R :=
  ∏ i, (x i * y i + (1 - x i) * (1 - y i))

/-- Evaluate the multilinear interpolation of a finite table. -/
def tableEval (v : Fin (2 ^ n) → R) (r : Fin n → R) : R :=
  ∑ j, eqWeight (finFunctionFinEquiv.symm j : Fin n → R) r * v j

/-- Evaluate a matrix extension, with the row point before the column point. -/
def matrixEval (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) (r_y : Fin n → R) : R :=
  tableEval (fun b => tableEval (fun a => M a b) r_x) r_y

/-- Evaluate a row product from its finite table. -/
def rowEval (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) : R :=
  tableEval (M *ᵥ z) r_x

/-- Evaluate the first virtual polynomial from the row tables. -/
def firstEval (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ r_x : Fin m → R) : R :=
  eqWeight τ r_x * (rowEval (matrix .A) z r_x * rowEval (matrix .B) z r_x -
    rowEval (matrix .C) z r_x)

@[simp]
theorem eqWeight_eq (x y : Fin n → R) : eqWeight x y = eqTilde x y :=
  (eqTilde_eq_prod x y).symm

@[simp]
theorem tableEval_eq (v : Fin (2 ^ n) → R) (r : Fin n → R) :
    tableEval v r = eval r (MLE' v) := by
  simp only [tableEval, eqWeight_eq, MLE'_eval]

@[simp]
theorem matrixEval_eq (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) (r_y : Fin n → R) :
    matrixEval M r_x r_y = eval r_y (eval (C ∘ r_x) M.toMLE) := by
  simp only [matrixEval, tableEval_eq, Matrix.toMLE_rowSlice]

@[simp]
theorem rowEval_eq (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) :
    rowEval M z r_x = eval r_x (Algebra.rowProduct M z) := tableEval_eq _ _

/-- Executable evaluation agrees with the first virtual polynomial. -/
theorem firstVirtual_realizes
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ r_x : Fin m → R) :
    firstEval matrix z τ r_x = eval r_x (Algebra.firstVirtual matrix z τ) := by
  simp only [firstEval, eqWeight_eq, rowEval_eq, Algebra.firstVirtual_eval]

variable (pp : PublicParams)

/-- The witness query point consists of the low column coordinates. -/
def witnessPoint (r : Fin pp.ℓ_n → R) : Fin pp.ℓ_w → R :=
  fun i => r (Fin.castLE pp.ℓ_w_le_ℓ_n i)

/-- Reconstruct the assignment evaluation from the public input and the witness answer. -/
def assignmentEval (x : R1CS.Statement R pp.toSizeR1CS)
    (r : Fin pp.ℓ_n → R) (wValue : R) : R :=
  (∑ j : Fin (2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w),
    eqWeight (finFunctionFinEquiv.symm (Fin.castLE (Nat.sub_le _ _) j) :
      Fin pp.ℓ_n → R) r * x j) +
    (∏ i : Fin (pp.ℓ_n - pp.ℓ_w), r ⟨pp.ℓ_w + i.val, by omega⟩) * wValue

/-- Reconstructing the assignment from a witness-table evaluation realizes its MLE. -/
theorem assignmentEval_realizes (x : R1CS.Statement R pp.toSizeR1CS)
    (w : R1CS.Witness R pp.toSizeR1CS) (r : Fin pp.ℓ_n → R) :
    assignmentEval pp x r (tableEval w (witnessPoint pp r)) =
      eval r (MLE' (R1CS.𝕫 x w)) := by
  change _ = eval r (assignmentMLE pp x w)
  rw [assignment_mle_split pp x w r]
  dsimp only [R1CS.Witness, R1CS.Statement, R1CS.Size.n_x, PublicParams.toSizeR1CS] at w x
  simp only [assignmentEval, eqWeight_eq, tableEval, MLE'_eval]
  rfl

/-- The executable terminal arithmetic on the four oracle answers. -/
def terminalValue (x : R1CS.Statement R pp.toSizeR1CS) (r_y : Fin pp.ℓ_n → R)
    (ρ values : R1CS.MatrixIdx → R) (wValue : R) : R :=
  (ρ .A * values .A + ρ .B * values .B + ρ .C * values .C) *
    assignmentEval pp x r_y wValue

/-- The retained matrix and witness table family. -/
def OracleStatement : R1CS.MatrixIdx ⊕ Fin 1 → Type :=
  Sum.elim (R1CS.OracleStatement R pp.toSizeR1CS)
    (fun _ : Fin 1 => R1CS.Witness R pp.toSizeR1CS)

/-- The semantic terminal relation is the second virtual polynomial's claimed evaluation. -/
def terminalRelation (stmt : FinalStatement (R := R) pp)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : Prop :=
  eval stmt.r_y (Algebra.secondVirtual (fun i => oracles (.inl i))
    (R1CS.𝕫 stmt.x (oracles (.inr 0))) stmt.r_x stmt.ρ) = stmt.e

/-- Executable evaluation agrees with the second virtual polynomial. -/
theorem secondVirtual_realizes (x : R1CS.Statement R pp.toSizeR1CS)
    (matrix : ∀ i, R1CS.OracleStatement R pp.toSizeR1CS i)
    (w : R1CS.Witness R pp.toSizeR1CS) (r_x : Fin pp.ℓ_m → R)
    (ρ : R1CS.MatrixIdx → R) (r_y : Fin pp.ℓ_n → R) :
    terminalValue pp x r_y ρ (fun i => matrixEval (matrix i) r_x r_y)
      (tableEval w (witnessPoint pp r_y)) =
      eval r_y (Algebra.secondVirtual matrix (R1CS.𝕫 x w) r_x ρ) := by
  rw [Algebra.secondVirtual_eval_assignment]
  dsimp only [R1CS.OracleStatement, R1CS.Witness, R1CS.Statement, R1CS.Size.n_x,
    PublicParams.toSizeR1CS] at matrix w x
  unfold terminalValue assignmentEval
  simp only [matrixEval, tableEval, eqWeight_eq, MLE'_eval, Matrix.toMLE_rowSlice]
  rfl

end Spartan.Realization
