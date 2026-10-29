/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Layout

/-!
# Spartan polynomial identities

The matrix multilinear extension takes the row point first and the column point second.
The row products are multilinear extensions of matrix-vector products. Their quadratic residual
and its multilinear interpolation are different polynomials: the first sumcheck uses the residual
times an equality polynomial, while its initial claim is an evaluation of the interpolation.

These identities use only the assembled assignment, independently of the public/witness layout.
The R1CS equivalences specialize to the public prefix and witness suffix used by `R1CS.𝕫`.
Polynomial views are noncomputable because Mathlib's `MvPolynomial` representation uses
nonconstructive coefficient equality; the underlying matrix-vector and residual tables are
computable.
-/

@[expose] public section

namespace Spartan.Algebra

open MvPolynomial Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The multilinear row-product polynomial `L_M = MLE(Mz)`. -/
noncomputable def rowProduct (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) : MvPolynomial (Fin m) R :=
  MLE' (M *ᵥ z)

/-- The quadratic row residual `F = L_A L_B - L_C`. -/
noncomputable def residual
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) : MvPolynomial (Fin m) R :=
  rowProduct (matrix .A) z * rowProduct (matrix .B) z - rowProduct (matrix .C) z

/-- The residual of each row of the constraint system. -/
def residualTable (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) : Fin (2 ^ m) → R :=
  fun a => (matrix .A *ᵥ z) a * (matrix .B *ᵥ z) a - (matrix .C *ᵥ z) a

/-- The multilinear interpolation `g` of the residual table. -/
noncomputable def residualMLE
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) : MvPolynomial (Fin m) R :=
  MLE' (residualTable matrix z)

/-- The first sumcheck polynomial `G_τ(X) = eq(τ,X) F(X)`. -/
noncomputable def firstVirtual
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) : MvPolynomial (Fin m) R :=
  eqPolynomial τ * residual matrix z

/-- Sum of a polynomial over its Boolean cube. -/
noncomputable def cubeSum (p : MvPolynomial (Fin n) R) : R :=
  ∑ b : Fin n → Fin 2, eval (b : Fin n → R) p

/-- The second sumcheck polynomial `H_{ρ,r_x}`, with three independent coefficients. -/
noncomputable def secondVirtual
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) (ρ : R1CS.MatrixIdx → R) :
    MvPolynomial (Fin n) R :=
  (C (ρ .A) * eval (C ∘ r_x) (matrix .A).toMLE +
    C (ρ .B) * eval (C ∘ r_x) (matrix .B).toMLE +
    C (ρ .C) * eval (C ∘ r_x) (matrix .C).toMLE) * MLE' z

@[simp]
theorem rowProduct_eval_zeroOne (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (b : Fin m → Fin 2) :
    eval (b : Fin m → R) (rowProduct M z) = (M *ᵥ z) (finFunctionFinEquiv b) := by
  exact MLE_eval_zeroOne b _

@[simp]
theorem residual_eval_zeroOne
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (b : Fin m → Fin 2) :
    eval (b : Fin m → R) (residual matrix z) =
      residualTable matrix z (finFunctionFinEquiv b) := by
  simp [residual, residualTable]

/-- Boolean vanishing of the residual is the matrix-vector constraint equation. -/
theorem residual_zero_iff_matrix_relation
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) :
    (∀ b : Fin m → Fin 2, eval (b : Fin m → R) (residual matrix z) = 0) ↔
      (matrix .A *ᵥ z) * (matrix .B *ᵥ z) = matrix .C *ᵥ z := by
  simp only [residual_eval_zeroOne, residualTable, sub_eq_zero]
  constructor
  · intro h
    funext a
    simpa only [Equiv.apply_symm_apply, Pi.mul_apply] using h (finFunctionFinEquiv.symm a)
  · intro h b
    exact congrFun h (finFunctionFinEquiv b)

/-- Boolean vanishing of the residual is precisely satisfaction of the R1CS relation. -/
theorem residual_zero_iff_r1cs (n_w : ℕ) (hn_w : n_w ≤ 2 ^ n)
    (x : Fin (2 ^ n - n_w) → R)
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (w : Fin n_w → R) :
    let sz : R1CS.Size := ⟨2 ^ m, 2 ^ n, n_w, hn_w⟩
    (∀ b : Fin m → Fin 2,
      eval (b : Fin m → R) (residual matrix (R1CS.𝕫 (sz := sz) x w)) = 0) ↔
      R1CS.relation R sz x matrix w := by
  exact residual_zero_iff_matrix_relation matrix _

/-- The residual interpolation is zero exactly when all row constraints hold. -/
theorem residualMLE_zero_iff_matrix_relation
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) :
    residualMLE matrix z = 0 ↔
      (matrix .A *ᵥ z) * (matrix .B *ᵥ z) = matrix .C *ᵥ z := by
  rw [residualMLE, MLE', MLE_eq_zero_iff]
  simpa only [Function.comp_apply, residual_eval_zeroOne] using
    residual_zero_iff_matrix_relation matrix z

/-- The residual interpolation is zero exactly when the R1CS is satisfied. -/
theorem residualMLE_zero_iff_r1cs (n_w : ℕ) (hn_w : n_w ≤ 2 ^ n)
    (x : Fin (2 ^ n - n_w) → R)
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (w : Fin n_w → R) :
    let sz : R1CS.Size := ⟨2 ^ m, 2 ^ n, n_w, hn_w⟩
    residualMLE matrix (R1CS.𝕫 (sz := sz) x w) = 0 ↔
      R1CS.relation R sz x matrix w := by
  exact residualMLE_zero_iff_matrix_relation matrix _

/-- Each row product is multilinear. -/
theorem rowProduct_degree_le_one (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (i : Fin m) : degreeOf i (rowProduct M z) ≤ 1 :=
  MLE_degreeOf _ i

/-- The row residual has individual degree at most two. -/
theorem residual_degree_le_two
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (i : Fin m) : degreeOf i (residual matrix z) ≤ 2 := by
  apply (degreeOf_sub_le i _ _).trans
  refine max_le ?_ ((rowProduct_degree_le_one _ _ i).trans (by decide))
  exact (degreeOf_mul_le i _ _).trans
    (Nat.add_le_add (rowProduct_degree_le_one _ _ i) (rowProduct_degree_le_one _ _ i))

/-- Equality weighting raises the residual's individual degree to at most three. -/
theorem firstVirtual_degree_le_three
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) (i : Fin m) :
    degreeOf i (firstVirtual matrix z τ) ≤ 3 := by
  exact (degreeOf_mul_le i _ _).trans
    (Nat.add_le_add (eqPolynomial_degreeOf τ i) (residual_degree_le_two matrix z i))

/-- The first sumcheck's cube sum is an evaluation of the residual interpolation. -/
theorem firstVirtual_cubeSum_eq_residualMLE
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) :
    cubeSum (firstVirtual matrix z τ) = eval τ (residualMLE matrix z) := by
  simp only [cubeSum, firstVirtual, map_mul, residual_eval_zeroOne, residualMLE, MLE', MLE_eval]
  apply Finset.sum_congr rfl
  intro b _
  rw [eqPolynomial_symm]
  rfl

/-- The residual interpolation is multilinear even when the residual is quadratic. -/
theorem residualMLE_degree_le_one
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (i : Fin m) : degreeOf i (residualMLE matrix z) ≤ 1 :=
  MLE_degreeOf _ i

/-- Evaluation of the first virtual polynomial from the three row-product evaluations. -/
theorem firstVirtual_eval
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ r_x : Fin m → R) :
    eval r_x (firstVirtual matrix z τ) = eqTilde τ r_x *
      (eval r_x (rowProduct (matrix .A) z) * eval r_x (rowProduct (matrix .B) z) -
        eval r_x (rowProduct (matrix .C) z)) := by
  simp [firstVirtual, residual, eqTilde]

/-- A row-product evaluation is the Boolean-column contraction of the matrix slice and assignment.
The matrix slice fixes the row coordinates before evaluating the column coordinates. -/
theorem rowProduct_eval_eq_contraction (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) :
    eval r_x (rowProduct M z) = ∑ b : Fin n → Fin 2,
      eval (b : Fin n → R) (eval (C ∘ r_x) M.toMLE) *
        eval (b : Fin n → R) (MLE' z) := by
  simp_rw [Matrix.toMLE_rowSlice_eval_zeroOne]
  simp only [MLE', MLE_eval_zeroOne, Function.comp_apply]
  simp only [rowProduct, MLE', MLE_eval, Function.comp_apply]
  simp only [mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Equiv.sum_comp finFunctionFinEquiv]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The second virtual polynomial has individual degree at most two. -/
theorem secondVirtual_degree_le_two
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) (ρ : R1CS.MatrixIdx → R)
    (i : Fin n) : degreeOf i (secondVirtual matrix z r_x ρ) ≤ 2 := by
  have h (j : R1CS.MatrixIdx) :
      degreeOf i (C (ρ j) * eval (C ∘ r_x) (matrix j).toMLE) ≤ 1 := by
    calc
      _ ≤ degreeOf i (C (ρ j)) +
          degreeOf i (eval (C ∘ r_x) (matrix j).toMLE) := degreeOf_mul_le i _ _
      _ ≤ 0 + 1 := Nat.add_le_add (le_of_eq (degreeOf_C _ _))
        (Matrix.toMLE_rowSlice_degreeOf _ _ i)
  apply (degreeOf_mul_le i _ _).trans
  refine Nat.add_le_add ?_ (MLE_degreeOf _ i)
  apply (degreeOf_add_le i _ _).trans
  exact max_le ((degreeOf_add_le i _ _).trans (max_le (h .A) (h .B))) (h .C)

/-- The second sumcheck's initial claim batches the three row-product evaluations. -/
theorem secondVirtual_cubeSum_eq
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) (ρ : R1CS.MatrixIdx → R) :
    cubeSum (secondVirtual matrix z r_x ρ) =
      ρ .A * eval r_x (rowProduct (matrix .A) z) +
      ρ .B * eval r_x (rowProduct (matrix .B) z) +
      ρ .C * eval r_x (rowProduct (matrix .C) z) := by
  simp only [cubeSum, secondVirtual, map_mul, map_add, eval_C]
  simp_rw [add_mul, mul_assoc]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← rowProduct_eval_eq_contraction, ← rowProduct_eval_eq_contraction,
    ← rowProduct_eval_eq_contraction]

/-- The terminal evaluation uses three matrix oracle values and one assignment oracle value. -/
theorem secondVirtual_eval
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (r_x : Fin m → R) (ρ : R1CS.MatrixIdx → R)
    (r_y : Fin n → R) :
    eval r_y (secondVirtual matrix z r_x ρ) =
      (ρ .A * eval r_y (eval (C ∘ r_x) (matrix .A).toMLE) +
        ρ .B * eval r_y (eval (C ∘ r_x) (matrix .B).toMLE) +
        ρ .C * eval r_y (eval (C ∘ r_x) (matrix .C).toMLE)) * eval r_y (MLE' z) := by
  simp [secondVirtual]

/-- The terminal evaluation uses three matrix values and a single witness MLE value.
The public contribution is computed from the public input at the full column point. -/
theorem secondVirtual_eval_assignment (pp : PublicParams)
    (x : R1CS.Statement R pp.toSizeR1CS)
    (matrix : ∀ idx, R1CS.OracleStatement R pp.toSizeR1CS idx)
    (w : R1CS.Witness R pp.toSizeR1CS) (r_x : Fin pp.ℓ_m → R)
    (ρ : R1CS.MatrixIdx → R) (r_y : Fin pp.ℓ_n → R) :
    eval r_y (secondVirtual matrix (R1CS.𝕫 x w) r_x ρ) =
      (ρ .A * eval r_y (eval (C ∘ r_x) (matrix .A).toMLE) +
        ρ .B * eval r_y (eval (C ∘ r_x) (matrix .B).toMLE) +
        ρ .C * eval r_y (eval (C ∘ r_x) (matrix .C).toMLE)) *
      ((∑ j : Fin (2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w),
        eqTilde (finFunctionFinEquiv.symm (Fin.castLE (Nat.sub_le _ _) j) :
          Fin pp.ℓ_n → R) r_y * x j) +
        (∏ i : Fin (pp.ℓ_n - pp.ℓ_w), r_y ⟨pp.ℓ_w + i.val, by omega⟩) *
          eval (fun i : Fin pp.ℓ_w => r_y (Fin.castLE pp.ℓ_w_le_ℓ_n i)) (MLE' w)) := by
  rw [secondVirtual_eval (m := pp.ℓ_m) (n := pp.ℓ_n) matrix (R1CS.𝕫 x w) r_x ρ r_y]
  exact congrArg (_ * ·) (assignment_mle_split pp x w r_y)

end Spartan.Algebra
