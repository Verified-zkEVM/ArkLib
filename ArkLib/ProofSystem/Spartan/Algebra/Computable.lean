/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Identities
public import CompPoly.Multivariate.Eval

/-!
# Executable Spartan virtual polynomials

The virtual polynomials are constructed by finite enumeration of the retained matrix and
assignment tables. Their polynomial interpretations agree with the algebraic definitions.
-/

@[expose] public section

namespace Spartan.Computable

open CPoly CPoly.CMvPolynomial MvPolynomial Matrix
open scoped BigOperators

variable {R : Type} [CommRing R] [BEq R] [LawfulBEq R] {m n : ℕ}

/-- Construct the row-product polynomial directly from the matrix-vector product table. -/
def rowProduct (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R) :
    CMvPolynomial m R :=
  ∑ b : Fin m → Fin 2,
    (∏ i : Fin m,
      ((1 - CMvPolynomial.C (b i : R)) * (1 - CMvPolynomial.X i) +
        CMvPolynomial.C (b i : R) * CMvPolynomial.X i)) *
      CMvPolynomial.C ((M *ᵥ z) (finFunctionFinEquiv b))

/-- The constructed row polynomial is the multilinear extension of the row-product table. -/
theorem rowProduct_toPolynomial (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) :
    CPoly.fromCMvPolynomial (rowProduct M z) = Algebra.rowProduct M z := by
  simp only [rowProduct, fromCMvPolynomial_sum, fromCMvPolynomial_prod, CPoly.map_mul,
    CPoly.map_add, sub_eq_add_neg, CPoly.map_neg, CPoly.map_one, fromCMvPolynomial_C,
    fromCMvPolynomial_X, Algebra.rowProduct, MLE', MLE, eqPolynomial_expanded,
    Function.comp_apply]

/-- Construct the assignment polynomial from its public and witness tables. -/
def assignment (pp : PublicParams) (x : R1CS.Statement R pp.toSizeR1CS)
    (w : R1CS.Witness R pp.toSizeR1CS) : CMvPolynomial pp.ℓ_n R :=
  ∑ b : Fin pp.ℓ_n → Fin 2,
    (∏ i : Fin pp.ℓ_n,
      ((1 - CMvPolynomial.C (b i : R)) * (1 - CMvPolynomial.X i) +
        CMvPolynomial.C (b i : R) * CMvPolynomial.X i)) *
      CMvPolynomial.C (R1CS.𝕫 x w (finFunctionFinEquiv b))

/-- The assignment construction has exactly the concatenated assignment's interpretation. -/
theorem assignment_toPolynomial (pp : PublicParams) (x : R1CS.Statement R pp.toSizeR1CS)
    (w : R1CS.Witness R pp.toSizeR1CS) :
    CPoly.fromCMvPolynomial (assignment pp x w) = MLE' (R1CS.𝕫 x w) := by
  simp only [assignment, fromCMvPolynomial_sum, fromCMvPolynomial_prod, CPoly.map_mul,
    CPoly.map_add, sub_eq_add_neg, CPoly.map_neg, CPoly.map_one, fromCMvPolynomial_C,
    fromCMvPolynomial_X, MLE', MLE, eqPolynomial_expanded]
  rfl

/-- Construct a matrix slice by evaluating the row equality weights in its column tables. -/
def matrixSlice (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (r_x : Fin m → R) :
    CMvPolynomial n R :=
  ∑ b : Fin n → Fin 2,
    (∏ i : Fin n,
      ((1 - CMvPolynomial.C (b i : R)) * (1 - CMvPolynomial.X i) +
        CMvPolynomial.C (b i : R) * CMvPolynomial.X i)) *
      CMvPolynomial.C (∑ a : Fin m → Fin 2,
        (∏ i : Fin m, ((a i : R) * r_x i + (1 - (a i : R)) * (1 - r_x i))) *
          M (finFunctionFinEquiv a) (finFunctionFinEquiv b))

/-- The constructed slice fixes the row coordinates of the matrix multilinear extension. -/
theorem matrixSlice_toPolynomial (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) :
    CPoly.fromCMvPolynomial (matrixSlice M r_x) =
      MvPolynomial.eval (MvPolynomial.C ∘ r_x) M.toMLE := by
  rw [Matrix.toMLE_rowSlice]
  have h (b : Fin (2 ^ n)) :
      eval r_x (MLE' (fun a => M a b)) =
        ∑ a : Fin m → Fin 2,
          (∏ i : Fin m, ((a i : R) * r_x i + (1 - (a i : R)) * (1 - r_x i))) *
            M (finFunctionFinEquiv a) b := by
    simp only [MLE', MLE_eval, eqTilde_eq_prod, Function.comp_apply]
  simp_rw [h]
  simp only [matrixSlice, fromCMvPolynomial_sum, fromCMvPolynomial_prod, CPoly.map_mul,
    CPoly.map_add, sub_eq_add_neg, CPoly.map_neg, CPoly.map_one, fromCMvPolynomial_C,
    fromCMvPolynomial_X, MLE', MLE, eqPolynomial_expanded, Function.comp_apply]

/-- Construct the first virtual polynomial from equality weights and row products. -/
def firstVirtual (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) : CMvPolynomial m R :=
  (∏ i : Fin m,
    ((1 - CMvPolynomial.C (τ i)) * (1 - CMvPolynomial.X i) +
      CMvPolynomial.C (τ i) * CMvPolynomial.X i)) *
    (rowProduct (matrix .A) z * rowProduct (matrix .B) z - rowProduct (matrix .C) z)

/-- The first computational virtual polynomial agrees with the semantic polynomial. -/
theorem firstVirtual_toPolynomial
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) :
    CPoly.fromCMvPolynomial (firstVirtual matrix z τ) = Algebra.firstVirtual matrix z τ := by
  simp only [firstVirtual, fromCMvPolynomial_prod, CPoly.map_mul, CPoly.map_add,
    sub_eq_add_neg, CPoly.map_neg, CPoly.map_one, fromCMvPolynomial_C, fromCMvPolynomial_X,
    rowProduct_toPolynomial, Algebra.firstVirtual, Algebra.residual, eqPolynomial_expanded]

/-- The first computational virtual polynomial has individual degree at most three. -/
theorem firstVirtual_degreeOf_le
    (matrix : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (z : Fin (2 ^ n) → R) (τ : Fin m → R) (i : Fin m) :
    (firstVirtual matrix z τ).degreeOf i ≤ 3 := by
  rw [congrFun (CPoly.degreeOf_equiv (S := R) (p := firstVirtual matrix z τ)) i,
    firstVirtual_toPolynomial]
  exact Algebra.firstVirtual_degree_le_three matrix z τ i

/-- Construct the second virtual polynomial from the three matrix slices and assignment. -/
def secondVirtual (pp : PublicParams) (x : R1CS.Statement R pp.toSizeR1CS)
    (matrix : ∀ i, R1CS.OracleStatement R pp.toSizeR1CS i)
    (w : R1CS.Witness R pp.toSizeR1CS) (r_x : Fin pp.ℓ_m → R)
    (ρ : R1CS.MatrixIdx → R) : CMvPolynomial pp.ℓ_n R :=
  (CMvPolynomial.C (ρ .A) * matrixSlice (matrix .A) r_x +
    CMvPolynomial.C (ρ .B) * matrixSlice (matrix .B) r_x +
    CMvPolynomial.C (ρ .C) * matrixSlice (matrix .C) r_x) * assignment pp x w

/-- The second computational virtual polynomial agrees with the semantic polynomial. -/
theorem secondVirtual_toPolynomial (pp : PublicParams) (x : R1CS.Statement R pp.toSizeR1CS)
    (matrix : ∀ i, R1CS.OracleStatement R pp.toSizeR1CS i)
    (w : R1CS.Witness R pp.toSizeR1CS) (r_x : Fin pp.ℓ_m → R)
    (ρ : R1CS.MatrixIdx → R) :
    CPoly.fromCMvPolynomial (secondVirtual pp x matrix w r_x ρ) =
      Algebra.secondVirtual matrix (R1CS.𝕫 x w) r_x ρ := by
  simp only [secondVirtual, CPoly.map_mul, CPoly.map_add, fromCMvPolynomial_C,
    assignment_toPolynomial, Algebra.secondVirtual]
  rw [matrixSlice_toPolynomial (matrix .A), matrixSlice_toPolynomial (matrix .B),
    matrixSlice_toPolynomial (matrix .C)]

/-- The second computational virtual polynomial has individual degree at most two. -/
theorem secondVirtual_degreeOf_le (pp : PublicParams) (x : R1CS.Statement R pp.toSizeR1CS)
    (matrix : ∀ i, R1CS.OracleStatement R pp.toSizeR1CS i)
    (w : R1CS.Witness R pp.toSizeR1CS) (r_x : Fin pp.ℓ_m → R)
    (ρ : R1CS.MatrixIdx → R) (i : Fin pp.ℓ_n) :
    (secondVirtual pp x matrix w r_x ρ).degreeOf i ≤ 2 := by
  rw [congrFun (CPoly.degreeOf_equiv
    (S := R) (p := secondVirtual pp x matrix w r_x ρ)) i, secondVirtual_toPolynomial]
  exact Algebra.secondVirtual_degree_le_two matrix (R1CS.𝕫 x w) r_x ρ i

end Spartan.Computable
