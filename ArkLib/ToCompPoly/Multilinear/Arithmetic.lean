/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Multilinear.Basic
public import ArkLib.ToCompPoly.Univariate.ArithmeticCost

/-!
# Measured construction of Boolean Lagrange tables

The arithmetic interpretation uses the same monadic recursion as the executable shared-table
builder. Profiles count field operations, independently of the coordinate values. Array
allocation, index arithmetic and memory accesses are outside these field-operation counts.
-/

@[expose] public section

namespace CompPoly.CMlPolynomialEval

open OracleComp OracleSpec

/-- Field-operation profile of the shared recursive Boolean Lagrange table construction. -/
def lagrangeBasisCost (n : ℕ) : ArithmeticCost
  | .mul => 2 ^ (n + 1) - 2
  | .sub => n
  | _ => 0

/-- A new coordinate complements its head once and multiplies each new output entry once. -/
theorem lagrangeBasisCost_succ (n : ℕ) (kind : ArithmeticCostKind) :
    lagrangeBasisCost (n + 1) kind = lagrangeBasisCost n kind +
      (if kind = .sub then 1 else 0) +
        2 ^ (n + 1) * (if kind = .mul then 1 else 0) := by
  cases kind <;> simp only [lagrangeBasisCost, ite_true, ite_false, reduceCtorEq,
    mul_one, mul_zero, add_zero]
  · have h : 2 ≤ 2 ^ (n + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
    omega

/-- The multiplication count adds exactly the size of the new output table. -/
theorem lagrangeBasisCost_mul_succ (n : ℕ) :
    lagrangeBasisCost (n + 1) .mul = lagrangeBasisCost n .mul + 2 ^ (n + 1) := by
  simpa using lagrangeBasisCost_succ n .mul

/-- The subtraction count adds exactly one complement per coordinate. -/
theorem lagrangeBasisCost_sub_succ (n : ℕ) :
    lagrangeBasisCost (n + 1) .sub = lagrangeBasisCost n .sub + 1 := by
  simpa using lagrangeBasisCost_succ n .sub

variable {F : Type} [CommRing F] [Inv F] [DecidableEq F]

/-- Interpret the shared Boolean-table builder using certified arithmetic requests.
The program requests no inversions or equality tests. -/
def lagrangeBasisProgram {n : ℕ} (w : Vector F n) :
    OracleComp (ArithmeticSpec F) (CMlPolynomialEval F n) :=
  lagrangeBasisWith 1 (fun x => Subtype.val <$> Arithmetic.sub 1 x)
    (fun x y => Subtype.val <$> Arithmetic.mul x y) w

/-- The measured interpretation returns the executable table and its exact operation profile. -/
theorem profileArithmetic_lagrangeBasisProgram {n : ℕ} (w : Vector F n) :
    profileArithmetic (lagrangeBasisProgram w) =
      (lagrangeBasisFast w, lagrangeBasisCost n) := by
  unfold lagrangeBasisProgram
  induction n with
  | zero =>
    simp only [lagrangeBasisWith, profileArithmetic_pure, lagrangeBasisFast_zero]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> norm_num [lagrangeBasisCost]
  | succ n ih =>
    rw [lagrangeBasisWith, profileArithmetic_bind, ih]
    dsimp only
    rw [profileArithmetic_bind]
    simp only [profileArithmetic_map, profileArithmetic_sub]
    rw [profileArithmetic_ofFnM_uniform
      (values := fun i : Fin (2 ^ (n + 1)) =>
        (if i.val % 2 = 0 then 1 - w.head else w.head) *
          (lagrangeBasisFast w.tail).get ⟨i.val / 2, by
            simp only [Nat.add_sub_cancel]
            have hi : i.val < 2 ^ n * 2 := by
              simpa only [pow_succ] using i.isLt
            omega⟩)
      (cost := arithmeticCost (ArithmeticOp.mul (0 : F) 0))]
    · apply Prod.ext
      · ext i hi
        simp only [Vector.getElem_ofFn, lagrangeBasisFast_succ, Vector.get_eq_getElem]
      · funext kind
        change lagrangeBasisCost n kind +
          ((if kind = .sub then 1 else 0) +
            2 ^ (n + 1) * (if kind = .mul then 1 else 0)) = _
        simpa only [add_assoc] using (lagrangeBasisCost_succ n kind).symm
    · intro i
      simp only [profileArithmetic_map, profileArithmetic_mul]
      apply Prod.ext
      · simp [Vector.get_eq_getElem, Fin.getElem_fin]
      · rfl

/-- Executing the arithmetic interpretation returns the canonical fast table. -/
theorem simulateQ_lagrangeBasisProgram {n : ℕ} (w : Vector F n) :
    simulateQ arithmeticAnswer (lagrangeBasisProgram w) = lagrangeBasisFast w := by
  rw [← profileArithmetic_fst, profileArithmetic_lagrangeBasisProgram]

end CompPoly.CMlPolynomialEval
