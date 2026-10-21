/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticCost
public import CompPoly.Univariate.Basic

import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Basic

/-!
# Measured power-sum evaluation

Evaluation follows the coefficient power sum. Each power is computed by repeated primitive
multiplication, and every coefficient is read through the arithmetic instruction interface.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec

section Monoid
variable {F : Type} [Zero F] [Add F] [Sub F] [Monoid F] [Inv F] [DecidableEq F]

/-- Accumulate a consecutive portion of the coefficient power sum. -/
def evalRawFrom (p : CPolynomial.Raw F) (x : F) (i : ℕ) (acc : F) :
    (t : ℕ) → OracleComp (ArithmeticSpec F) {r : F // r =
      (List.range' i t).foldl (fun a j ↦ a + (p[j]?.getD 0) * x ^ j) acc}
  | 0 => do
    tick
    pure ⟨acc, rfl⟩
  | t + 1 => do
    tick
    let a ← coefficientRead p i
    let b ← power x i
    let c ← mul a.val b.val
    let d ← add acc c.val
    let r ← evalRawFrom p x (i + 1) d.val t
    pure ⟨r.val, by rw [r.property, d.property, c.property, b.property, a.property]; rfl⟩

/-- The exact profile of a consecutive power-sum accumulation. -/
theorem profileArithmetic_evalRawFrom (p : CPolynomial.Raw F) (x : F) (i : ℕ) (acc : F) (t : ℕ) :
    (profileArithmetic (evalRawFrom p x i acc t)).2 = fun kind ↦
      if kind = .add ∨ kind = .coefficientRead then t
      else if kind = .mul then ((List.range' i t).map (fun j ↦ j + 1)).sum
      else if kind = .metadata then ((List.range' i t).map (fun j ↦ j + 1)).sum + t + 1
      else 0 := by
  induction t generalizing i acc with
  | zero =>
    funext kind
    cases kind <;> simp [evalRawFrom, arithmeticCost, ArithmeticOp.costKind]
  | succ t ih =>
    funext kind
    cases kind <;>
      simp [evalRawFrom, profileArithmetic_bind, profileArithmetic_power, ih, List.range'_succ,
        arithmeticCost, ArithmeticOp.costKind, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Monoid

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

private theorem toList_zipIdx_eq_range {R : Type} [Zero R] (p : Array R) :
    p.zipIdx.toList = (List.range' 0 p.size).map (fun i ↦ (p[i]?.getD 0, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have h : i < p.size := by simpa using hi
    simp [List.getElem_range', h]

/-- Evaluate the coefficient power sum, exposing each multiplication and coefficient read. -/
def evalRaw (p : CPolynomial.Raw F) (x : F) :
    OracleComp (ArithmeticSpec F) {y : F // y = CPolynomial.Raw.eval x p} := do
  let r ← evalRawFrom p x 0 0 p.size
  pure ⟨r.val, by
    rw [r.property, CPolynomial.Raw.eval, CPolynomial.Raw.eval₂, ← Array.foldl_toList,
      toList_zipIdx_eq_range, List.foldl_map]
    rfl⟩

/-- The exact profile of coefficient power-sum evaluation. -/
theorem profileArithmetic_evalRaw (p : CPolynomial.Raw F) (x : F) :
    (profileArithmetic (evalRaw p x)).2 = fun kind ↦
      if kind = .add ∨ kind = .coefficientRead then p.size
      else if kind = .mul then ((List.range' 0 p.size).map (fun j ↦ j + 1)).sum
      else if kind = .metadata then
        ((List.range' 0 p.size).map (fun j ↦ j + 1)).sum + p.size + 1
      else 0 := by
  simp [evalRaw, profileArithmetic_evalRawFrom]

private theorem powerSum_le (i t : ℕ) :
    ((List.range' i t).map (fun j ↦ j + 1)).sum ≤ t * (i + t) := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    have h := ih (i + 1)
    nlinarith

/-- The evaluator's multiplication count is at most the square of its coefficient count. -/
theorem profileArithmetic_evalRaw_mul_le (p : CPolynomial.Raw F) (x : F) :
    (profileArithmetic (evalRaw p x)).2 .mul ≤ p.size ^ 2 := by
  simpa [profileArithmetic_evalRaw, pow_two] using powerSum_le 0 p.size

/-- Additions and multiplications each satisfy the quadratic evaluation bound. -/
theorem profileArithmetic_evalRaw_add_mul_le (p : CPolynomial.Raw F) (x : F) :
    (profileArithmetic (evalRaw p x)).2 .add ≤ (p.size + 1) ^ 2 ∧
    (profileArithmetic (evalRaw p x)).2 .mul ≤ (p.size + 1) ^ 2 := by
  constructor
  · have h : (profileArithmetic (evalRaw p x)).2 .add = p.size := by
      simp [profileArithmetic_evalRaw]
    rw [h]
    nlinarith
  · exact (profileArithmetic_evalRaw_mul_le p x).trans (Nat.pow_le_pow_left (Nat.le_succ p.size) 2)

end Semiring

end CompPoly.Arithmetic

namespace CompPoly.CPolynomial

/-- Raw-array evaluation of a canonical polynomial is its canonical evaluation. -/
@[simp]
theorem Raw.eval_val {R : Type} [Semiring R] (x : R) (p : CPolynomial R) :
    Raw.eval x p.val = p.eval x := by
  rfl

end CompPoly.CPolynomial
