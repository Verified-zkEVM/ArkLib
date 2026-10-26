/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Multilinear.Fold
public import ArkLib.ToCompPoly.Multilinear.Arithmetic

/-!
# Measured adjacent-pair multilinear folding

The program reads each adjacent pair once and computes `a + r * (b - a)` in little-endian order.
Its deterministic erasure agrees with the existing head fold by a formal ring identity, and
therefore inherits the formal partial-evaluation theorem. Each output uses one multiplication.

Profiles count primitive requests, with no inversion requests. The instruction interface still
requires an inverse operation and decidable equality; no inverse laws or field premise are used.
Index arithmetic, vector construction, allocation and machine runtime are separate costs.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec
namespace CompPoly.CMlPolynomialEval
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F]

/-- Interpolate every adjacent pair using its difference and one multiplication. -/
def evalMleLayerProgram {n : Nat} (table : CMlPolynomialEval F (n + 1)) (r : F) :
    OracleComp (ArithmeticSpec F) (CMlPolynomialEval F n) :=
  Vector.ofFnM fun j : Fin (2 ^ n) => do
    let a ← Arithmetic.valueRead table.toArray (2 * j.val)
    let b ← Arithmetic.valueRead table.toArray (2 * j.val + 1)
    let slope ← Arithmetic.sub b.val a.val
    let term ← Arithmetic.mul r slope.val
    let value ← Arithmetic.add a.val term.val
    pure value.val

/-- Exact requests per head-fold output: two reads and one addition, difference and product. -/
def evalMleLayerCost (n : Nat) : ArithmeticCost
  | .add | .sub | .mul => 2 ^ n
  | .valueRead => 2 ^ (n + 1)
  | _ => 0

/-- The actual fold program returns the existing folded table with its exact primitive profile. -/
theorem profileArithmetic_evalMleLayerProgram {n : Nat}
    (table : CMlPolynomialEval F (n + 1)) (r : F) :
    profileArithmetic (evalMleLayerProgram table r) =
      (evalMleLayer table r, evalMleLayerCost n) := by
  unfold evalMleLayerProgram
  rw [profileArithmetic_ofFnM_uniform
    (values := fun j : Fin (2 ^ n) => (evalMleLayer table r).get j)
    (cost := fun kind => if kind = .valueRead then 2
      else if kind = .add ∨ kind = .sub ∨ kind = .mul then 1 else 0)]
  · apply Prod.ext
    · ext i hi
      simp [Vector.get_eq_getElem]
    · funext kind
      cases kind <;> simp [evalMleLayerCost, pow_succ]
  · intro j
    have h0 : 2 * j.val < 2 ^ (n + 1) := by rw [pow_succ]; omega
    have h1 : 2 * j.val + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
    simp only [profileArithmetic_bind, profileArithmetic_valueRead, profileArithmetic_sub,
      profileArithmetic_mul, profileArithmetic_add, profileArithmetic_pure]
    apply Prod.ext
    · rw [evalMleLayer_get]
      simp [Vector.get_eq_getElem, h0, h1]
      ring
    · funext kind
      cases kind <;> simp [arithmeticCost, ArithmeticOp.costKind]

/-- Executing the measured fold itself returns the canonical adjacent-pair fold. -/
theorem simulateQ_evalMleLayerProgram {n : Nat}
    (table : CMlPolynomialEval F (n + 1)) (r : F) :
    simulateQ arithmeticAnswer (evalMleLayerProgram table r) = evalMleLayer table r := by
  rw [← profileArithmetic_fst, profileArithmetic_evalMleLayerProgram]

end CompPoly.CMlPolynomialEval
