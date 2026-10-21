/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticCost

/-!
# Certified arithmetic powers and their costs

Successive squaring and fixed-length binary powering use explicit multiplication instructions.
Their profiles count all arithmetic coordinates and designated control ticks.
-/

@[expose] public section

namespace CompPoly.Arithmetic

open OracleComp

variable {F : Type} [Monoid F] [Zero F] [Add F] [Sub F] [Inv F] [DecidableEq F]

/-- Apply `t` successive squarings, retaining a proof of the resulting power. -/
def squareIter (x : F) : (t : ℕ) → OracleComp (ArithmeticSpec F) {y : F // y = x ^ (2 ^ t)}
  | 0 => pure ⟨x, by simp⟩
  | t + 1 => do
    tick
    let y ← squareIter x t
    let z ← mul y.val y.val
    pure ⟨z.val, by
      calc
        z.val = y.val * y.val := z.property
        _ = (x ^ (2 ^ t)) ^ 2 := by rw [y.property, pow_two]
        _ = x ^ (2 ^ t * 2) := (pow_mul x _ _).symm
        _ = x ^ (2 ^ (t + 1)) := by rw [Nat.pow_succ]⟩

/-- Compute a power by a fixed number of binary exponent steps. -/
def powerBits (x : F) : (bits m : ℕ) → m < 2 ^ bits →
    OracleComp (ArithmeticSpec F) {y : F // y = x ^ m}
  | 0, m, h => pure ⟨1, by
      have hm : m = 0 := by simpa using h
      simp [hm]⟩
  | bits + 1, m, h => do
    tick
    let y ← powerBits x bits (m / 2) (by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa [Nat.pow_succ] using h)
    let sq ← mul y.val y.val
    if hodd : m % 2 = 1 then
      let z ← mul sq.val x
      pure ⟨z.val, by
        calc
          z.val = (x ^ (m / 2) * x ^ (m / 2)) * x := by
            rw [z.property, sq.property, y.property]
          _ = x ^ (m / 2 + m / 2 + 1) := by rw [pow_add, pow_add, pow_one]
          _ = x ^ m := by congr 1; omega⟩
    else
      pure ⟨sq.val, by
        rw [sq.property, y.property, ← pow_add]
        congr 1
        omega⟩

/-- Successive squaring performs one multiplication and control tick per exponent step. -/
theorem profileArithmetic_squareIter (x : F) (t : ℕ) :
    (profileArithmetic (squareIter x t)).2 =
      fun kind ↦ if kind = .mul ∨ kind = .metadata then t else 0 := by
  induction t with
  | zero =>
    funext kind
    simp [squareIter]
  | succ t ih =>
    funext kind
    cases kind <;>
      simp [squareIter, profileArithmetic_bind, profileArithmetic_map,
        arithmeticCost, ArithmeticOp.costKind, ih, Nat.add_comm]

/-- Binary powering uses at most two multiplications and one control tick per bit. -/
theorem profileArithmetic_powerBits_apply_le (x : F) (bits m : ℕ) (h : m < 2 ^ bits)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (powerBits x bits m h)).2 kind ≤
      if kind = .mul then 2 * bits else if kind = .metadata then bits else 0 := by
  induction bits generalizing m with
  | zero =>
    simp [powerBits]
  | succ bits ih =>
    have hq : m / 2 < 2 ^ bits := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
      simpa [Nat.pow_succ] using h
    have hprev := ih (m / 2) hq
    by_cases hodd : m % 2 = 1
    · cases kind <;>
        simp [powerBits, hodd, profileArithmetic_bind,
          arithmeticCost, ArithmeticOp.costKind] at hprev ⊢ <;> omega
    · cases kind <;>
        simp [powerBits, hodd, profileArithmetic_bind,
          arithmeticCost, ArithmeticOp.costKind] at hprev ⊢ <;> omega

end CompPoly.Arithmetic
