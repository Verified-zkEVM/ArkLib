/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost
public import ArkLib.ToCompPoly.Univariate.Raw.Size

import all CompPoly.Univariate.Raw.Ops

/-!
# Exact profiles of padded convolution

The row counts include zero-padding additions even when the second coefficient array is empty.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
section Operations
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- A convolution row adds the scalar-product profile, padded-addition profile, and tail. -/
theorem profileArithmetic_mulRawFrom_succ (p q : CPolynomial.Raw F) (i : ℕ)
    (acc : CPolynomial.Raw F) (t : ℕ) :
    (profileArithmetic (mulRawFrom p q i acc (t + 1))).2 =
      let b := CPolynomial.Raw.smul (p[i]?.getD 0) q
      let c := CPolynomial.Raw.addRaw acc (CPolynomial.Raw.mulPowX i b)
      arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F) +
        arithmeticCost (.coefficientRead p i) +
        (profileArithmetic (smulRaw (p[i]?.getD 0) q)).2 +
        (profileArithmetic (addRaw acc (CPolynomial.Raw.mulPowX i b))).2 +
        (profileArithmetic (mulRawFrom p q (i + 1) c t)).2 := by
  funext kind
  simp [mulRawFrom, profileArithmetic_bind, Nat.add_assoc]

/-- The exact convolution profile when the accumulated rows fit their current padding. -/
theorem profileArithmetic_mulRawFrom (p q : CPolynomial.Raw F) (i : ℕ)
    (acc : CPolynomial.Raw F) (t : ℕ) (hacc : acc.size ≤ q.size + i) :
    (profileArithmetic (mulRawFrom p q i acc t)).2 =
      let a := ((List.range' i t).map (fun j ↦ q.size + j)).sum
      fun kind ↦ if kind = .add then a
        else if kind = .mul then t * q.size
        else if kind = .coefficientRead then t * (q.size + 1) + 2 * a
        else if kind = .metadata then t * (q.size + 3) + a + 1
        else 0 := by
  induction t generalizing i acc with
  | zero =>
    funext kind
    cases kind <;> simp [mulRawFrom, arithmeticCost, ArithmeticOp.costKind]
  | succ t ih =>
    have hb : (CPolynomial.Raw.smul (p[i]?.getD 0) q).size = q.size :=
      CPolynomial.Raw.size_smul _ _
    have hc : (CPolynomial.Raw.mulPowX i
        (CPolynomial.Raw.smul (p[i]?.getD 0) q)).size = q.size + i := by
      rw [CPolynomial.Raw.size_mulPowX, hb]
      omega
    have ha : (CPolynomial.Raw.addRaw acc (CPolynomial.Raw.mulPowX i
        (CPolynomial.Raw.smul (p[i]?.getD 0) q))).size = q.size + i := by
      rw [CPolynomial.Raw.size_addRaw, hc, max_eq_right hacc]
    have hnext : (CPolynomial.Raw.addRaw acc (CPolynomial.Raw.mulPowX i
        (CPolynomial.Raw.smul (p[i]?.getD 0) q))).size ≤ q.size + (i + 1) := by
      rw [ha]
      omega
    have hmax : max acc.size (i + q.size) = i + q.size := by omega
    funext kind
    rw [profileArithmetic_mulRawFrom_succ]
    cases kind <;>
      simp [profileArithmetic_smulRaw, profileArithmetic_addRaw, hc, hmax, ih _ _ hnext,
        List.range'_succ, arithmeticCost, ArithmeticOp.costKind, Nat.add_mul,
        Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Operations

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

/-- The exact padded-convolution profile, including asymmetric empty-array padding. -/
theorem profileArithmetic_mulRaw (p q : CPolynomial.Raw F) :
    (profileArithmetic (mulRaw p q)).2 =
      let a := ((List.range' 0 p.size).map (fun j ↦ q.size + j)).sum
      fun kind ↦ if kind = .add then a
        else if kind = .mul then p.size * q.size
        else if kind = .coefficientRead then p.size * (q.size + 1) + 2 * a
        else if kind = .metadata then p.size * (q.size + 3) + a + 1
        else 0 := by
  simpa [mulRaw] using profileArithmetic_mulRawFrom p q 0 #[] p.size (by simp)

private theorem rowSum_le_one (a b : ℕ) (ha : a ≤ 1) :
    ((List.range' 0 a).map (fun j ↦ b + j)).sum ≤ b := by
  cases a with
  | zero => simp
  | succ a =>
    have h : a = 0 := by omega
    subst a
    simp [List.range'_succ]

private theorem rowSum_le_two (a b : ℕ) (ha : a ≤ 2) :
    ((List.range' 0 a).map (fun j ↦ b + j)).sum ≤ 2 * b + 1 := by
  cases a with
  | zero => simp
  | succ a =>
    cases a with
    | zero => simpa [List.range'_succ] using (by omega : b ≤ 2 * b + 1)
    | succ a =>
      have h : a = 0 := by omega
      subst a
      simp [List.range'_succ, Nat.two_mul, Nat.add_assoc]

/-- A convolution with at most one left coefficient has linear primitive bounds. -/
theorem profileArithmetic_mulRaw_le_of_size_le_one (p q : CPolynomial.Raw F) (hp : p.size ≤ 1)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (mulRaw p q)).2 kind ≤
      if kind = .add ∨ kind = .mul then q.size
      else if kind = .coefficientRead then 3 * q.size + 1
      else if kind = .metadata then 2 * q.size + 4 else 0 := by
  have ha := rowSum_le_one p.size q.size hp
  have hb := Nat.mul_le_mul_right q.size hp
  have hc := Nat.mul_le_mul_right (q.size + 1) hp
  have ht := Nat.mul_le_mul_right (q.size + 3) hp
  cases kind <;> simp [profileArithmetic_mulRaw] <;> omega

/-- A convolution with at most two left coefficients has linear primitive bounds. -/
theorem profileArithmetic_mulRaw_le_of_size_le_two (p q : CPolynomial.Raw F) (hp : p.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (mulRaw p q)).2 kind ≤
      if kind = .add then 2 * q.size + 1
      else if kind = .mul then 2 * q.size
      else if kind = .coefficientRead then 6 * q.size + 4
      else if kind = .metadata then 4 * q.size + 8 else 0 := by
  have ha := rowSum_le_two p.size q.size hp
  have hb := Nat.mul_le_mul_right q.size hp
  have hc := Nat.mul_le_mul_right (q.size + 1) hp
  have ht := Nat.mul_le_mul_right (q.size + 3) hp
  cases kind <;> simp [profileArithmetic_mulRaw] <;> omega

end Semiring
end CompPoly.Arithmetic
