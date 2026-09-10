/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.QuadraticExtension.QuadraticDecoderMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Dispatch.Bounds
/-!
# Numerical total budgets for quadratic decoding

This sum combines the literal interpolation dispatch budget, quadratic setup budget, original
parameter decoder fuel, and fixed embedding/handoff allowance. The inequalities are numerical
primitive-work majorants. Attaching this sum to a whole execution and lowering its operations
to bit cost remain separate obligations. The field-size exponents are independent of growing
multiplicity at order zero, and all fixed-order parameter dependence is in the coefficient.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.QuadraticDecoderMachine

open HiddenDerivative QuadraticAlgebra

/-- Original integer parameters determine the complete numerical child-budget sum. -/
def totalBudget (k d m A n q e : ℕ) : ℕ :=
  InterpolationDispatch.budget k d m A n + SetupMachine.budget q (m * A) +
    decoderFuel d m q e + 16 * q + 112

private theorem setup_fixed (m A q : ℕ) (hq : 0 < q) (hA : A ≤ q) :
    SetupMachine.budget q (m * A) ≤ (591 + 90 * m) * q ^ 2 := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hm := Nat.mul_le_mul_left m (hA.trans hq2)
  rw [SetupMachine.budget_eq]
  nlinarith only [hq2, hpos, hm]

private theorem setup_zero (m A q : ℕ) (hq : 0 < q) (hm : m ≤ q) (hA : A ≤ q) :
    SetupMachine.budget q (m * A) ≤ 681 * q ^ 2 := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hpos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hmul : m * A ≤ q ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hm hA
  rw [SetupMachine.budget_eq]
  nlinarith only [hq2, hpos, hmul]

/-- Positive-order totals have the decoder's same exponent, with only a fixed-parameter coefficient.
The claim is uniform in k and in the numerical alphabet exponent e. -/
theorem budget_fixed (k d m A n q e : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hA : A ≤ n) (hn : n ≤ q) :
    totalBudget k d m A n q e ≤
      (NonzeroInterpolationMachine.attemptBudget d m 1 1 +
        SeparateSampleDecoder.sizePolynomial (SeparateSampleDecoder.fixedSizeCoefficient d m) +
        90 * m + 911) * q ^ (e * (d + 2) + 10) := by
  let E := e * (d + 2) + 10
  have h5 : q ^ 5 ≤ q ^ E := Nat.pow_le_pow_right hq (by dsimp [E]; omega)
  have h2 : q ^ 2 ≤ q ^ E := Nat.pow_le_pow_right hq (by dsimp [E]; omega)
  have h1 : q ≤ q ^ E := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (by dsimp [E]; omega : 1 ≤ E)
  have hpos : 1 ≤ q ^ E := Nat.one_le_pow _ _ hq
  have hi := (InterpolationDispatch.budget_fixed k d m A n q hd hq hA hn).trans
    (Nat.mul_le_mul_left _ h5)
  have hs := (setup_fixed m A q hq (hA.trans hn)).trans (Nat.mul_le_mul_left _ h2)
  have ht : 16 * q + 112 ≤ 128 * q ^ E := by omega
  unfold totalBudget decoderFuel
  rw [if_neg (by omega : d ≠ 0)]
  dsimp only [E] at hi hs ht
  nlinarith only [hi, hs, ht]

/-- Order-zero totals have a universal coefficient even when multiplicity grows with n.
For e=1 or e=2 the absolute exponents are 27 and 29 respectively. -/
theorem budget_zero (k m A n q e : ℕ) (hq : 0 < q) (hm : m ≤ n)
    (hA : A ≤ n) (hn : n ≤ q) :
    totalBudget k 0 m A n q e ≤
      (SeparateSampleDecoder.sizePolynomial 26 + 294227) * q ^ (2 * e + 25) := by
  let E := 2 * e + 25
  have h12 : q ^ 12 ≤ q ^ E := Nat.pow_le_pow_right hq (by dsimp [E]; omega)
  have h2 : q ^ 2 ≤ q ^ E := Nat.pow_le_pow_right hq (by dsimp [E]; omega)
  have h1 : q ≤ q ^ E := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (by dsimp [E]; omega : 1 ≤ E)
  have hpos : 1 ≤ q ^ E := Nat.one_le_pow _ _ hq
  have hi := (InterpolationDispatch.budget_zero k m A n q hq hm hA hn).trans
    (Nat.mul_le_mul_left _ h12)
  have hs := (setup_zero m A q hq (hm.trans hn) (hA.trans hn)).trans
    (Nat.mul_le_mul_left _ h2)
  have ht : 16 * q + 112 ≤ 128 * q ^ E := by omega
  simp only [totalBudget, decoderFuel, if_true]
  dsimp only [E, InterpolationDispatch.zeroCoefficient] at hi hs ht
  nlinarith only [hi, hs, ht]

end ReedSolomon.ListDecoding.QuadraticDecoderMachine
