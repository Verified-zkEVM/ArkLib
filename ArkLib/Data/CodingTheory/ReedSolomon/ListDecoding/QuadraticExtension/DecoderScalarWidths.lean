/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CapacityDecoderExecution
public import Mathlib.Data.Nat.Size
/-!
# Binary widths of original-parameter decoder scalars

These bounds concern the actual scalar fuel and budget expressions. The coefficient contributes
an additive binary width, while the field-size contribution retains its precise derivative-order
slope. Truncated remaining-fuel counters inherit these bounds by arithmetic monotonicity.

No work ledger is treated as a bound on arbitrary live data. Each backend state update still needs
its own magnitude invariant, and evaluating these expressions still needs charged arithmetic.
These are numerical width facts, not a bit-cost or host-interpreter refinement.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.DecoderScalarWidths

open HiddenDerivative QuadraticDecoderMachine

/-- A polynomial numerical bound gives an additive coefficient width and exact field-size slope.
The statement also covers zero coefficients, zero bases and zero exponents. -/
theorem size_le_mul_pow (x C q r : ℕ) (hx : x ≤ C * q ^ r) :
    Nat.size x ≤ Nat.size C + r * Nat.size q := by
  apply Nat.size_le.mpr
  have hq : q ^ r ≤ (2 ^ Nat.size q) ^ r :=
    Nat.pow_le_pow_left (Nat.lt_size_self q).le r
  have hC := Nat.lt_size_self C
  have hp : 0 < (2 ^ Nat.size q) ^ r := pow_pos (by positivity) _
  have hlt : C * q ^ r < 2 ^ Nat.size C * (2 ^ Nat.size q) ^ r := by
    nlinarith
  apply hx.trans_lt
  simpa only [pow_mul, pow_add, Nat.mul_comm r] using hlt

/-- The exact branch-selected scalar used to run the decoder has this binary width. -/
theorem decoderFuel_size (d m q e : ℕ) :
    Nat.size (decoderFuel d m q e) ≤
      if d = 0 then Nat.size (SeparateSampleDecoder.sizePolynomial 26) +
        (2 * e + 25) * Nat.size q
      else Nat.size (SeparateSampleDecoder.sizePolynomial
        (SeparateSampleDecoder.fixedSizeCoefficient d m)) +
        (e * (d + 2) + 10) * Nat.size q := by
  unfold decoderFuel
  split <;> exact size_le_mul_pow _ _ _ _ le_rfl

/-- Every arithmetically decremented original fuel has the same width bound.
This states the concrete subtraction invariant, without assuming a machine-state invariant. -/
theorem decoderFuel_remaining_size (d m q e used : ℕ) :
    Nat.size (decoderFuel d m q e - used) ≤
      if d = 0 then Nat.size (SeparateSampleDecoder.sizePolynomial 26) +
        (2 * e + 25) * Nat.size q
      else Nat.size (SeparateSampleDecoder.sizePolynomial
        (SeparateSampleDecoder.fixedSizeCoefficient d m)) +
        (e * (d + 2) + 10) * Nat.size q :=
  (Nat.size_le_size (Nat.sub_le _ _)).trans (decoderFuel_size d m q e)

/-- Positive-order whole-child budgets retain the precise exponent from the numerical bound. -/
theorem totalBudget_size_fixed (k d m A n q e : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hA : A ≤ n) (hnq : n ≤ q) :
    Nat.size (totalBudget k d m A n q e) ≤
      Nat.size (NonzeroInterpolationMachine.attemptBudget d m 1 1 +
        SeparateSampleDecoder.sizePolynomial (SeparateSampleDecoder.fixedSizeCoefficient d m) +
        90 * m + 911) + (e * (d + 2) + 10) * Nat.size q :=
  size_le_mul_pow _ _ _ _ (budget_fixed k d m A n q e hd hq hA hnq)

/-- At order zero the coefficient is absolute even when multiplicity grows with the block. -/
theorem totalBudget_size_zero (k m A n q e : ℕ) (hq : 0 < q)
    (hm : m ≤ n) (hA : A ≤ n) (hnq : n ≤ q) :
    Nat.size (totalBudget k 0 m A n q e) ≤
      Nat.size (SeparateSampleDecoder.sizePolynomial 26 + 294227) +
        (2 * e + 25) * Nat.size q :=
  size_le_mul_pow _ _ _ _ (budget_zero k m A n q e hq hm hA hnq)

/-- The actual whole-program envelope has slope e*d+29, with its coefficient width additive.
Taking e=2 or e=1 preserves the two capacity work exponents exactly. -/
theorem workEnvelope_size (d m q e : ℕ) :
    Nat.size (CapacityDecoderMachine.workCoefficient d m * q ^ (e * d + 29)) ≤
      Nat.size (CapacityDecoderMachine.workCoefficient d m) +
        (e * d + 29) * Nat.size q :=
  size_le_mul_pow _ _ _ _ le_rfl

/-- Original block, dimension and threshold widths, including oversized A up to twice the block. -/
theorem input_size (n k A q : ℕ) (hk : k ≤ n) (hn : n ≤ q) (hA : A ≤ 2 * n) :
    Nat.size n ≤ Nat.size q ∧ Nat.size k ≤ Nat.size q ∧
      Nat.size A ≤ 2 + Nat.size q := by
  refine ⟨Nat.size_le_size hn, Nat.size_le_size (hk.trans hn), ?_⟩
  have h := size_le_mul_pow A 2 q 1 (by simpa using hA.trans (Nat.mul_le_mul_left 2 hn))
  have htwo : Nat.size 2 = 2 := by decide +kernel
  simpa only [htwo, one_mul] using h

/-- The actual multiplicity selector has at most the larger input/block width. -/
theorem multiplicity_size (n d m q : ℕ) (hn : n ≤ q) :
    Nat.size (CapacityDecoderMachine.multiplicity n d m) ≤ max (Nat.size m) (Nat.size q) := by
  unfold CapacityDecoderMachine.multiplicity
  split
  · exact (Nat.size_le_size ((Nat.div_le_self n 2).trans hn)).trans (le_max_right _ _)
  · exact le_max_left _ _

/-- The setup guard gives a direct width bound on the actual recovery-sample count. -/
theorem sampleCount_size (n d m A q : ℕ)
    (hL : CapacityDecoderMachine.multiplicity n d m * A ≤ q ^ 2) :
    Nat.size (CapacityDecoderMachine.multiplicity n d m * A) ≤ 1 + 2 * Nat.size q := by
  simpa using size_le_mul_pow _ 1 q 2 (by simpa using hL)

/-- Field enumeration cardinality has an absolute quadratic field-width bound. -/
theorem alphabetCount_size (q : ℕ) : Nat.size (q ^ 2) ≤ 1 + 2 * Nat.size q := by
  simpa using size_le_mul_pow (q ^ 2) 1 q 2 (by simp)

/-- Both fuel exponent registers are bounded before choosing a field or block instance. -/
theorem fuelExponent_size (d e : ℕ) (he : e ≤ 2) :
    Nat.size (if d = 0 then 2 * e + 25 else e * (d + 2) + 10) ≤
      Nat.size (2 * d + 29) := by
  apply Nat.size_le_size
  split <;> nlinarith

end ReedSolomon.ListDecoding.DecoderScalarWidths
