/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.SeparateSample.SeparateSamplePolynomialBounds
/-!
# Field-size majorants from actual interpolation output

The alphabet length is a numerical power `q^e`; choosing one or two covers both field regimes.
No completeness property of that alphabet is needed for these primitive-budget inequalities.
The fixed-order bound has coefficients depending only on order and multiplicity. The order-zero
bound permits growing multiplicity and retains a universal coefficient and absolute exponent.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SeparateSampleDecoder

open HiddenDerivative NonzeroInterpolationMachine MvPolynomial
open PreparedDecoderMachine (Input Element)
open PartialDerivativeMachine (inputMass)

/-- Scaling a nonnegative degree-five polynomial retains degree five in the scale. -/
theorem sizePolynomial_scale (S C t : ℕ) (ht : 1 ≤ t) (hS : S ≤ C * t) :
    sizePolynomial S ≤ sizePolynomial C * t ^ 5 := by
  have hp (i : ℕ) (hi : i ≤ 5) : S ^ i ≤ C ^ i * t ^ 5 := by
    calc
      S ^ i ≤ (C * t) ^ i := Nat.pow_le_pow_left hS i
      _ = C ^ i * t ^ i := mul_pow _ _ _
      _ ≤ C ^ i * t ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ht hi)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 le_rfl
  unfold sizePolynomial
  nlinarith only [h0, h1, h2, h3, h4, h5]

/-- Coefficient of the quadratic field-size majorant for fixed order and multiplicity. -/
def fixedSizeCoefficient (d m : ℕ) : ℕ :=
  d + 4 * m + 4 + m * (2 * m) ^ (d + 1) * (3 * m + 2 * d + 5) +
    m * (2 * m) ^ (d + 1)

/-- Fixed-order size coefficient for independent strict jet cutoff `J`. -/
def fixedSizeCoefficientWithBudget (d m J : ℕ) : ℕ :=
  d + 2 * m + J + 4 + m * J ^ (d + 1) * (m + J + 2 * d + 5) +
    m * J ^ (d + 1)

variable {F : Type*} [Field F] {a : F}

/-- Only original numeric input sizes and actual materialized list lengths occur here. -/
structure FieldSizes (input : Input F a) (guards : List (Element F a))
    (m A n q e : ℕ) : Prop where
  degree : input.degree ≤ n
  block : n ≤ q
  agreement : A ≤ n
  residual : input.residualLength = m * A
  recovery : input.samples.length = m * A
  guard : guards.length ≤ q ^ 2
  rows : input.received.length ≤ n
  alphabet : input.alphabet.length = q ^ e

/-- A numerical size bound yields one alphabet exponent plus five times its size exponent. -/
theorem scaled_input_budget (input : Input F a) (guards : List (Element F a))
    (ts : List (PreparedDecoderMachine.Term F)) (Δ q e C r : ℕ) (hq : 0 < q)
    (halphabet : input.alphabet.length = q ^ e)
    (hsize : numericalSize input guards ts Δ ≤ C * q ^ r) :
    fuel input guards ts Δ + workBound input guards ts Δ ≤
      sizePolynomial C * q ^ (e * (input.order + 2) + r * 5) := by
  have hp := sizePolynomial_scale _ C (q ^ r) (Nat.one_le_pow _ _ hq) hsize
  have hb := input_bounds_polynomial input guards ts Δ _
    (by rw [halphabet]; exact pow_pos hq e) (numericalSize_bounds input guards ts Δ)
  calc
    _ ≤ input.alphabet.length ^ (input.order + 2) *
        (sizePolynomial C * (q ^ r) ^ 5) :=
      hb.trans (Nat.mul_le_mul_left _ hp)
    _ = _ := by
      rw [halphabet, pow_add q (e * (input.order + 2)) (r * 5),
        pow_mul q e (input.order + 2), pow_mul q r 5]
      ring

variable [DecidableEq F]

/-- The actual sparse emitter bounds every component of the original input by a quadratic in q. -/
theorem fixed_interpolation_size (input : Input F a) (guards : List (Element F a))
    (out : Output F) (m A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e)
    (hr : (run input.degree input.order m A input.received).1 = some out) :
    numericalSize input guards out.terms (2 * m) ≤ fixedSizeCoefficient input.order m * q ^ 2 := by
  obtain ⟨hlen, hmass, _hjet⟩ := run_output_bounds _ _ _ _ _ out hr
  let B := (2 * m) ^ (input.order + 1)
  let b := 2 * (input.order + 2) + 2 * m + 1
  have hAq : A ≤ q := hs.agreement.trans hs.block
  have hmq : m * A ≤ m * q := Nat.mul_le_mul_left m hAq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hinner : m * A + b ≤ (m + b) * q := by nlinarith
  have hm : inputMass out.terms ≤ m * B * (m + b) * q ^ 2 := by
    calc
      _ ≤ m * A * B * (m * A + b) := by
        simpa only [maximumColumns, B, b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using hmass
      _ ≤ m * q * B * ((m + b) * q) := by gcongr
      _ = _ := by ring
  have ht : out.terms.length ≤ m * B * q ^ 2 := by
    calc
      _ ≤ m * A * B := hlen
      _ ≤ m * q ^ 2 * B := by gcongr; exact hAq.trans hq2
      _ = _ := by ring
  have hw : input.degree + 1 ≤ 2 * q ^ 2 := by
    have := hs.degree.trans hs.block
    omega
  have hd : input.order ≤ input.order * q ^ 2 := by nlinarith
  have hL : input.residualLength ≤ m * q ^ 2 := by
    rw [hs.residual]
    exact Nat.mul_le_mul_left m (hAq.trans hq2)
  have hrec : input.samples.length ≤ m * q ^ 2 := by
    rw [hs.recovery]
    exact Nat.mul_le_mul_left m (hAq.trans hq2)
  have hrows : input.received.length ≤ q ^ 2 := (hs.rows.trans hs.block).trans hq2
  have hΔ : 2 * m ≤ 2 * m * q ^ 2 := by nlinarith
  have hg := hs.guard
  unfold numericalSize fixedSizeCoefficient
  dsimp only [B, b] at hm ht
  nlinarith only [hm, ht, hw, hd, hL, hrec, hrows, hΔ, hg]

/-- Fixed order and multiplicity leave only an absolute additive ten in the q exponent. -/
theorem fixed_interpolation_budget (input : Input F a) (guards : List (Element F a))
    (out : Output F) (m A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e)
    (hr : (run input.degree input.order m A input.received).1 = some out) :
    fuel input guards out.terms (2 * m) + workBound input guards out.terms (2 * m) ≤
      sizePolynomial (fixedSizeCoefficient input.order m) * q ^ (e * (input.order + 2) + 10) := by
  exact scaled_input_budget input guards out.terms (2 * m) q e _ 2 hq hs.alphabet
    (fixed_interpolation_size input guards out m A n q e hq hs hr)

/-- The sparse emitter bounds all inputs when interpolation uses strict jet cutoff `J`. -/
theorem fixed_interpolation_sizeWithBudget (input : Input F a)
    (guards : List (Element F a)) (out : Output F) (m J A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e)
    (hr : (runWithBudget input.degree input.order m J A input.received).1 = some out) :
    numericalSize input guards out.terms J ≤
      fixedSizeCoefficientWithBudget input.order m J * q ^ 2 := by
  obtain ⟨hlen, hmass, _hjet⟩ := runWithBudget_output_bounds _ _ _ _ _ _ out hr
  let B := J ^ (input.order + 1)
  let b := 2 * (input.order + 2) + J + 1
  have hAq : A ≤ q := hs.agreement.trans hs.block
  have hmq : m * A ≤ m * q := Nat.mul_le_mul_left m hAq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hinner : m * A + b ≤ (m + b) * q := by nlinarith
  have hm : inputMass out.terms ≤ m * B * (m + b) * q ^ 2 := by
    calc
      _ ≤ m * A * B * (m * A + b) := by
        simpa only [maximumColumnsWithBudget, B, b, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hmass
      _ ≤ m * q * B * ((m + b) * q) := by gcongr
      _ = _ := by ring
  have ht : out.terms.length ≤ m * B * q ^ 2 := by
    calc
      _ ≤ m * A * B := hlen
      _ ≤ m * q ^ 2 * B := by gcongr; exact hAq.trans hq2
      _ = _ := by ring
  have hw : input.degree + 1 ≤ 2 * q ^ 2 := by
    have := hs.degree.trans hs.block
    omega
  have hd : input.order ≤ input.order * q ^ 2 := by nlinarith
  have hL : input.residualLength ≤ m * q ^ 2 := by
    rw [hs.residual]
    exact Nat.mul_le_mul_left m (hAq.trans hq2)
  have hrec : input.samples.length ≤ m * q ^ 2 := by
    rw [hs.recovery]
    exact Nat.mul_le_mul_left m (hAq.trans hq2)
  have hrows : input.received.length ≤ q ^ 2 := (hs.rows.trans hs.block).trans hq2
  have hJ : J ≤ J * q ^ 2 := by nlinarith
  have hg := hs.guard
  unfold numericalSize fixedSizeCoefficientWithBudget
  dsimp only [B, b] at hm ht
  nlinarith only [hm, ht, hw, hd, hL, hrec, hrows, hJ, hg]

/-- Fixed order, multiplicity and strict jet cutoff give an absolute field-size exponent. -/
theorem fixed_interpolation_budgetWithBudget (input : Input F a)
    (guards : List (Element F a)) (out : Output F) (m J A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e)
    (hr : (runWithBudget input.degree input.order m J A input.received).1 = some out) :
    fuel input guards out.terms J + workBound input guards out.terms J ≤
      sizePolynomial (fixedSizeCoefficientWithBudget input.order m J) *
        q ^ (e * (input.order + 2) + 10) := by
  exact scaled_input_budget input guards out.terms J q e _ 2 hq hs.alphabet
    (fixed_interpolation_sizeWithBudget input guards out m J A n q e hq hs hr)

/-- Order-zero physical mass gives a universal size bound even for growing multiplicity. -/
theorem zero_interpolation_size (input : Input F a) (guards : List (Element F a))
    (out : Output F) (m A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e) (horder : input.order = 0) (hmn : m ≤ n)
    (hr : (run input.degree input.order m A input.received).1 = some out) :
    numericalSize input guards out.terms (2 * m) ≤ 26 * q ^ 5 := by
  have hr' : (run input.degree 0 m A input.received).1 = some out := by
    simpa only [horder] using hr
  obtain ⟨hlen, hmass, _hjet⟩ := run_zero_output_bounds _ _ _ _ out hr'
  have hmq : m ≤ q := hmn.trans hs.block
  have hAq : A ≤ q := hs.agreement.trans hs.block
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq5 : q ≤ q ^ 5 := by simpa using Nat.pow_le_pow_right hq (by decide : 1 ≤ 5)
  have h25 : q ^ 2 ≤ q ^ 5 := Nat.pow_le_pow_right hq (by decide)
  have h35 : q ^ 3 ≤ q ^ 5 := Nat.pow_le_pow_right hq (by decide)
  have hq2pos : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hq5pos : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
  have hmA : m * A ≤ q ^ 2 := by
    calc
      m * A ≤ q * q := Nat.mul_le_mul hmq hAq
      _ = _ := (pow_two q).symm
  have hinner : m * A + 2 * m + 5 ≤ 8 * q ^ 2 := by omega
  have hm : inputMass out.terms ≤ 16 * q ^ 5 := by
    calc
      _ ≤ (2 * m) * (m * A) * (m * A + 2 * m + 5) := hmass
      _ ≤ (2 * q) * (q ^ 2) * (8 * q ^ 2) := by gcongr
      _ = _ := by ring
  have ht : out.terms.length ≤ 2 * q ^ 5 := by
    calc
      _ ≤ m * A * (2 * m) := hlen
      _ ≤ q ^ 2 * (2 * q) := by gcongr
      _ = 2 * q ^ 3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 h35
  have hw : input.degree + 1 ≤ 2 * q ^ 5 := by
    have := hs.degree.trans hs.block
    omega
  have hL : input.residualLength ≤ q ^ 5 := by rw [hs.residual]; exact hmA.trans h25
  have hrec : input.samples.length ≤ q ^ 5 := by rw [hs.recovery]; exact hmA.trans h25
  have hg : guards.length ≤ q ^ 5 := hs.guard.trans h25
  have hrows : input.received.length ≤ q ^ 5 := (hs.rows.trans hs.block).trans hq5
  have hΔ : 2 * m ≤ 2 * q ^ 5 := Nat.mul_le_mul_left 2 (hmq.trans hq5)
  unfold numericalSize
  rw [horder]
  omega

/-- Order zero needs q^(2e+25) primitive work, with coefficient independent of multiplicity.
The choices e=1 and e=2 give absolute exponents 27 and 29 respectively. -/
theorem zero_interpolation_budget (input : Input F a) (guards : List (Element F a))
    (out : Output F) (m A n q e : ℕ) (hq : 0 < q)
    (hs : FieldSizes input guards m A n q e) (horder : input.order = 0) (hmn : m ≤ n)
    (hr : (run input.degree input.order m A input.received).1 = some out) :
    fuel input guards out.terms (2 * m) + workBound input guards out.terms (2 * m) ≤
      sizePolynomial 26 * q ^ (2 * e + 25) := by
  have h := scaled_input_budget input guards out.terms (2 * m) q e 26 5 hq hs.alphabet
    (zero_interpolation_size input guards out m A n q e hq hs horder hmn hr)
  simpa [horder, Nat.mul_comm] using h

end ReedSolomon.ListDecoding.SeparateSampleDecoder
