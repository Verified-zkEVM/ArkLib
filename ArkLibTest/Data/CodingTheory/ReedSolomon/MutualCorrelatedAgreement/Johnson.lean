/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.FullCode
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-! # Acceptance cases for Johnson decoding consequences -/

open Polynomial CoreDefinitions ReedSolomon ReedSolomon.HiddenDerivative

private def fullCodeDomain : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

example : code fullCodeDomain 3 = ⊤ :=
  code_eq_top_of_card_le fullCodeDomain (by simp)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def finiteJohnsonDomain : Fin 2 ↪ ZMod 2 := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

example : mcaError (AffineLineGenerator (ZMod 2))
    (code finiteJohnsonDomain 2) (1 / 2 : ℝ) = 0 := by
  exact mcaError_affineLine_fullRate_eq_zero finiteJohnsonDomain _

/-- At length `4`, degree `1` and slack `1/4`, the Johnson agreement fraction is `3/4`. -/
private theorem johnsonAgreement_four_one : johnsonAgreement 4 1 (1 / 4) = 3 / 4 := by
  have hsqrt : √((1 : ℝ) / 4) = 1 / 2 := by
    rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simp only [johnsonAgreement, johnsonRhoMinus, Nat.cast_one, Nat.cast_ofNat, hsqrt]
  norm_num

private def natDomain (n : ℕ) : Fin n ↪ ℚ := ⟨fun i ↦ (i : ℚ), fun i j h ↦ by
  apply Fin.ext
  change (i.val : ℚ) = (j.val : ℚ) at h
  exact_mod_cast h⟩

/-- On the zero line, at threshold `3 = (3/4) * 4`, some challenge outside the exceptional set
recovers the zero candidate. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) ≤ johnsonExceptionCount 4 1 3 (1 / 4) ∧
    ∃ z ∉ exceptional, HasExactCorrelatedPair (natDomain 4) 0 0 (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_johnson_line_exactCorrelatedPair
    (n := 4) (D := 1) (A := 3) (eta := 1 / 4) (natDomain 4) 0 0 le_rfl (by norm_num)
    (by norm_num) (by rw [johnsonAgreement_four_one]; norm_num) (by norm_num)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hcard, z, hz, ?_⟩
  convert hgood z hz 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe _) ?_
  simp [polynomialAgreementSet]

/-- At length `16`, dimension `2`, gap `1/2` and threshold `10`, the zero candidate on the zero
line is recovered outside fewer than `(343/3) * 16²` challenges. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℝ) < (343 / 3 : ℝ) * 16 ^ 2 ∧
    ∃ z ∉ exceptional, HasExactCorrelatedPair (natDomain 16) 0 0 (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_johnson_line_exactCorrelatedPair_of_gap
    (n := 16) (k := 2) (A := 10) (δ := 1 / 2) (natDomain 16) 0 0
    (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, by simpa using hcard, z, hz, ?_⟩
  convert hgood z hz 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe _) ?_
  simp [polynomialAgreementSet]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def johnsonFiniteDomain : Fin 4 ↪ ZMod 5 := ⟨![0, 1, 2, 3], by decide⟩

/-- Over `ZMod 5` at length `4`, degree `1` and slack `1/4`, the affine-line MCA error at radius
`1/4` is at most `min 1 (E₀ / 5)` with threshold `3`. -/
example : mcaError (AffineLineGenerator (ZMod 5)) (code johnsonFiniteDomain 2) (1 / 4 : ℝ) ≤
    min 1 (ENNReal.ofReal (johnsonExceptionCount 4 1 3 (1 / 4) / 5)) := by
  have h := mcaError_affineLine_johnson_le (n := 4) (D := 1) (eta := 1 / 4)
    johnsonFiniteDomain le_rfl (by norm_num) (by norm_num)
    (by rw [johnsonAgreement_four_one]; norm_num)
  rw [johnsonAgreement_four_one, show ⌈(3 / 4 : ℝ) * ((4 : ℕ) : ℝ)⌉₊ = 3 by norm_num,
    ZMod.card] at h
  norm_num at h ⊢
  exact h

/-- The weighted Johnson parameters at length `3`, degree `1`, agreement `3`, multiplicity `1`,
jet cutoff `1` and height `1` form a certificate, with weighted count `5`. -/
private theorem weightedJohnsonCertificate_three :
    IsJohnsonWeightedCertificate 3 1 3 1 1 1 :=
  ⟨le_rfl, le_rfl, by norm_num, by decide, by decide⟩

/-- On the zero line of length `3`, some challenge outside at most `5` exceptional challenges
recovers the zero candidate. -/
example : ∃ exceptional : Finset ℚ,
    (exceptional.card : ℚ) ≤ 5 ∧
    ∃ z ∉ exceptional, HasExactCorrelatedPair (natDomain 3) 0 0 (RingHom.id ℚ) 2 z 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ := exists_weightedJohnson_line_exactCorrelatedPair
    (natDomain 3) 0 0 weightedJohnsonCertificate_three le_rfl (by norm_num) le_rfl le_rfl
  obtain ⟨z, hz⟩ := Finset.exists_notMem exceptional
  refine ⟨exceptional, hcard.trans (by norm_num [johnsonWeightedRefinedExceptionCount]), z, hz,
    ?_⟩
  convert hgood z hz 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe _) ?_
  simp [polynomialAgreementSet]

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def weightedJohnsonFiniteDomain : Fin 3 ↪ ZMod 7 := ⟨![0, 1, 2], by decide⟩

/-- Over `ZMod 7` at length `3` and dimension `2`, the weighted certificate bounds the
affine-line MCA error at radius `0` by `5 / 7`. -/
example : mcaError (AffineLineGenerator (ZMod 7)) (code weightedJohnsonFiniteDomain 2) 0 ≤
    ENNReal.ofReal (5 / 7) := by
  have h := mcaError_affineLine_weightedJohnson_le weightedJohnsonFiniteDomain
    weightedJohnsonCertificate_three le_rfl (by norm_num) le_rfl le_rfl 0 (by norm_num)
  rw [ZMod.card] at h
  norm_num [johnsonWeightedRefinedExceptionCount] at h
  exact h
