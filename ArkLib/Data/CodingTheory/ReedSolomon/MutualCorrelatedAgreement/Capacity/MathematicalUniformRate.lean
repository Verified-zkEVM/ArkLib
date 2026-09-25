/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.MathematicalUniform
import Mathlib.Data.Fin.VecNotation

/-!
# Mathematical uniform rate-partition exact correlated agreement

For `0 < δ < 6/25`, the mathematical uniform recipe takes `d = ⌈exp (3/(2δ))⌉₊`, multiplicity
`m = ⌈300 d² log(6d)⌉₊`, jet cap `ν = ⌈m/δ²⌉₊ - 1`, and length threshold `ν + 1`. One exceptional
set is chosen before the challenge and candidate. For a power-batched curve of degree `ℓ`, its size
is at most `ℓ * C(δ) * n^(d+1)`, where `C(δ)` is the polynomial-curve agreement constant at jet
cap `ν` and height `150 ν`. Every close candidate outside the set has exact power agreement with
base-field constituents and the same complete agreement set. The curve theorems assume
characteristic zero or `max (k - 1) ν < char F`.

On affine lines the length threshold is raised to `max (ν + 1) ⌈4ν/δ²⌉₊`. When the curve
characteristic guard fails, the message dimension is at most `ν` and the characteristic-free
Johnson bound applies with fewer than `(343/3) n²` exceptions; constant messages are handled in
every characteristic. The line theorem therefore assumes only characteristic zero or
`k - 1 < char F`, with coefficient `max C(δ) (343/3)`.

## Main statements

* `ReedSolomon.exists_mathematicalUniformRatePartition_curve_exactPowerAgreement`:
  extension-field curve agreement.
* `ReedSolomon.exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement`:
  base-field curve agreement.
* `ReedSolomon.mathematicalUniformLineAgreementConstant`: the line coefficient
  `max C(δ) (343/3)`.
* `ReedSolomon.exists_mathematicalUniformRatePartition_line_exactCorrelatedPair`: exact
  agreement on affine lines.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative HiddenDerivative.RatePartition

universe u

open Classical in
/-- The mathematical uniform rate-partition parameters give an explicit exceptional-set bound for
a power-batched received curve over an algebraically closed extension. -/
theorem exists_mathematicalUniformRatePartition_curve_exactPowerAgreement
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (k - 1) (uniformMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ
        (uniformMathematicalJetBound δ) (150 * uniformMathematicalJetBound δ)
        (uniformDerivativeOrder δ) * (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (add_two_le_closedMultiplicity (by norm_num)
      (by omega : 1 ≤ uniformDerivativeOrder δ))
  obtain ⟨_, _, hν, _⟩ := uniformMathematical_integer_guards hδ hδone hm hn
  have hscale : (1 : ℝ) < 300 * (uniformDerivativeOrder δ : ℝ) ^ 3 := by
    have hd' : (519 : ℝ) ≤ uniformDerivativeOrder δ := by exact_mod_cast hd
    nlinarith [sq_nonneg (uniformDerivativeOrder δ : ℝ)]
  obtain ⟨cert⟩ := e.exists_curve_certificate (scale := 300) hδ hδone (by omega) hscale hAn
    domain (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg n)]
    exact_mod_cast h
  let K := max k (uniformDerivativeOrder δ + 1)
  have hKn : K ≤ n := max_le (hkA.trans hAn) (by have := e.order_le; have := e.ambient_le; omega)
  have hdν := uniformDerivativeOrder_le_mathematicalJetBound hδ hδsmall
  have hchar' : ringChar F = 0 ∨ max (K - 1) (uniformMathematicalJetBound δ) < ringChar F := by
    refine hchar.imp_right fun hc ↦ ?_
    have hkchar := (Nat.le_max_left _ _).trans_lt hc
    have hνchar := (Nat.le_max_right _ _).trans_lt hc
    dsimp only [K]
    omega
  exact exists_exceptional_exactPowerAgreement_of_certificate_of_jetCharacteristic
    domain values iota cert hk (Nat.le_max_left _ _) (by omega)
    (Nat.lt_succ_self _ |>.trans_le (Nat.le_max_right _ _)) hKn hkA hAn hν
    (by positivity) hℓ le_rfl hδ hδone.le hgap hchar'

open Classical in
/-- The extension-field curve bound descends to challenges and candidates over the base field. -/
theorem exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement
    {F : Type u} [Field F] {δ : ℝ} {n k A ℓ : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨ max (k - 1) (uniformMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductAgreementConstant δ
        (uniformMathematicalJetBound δ) (150 * uniformMathematicalJetBound δ)
        (uniformDerivativeOrder δ) * (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_mathematicalUniformRatePartition_curve_exactPowerAgreement
      hδ hδsmall hn hk hgap hAn hℓ domain values iota hchar
  obtain ⟨exceptional', hcard', hgood'⟩ :=
    uniformExactPowerAgreement_of_extension domain values iota k A exceptional hgood
  exact ⟨exceptional', (Nat.cast_le.mpr hcard').trans hcard, hgood'⟩

/-- The line coefficient `max C(δ) (343/3)`, where `C(δ)` is the polynomial-curve agreement
constant at the mathematical jet cap `ν`, height `150 ν` and the uniform derivative order, and
`343/3` is the coefficient of the Johnson bound. -/
def mathematicalUniformLineAgreementConstant (δ : ℝ) : ℝ :=
  max
    (polynomialCurveProductAgreementConstant δ (uniformMathematicalJetBound δ)
      (150 * uniformMathematicalJetBound δ) (uniformDerivativeOrder δ))
    (343 / 3)

open Classical in
/-- An exceptional set for exact power agreement of the pair `![f, g]` is an exceptional set for
exact correlated-pair agreement on the line `f + z g`. -/
private theorem exists_line_exactCorrelatedPair_of_powerAgreement
    {F : Type u} [Field F] {n k A : ℕ} {B : ℝ} (domain : Fin n ↪ F) (f g : Fin n → F)
    (h : ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord ![f, g] z) P).card →
        HasExactPowerAgreement domain ![f, g] (RingHom.id F) k z P) :
    ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ := h
  refine ⟨exceptional, hcard, fun z hz P hP hA ↦ ?_⟩
  have hword : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P
    (hgood z hz P hP (by rwa [hword]))

open Classical in
/-- **Mathematical uniform exact line agreement.** At length at least
`uniformMathematicalCapacityLength δ`, one set of at most
`mathematicalUniformLineAgreementConstant δ * n^(d+1)` challenges is exceptional for exact
correlated-pair agreement on the line `f + z g`, assuming only characteristic zero or
`k - 1 < char F`. -/
theorem exists_mathematicalUniformRatePartition_line_exactCorrelatedPair
    {F : Type u} [Field F] {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformMathematicalCapacityLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ mathematicalUniformLineAgreementConstant δ *
        (n : ℝ) ^ (uniformDerivativeOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  have hnBase : uniformMathematicalLength δ ≤ n := (le_max_left _ _).trans hn
  have hnJohnson : ⌈(4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  have hd := uniformDerivativeOrder_ge_519 hδ hδsmall
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkA : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by positivity))
  have hnOne : 1 ≤ n := by
    have hkn : k ≤ n := by exact_mod_cast hkA.trans (by exact_mod_cast hAn : (A : ℝ) ≤ n)
    omega
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (uniformDerivativeOrder δ + 1) :=
    pow_le_pow_right₀ (by exact_mod_cast hnOne) (by omega)
  have hJohnson : (343 / 3 : ℝ) * (n : ℝ) ^ 2 ≤
      mathematicalUniformLineAgreementConstant δ * (n : ℝ) ^ (uniformDerivativeOrder δ + 1) :=
    mul_le_mul (le_max_right _ _) hpow (by positivity)
      ((by norm_num : (0 : ℝ) ≤ 343 / 3).trans (le_max_right _ _))
  by_cases hkOne : k = 1
  · subst k
    apply exists_line_exactCorrelatedPair_of_powerAgreement
    obtain ⟨exceptional, hcard, hgood⟩ := uniformExactPowerAgreement_constantCode domain ![f, g] A
    refine ⟨exceptional, ?_, hgood⟩
    have hchoose : 1 * (Fintype.card (Fin n)).choose 2 / max (A - 1) 1 ≤ n ^ 2 := by
      rw [Fintype.card_fin, one_mul]
      exact (Nat.div_le_self _ _).trans (Nat.choose_le_pow n 2)
    have hcardR : (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard.trans hchoose
    refine hcardR.trans (le_trans ?_ hJohnson)
    nlinarith [sq_nonneg (n : ℝ)]
  by_cases hsupport :
      ringChar F = 0 ∨ max (k - 1) (uniformMathematicalJetBound δ) < ringChar F
  · obtain ⟨exceptional, hcard, hgood⟩ := exists_line_exactCorrelatedPair_of_powerAgreement
      domain f g (exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement
        hδ hδsmall hnBase hk hgap hAn (by norm_num : 0 < 1) domain ![f, g] hsupport)
    refine ⟨exceptional, hcard.trans ?_, hgood⟩
    rw [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hdegreeChar := hchar.resolve_left fun hzero ↦ hsupport (Or.inl hzero)
    have hkJet : k ≤ uniformMathematicalJetBound δ := by
      by_contra hjet
      exact hsupport (Or.inr (max_lt hdegreeChar (by omega)))
    have hscale : 4 * ((k : ℝ) - 1) ≤ δ ^ 2 * n := by
      have hjet : (4 : ℝ) * uniformMathematicalJetBound δ / δ ^ 2 ≤ n :=
        (Nat.le_ceil _).trans (by exact_mod_cast hnJohnson)
      have hkJetR : (k : ℝ) ≤ uniformMathematicalJetBound δ := by exact_mod_cast hkJet
      have := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hjet
      nlinarith
    obtain ⟨exceptional, hcard, hgood⟩ := exists_johnson_line_exactCorrelatedPair_of_gap
      domain f g hδ (by omega) hscale hgap hAn
    exact ⟨exceptional, hcard.le.trans hJohnson, hgood⟩

end ReedSolomon
