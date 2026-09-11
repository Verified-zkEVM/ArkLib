/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.MathematicalUniform

/-!
# Uniform correlated agreement for the revised 300-based mathematical recipe

These theorems expose the stronger mathematical parameter choice without changing the retained
1000-based reference executor. The exceptional set is fixed before the challenge and candidate,
and the conclusion recovers the complete agreement set.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- One exceptional set explains every close polynomial on a received polynomial curve, using
the revised 300-based mathematical multiplicity. -/
theorem exists_mathematicalUniformRatePartition_curveMCA
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionMathematicalJetBound δ)
        (150 * uniformRatePartitionMathematicalJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_order hd)
  obtain ⟨_hsize, _hmn, hν, _hνn⟩ :=
    uniformRatePartitionMathematical_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  let K := max k (uniformRatePartitionOrder δ + 1)
  have hKk : k ≤ K := Nat.le_max_left _ _
  have hdK : uniformRatePartitionOrder δ < K :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  have hKn : K ≤ n := by
    apply max_le (hkA.trans hAn)
    have := e.order_le
    have := e.ambient_le
    omega
  have hdν := uniformRatePartitionOrder_le_mathematicalJetBound hδ hδsmall
  have hchar' : ringChar F = 0 ∨
      max (K - 1)
        (uniformRatePartitionMathematicalJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hkchar := (Nat.le_max_left _ _).trans_lt hc
    have hνchar := (Nat.le_max_right _ _).trans_lt hc
    dsimp [K]
    omega
  exact exists_curveMCA_of_certificate_of_jetCharacteristic domain values iota cert hk
    hKk (by omega) hdK hKn hkA hAn hν
    (by positivity) hℓ le_rfl hδ hδone.le hgap hchar'

open Classical in
/-- The revised base-field curve theorem includes the prime-field boundary `q = n`. -/
theorem exists_mathematicalUniformRatePartition_baseCurveMCA
    {F : Type u} [Field F] {δ : ℝ} {n k A ℓ : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionMathematicalJetBound δ)
        (150 * uniformRatePartitionMathematicalJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨ex, hc, hg⟩ := exists_mathematicalUniformRatePartition_curveMCA
    hδ hδsmall hn hk hgap hAn hℓ domain values iota hchar
  obtain ⟨ex', hc', hg'⟩ :=
    exists_exceptional_powerAgreement_descend domain values iota k A ex hg
  exact ⟨ex', (Nat.cast_le.mpr hc').trans hc, hg'⟩

open Classical in
/-- Exact line MCA for the revised parameters, with the actual message-rate gap. -/
theorem exists_mathematicalUniformRatePartition_lineMCA
    {F : Type u} [Field F] {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
        (uniformRatePartitionMathematicalJetBound δ)
        (150 * uniformRatePartitionMathematicalJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  obtain ⟨ex, hc, hg⟩ := exists_mathematicalUniformRatePartition_baseCurveMCA
    hδ hδsmall hn hk hgap hAn (by norm_num : 0 < 1) domain ![f, g] hchar
  refine ⟨ex, by simpa only [Nat.cast_one, one_mul] using hc, ?_⟩
  intro z hz P hP hA
  have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
    funext i
    simp [powerBatchedWord, Fin.sum_univ_two]
  have h := hg z hz P hP (by rwa [hw])
  simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g]
    (RingHom.id F) z P h

end ReedSolomon
