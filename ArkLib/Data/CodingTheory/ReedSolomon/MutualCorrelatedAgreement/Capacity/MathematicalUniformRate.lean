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

For a capacity gap `delta < 6/25`, this module uses the same revised mathematical parameters as
`ListDecodability/Capacity/MathematicalUniformRate`:

* `d = ceil(exp(3/(2*delta)))`, the derivative order;
* `m = ceil(300*d^2*log(6*d))`, the interpolation multiplicity;
* `nu = ceil(m/delta^2)-1`, the total jet-degree bound; and
* `Ndelta = nu+1`, the sufficient block-length threshold.

The polynomial-curve theorem gives at most
`ell * C(delta) * n^(d+1)` exceptional challenges, where
`C(delta) = polynomialCurveProductMCAConstant delta nu (150*nu) d`. One exceptional set is fixed
before the challenge and candidate. Outside it, `HasExactPowerAgreement` recovers the constituent
messages and identifies the complete agreement set. The line theorem is the case `ell = 1`.

The characteristic guard is the sharp mathematical condition: characteristic zero, or
`max (k-1) nu < ringChar F`. The extension-field theorem constructs the exceptional set over an
algebraically closed target; the base-field theorem descends it back to `F`. These declarations do
not assemble the large-gap first-order and constant-code endpoints; the paper-facing all-gap wrapper
is `sharpCapacity_lineAgreement` in `MutualCorrelatedAgreement/Capacity`.

This 300-based family is independent of the retained 1000-based reference executor imported from
`Capacity/UniformRate`. It proves mathematical MCA bounds and makes no decoder-runtime or
bit-complexity claim.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], uniform small-gap MCA bound.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- **Extension-field polynomial-curve MCA for the revised 300-based recipe.**

For `ell+1` received words, one exceptional subset of the algebraically closed target field works
for every challenge and every close degree-`< k` candidate. Its size is linear in `ell` and at most
`ell * C(delta) * n^(d+1)`. The exact power-agreement conclusion includes equality of the complete
agreement set, rather than only agreements on a supplied subset. -/
theorem exists_mathematicalUniformRatePartition_curveMCA
    -- The small capacity gap fixes all interpolation parameters.
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    -- Length, dimension, threshold, and batching degree are fixed before the field data.
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    -- The embedding moves the base evaluation set and received curve into the target field.
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    -- Positive characteristic must exceed message degree and the revised jet bound.
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
/-- **Base-field polynomial-curve MCA for the revised parameters.**

Algebraic-closure recovery is descended back to `F`, including the exceptional set and all
constituent messages. The explicit length bound places the revised jet cap below `n`, so the sharp
characteristic premise includes the prime-field boundary `q = n` whenever the remaining message
degree guard holds. -/
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
/-- **Exact line MCA for the revised 300-based parameters.**

This is the `ell = 1` specialization of the base-field curve theorem. The threshold uses the actual
message dimension through `k + delta*n <= A`; one exceptional set works for every challenge and
candidate, and `HasExactCorrelatedPair` records full-set recovery. This is the small-gap line
theorem used by `sharpCapacity_lineAgreement`. -/
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
