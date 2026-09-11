/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformFirstOrder
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.RateBounds
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedLine
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedCurve
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.MathematicalUniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.HalfGap.Line
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ExtensionDescent
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.LineToAffine
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Mutual correlated agreement up to capacity: lines, affine families, and power batching

This file states all three public properties and their capacity theorems explicitly.
For every positive gap `δ`, the length threshold `N`, derivative order `d`, and constant
`C` depend only on that gap, not on the field, rate, evaluation set, or received words.

* **Lines:** at most `C * n ^ (d + 1)` exceptional challenges.
* **Affine families:** exceptional density at most `C * n ^ (d + 1) / (|F| - 1)`,
  independently of the number of directions.
* **Power batching:** at most `ℓ * C * n ^ (d + 1)` exceptional challenges for
  `w₀ + z * w₁ + ... + z ^ ℓ * wℓ`, with no characteristic restriction depending on `ℓ`.

Affine families use independent parameters; power batching uses powers of a single parameter.
An affine exceptional set can contain an entire polynomial curve, so these are distinct results.

## How to read the statements

`∃` means “there exist”, `∀` means “for every”, and `→` introduces an assumption.
The gap-only constants come first. Each exceptional set is chosen before the challenge and
every close polynomial. The constituent witnesses may depend on the challenge and polynomial.

`Fin n ↪ F` specifies distinct evaluation points. The condition `k + δ * n ≤ A` says
that the integer agreement threshold is at least `k + ceil(δ * n)`.
`P.degree < k` includes the zero polynomial. `F[X]` denotes polynomials;
`z • P` scales coefficients. A `let` abbreviates an expression rather than adding a hypothesis.

Every witness conclusion recovers the candidate polynomial and its **full** agreement set,
not merely a large common subset. Line and power-batching results allow infinite fields.
Affine densities and the final probability formulation require finite fields.

For a fixed physical rate, `automaticFirstOrder_list_and_lineMCA` supplies the automatic
first-order optimized and closed finite bounds under `char = 0` or `char > max(k-1,M)`.
`automaticFirstOrder_rate_bounds` supplies the cubic list and quintic exception slack bounds;
`automaticFirstOrder_hybrid_mcaError_le` gives the separate finite-field probability statement.

The small-gap line and curve theorems use the rate-partition construction with derivative
order `ceil(exp(3/(2δ)))`, the sharper uniform jet cap, and height `150ν`. Their public
quantitative statements retain the exact product-counting constant. The existential wrappers
below enlarge that constant by one to make positivity immediate.
For lines and affine consequences, gaps from `6/25` to one half use the fixed height-276
first-order certificate: from length `23`, the exceptional set has size at most
`1325775 * n²`. The half-gap line theorem retains the sharper `2 * n` bound over every field.
Power batching uses the general rate-partition parameters at gap `min(δ,1/8)`.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual Correlated
  Agreement: From Johnson to Capacity*][DKTZ26], “Mutual correlated agreement up to capacity”
  (`thm:mutual-ca`);
  “Uniform finite choices up to capacity”
  (`thm:ca-explicit`); “Mutual agreement for affine families” (`cor:affine-mutual-ca`);
  and “Symbolic transfer for polynomial curves” (`thm:curve-transfer`).
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators

universe u

/-! ## Lines: one challenge and two constituent messages -/

/-- Mutual correlated agreement at a fixed gap and specified error bound.

The exceptional set is chosen before the challenge and the close polynomial.
Equality of full agreement sets excludes accidental agreements outside the common set. -/
def HasCapacityLineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  -- Block length, message dimension, and agreement threshold.
  ∀ (n k A : ℕ),
    N ≤ n →
    0 < k →
    k ≤ n →
    (k : ℝ) + δ * n ≤ A →
  -- Fields may be infinite; only their characteristic is restricted.
  ∀ (F : Type u) [Field F] [DecidableEq F],
    (ringChar F = 0 ∨ n ≤ ringChar F) →
    ∀ (α : Fin n ↪ F) (f g : Fin n → F),
      -- S records every agreement with the received line at challenge z.
      let S := fun z P ↦ polynomialAgreementSet α (fun i ↦ f i + z * g i) P
      -- T records simultaneous agreement of a polynomial pair with f and g.
      let T := fun F₀ G₀ ↦ commonPolynomialAgreementSet α f g F₀ G₀
      -- One exceptional set works simultaneously for every close polynomial.
      ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E n ∧
        ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
          A ≤ (S z P).card →
          ∃ F₀ G₀ : F[X],
            F₀.degree < k ∧
            G₀.degree < k ∧
            -- Recover the candidate itself, not merely its evaluations on a subset.
            P = F₀ + z • G₀ ∧
            S z P = T F₀ G₀

/-- Characteristic-free mutual correlated agreement at the half gap.

Here `n / 2` is natural-number division: the threshold is `k + floor(n/2)`, which also covers
the paper's real half-gap threshold. There is no minimum block length and no
restriction on the field characteristic. One set of at most `2 * n` exceptional challenges works
for every close polynomial, and outside it the complete agreement set is the common agreement set
of two degree-`< k` constituents. Thresholds above `n` are allowed and give an empty exceptional
set because no polynomial can have that many agreements. -/
def HasHalfGapLineAgreement : Prop :=
  ∀ (n k A : ℕ),
    0 < k →
    k ≤ n →
    k + n / 2 ≤ A →
    ∀ (F : Type u) [Field F] [DecidableEq F],
      ∀ (α : Fin n ↪ F) (f g : Fin n → F),
        ∃ exceptional : Finset F, exceptional.card ≤ 2 * n ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet α (fun i ↦ f i + z * g i) P).card →
            ∃ F₀ G₀ : F[X],
              F₀.degree < k ∧
              G₀.degree < k ∧
              P = F₀ + z • G₀ ∧
              polynomialAgreementSet α (fun i ↦ f i + z * g i) P =
                commonPolynomialAgreementSet α f g F₀ G₀

/-- **Half-gap line agreement.** Reed--Solomon codes have exact mutual correlated agreement at
agreement `k + n / 2` over every field, outside at most `2 * n` challenges.

Unlike the general capacity theorem below, this endpoint has no characteristic hypothesis.
It gives the half-gap case of [DKTZ26, “Uniform finite choices up to capacity”], including
equality of full agreement sets. -/
theorem halfGap_lineAgreement : HasHalfGapLineAgreement := by
  intro n k A hk _hkn hhalf F _ _ domain f g
  by_cases hAn : A ≤ n
  · obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptionalSet_exactAgreement_of_messageDim_add_half_blockLength_le
        domain f g hk hAn hhalf
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hdegree hagree
    obtain ⟨F₀, G₀, hF₀, hG₀, heq, hsets⟩ := hgood z hz P hdegree hagree
    exact ⟨F₀, G₀, hF₀, hG₀, by simpa [Polynomial.smul_eq_C_mul] using heq, hsets⟩
  · refine ⟨∅, by simp, ?_⟩
    intro z _ P _ hagree
    have hcard :
        (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    exact (hAn (hagree.trans hcard)).elim

/-- Every real gap at least one half inherits the characteristic-free `2 * n` endpoint. This
specializes the common capacity interface while retaining the stronger standalone theorem
`halfGap_lineAgreement`, which does not ask for a characteristic witness. -/
theorem halfGap_capacity_lineAgreement (δ : ℝ) (hδ : (1 / 2 : ℝ) ≤ δ) :
    HasCapacityLineAgreement δ 0 (fun n ↦ 2 * n) := by
  intro n k A _hn hk hkn hgap F _ _ _hchar domain f g
  have hnHalf : (((n / 2 : ℕ) : ℝ)) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have hhalfReal : (k : ℝ) + (n / 2 : ℕ) ≤ A := by
    calc
      (k : ℝ) + (n / 2 : ℕ) ≤ (k : ℝ) + (n : ℝ) / 2 :=
        add_le_add_right hnHalf _
      _ = (k : ℝ) + (1 / 2 : ℝ) * n := by ring
      _ ≤ (k : ℝ) + δ * n := by
        gcongr
      _ ≤ A := hgap
  have hhalf : k + n / 2 ≤ A := by exact_mod_cast hhalfReal
  obtain ⟨exceptional, hcard, hgood⟩ :=
    halfGap_lineAgreement n k A hk hkn hhalf F domain f g
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardReal : (exceptional.card : ℝ) ≤ (2 * n : ℕ) := by
      exact_mod_cast hcard
    simpa using hcardReal
  · simpa only [Polynomial.smul_eq_C_mul] using hgood

/-- **Uniform first-order line agreement.** For `6/25 ≤ δ`, every block length `n ≥ 23`
inherits the fixed-gap height-276 theorem.  One exceptional set of at most
`1325775 * n²` challenges works for every close polynomial and preserves the complete
agreement set. -/
theorem uniformFirstOrder_capacity_lineAgreement (δ : ℝ)
    (huniform : (6 / 25 : ℝ) ≤ δ) :
    HasCapacityLineAgreement δ 23
      (fun n ↦ 1325775 * (n : ℝ) ^ 2) := by
  classical
  intro n k A hn hk hkn hgap F _ _ hchar domain f g
  by_cases hAn : A ≤ n
  · have hgapUniform : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hmul := mul_le_mul_of_nonneg_right huniform hnnonneg
      linarith
    have hcharUniform : 2 ≤ k →
        ringChar F = 0 ∨ max (k - 1) 4 < ringChar F := by
      intro hkTwo
      apply hchar.imp_right
      intro hnchar
      have hmax : max (k - 1) 4 < n := by omega
      exact hmax.trans_le hnchar
    obtain ⟨exceptional, hcard, hgood⟩ := exists_uniformFirstOrder_lineMCA
      n k A domain f g (by omega) hk hAn hgapUniform hcharUniform
    refine ⟨exceptional, hcard, ?_⟩
    intro z hz P hdegree hagree
    obtain ⟨pair, hleft, hright, heq, hsets⟩ := hgood z hz P hdegree hagree
    refine ⟨pair.1, pair.2, hleft, hright, ?_, ?_⟩
    · simpa [correlatedPairSpecialization, Polynomial.smul_eq_C_mul] using heq
    · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · norm_num
    · intro z _ P _ hagree
      have hcard :
          (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hAn (hagree.trans hcard)).elim

/-- Every positive gap has a field-independent polynomial bound on exceptional line
challenges, uniformly over all rates. The conclusion identifies the whole agreement set.
It covers characteristic zero and prime fields of size at least the block length. -/
theorem exists_capacity_lineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      HasCapacityLineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) := by
  classical
  by_cases hhalf : (1 / 2 : ℝ) ≤ δ
  · refine ⟨0, 0, 2, by norm_num, ?_⟩
    simpa using halfGap_capacity_lineAgreement δ hhalf
  by_cases huniform : (6 / 25 : ℝ) ≤ δ
  · refine ⟨23, 1, 1325775, by norm_num, ?_⟩
    simpa using uniformFirstOrder_capacity_lineAgreement δ huniform
  have hδuniform : δ < 6 / 25 := lt_of_not_ge huniform
  let d := HiddenDerivative.uniformRatePartitionOrder δ
  let ν := HiddenDerivative.uniformRatePartitionJetBound δ
  let C := polynomialCurveProductMCAConstant δ ν (150 * ν) d + 1
  have hC : 0 < C := by
    dsimp [C, polynomialCurveProductMCAConstant]
    positivity
  refine ⟨HiddenDerivative.uniformRatePartitionLength δ, d, C, hC, ?_⟩
  intro n k A hn hk _hkn hgap F instF decF hchar domain f g
  by_cases hAn : A ≤ n
  · obtain ⟨exceptional, hc, hg⟩ := exists_uniformRatePartition_lineMCA
      hδ hδuniform hn hk hgap hAn domain f g hchar
    have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) =
        decF := Subsingleton.elim _ _
    cases hdec
    refine ⟨exceptional, hc.trans ?_, ?_⟩
    · apply mul_le_mul_of_nonneg_right
      · dsimp [C, ν, d]; linarith
      · positivity
    · intro z hz P hdegree hagree
      obtain ⟨pair, hleft, hright, heq, hsets⟩ := hg z hz P hdegree hagree
      refine ⟨pair.1, pair.2, hleft, hright, ?_, ?_⟩
      · simpa [correlatedPairSpecialization, Polynomial.smul_eq_C_mul] using heq
      · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC.le (by positivity)
    · intro z _ P _ hagree
      have hc : (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hAn (hagree.trans hc)).elim

/-! ## Affine families: independently sampled directions -/

/-- Joint quantitative interface: one choice of constants gives both the probability bounds
and exact affine witnesses. For the paper-facing presentations, see
`exists_capacity_affineAgreement` and `exists_capacity_mcaError` below. -/
theorem exists_capacity_affineAgreement_and_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      -- Choose the code only after fixing the gap, length threshold and error bound.
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / (Fintype.card F : ℝ)) ∧
          ∀ s : ℕ, 1 ≤ s →
            mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / ((Fintype.card F : ℝ) - 1)) ∧
            ∀ U : Fin (s + 1) → Fin n → F,
              ∃ exceptional : Finset (Fin s → F),
                (exceptional.card : ℝ) ≤ C * (n : ℝ) ^ (d + 1) *
                  (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
                ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
                  ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                    ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
                      (k : ℝ) + δ * n →
                  ∃ P₀ : Fin (s + 1) → F[X],
                    (∀ j, (P₀ j).degree < k) ∧
                    P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
                    ∀ i, (P.eval (domain i) =
                        ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
                      ∀ j, (P₀ j).eval (domain i) = U j i := by
  classical
  obtain ⟨N, d, C, hC, hline⟩ := exists_capacity_lineAgreement δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  let radius : ℝ := 1 - (k : ℝ) / n - δ
  let A : ℕ := ⌈(n : ℝ) * (1 - radius)⌉₊
  have hthreshold : (n : ℝ) * (1 - radius) = k + δ * n := by
    dsimp [radius]
    field_simp
    ring
  have hgap : (k : ℝ) + δ * n ≤ A := by
    rw [← hthreshold]
    exact Nat.le_ceil _
  have hexact : LineExactAgreementBound domain k A (C * (n : ℝ) ^ (d + 1)) := by
    intro f g
    simpa only [Polynomial.smul_eq_C_mul] using hline n k A hn hk hkn hgap F hchar domain f g
  have hkthreshold : (k : ℝ) ≤ n * (1 - radius) := by
    rw [hthreshold]
    exact le_add_of_nonneg_right (mul_nonneg hδ.le hnpos.le)
  refine ⟨mcaError_affineLine_le_of_exactAgreement domain _ hexact radius (le_refl A), ?_⟩
  intro s hs
  refine ⟨mcaError_affineSpace_le_of_exactAgreement domain _ hexact hs radius (le_refl A), ?_⟩
  intro U
  simpa only [Fintype.card_fin, hthreshold] using
    exists_affine_exceptionalSet_full_agreement_of_exactLine domain _ hexact hs radius
      (le_refl A) hkthreshold U

/-- Exact mutual agreement for affine families with a dimension-independent error bound.

The directions are sampled independently. The cardinality bound divided by the parameter
space size is `E n / (|F| - 1)`, regardless of the number of directions. This property does
not assert the analogous bound for the correlated powers `(z, z², ...)` of one challenge. -/
def HasCapacityAffineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          -- The affine dimension is arbitrary; a is the offset and u the directions.
          ∀ s : ℕ, 1 ≤ s → ∀ (a : Fin n → F) (u : Fin s → Fin n → F),
            -- The parameter space has |F|^s elements; its exceptional density is
            -- at most E(n)/(|F|-1), with no dimension factor.
            ∃ exceptional : Finset (Fin s → F),
              (exceptional.card : ℝ) ≤ E n *
                (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
              ∀ t ∉ exceptional, ∀ P : F[X], P.degree < k →
                ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                  a i + ∑ j, t j * u j i).card : ℝ) ≥ (k : ℝ) + δ * n →
                -- Recover one constituent polynomial per direction and the offset.
                ∃ (F₀ : F[X]) (G : Fin s → F[X]),
                  F₀.degree < k ∧ (∀ j, (G j).degree < k) ∧
                  P = F₀ + ∑ j, t j • G j ∧
                  ∀ i, (P.eval (domain i) = a i + ∑ j, t j * u j i) ↔
                    F₀.eval (domain i) = a i ∧ ∀ j, (G j).eval (domain i) = u j i

/-- **Affine-family agreement, qualitatively [DKTZ26].** For each positive gap, choose
constants before the field, code, and affine dimension. For a constant word `a` and directions
`u`, one exceptional set works for every parameter `t` and every close polynomial `P`.
Outside it, `P` is the same affine combination of low-degree constituent polynomials, and
its entire agreement set is their common agreement set. The exceptional density is at most
`C * n ^ (d + 1) / (|F| - 1)`, independently of the number of directions. -/
theorem exists_capacity_affineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      HasCapacityAffineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) := by
  classical
  obtain ⟨N, d, C, hC, hall⟩ := exists_capacity_affineAgreement_and_mcaError δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain s hs a u
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ((hall n k hn hk hkn F hchar domain).2 s hs).2 (Fin.cons a u)
  refine ⟨exceptional, hcard, ?_⟩
  intro t ht P hp ha
  have ha' : ((Finset.univ.filter fun i ↦ P.eval (domain i) =
      ∑ j, AffineSpaceGenerator F s t j *
        (Fin.cons a u : Fin (s + 1) → Fin n → F) j i).card : ℝ) ≥
        (k : ℝ) + δ * n := by
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using ha
  obtain ⟨P₀, hdegree, heq, hsets⟩ := hgood t ht P hp ha'
  refine ⟨P₀ 0, fun j ↦ P₀ j.succ, hdegree 0, fun j ↦ hdegree j.succ, ?_, ?_⟩
  · simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using heq
  · intro i
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ, Fin.forall_fin_succ] using hsets i

/-- **MCA error bounds, qualitatively [DKTZ26].** The same gap-only constants work for
every code and every positive affine dimension at distance radius `1 - k / n - δ`.
The line error is at most `C * n ^ (d + 1) / |F|`; passing to affine spaces changes only
the denominator to `|F| - 1`, with no dependence on their dimension. -/
theorem exists_capacity_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
        (ringChar F = 0 ∨ n ≤ ringChar F) → ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / (Fintype.card F : ℝ)) ∧
          ∀ s : ℕ, 1 ≤ s →
            mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / ((Fintype.card F : ℝ) - 1)) := by
  obtain ⟨N, d, C, hC, hall⟩ := exists_capacity_affineAgreement_and_mcaError δ hδ
  refine ⟨N, d, C, hC, ?_⟩
  intro n k hn hk hkn F _ _ _ hchar domain
  exact ⟨(hall n k hn hk hkn F hchar domain).1,
    fun s hs ↦ ((hall n k hn hk hkn F hchar domain).2 s hs).1⟩

/-! ## Power batching: powers of one challenge -/

/-- Mutual correlated agreement for powers batching at a fixed gap and error bound.

The constants are chosen before the batching degree, block length, field, received words,
challenge, and close polynomial.  The exceptional set is chosen before the last two. -/
def HasCapacityPowerBatchingAgreement
    (δ : ℝ) (N : ℕ) (E : ℕ → ℕ → ℝ) : Prop :=
  -- The batching degree is arbitrary and is chosen after the gap-only constants.
  ∀ (ℓ n k A : ℕ),
    0 < ℓ →
    N ≤ n →
    0 < k →
    k ≤ n →
    (k : ℝ) + δ * n ≤ A →
  -- No restriction on the batching degree relative to the characteristic is needed.
  ∀ (F : Type u) [Field F] [DecidableEq F],
    (ringChar F = 0 ∨ n ≤ ringChar F) →
    ∀ (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F),
      -- S is the complete agreement set at challenge z; T is simultaneous agreement.
      let S := fun z P ↦ polynomialAgreementSet domain (powerBatchedWord w z) P
      let T := fun P : Fin (ℓ + 1) → F[X] ↦ commonCurveAgreementSet domain w P
      -- One exceptional set works for every challenge and every close candidate.
      ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E ℓ n ∧
        ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k → A ≤ (S z Q).card →
          ∃ P : Fin (ℓ + 1) → F[X],
            (∀ t, (P t).degree < k) ∧
            -- Recover the polynomial itself, then identify its entire agreement set.
            Q = powerBatchedPolynomial P z ∧
            S z Q = T P

/-- **Power-batching MCA up to capacity.** Every positive gap admits a block threshold,
derivative order, and positive field-independent constant such that degree-`ℓ` powers batching
has at most `ℓ * C * n^(d+1)` exceptional challenges.  Outside them, every close polynomial is
the exact power combination of low-degree constituent messages and has precisely their common
agreement set. -/
theorem exists_capacity_powerBatchingAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 0 < C ∧
      HasCapacityPowerBatchingAgreement δ N
        (fun ℓ n ↦ (ℓ : ℝ) * C * (n : ℝ) ^ (d + 1)) := by
  classical
  let ε := min δ (1 / 8 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεsmall : ε < 6 / 25 := (min_le_right _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  let d := HiddenDerivative.uniformRatePartitionOrder ε
  let ν := HiddenDerivative.uniformRatePartitionJetBound ε
  let C := polynomialCurveProductMCAConstant ε ν (150 * ν) d + 1
  have hC : 0 < C := by
    dsimp [C, polynomialCurveProductMCAConstant]
    positivity
  refine ⟨HiddenDerivative.uniformRatePartitionLength ε, d, C, hC, ?_⟩
  intro ℓ n k A hℓ hn hk _hkn hgap F instF decF hchar domain w
  have hgap' : (k : ℝ) + ε * n ≤ A := by
    have h := mul_le_mul_of_nonneg_right hεδ (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
    linarith
  by_cases hAn : A ≤ n
  · obtain ⟨exceptional, hc, hg⟩ := exists_uniformRatePartition_baseCurveMCA
      hε hεsmall hn hk hgap' hAn hℓ domain w hchar
    have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) =
        decF := Subsingleton.elim _ _
    cases hdec
    refine ⟨exceptional, hc.trans ?_, ?_⟩
    · apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · dsimp [C, ν, d]; linarith
        · positivity
      · positivity
    · intro z hz Q hdegree hagree
      obtain ⟨P, hP, heq, hsets⟩ := hg z hz Q hdegree hagree
      refine ⟨P, hP, ?_, ?_⟩
      · simpa [powerBatchedPolynomial, Polynomial.smul_eq_C_mul] using heq
      · simpa [mappedDomain] using hsets
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro z _ Q _ hagree
      have hc : (polynomialAgreementSet domain (powerBatchedWord w z) Q).card ≤ n :=
        (Finset.card_filter_le _ _).trans_eq (by simp)
      exact (hAn (hagree.trans hc)).elim

/-! ## Sharp mathematical capacity interfaces

The declarations above are retained for compatibility with the executable 1000-based parameter
family and its convenient `n ≤ ringChar F` hypothesis.  The interfaces below assemble the
manuscript's sharper mathematical statements.  They use the revised 300-based rate-partition
parameters at small gaps, the first-order support cap `4` at gaps at least `6/25`, and the
characteristic-free constant-code endpoint.
-/

/-- Derivative order in the sharp mathematical line-MCA capacity theorem. -/
def sharpCapacityDerivativeOrder (δ : ℝ) : ℕ :=
  if δ < (6 / 25 : ℝ) then HiddenDerivative.uniformRatePartitionOrder δ else 1

/-- The paper's characteristic threshold `bδ`: revised `Bjet(δ)` below `6/25`, and `4` above. -/
def sharpCapacityJetBound (δ : ℝ) : ℕ :=
  if δ < (6 / 25 : ℝ) then
    HiddenDerivative.uniformRatePartitionMathematicalJetBound δ
  else 4

/-- Length threshold for the sharp line/affine theorem, normalized to be at least four. -/
def sharpCapacityLengthThreshold (δ : ℝ) : ℕ :=
  max 4 (if δ < (6 / 25 : ℝ) then
    HiddenDerivative.uniformRatePartitionMathematicalLength δ else 23)

/-- Gap-only leading constant for the sharp line/affine exceptional-set bound. -/
def sharpCapacityLineConstant (δ : ℝ) : ℝ :=
  if δ < (6 / 25 : ℝ) then
    polynomialCurveProductMCAConstant δ
      (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ)
      (150 * HiddenDerivative.uniformRatePartitionMathematicalJetBound δ)
      (HiddenDerivative.uniformRatePartitionOrder δ) + 1
  else 1325775

/-- The sharp line/affine length threshold is at least four. -/
theorem sharpCapacityLengthThreshold_ge_four (δ : ℝ) :
    4 ≤ sharpCapacityLengthThreshold δ := by
  simp [sharpCapacityLengthThreshold]

/-- The sharp capacity exponent is positive at every positive gap. -/
theorem sharpCapacityDerivativeOrder_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < sharpCapacityDerivativeOrder δ := by
  by_cases hsmall : δ < (6 / 25 : ℝ)
  · have := HiddenDerivative.uniformRatePartitionOrder_ge_519 hδ hsmall
    simp only [sharpCapacityDerivativeOrder, if_pos hsmall]
    omega
  · simp [sharpCapacityDerivativeOrder, hsmall]

/-- The selected line constant is at least one, including on the revised small-gap branch. -/
theorem one_le_sharpCapacityLineConstant {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ sharpCapacityLineConstant δ := by
  by_cases hsmall : δ < (6 / 25 : ℝ)
  · have hbase : 0 ≤ polynomialCurveProductMCAConstant δ
        (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ)
        (150 * HiddenDerivative.uniformRatePartitionMathematicalJetBound δ)
        (HiddenDerivative.uniformRatePartitionOrder δ) := by
      unfold polynomialCurveProductMCAConstant
      positivity
    simp only [sharpCapacityLineConstant, if_pos hsmall]
    linarith
  · simp [sharpCapacityLineConstant, hsmall]

/-- The selected line constant is positive. -/
theorem sharpCapacityLineConstant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < sharpCapacityLineConstant δ :=
  lt_of_lt_of_le zero_lt_one (one_le_sharpCapacityLineConstant hδ)

private theorem constantCurveExceptionalBound_le_power
    {n A ell d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ)) ≤
      (ell : ℝ) * (n : ℝ) ^ (d + 1) := by
  have hchoose : n.choose 2 ≤ n ^ 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans
      (by simpa only [pow_two] using Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have hraw :
      (if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1)) ≤ ell * n ^ 2 := by
    split
    · exact Nat.mul_le_mul_left ell hchoose
    · exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left ell hchoose)
  have hrawReal :
      (((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ)) ≤
        (ell : ℝ) * (n : ℝ) ^ 2 := by
    exact_mod_cast hraw
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ ((1 + e) + 1) := by
    calc
      (n : ℝ) ^ 2 = 1 * (n : ℝ) ^ 2 := by ring
      _ ≤ (n : ℝ) ^ e * (n : ℝ) ^ 2 := by
        gcongr
        exact one_le_pow₀ hnReal
      _ = (n : ℝ) ^ ((1 + e) + 1) := by ring
  exact hrawReal.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg ell))

/-- Paper-facing line agreement with the exact piecewise characteristic guard.

At `k=1` there is no characteristic restriction.  Otherwise the positive characteristic must
exceed `max (k-1) bδ`.  The exceptional set is fixed before the challenge and candidate and the
conclusion identifies the complete agreement set.  Agreement thresholds above `n` are supported
and make the conclusion vacuous via an empty exceptional set. -/
def HasSharpCapacityLineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ (n k A : ℕ),
    N ≤ n → 0 < k → k ≤ n → (k : ℝ) + δ * n ≤ A →
    ∀ (F : Type u) [Field F] [DecidableEq F],
      (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) (sharpCapacityJetBound δ) < ringChar F) →
      ∀ (domain : Fin n ↪ F) (f g : Fin n → F),
        ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E n ∧
          ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
            A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
            HasExactCorrelatedPair domain f g (RingHom.id F) k z P

open Classical in
/-- Sharp all-rate line MCA with the manuscript's explicit order, support, and length threshold. -/
theorem sharpCapacity_lineAgreement (δ : ℝ) (hδ : 0 < δ) :
    HasSharpCapacityLineAgreement δ (sharpCapacityLengthThreshold δ)
      (fun n ↦ sharpCapacityLineConstant δ *
        (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1)) := by
  intro n k A hn hk _hkn hgap F instF decF hchar domain f g
  have hnFour : 4 ≤ n := (sharpCapacityLengthThreshold_ge_four δ).trans hn
  have hnOne : 1 ≤ n := by omega
  have hApos : 0 < A := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hδn : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg n)
    exact_mod_cast (show (0 : ℝ) < A by linarith)
  by_cases hAn : A ≤ n
  · by_cases hkOne : k = 1
    · subst k
      obtain ⟨exceptional, hcard, hgood⟩ :=
        uniformExactPowerAgreement_constantCode domain ![f, g] A hApos
      refine ⟨exceptional, ?_, ?_⟩
      · have hraw := constantCurveExceptionalBound_le_power
          (A := A) (ell := 1) hnOne (show 1 ≤ sharpCapacityDerivativeOrder δ by
            exact sharpCapacityDerivativeOrder_pos hδ)
        have hC : 1 ≤ sharpCapacityLineConstant δ := by
          exact one_le_sharpCapacityLineConstant hδ
        calc
          (exceptional.card : ℝ) ≤
              ((if A = 1 then 1 * n.choose 2 else 1 * n.choose 2 / (A - 1) : ℕ) : ℝ) := by
                exact_mod_cast hcard
          _ ≤ (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) := by simpa using hraw
          _ ≤ sharpCapacityLineConstant δ *
              (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) := by
                simpa only [one_mul] using mul_le_mul_of_nonneg_right hC
                  (pow_nonneg (Nat.cast_nonneg n) _)
      · intro z hz P hP hclose
        have hw : powerBatchedWord (ℓ := 1) ![f, g] z = (fun i ↦ f i + z * g i) := by
          funext i
          simp [powerBatchedWord, Fin.sum_univ_two]
        have hp := hgood z hz P hP (by rwa [hw])
        simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g]
          (RingHom.id F) z P hp
    · have hkTwo : 2 ≤ k := by omega
      have hchar' : ringChar F = 0 ∨
          max (k - 1) (sharpCapacityJetBound δ) < ringChar F :=
        hchar.resolve_left hkOne
      by_cases hsmall : δ < (6 / 25 : ℝ)
      · have hnMath : HiddenDerivative.uniformRatePartitionMathematicalLength δ ≤ n := by
          simp only [sharpCapacityLengthThreshold, if_pos hsmall] at hn
          omega
        have hcharMath : ringChar F = 0 ∨
            max (k - 1) (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ) <
              ringChar F := by
          simpa only [sharpCapacityJetBound, if_pos hsmall] using hchar'
        obtain ⟨exceptional, hcard, hgood⟩ :=
          exists_mathematicalUniformRatePartition_lineMCA hδ hsmall hnMath hk hgap hAn
            domain f g hcharMath
        have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
          Subsingleton.elim _ _
        cases hdec
        refine ⟨exceptional, hcard.trans ?_, hgood⟩
        simp only [sharpCapacityLineConstant, sharpCapacityDerivativeOrder, if_pos hsmall]
        gcongr
        linarith
      · have hlarge : (6 / 25 : ℝ) ≤ δ := le_of_not_gt hsmall
        have hn23 : 23 ≤ n := by
          simp only [sharpCapacityLengthThreshold, if_neg hsmall] at hn
          omega
        have hgapLarge : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
          have := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg n)
          linarith
        have hcharLarge : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F := by
          simpa only [sharpCapacityJetBound, if_neg hsmall] using hchar'
        obtain ⟨exceptional, hcard, hgood⟩ := exists_uniformFirstOrder_lineMCA
          n k A domain f g (by omega) hk hAn hgapLarge (fun _ ↦ hcharLarge)
        refine ⟨exceptional, ?_, hgood⟩
        simpa [sharpCapacityLineConstant, sharpCapacityDerivativeOrder, hsmall] using hcard
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (sharpCapacityLineConstant_pos hδ).le
        (pow_nonneg (Nat.cast_nonneg n) _)
    intro z _ P _ hagree
    have hc : (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card ≤ n :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    exact (hAn (hagree.trans hc)).elim

/-- Existential form of the sharp headline theorem, explicitly retaining `N ≥ 4`. -/
theorem exists_sharpCapacity_lineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasSharpCapacityLineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) :=
  ⟨sharpCapacityLengthThreshold δ, sharpCapacityDerivativeOrder δ,
    sharpCapacityLineConstant δ, sharpCapacityLengthThreshold_ge_four δ,
    sharpCapacityLineConstant_pos hδ, sharpCapacity_lineAgreement δ hδ⟩

open Classical in
/-- Finite-field adapter for the sharp line theorem. -/
theorem lineExactAgreementBound_sharpCapacity
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {δ : ℝ} (hδ : 0 < δ) (n k A : ℕ)
    (hn : sharpCapacityLengthThreshold δ ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A) (domain : Fin n ↪ F)
    (hchar : k = 1 ∨ ringChar F = 0 ∨
      max (k - 1) (sharpCapacityJetBound δ) < ringChar F) :
    LineExactAgreementBound domain k A
      (sharpCapacityLineConstant δ * (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1)) := by
  intro f g
  obtain ⟨exceptional, hcard, hgood⟩ :=
    sharpCapacity_lineAgreement δ hδ n k A hn hk hkn hgap F hchar domain f g
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hP hA
  obtain ⟨pair, hp₀, hp₁, heq, hsets⟩ := hgood z hz P hP hA
  exact ⟨pair.1, pair.2, hp₀, hp₁, by simpa [correlatedPairSpecialization] using heq,
    by simpa [mappedDomain] using hsets⟩

/-! ### Sharp affine and probability interfaces -/

/-- Affine-family agreement under the same sharp line characteristic condition. -/
def HasSharpCapacityAffineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) (sharpCapacityJetBound δ) < ringChar F) →
      ∀ domain : Fin n ↪ F, ∀ s : ℕ, 1 ≤ s →
        ∀ (a : Fin n → F) (u : Fin s → Fin n → F),
          ∃ exceptional : Finset (Fin s → F),
            (exceptional.card : ℝ) ≤ E n * (Fintype.card F : ℝ) ^ s /
              ((Fintype.card F : ℝ) - 1) ∧
            ∀ t ∉ exceptional, ∀ P : F[X], P.degree < k →
              ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                a i + ∑ j, t j * u j i).card : ℝ) ≥ (k : ℝ) + δ * n →
              ∃ (F₀ : F[X]) (G : Fin s → F[X]),
                F₀.degree < k ∧ (∀ j, (G j).degree < k) ∧
                P = F₀ + ∑ j, t j • G j ∧
                ∀ i, (P.eval (domain i) = a i + ∑ j, t j * u j i) ↔
                  F₀.eval (domain i) = a i ∧ ∀ j, (G j).eval (domain i) = u j i

open Classical in
/-- One sharp line theorem supplies line error, dimension-independent affine error, and exact
affine witnesses with the same gap-only constants. -/
theorem sharpCapacity_affineAgreement_and_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∀ n k : ℕ, sharpCapacityLengthThreshold δ ≤ n → 0 < k → k ≤ n →
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
      (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) (sharpCapacityJetBound δ) < ringChar F) →
      ∀ domain : Fin n ↪ F,
        mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
          ENNReal.ofReal (sharpCapacityLineConstant δ *
            (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) /
              (Fintype.card F : ℝ)) ∧
        ∀ s : ℕ, 1 ≤ s →
          mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (sharpCapacityLineConstant δ *
              (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) /
                ((Fintype.card F : ℝ) - 1)) ∧
          ∀ U : Fin (s + 1) → Fin n → F,
            ∃ exceptional : Finset (Fin s → F),
              (exceptional.card : ℝ) ≤ sharpCapacityLineConstant δ *
                (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) *
                  (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
              ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
                ((Finset.univ.filter fun i ↦ P.eval (domain i) =
                  ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
                    (k : ℝ) + δ * n →
                ∃ P₀ : Fin (s + 1) → F[X],
                  (∀ j, (P₀ j).degree < k) ∧
                  P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
                  ∀ i, (P.eval (domain i) =
                      ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
                    ∀ j, (P₀ j).eval (domain i) = U j i := by
  intro n k hn hk hkn F _ _ _ hchar domain
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  let radius : ℝ := 1 - (k : ℝ) / n - δ
  let A : ℕ := ⌈(n : ℝ) * (1 - radius)⌉₊
  have hthreshold : (n : ℝ) * (1 - radius) = k + δ * n := by
    dsimp [radius]
    field_simp
    ring
  have hgap : (k : ℝ) + δ * n ≤ A := by
    rw [← hthreshold]
    exact Nat.le_ceil _
  have hexact := lineExactAgreementBound_sharpCapacity hδ n k A hn hk hkn hgap domain hchar
  have hkthreshold : (k : ℝ) ≤ n * (1 - radius) := by
    rw [hthreshold]
    exact le_add_of_nonneg_right (mul_nonneg hδ.le hnpos.le)
  refine ⟨mcaError_affineLine_le_of_exactAgreement domain _ hexact radius (le_refl A), ?_⟩
  intro s hs
  refine ⟨mcaError_affineSpace_le_of_exactAgreement domain _ hexact hs radius (le_refl A), ?_⟩
  intro U
  simpa only [Fintype.card_fin, hthreshold] using
    exists_affine_exceptionalSet_full_agreement_of_exactLine domain _ hexact hs radius
      (le_refl A) hkthreshold U

open Classical in
/-- Sharp affine-family agreement with the concrete piecewise capacity parameters. -/
theorem sharpCapacity_affineAgreement (δ : ℝ) (hδ : 0 < δ) :
    HasSharpCapacityAffineAgreement δ (sharpCapacityLengthThreshold δ)
      (fun n ↦ sharpCapacityLineConstant δ *
        (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1)) := by
  intro n k hn hk hkn F _ _ _ hchar domain s hs a u
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ((sharpCapacity_affineAgreement_and_mcaError δ hδ n k hn hk hkn F hchar domain).2 s hs).2
      (Fin.cons a u)
  refine ⟨exceptional, hcard, ?_⟩
  intro t ht P hp ha
  have ha' : ((Finset.univ.filter fun i ↦ P.eval (domain i) =
      ∑ j, AffineSpaceGenerator F s t j *
        (Fin.cons a u : Fin (s + 1) → Fin n → F) j i).card : ℝ) ≥
        (k : ℝ) + δ * n := by
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using ha
  obtain ⟨P₀, hdegree, heq, hsets⟩ := hgood t ht P hp ha'
  refine ⟨P₀ 0, fun j ↦ P₀ j.succ, hdegree 0, fun j ↦ hdegree j.succ, ?_, ?_⟩
  · simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using heq
  · intro i
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ, Fin.forall_fin_succ] using hsets i

/-- Existential sharp affine-family theorem with a normalized length threshold `N ≥ 4`. -/
theorem exists_sharpCapacity_affineAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasSharpCapacityAffineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) :=
  ⟨sharpCapacityLengthThreshold δ, sharpCapacityDerivativeOrder δ,
    sharpCapacityLineConstant δ, sharpCapacityLengthThreshold_ge_four δ,
    sharpCapacityLineConstant_pos hδ, sharpCapacity_affineAgreement δ hδ⟩

/-- Paper-facing line and affine-space MCA error bounds under the sharp characteristic guard. -/
theorem sharpCapacity_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∀ n k : ℕ, sharpCapacityLengthThreshold δ ≤ n → 0 < k → k ≤ n →
    ∀ (F : Type) [Field F] [Fintype F],
      (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) (sharpCapacityJetBound δ) < ringChar F) →
      ∀ domain : Fin n ↪ F,
        mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
          ENNReal.ofReal (sharpCapacityLineConstant δ *
            (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) /
              (Fintype.card F : ℝ)) ∧
        ∀ s : ℕ, 1 ≤ s →
          mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (sharpCapacityLineConstant δ *
              (n : ℝ) ^ (sharpCapacityDerivativeOrder δ + 1) /
                ((Fintype.card F : ℝ) - 1)) := by
  classical
  intro n k hn hk hkn F _ _ hchar domain
  exact ⟨(sharpCapacity_affineAgreement_and_mcaError δ hδ n k hn hk hkn F hchar domain).1,
    fun s hs ↦
      ((sharpCapacity_affineAgreement_and_mcaError δ hδ n k hn hk hkn F hchar domain).2 s hs).1⟩

/-- Existential sharp finite-field error theorem with the same line and affine constants. -/
theorem exists_sharpCapacity_mcaError (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F],
        (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) (sharpCapacityJetBound δ) < ringChar F) →
        ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
            ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / (Fintype.card F : ℝ)) ∧
          ∀ s : ℕ, 1 ≤ s →
            mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) /
                ((Fintype.card F : ℝ) - 1)) :=
  ⟨sharpCapacityLengthThreshold δ, sharpCapacityDerivativeOrder δ,
    sharpCapacityLineConstant δ, sharpCapacityLengthThreshold_ge_four δ,
    sharpCapacityLineConstant_pos hδ, sharpCapacity_mcaError δ hδ⟩

/-! ### Sharp powers-batching interface -/

/-- Auxiliary gap used for uniform powers batching; it stays below `6/25` and below `δ`. -/
def sharpCapacityPowerGap (δ : ℝ) : ℝ := min δ (1 / 8)

/-- Derivative order for powers batching, evaluated at the auxiliary gap `min δ (1/8)`. -/
def sharpCapacityPowerDerivativeOrder (δ : ℝ) : ℕ :=
  HiddenDerivative.uniformRatePartitionOrder (sharpCapacityPowerGap δ)

/-- Revised 300-based jet cap for powers batching at the auxiliary gap `min δ (1/8)`.
This generally differs from the piecewise line threshold `sharpCapacityJetBound δ`. -/
def sharpCapacityPowerJetBound (δ : ℝ) : ℕ :=
  HiddenDerivative.uniformRatePartitionMathematicalJetBound (sharpCapacityPowerGap δ)

/-- Powers-batching length threshold, normalized to be at least four. -/
def sharpCapacityPowerLengthThreshold (δ : ℝ) : ℕ :=
  max 4 (HiddenDerivative.uniformRatePartitionMathematicalLength (sharpCapacityPowerGap δ))

/-- Gap-only powers-batching constant from the revised mathematical rate-partition theorem. -/
def sharpCapacityPowerConstant (δ : ℝ) : ℝ :=
  polynomialCurveProductMCAConstant (sharpCapacityPowerGap δ)
    (sharpCapacityPowerJetBound δ) (150 * sharpCapacityPowerJetBound δ)
    (sharpCapacityPowerDerivativeOrder δ) + 1

/-- The powers-batching length threshold is at least four. -/
theorem sharpCapacityPowerLengthThreshold_ge_four (δ : ℝ) :
    4 ≤ sharpCapacityPowerLengthThreshold δ := by
  simp [sharpCapacityPowerLengthThreshold]

/-- The powers-batching constant is at least one at every positive gap. -/
theorem one_le_sharpCapacityPowerConstant {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ sharpCapacityPowerConstant δ := by
  have hepsilon : 0 < sharpCapacityPowerGap δ := lt_min hδ (by norm_num)
  have hbase : 0 ≤ polynomialCurveProductMCAConstant (sharpCapacityPowerGap δ)
      (sharpCapacityPowerJetBound δ) (150 * sharpCapacityPowerJetBound δ)
      (sharpCapacityPowerDerivativeOrder δ) := by
    unfold polynomialCurveProductMCAConstant
    positivity
  unfold sharpCapacityPowerConstant
  linarith

/-- The powers-batching constant is positive at every positive gap. -/
theorem sharpCapacityPowerConstant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < sharpCapacityPowerConstant δ :=
  lt_of_lt_of_le zero_lt_one (one_le_sharpCapacityPowerConstant hδ)

/-- Powers batching with the sharp characteristic guard for the revised mathematical selector.
The guard is independent of the batching degree, and disappears for constant codes. -/
def HasSharpCapacityPowerBatchingAgreement
    (δ : ℝ) (N : ℕ) (E : ℕ → ℕ → ℝ) : Prop :=
  ∀ (ell n k A : ℕ), 0 < ell → N ≤ n → 0 < k → k ≤ n →
    (k : ℝ) + δ * n ≤ A →
    ∀ (F : Type u) [Field F] [DecidableEq F],
      (k = 1 ∨ ringChar F = 0 ∨
        max (k - 1) (sharpCapacityPowerJetBound δ) < ringChar F) →
      ∀ (domain : Fin n ↪ F) (w : Fin (ell + 1) → Fin n → F),
        ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E ell n ∧
          ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
            A ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
            HasExactPowerAgreement domain w (RingHom.id F) k z Q

open Classical in
/-- Revised-300 all-rate powers batching using the auxiliary gap `min δ (1/8)`.

This theorem does not claim the line theorem's piecewise `bδ` above `1/8`: its separate jet bound
is `sharpCapacityPowerJetBound δ`. The characteristic guard remains independent of `ell`. -/
theorem sharpCapacity_powerBatchingAgreement (δ : ℝ) (hδ : 0 < δ) :
    HasSharpCapacityPowerBatchingAgreement δ (sharpCapacityPowerLengthThreshold δ)
      (fun ell n ↦ (ell : ℝ) * sharpCapacityPowerConstant δ *
        (n : ℝ) ^ (sharpCapacityPowerDerivativeOrder δ + 1)) := by
  let epsilon := sharpCapacityPowerGap δ
  have hepsilon : 0 < epsilon := lt_min hδ (by norm_num)
  have hepsilonSmall : epsilon < (6 / 25 : ℝ) :=
    (min_le_right δ (1 / 8 : ℝ)).trans_lt (by norm_num)
  have hepsilonDelta : epsilon ≤ δ := min_le_left _ _
  have hdPos : 1 ≤ sharpCapacityPowerDerivativeOrder δ := by
    have := HiddenDerivative.uniformRatePartitionOrder_ge_519 hepsilon hepsilonSmall
    change 1 ≤ HiddenDerivative.uniformRatePartitionOrder epsilon
    omega
  intro ell n k A hell hn hk _hkn hgap F instF decF hchar domain w
  have hnFour : 4 ≤ n := (sharpCapacityPowerLengthThreshold_ge_four δ).trans hn
  have hnOne : 1 ≤ n := by omega
  have hApos : 0 < A := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hδn : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg n)
    exact_mod_cast (show (0 : ℝ) < A by linarith)
  by_cases hAn : A ≤ n
  · by_cases hkOne : k = 1
    · subst k
      obtain ⟨exceptional, hcard, hgood⟩ :=
        uniformExactPowerAgreement_constantCode domain w A hApos
      refine ⟨exceptional, ?_, hgood⟩
      have hraw := constantCurveExceptionalBound_le_power
        (A := A) (ell := ell) hnOne hdPos
      have hC : 1 ≤ sharpCapacityPowerConstant δ := by
        exact one_le_sharpCapacityPowerConstant hδ
      calc
        (exceptional.card : ℝ) ≤
            ((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ) := by
              exact_mod_cast hcard
        _ ≤ (ell : ℝ) * (n : ℝ) ^ (sharpCapacityPowerDerivativeOrder δ + 1) := hraw
        _ ≤ (ell : ℝ) * sharpCapacityPowerConstant δ *
            (n : ℝ) ^ (sharpCapacityPowerDerivativeOrder δ + 1) := by
              calc
                _ = (ell : ℝ) * 1 *
                    (n : ℝ) ^ (sharpCapacityPowerDerivativeOrder δ + 1) := by ring
                _ ≤ _ := by gcongr
    · have hchar' : ringChar F = 0 ∨
          max (k - 1) (sharpCapacityPowerJetBound δ) < ringChar F :=
        hchar.resolve_left hkOne
      have hnMath : HiddenDerivative.uniformRatePartitionMathematicalLength epsilon ≤ n := by
        change max 4 (HiddenDerivative.uniformRatePartitionMathematicalLength epsilon) ≤ n at hn
        omega
      have hgapEpsilon : (k : ℝ) + epsilon * n ≤ A := by
        have := mul_le_mul_of_nonneg_right hepsilonDelta (Nat.cast_nonneg n)
        linarith
      obtain ⟨exceptional, hcard, hgood⟩ :=
        exists_mathematicalUniformRatePartition_baseCurveMCA hepsilon hepsilonSmall hnMath hk
          hgapEpsilon hAn hell domain w
            (by simpa [sharpCapacityPowerJetBound, epsilon] using hchar')
      have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
        Subsingleton.elim _ _
      cases hdec
      refine ⟨exceptional, hcard.trans ?_, hgood⟩
      dsimp only [sharpCapacityPowerConstant, sharpCapacityPowerJetBound,
        sharpCapacityPowerDerivativeOrder, epsilon]
      gcongr
      linarith
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg ell) (sharpCapacityPowerConstant_pos hδ).le)
        (pow_nonneg (Nat.cast_nonneg n) _)
    intro z _ Q _ hagree
    have hc : (polynomialAgreementSet domain (powerBatchedWord w z) Q).card ≤ n :=
      (Finset.card_filter_le _ _).trans_eq (by simp)
    exact (hAn (hagree.trans hc)).elim

/-- Existential form of revised-300 powers batching with `N ≥ 4` and an `ell`-linear bound. -/
theorem exists_sharpCapacity_powerBatchingAgreement (δ : ℝ) (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasSharpCapacityPowerBatchingAgreement δ N
        (fun ell n ↦ (ell : ℝ) * C * (n : ℝ) ^ (d + 1)) :=
  ⟨sharpCapacityPowerLengthThreshold δ, sharpCapacityPowerDerivativeOrder δ,
    sharpCapacityPowerConstant δ, sharpCapacityPowerLengthThreshold_ge_four δ,
    sharpCapacityPowerConstant_pos hδ, sharpCapacity_powerBatchingAgreement δ hδ⟩

end ReedSolomon
