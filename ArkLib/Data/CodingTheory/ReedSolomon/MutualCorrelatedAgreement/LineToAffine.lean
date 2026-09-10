/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.AffineGenerator
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullAgreement
/-!
# Exact line agreement implies affine mutual correlated agreement

A uniform finite exceptional-set bound for exact line agreement bounds the canonical MCA
bad event. The existing affine-space reduction loses only the factor `|F| / (|F| - 1)`,
independently of affine dimension. Integer thresholds use the ceiling of the real threshold.
Here `radius` is the relative-distance radius, not the gap to capacity.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial CoreDefinitions LinearCode
open scoped BigOperators ProbabilityTheory ENNReal

/-- Every received line has one bounded exceptional set before all close polynomials. -/
def LineExactAgreementBound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (domain : Fin n ↪ F) (k A : ℕ) (B : ℝ) : Prop :=
  ∀ f g : Fin n → F, ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ B ∧
    ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
      A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
      ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
        P = P₀ + Polynomial.C z * P₁ ∧
        polynomialAgreementSet domain (fun i ↦ f i + z * g i) P =
          commonPolynomialAgreementSet domain f g P₀ P₁

/-- Enlarging the exceptional-cardinality budget preserves exact line agreement. -/
theorem LineExactAgreementBound.mono
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n k A : ℕ} {domain : Fin n ↪ F} {B B' : ℝ}
    (h : LineExactAgreementBound domain k A B) (hBB' : B ≤ B') :
    LineExactAgreementBound domain k A B' := by
  intro f g
  obtain ⟨exceptional, hcard, hgood⟩ := h f g
  exact ⟨exceptional, hcard.trans hBB', hgood⟩

open Classical in
/-- Every canonical line bad seed belongs to the line's exceptional set. -/
theorem affineLine_bad_set_card_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊)
    (U : Fin 2 → Fin n → F) :
    ((Finset.univ.filter fun z : F ↦
      IsMCA (AffineLineGenerator F) (code domain k) z U radius).card : ℝ) ≤ B := by
  classical
  obtain ⟨exceptional, hExceptionalCard, hExceptional⟩ :=
    hline (U 0) (U 1)
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hExceptionalCard
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  obtain ⟨T, hTCard, hCombination, j, hj⟩ := hz
  have hAT : A ≤ T.card := by
    have hTCard' : (n : ℝ) * (1 - radius) ≤ T.card := by
      simpa only [Fintype.card_fin] using hTCard
    exact hthreshold.trans (Nat.ceil_le.mpr hTCard')
  have hCombination' :
      projectedWord (fun i ↦ U 0 i + z * U 1 i) T ∈
        projectedCodeSubmod (code domain k) T := by
    simpa [AffineLineGenerator, Fin.sum_univ_two, smul_eq_mul] using hCombination
  obtain ⟨P, hPDegree, hPOnT⟩ :=
    (projectedWord_mem_code_iff_exists_polynomial
      domain k (fun i ↦ U 0 i + z * U 1 i) T).mp hCombination'
  have hTSubset :
      T ⊆ polynomialAgreementSet domain (fun i ↦ U 0 i + z * U 1 i) P := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hPOnT i hi⟩
  have hAgreement :
      A ≤ (polynomialAgreementSet domain (fun i ↦ U 0 i + z * U 1 i) P).card :=
    hAT.trans (Finset.card_le_card hTSubset)
  by_contra hzExceptional
  obtain ⟨F₀, G₀, hF₀Degree, hG₀Degree, _hPFormula, hExact⟩ :=
    hExceptional z hzExceptional P hPDegree hAgreement
  apply hj
  apply (projectedWord_mem_code_iff_exists_polynomial domain k (U j) T).mpr
  fin_cases j
  · refine ⟨F₀, hF₀Degree, fun i hi ↦ ?_⟩
    have hiCommon :
        i ∈ commonPolynomialAgreementSet domain (U 0) (U 1) F₀ G₀ := by
      rw [← hExact]
      exact hTSubset hi
    exact (Finset.mem_filter.mp hiCommon).2.1
  · refine ⟨G₀, hG₀Degree, fun i hi ↦ ?_⟩
    have hiCommon :
        i ∈ commonPolynomialAgreementSet domain (U 0) (U 1) F₀ G₀ := by
      rw [← hExact]
      exact hTSubset hi
    exact (Finset.mem_filter.mp hiCommon).2.2

open Classical in
/-- Exact line agreement bounds canonical line MCA error by `B / |F|`. -/
theorem mcaError_affineLine_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤
      ENNReal.ofReal (B / (Fintype.card F : ℝ)) := by
  unfold mcaError
  refine iSup_le fun U ↦ ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact affineLine_bad_set_card_le_of_exactAgreement domain B hline radius hthreshold U

open Classical in
/-- The line bound also retains the trivial probability bound of one. -/
theorem mcaError_affineLine_le_min_one_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain k) radius ≤
      min 1 (ENNReal.ofReal (B / (Fintype.card F : ℝ))) := by
  exact le_min (mcaError_le_one _ _ _) <|
    mcaError_affineLine_le_of_exactAgreement domain B hline radius hthreshold

open Classical in
/-- The existing line reduction controls affine bad-event density without dimension loss. -/
theorem affineSpace_bad_density_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊)
    (U : Fin (s + 1) → Fin n → F) :
    ((Finset.univ.filter fun x : Fin s → F ↦
      IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius).card : ℝ) /
        (Fintype.card F : ℝ) ^ s ≤
      B / ((Fintype.card F : ℝ) - 1) := by
  classical
  obtain ⟨W, hLineTransfer⟩ :=
    AffineMCALemmas.exists_line_bound hs (code domain k) U radius
  have hLineCard :
      ((Finset.univ.filter fun z : F ↦
        IsMCA (AffineLineGenerator F) (code domain k) z W radius).card : ℝ) ≤ B :=
    affineLine_bad_set_card_le_of_exactAgreement domain B hline radius hthreshold W
  have hq : (1 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.one_lt_card (α := F)
  have hLineDensity :
      ((Finset.univ.filter fun z : F ↦
        IsMCA (AffineLineGenerator F) (code domain k) z W radius).card : ℝ) /
          (Fintype.card F : ℝ) ≤
        B / (Fintype.card F : ℝ) := by
    gcongr
  have hChain := hLineTransfer.trans hLineDensity
  have hFactor : 0 < 1 - 1 / (Fintype.card F : ℝ) := by
    rw [sub_pos, div_lt_one] <;> linarith
  calc
    ((Finset.univ.filter fun x : Fin s → F ↦
        IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius).card : ℝ) /
          (Fintype.card F : ℝ) ^ s
        ≤ (B / (Fintype.card F : ℝ)) /
            (1 - 1 / (Fintype.card F : ℝ)) :=
      (le_div_iff₀ hFactor).2 (by simpa [mul_comm] using hChain)
    _ = B / ((Fintype.card F : ℝ) - 1) := by
      field_simp

open Classical in
/-- Exact line agreement bounds every positive-dimensional affine MCA error by
`B / (|F| - 1)`, independently of its dimension. -/
theorem mcaError_affineSpace_le_of_exactAgreement
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal (B / ((Fintype.card F : ℝ) - 1)) := by
  unfold mcaError
  refine iSup_le fun U ↦ ?_
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  simpa [Fintype.card_fun, Fintype.card_fin, Finset.prod_const] using
    affineSpace_bad_density_le_of_exactAgreement
      domain B hline hs radius hthreshold U

open Classical in
/-- Outside an affine exceptional set of density at most `B / (|F| - 1)`, every close
Reed--Solomon polynomial is the affine combination of constituent degree-`< k` polynomials, and
its full agreement set is exactly their common agreement set. -/
theorem exists_affine_exceptionalSet_full_agreement_of_exactLine
    {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k A s : ℕ}
    (domain : Fin n ↪ F) (B : ℝ) (hline : LineExactAgreementBound domain k A B)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊)
    (hkThreshold : (k : ℝ) ≤ n * (1 - radius))
    (U : Fin (s + 1) → Fin n → F) :
    ∃ exceptional : Finset (Fin s → F),
      (exceptional.card : ℝ) ≤
          B * (Fintype.card F : ℝ) ^ s /
            ((Fintype.card F : ℝ) - 1) ∧
      ∀ x ∉ exceptional, ∀ P : F[X], P.degree < k →
        ((Finset.univ.filter fun i ↦
          P.eval (domain i) = ∑ j, AffineSpaceGenerator F s x j * U j i).card : ℝ) ≥
            Fintype.card (Fin n) * (1 - radius) →
        ∃ P₀ : Fin (s + 1) → F[X],
          (∀ j, (P₀ j).degree < k) ∧
          P = ∑ j, AffineSpaceGenerator F s x j • P₀ j ∧
          ∀ i,
            (P.eval (domain i) =
                ∑ j, AffineSpaceGenerator F s x j * U j i) ↔
              ∀ j, (P₀ j).eval (domain i) = U j i := by
  classical
  let exceptional := Finset.univ.filter fun x : Fin s → F ↦
    IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius
  refine ⟨exceptional, ?_, ?_⟩
  · have hDensity := affineSpace_bad_density_le_of_exactAgreement
      domain B hline hs radius hthreshold U
    have hqPow : 0 < (Fintype.card F : ℝ) ^ s := by positivity
    calc
      (exceptional.card : ℝ) ≤
          (B / ((Fintype.card F : ℝ) - 1)) *
            (Fintype.card F : ℝ) ^ s := (div_le_iff₀ hqPow).1 hDensity
      _ = B * (Fintype.card F : ℝ) ^ s /
            ((Fintype.card F : ℝ) - 1) := by ring
  · intro x hx P hPDegree hClose
    have hGood : ¬ IsMCA (AffineSpaceGenerator F s) (code domain k) x U radius := by
      simpa only [exceptional, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact ReedSolomon.exists_polynomials_full_agreement_of_not_isMCA
      domain k (AffineSpaceGenerator F s) x U radius (by simpa using hkThreshold) hGood P hPDegree
        (by
          convert hClose using 1
          congr 2
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end

end ReedSolomon
