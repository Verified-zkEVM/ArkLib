/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Separation
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FullAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Interleaving

/-!
# Uniform probabilities for affine combiners and scalar MCA

`ReedSolomon.affineMcaError` and `ReedSolomon.scalarMcaError` are suprema of native uniform
exceptional-event probabilities.
Their counting definitions and counting bounds do not require a sampler instance.
This module supplies the sampling characterizations under `SampleableType F`.

At loss zero, the scalar exceptional event equals `Code.IsProjectionBad` for
`CoreDefinitions.AffineLineGenerator F` and `ReedSolomon.code domain (d + 1)`.
Write `n` for the domain size.
If `⌈n (1 - δ)⌉₊ = A`, the scalar error equals
`CoreDefinitions.mcaError` for that generator and code at radius `δ`.
The scalar lower bound therefore gives a lower bound on this value.
An affine witness of degree at most `d` evaluates to a word in `code domain (d + 1)` by
`ReedSolomon.evalOnPoints_mem_code_succ_of_degree_le`.
The second witness, of degree below `d`, uses `ReedSolomon.evalOnPoints_mem_code_of_degree_lt`
and message length `d`.

The errors use the agreement-loss definition in Section 1.1 of [CWYZ26].
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) gives the statement correspondence.

## Main statements

* `ReedSolomon.prob_isAffineExceptional_eq` and `ReedSolomon.prob_isScalarExceptional_eq`:
  uniform probabilities as counting fractions.
* `ReedSolomon.affineMcaError_eq_iSup_prob` and `ReedSolomon.scalarMcaError_eq_iSup_prob`:
  error values as suprema of native probabilities.
* `ReedSolomon.prob_isAffineExceptional_le` and `ReedSolomon.prob_isScalarExceptional_le`:
  the error values bound the probability for each received word pair.
* `ReedSolomon.exists_isScalarExceptional_zero_iff_isProjectionBad` and
  `ReedSolomon.exists_isScalarExceptional_zero_iff_isMCA`: scalar event equivalences.
* `ReedSolomon.scalarMcaError_zero_eq_mcaError`: scalar error equality at a matching threshold.
* `ReedSolomon.le_mcaError_affineLine_of_ceil_eq`: the lower bound `(1 + n - A) / q`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode Finset
open scoped ProbabilityTheory

variable {F ι : Type} [Field F]

private theorem degree_lt_succ_iff_degree_le (P : F[X]) {d : ℕ} :
    P.degree < (d + 1 : ℕ) ↔ P.degree ≤ d := by
  rw [← mem_degreeLT, degreeLT_succ_eq_degreeLE, mem_degreeLE]

variable [DecidableEq F] [Fintype ι]

/-- A scalar challenge has an exceptional candidate at loss zero exactly when
`Code.IsProjectionBad` holds for the affine-line generator and `code domain (d + 1)`.

For every threshold `A`, an extension `G₀` of `g` supplies the partner
`P - C α * G₀` on the entire agreement set. -/
theorem exists_isScalarExceptional_zero_iff_isProjectionBad (domain : ι ↪ F)
    (f g : ι → F) (d A : ℕ) (α : F) :
    (∃ P, IsScalarExceptional domain f g d A 0 α P) ↔
      Code.IsProjectionBad (AffineLineGenerator F) (code domain (d + 1)) A α ![f, g] := by
  classical
  have hcomb : (fun i ↦ ∑ j, AffineLineGenerator F α j • (![f, g] : Fin 2 → ι → F) j i) =
      combinedWord domain f g (C α) := by
    funext i
    simp [AffineLineGenerator, Fin.sum_univ_two]
  constructor
  · rintro ⟨P, hP, hA, hex⟩
    let T := polynomialAgreementSet domain (combinedWord domain f g (C α)) P
    refine ⟨T, hA, ?_, 1, ?_⟩
    · rw [hcomb, projectedWord_mem_code_iff_exists_polynomial]
      exact ⟨P, (degree_lt_succ_iff_degree_le P).mpr hP,
        fun i hi ↦ (mem_polynomialAgreementSet _ _ _ _).mp hi⟩
    · intro hg
      obtain ⟨G₀, hG, hGeval⟩ := (projectedWord_mem_code_iff_exists_polynomial domain
        (d + 1) g T).mp (by simpa using hg)
      apply hex (P - C α * G₀) G₀
      · have hprod : (C α * G₀).degree ≤ G₀.degree := by
          simpa only [smul_eq_C_mul] using degree_smul_le α G₀
        exact (degree_sub_le _ _).trans
          (max_le hP (hprod.trans ((degree_lt_succ_iff_degree_le G₀).mp hG)))
      · exact (degree_lt_succ_iff_degree_le G₀).mp hG
      refine ⟨by ring, ?_⟩
      apply Nat.le_zero.mpr
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      have hGi := hGeval i hi
      have hPi := (mem_polynomialAgreementSet _ _ _ _).mp hi
      simp only [combinedWord_C] at hPi
      simp [hGi, hPi]
  · rintro ⟨T, hT, hP, j, hj⟩
    rw [hcomb, projectedWord_mem_code_iff_exists_polynomial] at hP
    obtain ⟨P, hP, hPeval⟩ := hP
    refine ⟨P, (degree_lt_succ_iff_degree_le P).mp hP, hT.trans (Finset.card_le_card ?_), ?_⟩
    · intro i hi
      exact (mem_polynomialAgreementSet _ _ _ _).mpr (hPeval i hi)
    · intro F₀ G₀ hF hG hw
      have hagree : ∀ i ∈ T, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i := by
        intro i hi
        by_contra hne
        have hiS := (mem_polynomialAgreementSet _ _ _ _).mpr (hPeval i hi)
        have hloss : i ∈ agreementLoss domain f g (C α) P F₀ G₀ := by
          exact Finset.mem_filter.mpr ⟨hiS, not_and_or.mp hne⟩
        have hpos := Finset.card_pos.mpr ⟨i, hloss⟩
        exact (Nat.not_lt_of_ge hw.2) hpos
      fin_cases j
      · apply hj
        rw [projectedWord_mem_code_iff_exists_polynomial]
        exact ⟨F₀, (degree_lt_succ_iff_degree_le F₀).mpr hF, fun i hi ↦ (hagree i hi).1⟩
      · apply hj
        rw [projectedWord_mem_code_iff_exists_polynomial]
        exact ⟨G₀, (degree_lt_succ_iff_degree_le G₀).mpr hG, fun i hi ↦ (hagree i hi).2⟩

/-- If `⌈n (1 - δ)⌉₊ = A`, scalar exceptionality at loss zero is
`CoreDefinitions.IsMCA` for the affine-line generator, `code domain (d + 1)`, and radius `δ`,
where `n = |ι|`. -/
theorem exists_isScalarExceptional_zero_iff_isMCA [Fintype F] (domain : ι ↪ F)
    (f g : ι → F) (d A : ℕ) (α : F) (δ : ℝ)
    (hδ : ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ = A) :
    (∃ P, IsScalarExceptional domain f g d A 0 α P) ↔
      IsMCA (AffineLineGenerator F) (code domain (d + 1)) α ![f, g] δ := by
  rw [isMCA_iff_isProjectionBad, hδ]
  exact exists_isScalarExceptional_zero_iff_isProjectionBad domain f g d A α

section Sampling

variable [Fintype F] [SampleableType F]

open Classical in
/-- A uniform affine exceptional-event probability equals its counting fraction. -/
theorem prob_isAffineExceptional_eq (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F)}[∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P] =
      ENNReal.ofReal
        ((#{c : F × F | ∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P} : ℝ) /
          (Fintype.card F : ℝ) ^ 2) := by
  classical
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  simp [sq]

open Classical in
/-- A uniform scalar exceptional-event probability equals its counting fraction. -/
theorem prob_isScalarExceptional_eq (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let α ← $ᵗ F}[∃ P, IsScalarExceptional domain f g d A s α P] =
      ENNReal.ofReal
        ((#{α : F | ∃ P, IsScalarExceptional domain f g d A s α P} : ℝ) /
          (Fintype.card F : ℝ)) := by
  classical
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]

/-- The affine counting error is the worst-case native probability of exceptionality. -/
theorem affineMcaError_eq_iSup_prob (domain : ι ↪ F) (d A s : ℕ) :
    affineMcaError domain d A s =
      ⨆ w : (ι → F) × (ι → F),
        Pr{let c ← $ᵗ (F × F)}[∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P] := by
  simp only [affineMcaError, prob_isAffineExceptional_eq]

/-- The scalar counting error is the worst-case native probability of exceptionality. -/
theorem scalarMcaError_eq_iSup_prob (domain : ι ↪ F) (d A s : ℕ) :
    scalarMcaError domain d A s =
      ⨆ w : (ι → F) × (ι → F),
        Pr{let α ← $ᵗ F}[∃ P, IsScalarExceptional domain w.1 w.2 d A s α P] := by
  simp only [scalarMcaError, prob_isScalarExceptional_eq]

/-- The affine error bounds the exceptional-event probability for each pair of words. -/
theorem prob_isAffineExceptional_le (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F)}[∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P] ≤
      affineMcaError domain d A s := by
  rw [prob_isAffineExceptional_eq]
  exact le_affineMcaError domain d A s f g

/-- The scalar error bounds the exceptional-event probability for each pair of words. -/
theorem prob_isScalarExceptional_le (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let α ← $ᵗ F}[∃ P, IsScalarExceptional domain f g d A s α P] ≤
      scalarMcaError domain d A s := by
  rw [prob_isScalarExceptional_eq]
  exact le_scalarMcaError domain d A s f g

/-- If `⌈n (1 - δ)⌉₊ = A`, `scalarMcaError domain d A 0` equals
`CoreDefinitions.mcaError` for the affine-line generator, `code domain (d + 1)`, and radius `δ`,
where `n = |ι|`. -/
theorem scalarMcaError_zero_eq_mcaError (domain : ι ↪ F) (d A : ℕ) (δ : ℝ)
    (hδ : ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ = A) :
    scalarMcaError domain d A 0 =
      mcaError (AffineLineGenerator F) (code domain (d + 1)) δ := by
  classical
  have hprob (f g : ι → F) :
      Pr{let α ← $ᵗ F}[∃ P, IsScalarExceptional domain f g d A 0 α P] =
        Pr{let α ← $ᵗ F}[IsMCA (AffineLineGenerator F) (code domain (d + 1)) α ![f, g] δ] :=
    prEvent_congr _ _ _ fun α ↦ exists_isScalarExceptional_zero_iff_isMCA domain f g d A α δ hδ
  rw [scalarMcaError_eq_iSup_prob, mcaError]
  refine le_antisymm (iSup_le fun w ↦ ?_) (iSup_le fun U ↦ ?_)
  · rw [hprob]
    exact le_iSup_of_le ![w.1, w.2] le_rfl
  · have hU : U = ![U 0, U 1] := by
      funext j
      fin_cases j <;> simp
    rw [hU, ← hprob]
    exact le_iSup_of_le (U 0, U 1) le_rfl

omit [DecidableEq F] in
/-- If `d + 1 < A ≤ n` and `⌈n (1 - δ)⌉₊ = A`, the affine-line MCA error for
`code domain (d + 1)` at radius `δ` is at least `(1 + n - A) / q`,
where `n = |ι|` and `q = |F|`. -/
theorem le_mcaError_affineLine_of_ceil_eq (domain : ι ↪ F) {d A : ℕ} (δ : ℝ)
    (hdA : d + 1 < A) (hAn : A ≤ Fintype.card ι)
    (hδ : ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ = A) :
    ENNReal.ofReal (((1 + (Fintype.card ι - A) : ℕ) : ℝ) / (Fintype.card F : ℝ)) ≤
      mcaError (AffineLineGenerator F) (code domain (d + 1)) δ := by
  classical
  rw [← scalarMcaError_zero_eq_mcaError domain d A δ hδ]
  simpa using le_scalarMcaError_of_degree_add_loss_add_one_lt domain (s := 0) hdA hAn

end Sampling

end ReedSolomon
