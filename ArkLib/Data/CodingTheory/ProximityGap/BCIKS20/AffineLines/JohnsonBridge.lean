/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
public import ArkLib.Data.CodingTheory.ProximityGap.Errors
public import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# Coordinate transport for Johnson line agreement

Reindexing a finite evaluation domain preserves code membership, distance and exact agreement.
This transports the Johnson theorem on `Fin n` to the existing line agreement carrier on any
finite coordinate type. Constant messages use the collision bound instead of Johnson parameters.
-/

@[expose] public section

namespace ProximityGap

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

variable {ι κ F : Type} [Fintype ι] [Fintype κ] [Field F] [decF : DecidableEq F]

omit [Fintype ι] [Fintype κ] [DecidableEq F] in
/-- Coordinate reindexing preserves membership in the same Reed–Solomon code. -/
theorem mem_code_comp_equiv (e : κ ≃ ι) (domain : ι ↪ F) (k : ℕ) (w : ι → F) :
    w ∘ e ∈ code (e.toEmbedding.trans domain) k ↔ w ∈ code domain k := by
  simp only [mem_code_iff_eval]
  constructor
  · rintro ⟨P, hP, he⟩
    exact ⟨P, hP, fun i ↦ by simpa using he (e.symm i)⟩
  · rintro ⟨P, hP, he⟩
    exact ⟨P, hP, fun i ↦ he (e i)⟩

omit [Field F] in
/-- Coordinate reindexing preserves normalized Hamming distance. -/
theorem relHammingDist_comp_equiv (e : κ ≃ ι) (u v : ι → F) :
    Code.relHammingDist (u ∘ e) (v ∘ e) = Code.relHammingDist u v := by
  simp only [Code.relHammingDist, hammingDist_comp_equiv, Fintype.card_congr e]

/-- The number of polynomial agreements is invariant under coordinate reindexing. -/
theorem polynomialAgreementSet_card_comp_equiv (e : κ ≃ ι) (domain : ι ↪ F)
    (w : ι → F) (P : F[X]) :
    (polynomialAgreementSet (e.toEmbedding.trans domain) (w ∘ e) P).card =
      (polynomialAgreementSet domain w P).card := by
  classical
  apply Finset.card_nbij' e e.symm
  · intro i hi
    simpa [mem_polynomialAgreementSet] using hi
  · intro i hi
    simpa [mem_polynomialAgreementSet] using hi
  · intro i _
    simp
  · intro i _
    simp

/-- Exact line agreement transports along a coordinate equivalence. -/
theorem lineExactAgreementBound_of_comp_equiv (e : κ ≃ ι) (domain : ι ↪ F)
    {k A : ℕ} {B : ℝ}
    (h : LineExactAgreementBound (e.toEmbedding.trans domain) k A B) :
    LineExactAgreementBound domain k A B := by
  intro f g
  obtain ⟨ex, hcard, hgood⟩ := h (f ∘ e) (g ∘ e)
  refine ⟨ex, hcard, fun z hz P hP hA ↦ ?_⟩
  have hA' : A ≤ (polynomialAgreementSet (e.toEmbedding.trans domain)
      (fun i ↦ (f ∘ e) i + z * (g ∘ e) i) P).card := by
    convert (polynomialAgreementSet_card_comp_equiv e domain
      (fun i ↦ f i + z * g i) P).symm ▸ hA using 1
    simp only [Function.comp_def]
  obtain ⟨P₀, P₁, hp0, hp1, heq, hset⟩ := hgood z hz P hP hA'
  refine ⟨P₀, P₁, hp0, hp1, heq, ?_⟩
  ext i
  have hi := congrArg (e.symm i ∈ ·) hset
  simpa [mem_polynomialAgreementSet, mem_commonPolynomialAgreementSet] using hi

/-- Johnson's exact agreement bound on an arbitrary finite evaluation domain. -/
theorem lineExactAgreementBound_johnson (domain : ι ↪ F) {D : ℕ} {eta : ℝ}
    (hD : 1 ≤ D) (hDn : D ≤ Fintype.card ι - 2) (heta : 0 < eta)
    (ha : johnsonAgreement (Fintype.card ι) D eta ≤ 1) :
    LineExactAgreementBound domain (D + 1)
      ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊
      (johnsonExceptionCount (Fintype.card ι) D
        ⌈johnsonAgreement (Fintype.card ι) D eta * Fintype.card ι⌉₊ eta) := by
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
  cases hdec
  classical
  apply lineExactAgreementBound_of_comp_equiv (Fintype.equivFin ι).symm domain
  apply lineExactAgreementBound_of_exactCorrelatedPair
  intro f g
  exact exists_johnson_line_exactCorrelatedPair_ceil _ f g hD hDn heta ha

/-- Constant messages have at most one exceptional challenge per coordinate pair. -/
theorem lineExactAgreementBound_constantCode (domain : ι ↪ F) (A : ℕ) :
    LineExactAgreementBound domain 1 A ((Fintype.card ι).choose 2 : ℝ) := by
  classical
  apply lineExactAgreementBound_of_comp_equiv (Fintype.equivFin ι).symm domain
  apply lineExactAgreementBound_of_exactCorrelatedPair
  intro f g
  apply exists_line_exactCorrelatedPair_of_powerAgreement
  obtain ⟨ex, hcard, hgood⟩ := uniformExactPowerAgreement_constantCode
    ((Fintype.equivFin ι).symm.toEmbedding.trans domain) ![f, g] A
  refine ⟨ex, ?_, hgood⟩
  have hbound : 1 * (Fintype.card (Fin (Fintype.card ι))).choose 2 / max (A - 1) 1 ≤
      (Fintype.card ι).choose 2 := by
    simp only [Fintype.card_fin, one_mul]
    exact Nat.div_le_self _ _
  exact_mod_cast hcard.trans hbound

end ProximityGap
