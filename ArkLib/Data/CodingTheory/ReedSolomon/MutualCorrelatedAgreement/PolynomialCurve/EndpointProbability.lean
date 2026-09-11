/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullDimension
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FailureProbability
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine

/-!
# Finite-field probability at the constant and full-code endpoints

The arbitrary-field endpoint theorems construct the exceptional sets. Finiteness of the field
is used here only to divide their cardinalities by the challenge-space size.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n ell A : ℕ}

/-- Constant-code curve failure has the exact finite collision bound, including `A=1`. -/
theorem probability_powerAgreementFailure_constantCode_le
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (hA : 0 < A) :
    Pr_{let z ←$ᵖ F}[PowerAgreementFailure domain values 1 A z] ≤
      ENNReal.ofReal
        (((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ) /
          Fintype.card F) := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    uniformExactPowerAgreement_constantCode domain values A hA
  exact probability_powerAgreementFailure_le domain values exceptional _
    (by exact_mod_cast hcard) hgood

/-- The full code has no failing challenges, including at block length zero. -/
theorem probability_powerAgreementFailure_fullDimension_eq_zero
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) :
    Pr_{let z ←$ᵖ F}[PowerAgreementFailure domain values n n z] = 0 := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    uniformExactPowerAgreement_fullDimension n ell domain values
  apply le_antisymm _ (by positivity)
  have h := probability_powerAgreementFailure_le domain values exceptional 0
    (by exact_mod_cast hcard) hgood
  simpa using h

/-- The exact constant-code count supplies the existing line-to-affine adapter. -/
theorem lineExactAgreementBound_constantCode (domain : Fin n ↪ F) (hA : 0 < A) :
    LineExactAgreementBound domain 1 A
      ((if A = 1 then n.choose 2 else n.choose 2 / (A - 1) : ℕ) : ℝ) := by
  intro f g
  obtain ⟨exceptional, hcard, hgood⟩ :=
    uniformExactPowerAgreement_constantCode domain ![f, g] A hA
  refine ⟨exceptional, ?_, ?_⟩
  · exact_mod_cast (show exceptional.card ≤
      (if A = 1 then n.choose 2 else n.choose 2 / (A - 1)) by simpa using hcard)
  · intro z hz P hP hA'
    have hw : powerBatchedWord ![f, g] z = (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hp := hgood z hz P hP (by rwa [hw])
    obtain ⟨pair, hp₀, hp₁, heq, hagree⟩ :=
      exactCorrelatedPair_of_powerAgreement_one domain ![f, g] (RingHom.id F) z P hp
    exact ⟨pair.1, pair.2, hp₀, hp₁, by simpa [correlatedPairSpecialization] using heq,
      by simpa [mappedDomain] using hagree⟩

omit [DecidableEq F] in
/-- Every positive-dimensional affine family inherits the constant-code count divided by
`|F|-1`, with no characteristic restriction. -/
theorem mcaError_affineSpace_constantCode_le {s : ℕ}
    (domain : Fin n ↪ F) (hA : 0 < A) (hs : 1 ≤ s)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain 1) radius ≤
      ENNReal.ofReal
        (((if A = 1 then n.choose 2 else n.choose 2 / (A - 1) : ℕ) : ℝ) /
          ((Fintype.card F : ℝ) - 1)) := by
  classical
  exact mcaError_affineSpace_le_of_exactAgreement domain _
    (lineExactAgreementBound_constantCode domain hA) hs radius hthreshold

end ReedSolomon
