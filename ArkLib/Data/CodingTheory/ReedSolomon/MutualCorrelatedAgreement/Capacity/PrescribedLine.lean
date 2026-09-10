/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedCurve
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
/-!
# Prescribed mutual correlated agreement on extension-field lines

A line is a power-batched curve of degree one. Specializing the sharp curve theorem gives
the same gap-only constant for lines, without a separate geometric or scalar estimate.
The conclusion preserves equality of the entire agreement sets.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative SymbolicReceivedInterpolation

universe u

/-- The prescribed small-gap regime has one finite exceptional set for all close
extension-field polynomials, with the explicit constant of [DKTZ26, Theorem 5.11(1)].
Every other witness has an exact base-field correlated pair. -/
theorem exists_prescribedLineMCA {F E : Type u} [Field F] [Field E]
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar :
      let d := Nat.ceil (Real.exp ((27 / 10) / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
      let ν := 2 * m - 1
      let K := max k (Nat.floor (δ * n / 2))
      ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ prescribedMCAConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp ((27 / 10) / δ)) + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        agreementThreshold δ n k ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota k z P := by
  classical
  let values : Fin 2 → Fin n → F := ![f, g]
  obtain ⟨exceptional, hcard, hgood⟩ := exists_prescribedCurveMCA
    δ n k 1 domain values iota hδ hδ' hk (by decide) hblock hA hchar
  refine ⟨exceptional, by simpa using hcard, ?_⟩
  intro z hz P hdegree hagree
  have hword : powerBatchedWord (ℓ := 1) (fun t i ↦ iota (values t i)) z =
      (fun i ↦ iota (f i) + z * iota (g i)) := by
    funext i
    simp [values, powerBatchedWord, Fin.sum_univ_two]
  have hpower := hgood z hz P hdegree (by
    rw [hword]
    exact hagree)
  simpa [values] using exactCorrelatedPair_of_powerAgreement_one
    domain values iota z P hpower

end ReedSolomon
