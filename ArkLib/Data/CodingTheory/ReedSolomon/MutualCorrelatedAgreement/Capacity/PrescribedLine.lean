/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.PrescribedCurve
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine

/-!
# Prescribed mutual correlated agreement on lines

The prescribed-curve bound specializes to affine lines with an explicit exceptional-set bound and
an exact correlated-pair conclusion.

## Main statements

* `ReedSolomon.exists_prescribedLine_exactCorrelatedPair`: exact correlated agreement outside one
  finite set.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative.WeightedSupportParameters

universe u

open Classical in
/-- Under the prescribed small-gap hypotheses, all sufficiently agreeing line polynomials outside
one finite exceptional set have exact correlated-pair witnesses. -/
theorem exists_prescribedLine_exactCorrelatedPair {F E : Type u} [Field F] [Field E]
    [IsAlgClosed E]
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonic (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : capacityAgreementThreshold δ n k ≤ n)
    (hchar :
      let d := Nat.ceil (Real.exp ((27 / 10) / δ))
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonic (d - 1))
      let ν := 2 * m - 1
      let K := max k (Nat.floor (δ * n / 2))
      ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ prescribedProductAgreementConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp ((27 / 10) / δ)) + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        capacityAgreementThreshold δ n k ≤
          (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
            (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota k z P := by
  let values : Fin 2 → Fin n → F := ![f, g]
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_of_prescribedCurve δ n k 1 domain values iota
      hδ hδ' hk (by norm_num) (by simpa [xi] using hblock)
    hA (by simpa [xi] using hchar)
  refine ⟨exceptional, by simpa [xi] using hcard, ?_⟩
  intro z hz P hdegree hagree
  have hword : powerBatchedWord (ℓ := 1) (fun t i ↦ iota (values t i)) z =
      (fun i ↦ iota (f i) + z * iota (g i)) := by
    funext i
    simp [values, powerBatchedWord, Fin.sum_univ_two]
  have hagree' : capacityAgreementThreshold δ n k ≤
      (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card := by
    rw [hword]
    exact hagree
  have hpower := hgood z hz P hdegree hagree'
  simpa [values] using exactCorrelatedPair_of_powerAgreement_one domain values iota z P hpower

end ReedSolomon
