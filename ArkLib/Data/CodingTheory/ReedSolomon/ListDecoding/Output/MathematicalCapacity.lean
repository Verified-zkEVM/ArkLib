/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CapacityOutputBounds
public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.MathematicalUniformRate

/-!
# Revised mathematical capacity bounds for exact decoder outputs

The theorem in this file applies the 300-based mathematical list estimate to any already-proved
`ExactOutput`. It changes neither the output nor the interpolation recipe used to compute it.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CapacityOutputBounds

open Polynomial JetHornerMachine SeparateSampleFieldExecution ReedSolomon

variable {F : Type*} [fieldF : Field F] [decEqF : DecidableEq F] {n k A : ℕ}

/-- Every physical coefficient list satisfying `ExactOutput` inherits the revised 300-based
uniform capacity bound. In particular, this applies unchanged to both retained complete
inefficient decoders. -/
theorem uniform_capacity_length_le_300
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (domain : Fin n ↪ F) (received : Fin n → F) (out : List (List F))
    (hn : HiddenDerivative.uniformRatePartitionMathematicalLength δ ≤ n)
    (hk : 0 < k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ) < ringChar F)
    (he : ExactOutput domain received k A out) :
    (out.length : ℝ) ≤
      (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
        (2 * HiddenDerivative.uniformRatePartitionMathematicalJetBound δ / δ) ^
          HiddenDerivative.uniformRatePartitionOrder δ *
        n ^ HiddenDerivative.uniformRatePartitionOrder δ := by
  obtain ⟨hfinite, hbound⟩ := mathematicalUniformRatePartition_close_list_bound
    hδ hδsmall hn hk hgap hAn domain received hchar
  have hagreement (P : F[X]) :
      @Code.agree (Fin n) inferInstance F decEqF (evalOnPoints domain P) received =
        (@polynomialAgreementSet F fieldF (Classical.decEq F) n
          domain received P).card := by
    apply congrArg Finset.card
    ext i
    simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hsame : (out.map coefficientPolynomial).toFinset = hfinite.toFinset := by
    ext P
    simp only [List.mem_toFinset, Set.Finite.mem_toFinset]
    rw [he.2.2.1]
    change (P.degree < k ∧
      A ≤ @Code.agree (Fin n) inferInstance F decEqF
        (evalOnPoints domain P) received) ↔
      P.degree < k ∧ A ≤ (@polynomialAgreementSet F fieldF
        (Classical.decEq F) n domain received P).card
    rw [hagreement P]
  calc
    (out.length : ℝ) = ((out.map coefficientPolynomial).toFinset.card : ℝ) := by
      rw [List.toFinset_card_of_nodup he.1, List.length_map]
    _ = (hfinite.toFinset.card : ℝ) := by rw [hsame]
    _ = ((@closePolynomialSet F _ (Classical.decEq F) n
        domain received k A).ncard : ℝ) := by
      congr 1
      exact (Set.ncard_eq_toFinset_card _ hfinite).symm
    _ ≤ _ := hbound

end ReedSolomon.ListDecoding.CapacityOutputBounds
