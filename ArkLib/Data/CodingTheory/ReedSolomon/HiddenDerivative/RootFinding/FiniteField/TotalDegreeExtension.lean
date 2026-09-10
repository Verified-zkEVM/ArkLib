/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Counting.TotalJetDegreeRootCount
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.ExtensionRootCount
/-!
# Extension-field witnesses with a total-jet-degree budget

Injective coefficient extension preserves the original equation's total jet degree. Counting
its solutions over an extension therefore bounds the base-field solutions by `2*Δ*q^(e*d)`
when half the witness field avoids the separant degree budget. No normalization is required.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], differential root counting and the larger-field clause of Theorem 1.1.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F E : Type*} [Field F] [Field E] {d D : ℕ}

/-- Injective coefficient extension preserves total degree in the jet variables. -/
theorem jetTotalDegree_map_eq (f : F →+* E) (hf : Function.Injective f)
    (Q : DifferentialPolynomial F d) : jetTotalDegree (MvPolynomial.map f Q) =
      jetTotalDegree Q := by
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q hf]

/-- Extension witnesses give the twice-total-degree root bound for base-field solutions. -/
theorem natCard_boundedSolution_le_extension_two_totalJetDegree [Finite F]
    (Q : DifferentialPolynomial F d) (e H Δ : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H)
    (hDegree : jetTotalDegree Q ≤ Δ) (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ (e * d) := by
  let : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  let : NeZero e := ⟨he.ne'⟩
  let E := FiniteField.Extension F (ringChar F) e
  let Qₑ : DifferentialPolynomial E d := MvPolynomial.map (algebraMap F E) Q
  have hcardE : Nat.card E = Nat.card F ^ e :=
    FiniteField.natCard_extension F (ringChar F) e
  have hQₑ : Qₑ ≠ 0 := by
    intro hzero
    apply hQ
    apply MvPolynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    simpa [Qₑ] using hzero
  have hcharₑ : IsBelowCharacteristic D Qₑ :=
    (isBelowCharacteristic_map_iff Q D).mpr hchar
  have hWeightₑ : differentialWeightedDegree D Qₑ - (D - d) ≤ H := by
    simpa only [Qₑ, differentialWeightedDegree_map_eq
      (algebraMap F E) (algebraMap F E).injective Q] using hWeight
  have hDegreeₑ : jetTotalDegree Qₑ ≤ Δ := by
    simpa only [Qₑ, jetTotalDegree_map_eq (algebraMap F E) (algebraMap F E).injective Q]
      using hDegree
  have hcount := natCard_boundedSolution_le_two_totalJetDegree Qₑ H Δ hQₑ hcharₑ
    hWeightₑ hDegreeₑ (by simpa only [hcardE] using hlarge)
  exact (BoundedSolution.natCard_le_extension Q D).trans
    (by simpa only [hcardE, pow_mul] using hcount)

/-- A strict interpolation degree cutoff gives the reduced budget `max(0,L-(D+1)+d)`
and the prefactor twice the total jet degree in either witness-field regime. -/
theorem natCard_boundedSolution_le_extension_totalJetDegree_of_interpolation_degree [Finite F]
    (Q : DifferentialPolynomial F d) (e L Δ : ℕ) (he : 0 < e) (hdD : d ≤ D)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q < L)
    (hDegree : jetTotalDegree Q ≤ Δ)
    (hlarge : 2 * (L + d - (D + 1)) ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ (e * d) := by
  apply natCard_boundedSolution_le_extension_two_totalJetDegree
    Q e (L + d - (D + 1)) Δ he hQ hchar ?_ hDegree hlarge
  omega

end
end ReedSolomon.HiddenDerivative
