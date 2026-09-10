/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Extension
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RecursiveCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RegularCounting


/-!
# Differential root counts at a chosen extension degree

This file keeps the individual jet-degree bound `t` in the prefactor and allows any positive
extension degree `e`. The resulting bound is `2 * (d + 1) * t^2 * |F|^(e*d)` when the extension
contains at least twice the weighted-degree budget. Thus degrees one and two give the desired
field-size exponents once `t` is bounded independently of the field size.

The prefactor is deliberately conservative: the existing singular recursion charges at most
`(d + 1) * t` branches, each with regular-jet cost `t`. This is not the sharper total-jet-degree
prefactor from the manuscript. The witness budget here bounds the original polynomial's weighted
degree, rather than the smaller first-separant degree. All regular-jet injectivity premises are
discharged by the proved below-characteristic lifting theorem. No enumeration or runtime claim
is made.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Appendix A.2, Theorem A.2,
  recursive differential root bound and extension-field descent.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F] [Finite F] {d D : ℕ}

/-- Division-free counting in the witness field, with the individual jet-degree budget retained
in the prefactor. The regular-branch counting premise is discharged by coefficient lifting. -/
theorem boundedSolution_sub_mul_le_of_jetDegree_le
    (Q : DifferentialPolynomial F d) (H t : ℕ)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F * ((d + 1) * t ^ 2 * Nat.card F ^ d) := by
  let := Fintype.ofFinite (BoundedSolution Q D)
  have hRegular : RegularBranchBudget Q D (Nat.card F - H)
      (Nat.card F * t * Nat.card F ^ d) := by
    intro current s hreach hactive hcurrent regular hregular
    apply regularBranch_counting_pow_le current s H t
    · exact isHighestActiveJet_of_highestActiveJet_eq_some hactive
    · exact hcurrent.1
    · exact (differentialWeightedDegree_le_of_reflTransGen_singularStep hreach).trans hWeight
    · exact (jetDegree_le_of_reflTransGen_singularStep hreach s).trans (hDegree s)
    · exact hregular
  have hcount := boundedSolution_recursive_counting_of_jetDegree_le Q hQ hchar
    (Nat.card F - H) (Nat.card F * t * Nat.card F ^ d) t Finset.univ hDegree hRegular
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcount
  calc
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
        ((d + 1) * t) * (Nat.card F * t * Nat.card F ^ d) := hcount
    _ = Nat.card F * ((d + 1) * t ^ 2 * Nat.card F ^ d) := by ring

/-- Count base-field solutions using witnesses in the extension of degree `e`.
The characteristic remains that of the base field; only the witness cardinality increases.
No lower bound on the witness cardinality is needed for this division-free inequality. -/
theorem boundedSolution_extension_sub_mul_le
    (Q : DifferentialPolynomial F d) (e H t : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d)) := by
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
  have hWeightₑ : differentialWeightedDegree D Qₑ ≤ H := by
    simpa only [Qₑ, differentialWeightedDegree_map_eq
      (algebraMap F E) (algebraMap F E).injective Q] using hWeight
  have hDegreeₑ : ∀ s, jetDegree Qₑ s ≤ t := by
    intro s
    simpa only [Qₑ, jetDegree_map_eq (algebraMap F E) (algebraMap F E).injective Q s]
      using hDegree s
  have hcount := boundedSolution_sub_mul_le_of_jetDegree_le Qₑ H t hQₑ hcharₑ
    hWeightₑ hDegreeₑ
  have hDescent : Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution Qₑ D) :=
    BoundedSolution.natCard_le_extension Q D
  calc
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
        (Nat.card F ^ e - H) * Nat.card (BoundedSolution Qₑ D) :=
      Nat.mul_le_mul_left _ hDescent
    _ ≤ Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d)) := by
      simpa only [hcardE, pow_mul] using hcount

/-- With at least half the extension field available as regular witnesses, the root count has
exponent `e*d` and prefactor `2*(d+1)*t²`. Both ambient and individual jet degrees are strictly
below the characteristic through `IsBelowCharacteristic`; `t` itself need not be below it. -/
theorem natCard_boundedSolution_le_extension_pow
    (Q : DifferentialPolynomial F d) (e H t : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * t ^ 2 * Nat.card F ^ (e * d) := by
  have hcount := boundedSolution_extension_sub_mul_le Q e H t he hQ hchar hWeight hDegree
  have hS : 0 < Nat.card F ^ e := pow_pos Nat.card_pos e
  have hhalf : Nat.card F ^ e ≤ 2 * (Nat.card F ^ e - H) := by omega
  apply Nat.le_of_mul_le_mul_left ?_ hS
  calc
    Nat.card F ^ e * Nat.card (BoundedSolution Q D) ≤
        (2 * (Nat.card F ^ e - H)) * Nat.card (BoundedSolution Q D) :=
      Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D)) := by ring
    _ ≤ 2 * (Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d))) :=
      Nat.mul_le_mul_left 2 hcount
    _ = Nat.card F ^ e * (2 * (d + 1) * t ^ 2 * Nat.card F ^ (e * d)) := by ring

/-- The characteristic contract supplies a uniform individual jet-degree bound by the base-field
cardinality. This is the convenient extension-degree-polymorphic form for consumers that do not
have a sharper jet-degree estimate. -/
theorem natCard_boundedSolution_le_extension_pow_of_weightedDegree
    (Q : DifferentialPolynomial F d) (e H : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤
      2 * (d + 1) * Nat.card F ^ 2 * Nat.card F ^ (e * d) := by
  let _ := Fintype.ofFinite F
  have hCharCard : ringChar F ≤ Nat.card F := by
    obtain ⟨extensionDegree, _hprime, hcard⟩ := FiniteField.card F (ringChar F)
    apply Nat.le_of_dvd Nat.card_pos
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self _ extensionDegree.ne_zero
  apply natCard_boundedSolution_le_extension_pow Q e H (Nat.card F) he hQ hchar hWeight
  · intro s
    exact (hchar.2 s).le.trans hCharCard
  · exact hlarge

end
end ReedSolomon.HiddenDerivative
