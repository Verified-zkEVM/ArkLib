/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedGraphCounting
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
import ArkLib.Data.Polynomial.Differential.BaseChange
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.DerivativeCappedCounting

/-!
# Derivative-capped counting for admissible polynomial tuple graphs

Specializing an admissible tuple at one common challenge injects it into a regular first-order
Taylor chart. Bounding the total jet degree and the derivative degree separately then bounds every
finite family of admissible tuples by the first-order fixed-fiber degree and the sharp agreement
ratio.

## Main statements

* `admissibleChartTuples_card_le_derivativeCapped_of_exponent`: the derivative-capped bound for
  every finite family of admissible tuple graphs.
* `admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped`: the bound for the complete
  finite family of admissible tuple graphs.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Every finite family of admissible first-order tuple graphs has size at most the fixed-fiber
degree from the total and derivative degree bounds, times the sharp agreement ratio. -/
theorem admissibleChartTuples_card_le_derivativeCapped_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ firstOrderCurveFiberStageOne K v u τ *
      (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨z, jets, _, _, _, hcard, hS, hA⟩ :=
    exists_regularHighCutJetImage_of_admissibleChartTuples
    domain w iota center Q K k L τ hτ hkK tuples htuples
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let domainE : Fin n ↪ E :=
    ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hw : (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) =
      jetDegreeWeight (d := 1) := by
    funext i
    cases i <;> rfl
  have htotal : jetTotalDegree Q ≤ v := by
    simpa only [jetTotalDegree, ← hw] using hjet
  have htotalz : jetTotalDegree Qz ≤ v :=
    (jetTotalDegree_map_le (Polynomial.evalRingHom z) Q).trans htotal
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    simpa only [jetTotalDegree, ← hw] using htotalz
  have hderivz : Qz.degreeOf (some 1) ≤ u := by
    calc
      Qz.degreeOf (some 1) = jetDegree Qz 1 := rfl
      _ ≤ jetDegree Q 1 := by
        simpa only [Qz] using jetDegree_map_le (Polynomial.evalRingHom z) Q 1
      _ = Q.degreeOf (some 1) := rfl
      _ ≤ u := hderiv
  have hbound := finite_regularHighCutJets_card_le_derivativeCapped_of_exponent
    center Qz K k v u τ hτ hτpos hK hu huv hvle hderivz
    domainE received hkL hLn jets hS hA
  rw [hcard] at hbound
  exact hbound

/-- The complete finite family of admissible first-order tuple graphs has the derivative-capped
bound from the total and derivative degree bounds. -/
theorem admissibleChartTupleFamilyAtExponent_card_le_derivativeCapped
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] 1) (K k L v u τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ)
    (hK : 1 < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hu : 0 < u) (huv : u ≤ v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hderiv : Q.degreeOf (some 1) ≤ u) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      firstOrderCurveFiberStageOne K v u τ *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
  apply admissibleChartTuples_card_le_derivativeCapped_of_exponent
    domain w iota center Q K k L v u τ hτ hτpos hK hkK hkL hLn hu huv hjet hderiv
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
