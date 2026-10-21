/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.StageCharges
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence

/-!
# Derivative-capped counting in the first-order Taylor chart

The first-order Taylor chart bounds the number of regular jets satisfying high Taylor cuts and
many agreement equations by the fixed-fiber stage degree and the sharp agreement-incidence ratio.

## Main statements

* `finite_regularHighCutJets_card_le_derivativeCapped_of_exponent`: the finite-set counting bound
  with explicit sufficient exponent and derivative-capped stage degree.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial PolynomialDifferential

variable {F : Type*} [Field F]

/-- A finite set of regular first-order jets satisfying the high Taylor cuts and at least `A`
agreement equations has size at most the fixed-fiber stage degree times the sharp
`(n-k+1)/(A-k+1)` agreement-incidence ratio. -/
theorem finite_regularHighCutJets_card_le_derivativeCapped_of_exponent [IsAlgClosed F]
    (center : F) (Q : DifferentialPolynomial F 1) (K k j r τ : ℕ)
    (hτ : TaylorExponentSufficient 1 K τ) (hτpos : 0 < τ) (hK : 1 < K)
    (hr : 0 < r) (hrj : r ≤ j)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ j)
    (hderiv : Q.degreeOf (some 1) ≤ r)
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hkA : k ≤ A) (hAn : A ≤ n) (S : Finset (Fin 2 → F))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q τ l.val) = 0)
    (hA : ∀ jet ∈ S, A ≤
      {i | aeval jet
        (taylorAgreementEquation center Q K τ (domain i) (received i)) = 0}.ncard) :
    (S.card : ℚ) ≤ firstOrderCurveFiberStageOne K j r τ *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  let b := firstOrderTaylorTotalCap j τ
  let c := firstOrderTaylorDerivativeCap K j r τ
  have hjet' : jetTotalDegree Q ≤ j := by
    have hw : (fun i : Option (Fin 2) ↦ i.elim 0 (fun _ ↦ 1)) = jetDegreeWeight := by
      funext i
      cases i <;> rfl
    change Q.weightedTotalDegree jetDegreeWeight ≤ j
    rw [← hw]
    exact hjet
  have hb : 0 < b := by simp [b, firstOrderTaylorTotalCap]
  have hc : 0 < c := by
    simp only [c, firstOrderTaylorDerivativeCap]
    apply lt_min hb
    have : 0 < K - 1 := by omega
    omega
  have hjb : j ≤ b := by
    simp only [b, firstOrderTaylorTotalCap]
    calc
      j = 1 + (j - 1) := by omega
      _ ≤ 1 + τ * (j - 1) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_left (j - 1) hτpos) 1
  have hrc : r ≤ c := by
    simp only [c, firstOrderTaylorDerivativeCap]
    apply le_min
    · exact hrj.trans hjb
    · calc
        r = 1 + (r - 1) := by omega
        _ ≤ (K - 1) + τ * (r - 1) :=
          Nat.add_le_add (by omega) (Nat.le_mul_of_pos_left (r - 1) hτpos)
        _ = τ * (r - 1) + (K - 1) := by omega
  have hchart : 1 + τ * (j - 1) ≤ b := by simp [b, firstOrderTaylorTotalCap]
  have hbound := card_le_of_firstOrderHighTaylorCuts_of_agreement_capped
    center Q hτ hK hb hc hjb hrc hchart hr hjet'
    hderiv domain (received := received) hkA hAn S hS hA
  simpa [firstOrderCurveFiberStageOne, firstOrderTaylorDerivativeCap,
    firstOrderTaylorTotalCap, b, c] using hbound

end

end ReedSolomon.HiddenDerivative
