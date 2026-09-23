/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

private abbrev oneJet : DifferentialPolynomial (Polynomial ℚ) 0 := X (some 0)

private theorem oneJet_jetDegree : jetTotalDegree oneJet ≤ 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  rw [support_X] at hu
  simp only [Finset.mem_singleton] at hu
  subst u
  rw [totalJetDegree_eq_sum]
  simp

/-- The first coordinate of a zero-order equation has bidegree `(0, 1)` after flattening. -/
example :
    (optionEquivRight ℚ (Fin 1)).symm
        (commonTaylorNumeratorOver ℚ (Polynomial.C (0 : ℚ)) oneJet 0 0) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
  exact commonTaylorNumeratorOver_mem_restrictBidegree (F := ℚ) (r := 0) 0 oneJet
    0 1 1 0 (by norm_num [TaylorExponentSufficient]) (coeffNatDegreeLE_X (some 0))
    (by norm_num) oneJet_jetDegree ⟨0, by decide⟩

/-- Agreement at the origin with the zero received value keeps the same bidegree bound. -/
example :
    (optionEquivRight ℚ (Fin 1)).symm
        (taylorAgreementEquationOver (F := ℚ) (A := Polynomial ℚ)
          (Polynomial.C 0) oneJet 1 0 (Polynomial.C 0) 0) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
  exact taylorAgreementEquationOver_mem_restrictBidegree (F := ℚ) (r := 0)
    0 0 0 oneJet 0 0 1 1 0 (by norm_num [TaylorExponentSufficient]) (by norm_num)
    (coeffNatDegreeLE_X (some 0)) (by norm_num) oneJet_jetDegree

end

end PolynomialDifferential
