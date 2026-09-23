/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.Certificate

/-!
# Symbolic interpolation acceptance test

This concrete instance has an empty received set and a nonzero weighted-support space. The strict
dimension surplus yields a certificate with the prescribed degree bounds.
-/

open PolynomialDifferential ReedSolomon.HiddenDerivative

namespace SymbolicInterpolationTest

private def noCenters : Fin 0 ↪ ℚ where
  toFun := Fin.elim0
  inj' := by
    intro i
    exact Fin.elim0 i

/-- The fixed-margin certificate construction has a concrete instance with no received points. -/
example : Nonempty (WeightedSupportCertificate ℚ 1 1 1 0 11 noCenters Fin.elim0 Fin.elim0) := by
  have hD : 0 < 1 := by omega
  have hzero : (0 : JetVariable 0 →₀ ℕ) ∈
      weightedSupportExponents 1 0 0
        (((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (0 : ℝ))) hD := by
    simp [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree]
  have hdim : 0 < Module.finrank ℚ
      (weightedSupportSpace ℚ 1 0 0
        (((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * (1 + (0 : ℝ))) hD) := by
    rw [finrank_weightedSupportSpace_eq_card hD]
    exact Finset.card_pos.mpr ⟨0, hzero⟩
  exact exists_weightedSupport_certificate_of_fixed_margin (F := ℚ) (D := 1) (d := 0)
    (W := 0) (m := 1) (A := 1) (k := 1) (g₀ := 0) hD (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) noCenters Fin.elim0 Fin.elim0
    (by
      norm_num [Fintype.card_fin]
      exact_mod_cast hdim)

end SymbolicInterpolationTest
