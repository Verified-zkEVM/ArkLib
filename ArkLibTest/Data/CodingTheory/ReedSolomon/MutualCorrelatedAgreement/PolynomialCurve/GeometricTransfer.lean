/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.UnifiedCurve
/-!
# Geometric-transfer interface tests

These examples pin the order-zero incidence convention, the exact free-retention ordinary
formula, and compatibility with the historical `L = D + 1` budget.
-/

namespace ReedSolomon

/-- Zero-dimensional incidence contributes the empty product `1`. -/
example : geometricTransferIncidenceProduct 20 12 4 0 = 1 := by
  simp

/-- The free-retention formula keeps preliminary, joint, and accidental terms separate. -/
example : ordinaryUnifiedPowerFactorAt 20 3 2 4 5 12 7 = 1733 / 3 := by
  norm_num [ordinaryUnifiedPowerFactorAt, ordinaryUnifiedPowerFactorRawAt, ordinaryPsi]

/-- At `L = D + 1`, the new formula is exactly the old fixed-split expression. -/
example : ordinaryUnifiedPowerFactorAt 20 3 2 4 5 12 (3 + 1) =
    ordinaryUnifiedPowerFactorRaw
      (((20 - 3 : ℕ) : ℚ) / ((12 - 3 : ℕ) : ℚ)) 20 3 2 4 5 := by
  exact ordinaryUnifiedPowerFactorAt_succ_eq 20 3 2 4 5 12 (by omega) (by omega)

/-- Root-degree zero is the separate height-only branch. -/
example : ordinaryUnifiedPowerFactorAtOrHeight 20 3 2 0 5 12 7 = 5 := by
  simp

#check exists_geometricTransfer_exceptional
#check exists_geometricTransfer_baseField_semantic
#check exists_exceptional_ordinaryPowerEquation_freeRetention_of_certificates
#check exists_exceptional_ordinaryPowerEquation_unifiedAt_succ
#check commonAgreement_of_frobeniusPowerCut_mem_prime
#check principalOpen_subset_sourceFrobeniusPowerGraphLocusAt
#check finite_sourceFrobeniusPower_points_off_graphs_card_le_at
#check finite_frobeniusPowerRegularBadWitnesses_card_le_at
#check exists_exceptional_frobeniusPowerSeparableSolutions_at
#check exists_exceptional_ordinaryPowerEquation_freeRetention
#check exists_exceptional_ordinaryPowerEquation_base_freeRetention
#check exists_exceptional_ordinaryPowerEquation_base_zeroDegree
#check exists_exceptional_ordinaryPowerEquation_base_freeRetention_allDegrees

end ReedSolomon
