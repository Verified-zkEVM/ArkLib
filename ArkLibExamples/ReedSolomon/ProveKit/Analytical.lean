/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalBudgets
import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalCertificates
import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalExpectedPayload

/-!
# Further analytical ProveKit certificates

This capstone exposes the distinct analytical Passport and Goldilocks configurations, their exact
local budgets, sharp squarefree arithmetic, and expected-payload calculations.  The original
measured schedules remain the declarations in `Parameters.lean`.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields

/-- Both Passport supports satisfy their sharp squarefree characteristic guards over BN254. -/
theorem passportOuterAnalytical_characteristicGuards :
    passportOuterAnalyticalMcaData.characteristicGuard < ringChar BN254Scalar ∧
      passportOuterAnalyticalListData.characteristicGuard < ringChar BN254Scalar := by
  rw [passportOuterAnalyticalMca_characteristicGuard,
    passportOuterAnalyticalList_characteristicGuard, bn254Scalar_ringChar]
  norm_num [BN254.scalarFieldSize]

/-- Both lookup supports satisfy their sharp squarefree characteristic guards over Goldilocks. -/
theorem goldilocksLookupAnalytical_characteristicGuards :
    goldilocksLookupAnalyticalMcaData.characteristicGuard < ringChar GoldilocksCubic ∧
      goldilocksLookupAnalyticalListData.characteristicGuard < ringChar GoldilocksCubic := by
  rw [goldilocksLookupAnalyticalMca_characteristicGuard,
    goldilocksLookupAnalyticalList_characteristicGuard, goldilocksCubic_ringChar]
  norm_num [Goldilocks.fieldSize]

end ArkLibExamples.ReedSolomon.ProveKit
