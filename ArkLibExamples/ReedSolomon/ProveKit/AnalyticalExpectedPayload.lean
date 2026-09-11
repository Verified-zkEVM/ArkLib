/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.AnalyticalParameters
import ArkLibExamples.ReedSolomon.ProveKit.ExpectedPayload
import Mathlib.Tactic.Linarith

/-!
# Expected payload changes for the analytical ProveKit schedules

These are analytical expectations in the existing uniform-query Merkle model.  They do not alter
the measured proof-size values.  Passport removes one ordinary opening from each of two outer
witness proofs.  Goldilocks removes one 24-byte OOD field element from each of two lookup witness
commitments; its query schedule is unchanged.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open ArkLib.FiniteFieldBudget

/-- Additional expected Passport saving from changing the fifth outer row from 23 to 22 queries
in each of the two outer witness proofs. -/
def passportAnalyticalAdditionalSaving : ℚ :=
  2 * expectedPayloadSaving 16384 14 23 22 256 32 0

/-- Complete expected raw Passport saving for the analytical configuration. -/
def passportAnalyticalExpectedSaving : ℚ :=
  passportExpectedSaving + passportAnalyticalAdditionalSaving

set_option maxHeartbeats 12000000 in
-- The exact occupancy expression contains rational powers at every Merkle level.
/-- The additional Passport saving is approximately 971.476 bytes. -/
theorem passportAnalyticalAdditionalSaving_interval :
    (9714762 : ℚ) / 10000 < passportAnalyticalAdditionalSaving ∧
      passportAnalyticalAdditionalSaving < (9714763 : ℚ) / 10000 := by
  norm_num [passportAnalyticalAdditionalSaving, expectedPayloadSaving,
    expectedAuthenticationHashes, Finset.sum_range_succ]

/-- The complete analytical Passport expected raw saving rounds to 80,536.23 bytes at the
precision displayed in the manuscript. -/
theorem passportAnalyticalExpectedSaving_interval :
    (8053623 : ℚ) / 100 < passportAnalyticalExpectedSaving ∧
      passportAnalyticalExpectedSaving < (8053624 : ℚ) / 100 := by
  obtain ⟨hc, hc'⟩ := passportExpectedSaving_interval
  obtain ⟨ha, ha'⟩ := passportAnalyticalAdditionalSaving_interval
  dsimp [passportAnalyticalExpectedSaving]
  constructor <;> linarith

/-- Removing one 24-byte OOD element from each of two Goldilocks witness commitments adds 48
raw bytes of saving. -/
def goldilocksLookupAnalyticalAdditionalSaving : ℕ := 2 * 24

theorem goldilocksLookupAnalyticalAdditionalSaving_eq :
    goldilocksLookupAnalyticalAdditionalSaving = 48 := by
  rfl

/-- Complete expected raw Goldilocks lookup saving for the analytical configuration. -/
def goldilocksLookupAnalyticalExpectedSaving : ℚ :=
  goldilocksLookupExpectedSaving + goldilocksLookupAnalyticalAdditionalSaving

/-- The complete analytical lookup expected raw saving rounds to 24,282.60 bytes. -/
theorem goldilocksLookupAnalyticalExpectedSaving_interval :
    (2428259 : ℚ) / 100 < goldilocksLookupAnalyticalExpectedSaving ∧
      goldilocksLookupAnalyticalExpectedSaving < (2428260 : ℚ) / 100 := by
  obtain ⟨h, h'⟩ := goldilocksLookupExpectedSaving_interval
  rw [goldilocksLookupAnalyticalExpectedSaving,
    goldilocksLookupAnalyticalAdditionalSaving_eq]
  constructor <;> linarith

end ArkLibExamples.ReedSolomon.ProveKit
