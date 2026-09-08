/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.Parameters
import ArkLib.Data.Probability.StridedQueryBoundary
import Mathlib.Tactic.Linarith

/-!
# Expected raw proof-size reductions for the actual ProveKit schedules

The query rows are serialized even when indices repeat; authentication hashes are deduplicated.
Accordingly each removed query saves its row payload deterministically, while the hash saving
uses independent uniform sampling with replacement. These statements evaluate that mathematical
model. They do not assert serializer correctness or describe compressed proof sizes.

Passport has two outer witness proofs and two internal proofs. Its outer consistency opening
samples every other leaf, so its hash expectation uses the strided-tree theorem rather than the
ordinary uniform-leaf formula. Two masking evaluations accompany each changed outer query and
consistency query. The Goldilocks lookup has two witnesses and a separate blinding proof, and
we charge the two added out-of-domain evaluations before stating its saving.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open scoped BigOperators
open ArkLib.FiniteFieldBudget

/-- Expected saving in ordinary openings across one schedule, with field elements of the
given byte width. Additional consistency openings and OOD messages are accounted for separately. -/
def Schedule.expectedOpeningSaving {rounds : ℕ} (s : Schedule rounds)
    (elementBytes : ℕ) : ℚ :=
  ∑ i : Fin rounds,
    expectedPayloadSaving (s.row i).n (Nat.log2 (s.row i).n)
      (s.row i).baselineQueries (s.row i).revisedQueries
      ((s.row i).leafPayloadWidth * elementBytes) 32 0

/-- Ordinary openings in both outer Passport witness proofs. -/
def passportOrdinarySaving : ℚ := 2 * passportOuterWitness.expectedOpeningSaving 32

/-- Consistency openings in the two outer Passport proofs. Queries have stride two in the
initial tree, and each opened row contains eight BN254 field elements. -/
def passportConsistencySaving : ℚ :=
  2 * (((passportOuterWitness.row 1).baselineQueries -
      (passportOuterWitness.row 1).revisedQueries : ℕ) * (8 * 32) +
    32 * (expectedStridedAuthenticationHashes 131072 17 1
        (passportOuterWitness.row 1).baselineQueries -
      expectedStridedAuthenticationHashes 131072 17 1
        (passportOuterWitness.row 1).revisedQueries))

/-- Two masking evaluations per removed outer or consistency query, in each witness proof. -/
def passportMaskingSaving : ℕ :=
  2 * (((passportOuterWitness.row 0).baselineQueries -
      (passportOuterWitness.row 0).revisedQueries) +
    ((passportOuterWitness.row 1).baselineQueries -
      (passportOuterWitness.row 1).revisedQueries)) * 2 * 32

/-- Ordinary openings in the two internal Passport proofs. The initial row width is sixteen. -/
def passportInternalSaving : ℚ := 2 * passportInternalZk.expectedOpeningSaving 32

/-- Complete expected raw saving from the changes to the Passport proof. -/
def passportExpectedSaving : ℚ :=
  passportOrdinarySaving + passportConsistencySaving + passportMaskingSaving +
    passportInternalSaving

/-- Expected raw saving for two lookup witnesses and their independent blinding proof,
after charging the two added cubic-field OOD values. The fixed blind tail cancels. -/
def goldilocksLookupExpectedSaving : ℚ :=
  2 * goldilocksLookupWitness.expectedOpeningSaving 24 +
    goldilocksLookupBlind.expectedOpeningSaving 24 - 2 * 24

set_option maxRecDepth 16384

private theorem log2_32 : Nat.log2 32 = 5 := by decide
private theorem log2_512 : Nat.log2 512 = 9 := by decide
private theorem log2_1024 : Nat.log2 1024 = 10 := by decide
private theorem log2_2048 : Nat.log2 2048 = 11 := by decide
private theorem log2_4096 : Nat.log2 4096 = 12 := by decide
private theorem log2_8192 : Nat.log2 8192 = 13 := by decide
private theorem log2_16384 : Nat.log2 16384 = 14 := by decide
private theorem log2_32768 : Nat.log2 32768 = 15 := by decide
private theorem log2_65536 : Nat.log2 65536 = 16 := by decide
private theorem log2_131072 : Nat.log2 131072 = 17 := by decide
private theorem log2_262144 : Nat.log2 262144 = 18 := by decide

set_option maxHeartbeats 12000000 in
-- Exact occupancy probabilities involve large rational powers across all Merkle levels.
/-- Exact rational evaluation of the ordinary outer-opening contribution. -/
theorem passportOrdinarySaving_interval :
    (358910863 : ℚ) / 10000 < passportOrdinarySaving ∧
      passportOrdinarySaving < (358910864 : ℚ) / 10000 := by
  norm_num [passportOrdinarySaving, Schedule.expectedOpeningSaving, passportOuterWitness,
    codeRound, expectedPayloadSaving, expectedAuthenticationHashes, Fin.sum_univ_succ,
    Finset.sum_range_succ,
    log2_32, log2_512, log2_1024, log2_2048, log2_4096, log2_8192,
    log2_16384, log2_32768, log2_65536, log2_131072, log2_262144]

set_option maxHeartbeats 12000000 in
-- Exact occupancy probabilities involve large rational powers across all Merkle levels.
/-- The consistency opening saves approximately 7,973.77 raw bytes. -/
theorem passportConsistencySaving_interval :
    (79737728 : ℚ) / 10000 < passportConsistencySaving ∧
      passportConsistencySaving < (79737729 : ℚ) / 10000 := by
  norm_num [passportConsistencySaving, passportOuterWitness, codeRound,
    expectedStridedAuthenticationHashes, expectedAuthenticationHashes, Finset.sum_range_succ,
    log2_32, log2_512, log2_1024, log2_2048, log2_4096, log2_8192,
    log2_16384, log2_32768, log2_65536, log2_131072, log2_262144]

/-- The masking-evaluation contribution is deterministic. -/
theorem passportMaskingSaving_eq : passportMaskingSaving = 3200 := by decide

set_option maxHeartbeats 12000000 in
-- Exact occupancy probabilities involve large rational powers across all Merkle levels.
/-- Both internal proofs together save approximately 32,499.90 expected raw bytes. -/
theorem passportInternalSaving_interval :
    (324998993 : ℚ) / 10000 < passportInternalSaving ∧
      passportInternalSaving < (324998994 : ℚ) / 10000 := by
  norm_num [passportInternalSaving, Schedule.expectedOpeningSaving, passportInternalZk,
    codeRound, expectedPayloadSaving, expectedAuthenticationHashes, Fin.sum_univ_succ,
    Finset.sum_range_succ,
    log2_32, log2_512, log2_1024, log2_2048, log2_4096, log2_8192,
    log2_16384, log2_32768, log2_65536, log2_131072, log2_262144]

/-- A rational interval for the combined Passport saving, derived from its four contributions. -/
theorem passportExpectedSaving_interval :
    (795647584 : ℚ) / 10000 < passportExpectedSaving ∧
      passportExpectedSaving < (795647587 : ℚ) / 10000 := by
  obtain ⟨ho, ho'⟩ := passportOrdinarySaving_interval
  obtain ⟨hc, hc'⟩ := passportConsistencySaving_interval
  obtain ⟨hi, hi'⟩ := passportInternalSaving_interval
  dsimp [passportExpectedSaving]
  rw [passportMaskingSaving_eq]
  constructor <;> linarith

set_option maxHeartbeats 12000000 in
-- Exact occupancy probabilities involve large rational powers across all Merkle levels.
/-- The full lookup comparison saves approximately 24,234.60 expected raw bytes, net of OOD. -/
theorem goldilocksLookupExpectedSaving_interval :
    (242345980 : ℚ) / 10000 < goldilocksLookupExpectedSaving ∧
      goldilocksLookupExpectedSaving < (242345981 : ℚ) / 10000 := by
  norm_num [goldilocksLookupExpectedSaving, Schedule.expectedOpeningSaving,
    goldilocksLookupWitness, goldilocksLookupBlind, codeRound, expectedPayloadSaving,
    expectedAuthenticationHashes, Fin.sum_univ_succ, Finset.sum_range_succ,
    log2_32, log2_512, log2_1024, log2_2048, log2_4096, log2_8192,
    log2_16384, log2_32768, log2_65536, log2_131072, log2_262144]

end ArkLibExamples.ReedSolomon.ProveKit
