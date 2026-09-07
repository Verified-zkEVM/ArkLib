/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.FiniteFieldBudget
import Mathlib.Tactic.NormNum

/-!
# ProveKit WHIR parameter arithmetic

This module checks two proposed local replacements for the pinned ProveKit WHIR Standard witness
profile at revision `8804e80e8e890d01bb585f2bd5e5b564ac0fd80d`. Both rows have Reed--Solomon
block length `n = 2^20`, message dimension `k = 2^18`, interleaving width eight, batch size one,
and vector size `2^21`. The BN254 row selects agreement `492831 / 1048576` and 109 queries. The
cubic Goldilocks row selects agreement `508263 / 1048576`, 113 queries, and a second initial
out-of-domain sample.

The BN254 certificate supplies `E = 513074544911280471520373905` and
`L = 147000408479737`. The cubic Goldilocks arithmetic uses
`E = 14436064712520704240` and `L = 8279136487`. Their derivation from the revised finite
certificate remains a separate geometric seam.

## Reading the statements

For a row with field cardinality `q`, agreement numerator `A`, exceptional-count bound `E`, list
bound `L`, and query count `t`, the five changed error slots are

```text
choose(L, 2) * ((vectorSize - 1) / q)^initialOodSamples,
E / q,
2 * L / q,
(E + 2 * L) / q,
2 * (1 + t) * 160 / q.
```

`*_changed_slots_meet_target` states that each term is at most `2^-128`, using cross-multiplied
natural-number inequalities. `*_query_selection` checks the existing proof-of-work acceptance
probability `(powThreshold + 1) / 2^64` times `(A / n)^t`; it also shows that one fewer query
exceeds the same query-only target.

The payload theorem uses the conservative lower bound
`(oldQueries - t) * (rowBytes - 32) - extraOodBytes`. Here `rowBytes` is eight field elements, 32
bytes bounds the possible authentication-path increase when one query is removed, and
`extraOodBytes` charges the second cubic-Goldilocks sample. The nominal comparison uses 127
queries; the auxiliary zero-slack comparison uses 119.

Every theorem is a closed proposition about one of the two fixed rows; no received word, code, or
field instance is quantified.

## Proof route and scope

The two `Profile` values expose the parameters specific to each row, and `norm_num` verifies the
resulting closed inequalities. The exceptional and list counts are supplied by
`modular-whir-beyond-johnson.json`. Establishing them from ArkLib's interpolation, root-counting,
and polynomial-curve results remains a separate mathematical bridge. Thus these theorems certify
the local numerical calculation and modeled raw payload, not a complete WHIR coding-soundness
theorem or a measured serialized proof size.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

open ArkLib.FiniteFieldBudget

/-! ## Parameter rows -/

/-- A pinned row of the ProveKit WHIR parameter calculation. -/
structure Profile where
  /-- Reed--Solomon block length. -/
  n : Nat
  /-- Reed--Solomon dimension. -/
  k : Nat
  /-- Length of the interleaved vector tested by the initial out-of-domain check. -/
  vectorSize : Nat
  /-- Number of field elements in one queried row. -/
  interleavingWidth : Nat
  /-- Number of polynomials batched in this calculation. -/
  batchSize : Nat
  /-- Cardinality of the challenge field. -/
  fieldSize : Nat
  /-- Numerator of the agreement fraction, whose denominator is `n`. -/
  agreementNumerator : Nat
  /-- Multiplicity parameter in the concrete list-decoding certificate. -/
  multiplicity : Nat
  /-- First-derivative exponent cap in the concrete list-decoding certificate. -/
  firstJetCap : Nat
  /-- Total jet-degree cap in the concrete list-decoding certificate. -/
  totalJetDegreeCap : Nat
  /-- Upper bound for the exceptional challenge count. -/
  exceptionalCount : Nat
  /-- Upper bound for the decoded list size. -/
  listSize : Nat
  /-- Selected number of uniform queries. -/
  queries : Nat
  /-- Number of initial out-of-domain samples. -/
  initialOodSamples : Nat
  /-- Inclusive 64-bit proof-of-work acceptance threshold. -/
  powThreshold : Nat
  /-- Query count in the pinned nominal ProveKit profile. -/
  nominalQueries : Nat
  /-- Auxiliary zero-slack query reference used by the source checker. -/
  zeroSlackQueryReference : Nat
  /-- Encoded bytes per base-field element. -/
  fieldBytes : Nat
  /-- Encoded bytes per extension-field element. -/
  extensionBytes : Nat

/-- The pinned BN254 parameter row. -/
def bn254 : Profile where
  n := 1048576
  k := 262144
  vectorSize := 2097152
  interleavingWidth := 8
  batchSize := 1
  fieldSize := 21888242871839275222246405745257275088548364400416034343698204186575808495617
  agreementNumerator := 492831
  multiplicity := 384
  firstJetCap := 168
  totalJetDegreeCap := 688
  exceptionalCount := 513074544911280471520373905
  listSize := 147000408479737
  queries := 109
  initialOodSamples := 1
  powThreshold := 18786624067678312
  nominalQueries := 127
  zeroSlackQueryReference := 119
  fieldBytes := 32
  extensionBytes := 32

/-- The revised cubic Goldilocks parameter row. -/
def goldilocksCubic113 : Profile where
  n := 1048576
  k := 262144
  vectorSize := 2097152
  interleavingWidth := 8
  batchSize := 1
  fieldSize := 6277101731002175853884774869567645561244584131361410908161
  agreementNumerator := 508263
  multiplicity := 16
  firstJetCap := 7
  totalJetDegreeCap := 30
  exceptionalCount := 14436064712520704240
  listSize := 8279136487
  queries := 113
  initialOodSamples := 2
  powThreshold := 18786624067678312
  nominalQueries := 127
  zeroSlackQueryReference := 119
  fieldBytes := 8
  extensionBytes := 24

/-! ## BN254 checks -/

/-- The BN254 row has rate one quarter and the expected interleaved vector size. Its agreement is
below the finite Johnson agreement threshold, so its decoding radius is beyond Johnson. -/
theorem bn254_code_arithmetic :
    bn254.k * 4 = bn254.n ∧
      bn254.interleavingWidth * bn254.k = bn254.vectorSize ∧
      bn254.agreementNumerator ^ 2 < bn254.n * (bn254.k - 1) := by
  norm_num [bn254]

/-- Every changed BN254 error slot is at most `2^-128`, expressed without rational division. -/
theorem bn254_changed_slots_meet_target :
    bn254.listSize * (bn254.listSize - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
        2 * bn254.fieldSize ∧
      bn254.exceptionalCount * 2 ^ 128 ≤ bn254.fieldSize ∧
      2 * bn254.listSize * 2 ^ 128 ≤ bn254.fieldSize ∧
      (bn254.exceptionalCount + 2 * bn254.listSize) * 2 ^ 128 ≤ bn254.fieldSize ∧
      2 * (1 + bn254.queries) * 160 * 2 ^ 128 ≤ bn254.fieldSize := by
  norm_num [bn254]

/-- The BN254 OOD collision term is an instance of the shared one-sample predicate. -/
theorem bn254_ood_meets_target :
    RepeatedOodMeetsTarget bn254.listSize bn254.vectorSize bn254.fieldSize
      bn254.initialOodSamples 128 := by
  norm_num [RepeatedOodMeetsTarget, bn254]

/-- The BN254 first-switch term uses the unchanged target list of size 160. -/
theorem bn254_first_switch_meets_target :
    FirstSwitchMeetsTarget 160 bn254.queries bn254.fieldSize 128 := by
  norm_num [FirstSwitchMeetsTarget, bn254]

/-- The BN254 query selection through the shared inclusive-threshold predicate. -/
theorem bn254_query_selection_shared :
    QueryMeetsTarget (2 ^ 64) bn254.powThreshold bn254.agreementNumerator bn254.n
        bn254.queries 128 ∧
      QueryFailsTarget (2 ^ 64) bn254.powThreshold bn254.agreementNumerator bn254.n
        (bn254.queries - 1) 128 := by
  norm_num [QueryMeetsTarget, QueryFailsTarget, bn254]

/-- The BN254 query contribution meets `2^-128` at 109 queries and exceeds it at 108. -/
theorem bn254_query_selection :
    (bn254.powThreshold + 1) * bn254.agreementNumerator ^ bn254.queries * 2 ^ 128 ≤
        2 ^ 64 * bn254.n ^ bn254.queries ∧
      2 ^ 64 * bn254.n ^ (bn254.queries - 1) <
        (bn254.powThreshold + 1) *
          bn254.agreementNumerator ^ (bn254.queries - 1) * 2 ^ 128 := by
  norm_num [bn254]

/-- The checker's conservative BN254 raw-payload lower bounds are 4032 bytes against the nominal
profile and 2240 bytes against its auxiliary zero-slack reference. -/
theorem bn254_payload_lower_bounds :
    (bn254.nominalQueries - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 4032 ∧
      (bn254.zeroSlackQueryReference - bn254.queries) *
          (bn254.interleavingWidth * bn254.fieldBytes - 32) -
        (bn254.initialOodSamples - 1) * bn254.extensionBytes = 2240 := by
  norm_num [bn254]

/-! ## Revised cubic Goldilocks checks -/

/-- The cubic Goldilocks row has rate one quarter and the expected interleaved vector size. Its
agreement is below the finite Johnson agreement threshold, so its decoding radius is beyond
Johnson. -/
theorem goldilocksCubic113_code_arithmetic :
    goldilocksCubic113.k * 4 = goldilocksCubic113.n ∧
      goldilocksCubic113.interleavingWidth * goldilocksCubic113.k =
        goldilocksCubic113.vectorSize ∧
      goldilocksCubic113.agreementNumerator ^ 2 <
        goldilocksCubic113.n * (goldilocksCubic113.k - 1) := by
  norm_num [goldilocksCubic113]

/-- Every changed cubic Goldilocks error slot is at most `2^-128`, expressed without rational
division. The initial out-of-domain term includes both extension-field samples. -/
theorem goldilocksCubic113_changed_slots_meet_target :
    goldilocksCubic113.listSize * (goldilocksCubic113.listSize - 1) *
          (goldilocksCubic113.vectorSize - 1) ^ 2 * 2 ^ 128 ≤
        2 * goldilocksCubic113.fieldSize ^ 2 ∧
      goldilocksCubic113.exceptionalCount * 2 ^ 128 ≤ goldilocksCubic113.fieldSize ∧
      2 * goldilocksCubic113.listSize * 2 ^ 128 ≤ goldilocksCubic113.fieldSize ∧
      (goldilocksCubic113.exceptionalCount + 2 * goldilocksCubic113.listSize) * 2 ^ 128 ≤
        goldilocksCubic113.fieldSize ∧
      2 * (1 + goldilocksCubic113.queries) * 160 * 2 ^ 128 ≤
        goldilocksCubic113.fieldSize := by
  norm_num [goldilocksCubic113]

/-- The revised OOD pair-collision term meets its local target after two samples. -/
theorem goldilocksCubic113_ood_meets_target :
    RepeatedOodMeetsTarget goldilocksCubic113.listSize goldilocksCubic113.vectorSize
      goldilocksCubic113.fieldSize goldilocksCubic113.initialOodSamples 128 := by
  norm_num [RepeatedOodMeetsTarget, goldilocksCubic113]

/-- The revised affine MCA and two identity tests meet their combined local target. -/
theorem goldilocksCubic113_affine_mca_identity_meets_target :
    AffineMcaIdentityMeetsTarget goldilocksCubic113.exceptionalCount
      goldilocksCubic113.listSize goldilocksCubic113.fieldSize 128 := by
  norm_num [AffineMcaIdentityMeetsTarget, goldilocksCubic113]

/-- The unchanged target list of size 160 makes the first-switch term meet its local target. -/
theorem goldilocksCubic113_first_switch_meets_target :
    FirstSwitchMeetsTarget 160 goldilocksCubic113.queries goldilocksCubic113.fieldSize 128 := by
  norm_num [FirstSwitchMeetsTarget, goldilocksCubic113]

/-- The cubic Goldilocks query contribution meets `2^-128` at 113 queries and exceeds it at 112
for this fixed profile and grinding threshold. -/
theorem goldilocksCubic113_query_selection :
    QueryMeetsTarget (2 ^ 64) goldilocksCubic113.powThreshold
        goldilocksCubic113.agreementNumerator goldilocksCubic113.n
          goldilocksCubic113.queries 128 ∧
      QueryFailsTarget (2 ^ 64) goldilocksCubic113.powThreshold
        goldilocksCubic113.agreementNumerator goldilocksCubic113.n
          (goldilocksCubic113.queries - 1) 128 := by
  norm_num [QueryMeetsTarget, QueryFailsTarget, goldilocksCubic113]

/-- The conservative cubic Goldilocks raw-payload lower bounds are 424 bytes against the nominal
profile and 168 bytes against its auxiliary zero-slack reference. Both charge the extra 24-byte
extension-field OOD value. -/
theorem goldilocksCubic113_payload_lower_bounds :
    conservativePayloadSaving goldilocksCubic113.nominalQueries goldilocksCubic113.queries
        (goldilocksCubic113.interleavingWidth * goldilocksCubic113.fieldBytes) 32
        ((goldilocksCubic113.initialOodSamples - 1) * goldilocksCubic113.extensionBytes) = 424 ∧
      conservativePayloadSaving goldilocksCubic113.zeroSlackQueryReference
        goldilocksCubic113.queries
        (goldilocksCubic113.interleavingWidth * goldilocksCubic113.fieldBytes) 32
        ((goldilocksCubic113.initialOodSamples - 1) * goldilocksCubic113.extensionBytes) = 168 := by
  norm_num [conservativePayloadSaving, fixedPayloadSaving, goldilocksCubic113]

end ArkLibExamples.ReedSolomon.ProveKit
