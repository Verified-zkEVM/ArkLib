/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.Fields
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Frozen ProveKit code-round parameters

This file records the Passport and cubic-Goldilocks schedules measured on 2026-09-07.  The only
changes from the preceding measured schedules are two Passport outer query counts and one lookup
query count.  Fold geometry, OOD counts, grinding thresholds, and both blinding protocols remain
fixed.

`coefficientsPerVector` is kept separate from `leafPayloadWidth`.  In particular, the initial
Passport internal commitment contains two vectors of 8192 coefficients, has fold width eight,
and opens leaves of width sixteen.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

/-- One committed Reed--Solomon code in a ProveKit transcript. -/
structure CodeRound where
  n : ℕ
  k : ℕ
  foldHeight : ℕ
  foldWidth : ℕ
  vectorCount : ℕ
  coefficientsPerVector : ℕ
  leafPayloadWidth : ℕ
  agreement : ℕ
  multiplicity : ℕ
  derivativeCap : ℕ
  jetDegree : ℕ
  baselineQueries : ℕ
  revisedQueries : ℕ
  oodSamples : ℕ
  powThreshold : ℕ
  exceptionalCount : ℕ
  listSize : ℕ
  deriving DecidableEq, Repr

/-- A fixed sequence of committed codes over one challenge field. -/
structure Schedule (rounds : ℕ) where
  row : Fin rounds → CodeRound
  fieldSize : ℕ
  security : ℕ
  nonceSpace : ℕ

/-- Structural facts independent of any semantic list-decoding theorem. -/
def CodeRound.StructurallyValid (r : CodeRound) (fieldSize : ℕ) : Prop :=
  0 < r.n ∧ 1 < r.k ∧ r.k < r.agreement ∧ r.agreement ≤ r.n ∧
  r.foldWidth = 2 ^ r.foldHeight ∧
  r.coefficientsPerVector = r.foldWidth * r.k ∧
  r.leafPayloadWidth = r.vectorCount * r.foldWidth ∧
  r.agreement ^ 2 < r.n * (r.k - 1) ∧
  r.n ≤ fieldSize ∧ r.jetDegree < fieldSize

/-- Every row of a schedule has the advertised geometry and is strictly beyond Johnson. -/
def Schedule.StructurallyValid {rounds : ℕ} (s : Schedule rounds) : Prop :=
  ∀ i, (s.row i).StructurallyValid s.fieldSize

/-- BN254 scalar-field cardinality used by Passport. -/
def bn254FieldSize : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Cubic-Goldilocks cardinality used by the lookup and its blinding proof. -/
def goldilocksCubicFieldSize : ℕ :=
  6277101731002175853884774869567645561244584131361410908161

/-- The inclusive grinding nonce space. -/
def nonceSpace : ℕ := 2 ^ 64

/-- The local per-phase security target used by the implementation generator. -/
def security : ℕ := 128

/-- The six unchanged inclusive PoW thresholds, indexed by WHIR round. -/
def powThreshold : Fin 6 → ℕ := ![
  18786624067678312, 55983906202016720, 77984534171686272,
  254057177368005792, 22342747603335828, 27157749354027232
]

@[simp] theorem powThreshold_zero : powThreshold 0 = 18786624067678312 := rfl
@[simp] theorem powThreshold_one : powThreshold 1 = 55983906202016720 := rfl
@[simp] theorem powThreshold_two : powThreshold 2 = 77984534171686272 := rfl
@[simp] theorem powThreshold_three : powThreshold 3 = 254057177368005792 := rfl
@[simp] theorem powThreshold_four : powThreshold 4 = 22342747603335828 := rfl
@[simp] theorem powThreshold_five : powThreshold 5 = 27157749354027232 := rfl

/-- Constructor for the common height-three, width-eight code geometry. -/
def codeRound (n k agreement multiplicity derivativeCap jetDegree baseline revised ood threshold
    exceptional list : ℕ) (vectors : ℕ := 1) : CodeRound where
  n := n
  k := k
  foldHeight := 3
  foldWidth := 8
  vectorCount := vectors
  coefficientsPerVector := 8 * k
  leafPayloadWidth := vectors * 8
  agreement := agreement
  multiplicity := multiplicity
  derivativeCap := derivativeCap
  jetDegree := jetDegree
  baselineQueries := baseline
  revisedQueries := revised
  oodSamples := ood
  powThreshold := threshold
  exceptionalCount := exceptional
  listSize := list

/-- Two Passport outer witnesses use this identical six-round schedule. -/
def passportOuterWitness : Schedule 6 where
  row := ![
    codeRound 262144 65536 123208 384 168 688 127 109 1 18786624067678312
      7182918955532022233234958 7283426240515,
    codeRound 131072 8192 29020 48 30 170 62 55 1 55983906202016720
      192919778745640861856 13248396686,
    codeRound 65536 1024 6906 40 34 310 41 37 1 77984534171686272
      34983022109232046957 7553849244,
    codeRound 32768 128 1782 12 12 168 31 29 1 254057177368005792
      2054108680967524 119648513,
    codeRound 16384 16 463 8 4 246 24 23 1 22342747603335828
      22036239199940 4684265,
    codeRound 8192 2 85 4 4 339 20 18 1 27157749354027232
      2312883154548 712536
  ]
  fieldSize := bn254FieldSize
  security := security
  nonceSpace := nonceSpace

/-- Each Passport outer witness has its own internal four-round zkWHIR proof. -/
def passportInternalZk : Schedule 4 where
  row := ![
    codeRound 4096 1024 1933 96 42 174 127 109 1 18786624067678312
      254185820640272772 1797616743 2,
    codeRound 2048 128 453 68 34 241 62 55 1 55983906202016720
      18195347444920928 381552558,
    codeRound 1024 16 107 16 16 114 41 37 1 77984534171686272
      80254527918922 8676197,
    codeRound 512 2 19 12 12 227 31 26 1 254057177368005792
      170140322205 993837
  ]
  fieldSize := bn254FieldSize
  security := security
  nonceSpace := nonceSpace

/-- Two lookup witnesses use this cubic-Goldilocks four-round schedule. -/
def goldilocksLookupWitness : Schedule 4 where
  row := ![
    codeRound 4096 1024 1933 96 42 174 127 109 2 18786624067678312
      254185820640272772 1797616743,
    codeRound 2048 128 453 38 23 133 62 55 1 55983906202016720
      165690490040644163 94687835,
    codeRound 1024 16 107 16 16 114 41 37 1 77984534171686272
      80254527918922 8676197,
    codeRound 512 2 19 12 12 227 31 26 1 254057177368005792
      170140322205 993837
  ]
  fieldSize := goldilocksCubicFieldSize
  security := security
  nonceSpace := nonceSpace

/-- Initial code of the independent lookup blinding proof. -/
def goldilocksLookupBlind : Schedule 1 where
  row := ![
    codeRound 32 8 14 64 28 116 127 99 1 18786624067678312
      702205349454 3609466
  ]
  fieldSize := goldilocksCubicFieldSize
  security := security
  nonceSpace := nonceSpace

/-- Fixed final tail of the lookup blinding proof.  Its query ratio is `21/80`; `n=16` and `k=1`
describe the final code rather than that query experiment's denominator. -/
structure BlindTail where
  n : ℕ
  k : ℕ
  coefficientsPerVector : ℕ
  queryAgreement : ℕ
  queryDomain : ℕ
  queries : ℕ
  oodSamples : ℕ
  powThreshold : ℕ
  listSize : ℕ
  deriving DecidableEq, Repr

/-- The tail is unchanged by the derivative-degree retuning. -/
def goldilocksLookupBlindTail : BlindTail where
  n := 16
  k := 1
  coefficientsPerVector := 8
  queryAgreement := 21
  queryDomain := 80
  queries := 62
  oodSamples := 1
  powThreshold := powThreshold 1
  listSize := 160

theorem passportOuterWitness_structurallyValid : passportOuterWitness.StructurallyValid := by
  intro i
  fin_cases i <;>
    norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid, passportOuterWitness,
      codeRound, powThreshold, bn254FieldSize]

theorem passportInternalZk_structurallyValid : passportInternalZk.StructurallyValid := by
  intro i
  fin_cases i <;>
    norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid, passportInternalZk,
      codeRound, powThreshold, bn254FieldSize]

theorem goldilocksLookupWitness_structurallyValid :
    goldilocksLookupWitness.StructurallyValid := by
  intro i
  fin_cases i <;>
    norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid, goldilocksLookupWitness,
      codeRound, powThreshold, goldilocksCubicFieldSize]

theorem goldilocksLookupBlind_structurallyValid : goldilocksLookupBlind.StructurallyValid := by
  intro i
  fin_cases i
  norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid, goldilocksLookupBlind,
    codeRound, powThreshold, goldilocksCubicFieldSize]

/-- The internal initial row distinguishes two coefficient vectors from one width-sixteen leaf. -/
theorem passportInternalZk_initial_geometry :
    (passportInternalZk.row 0).foldWidth = 8 ∧
    (passportInternalZk.row 0).vectorCount = 2 ∧
    (passportInternalZk.row 0).coefficientsPerVector = 8192 ∧
    (passportInternalZk.row 0).leafPayloadWidth = 16 := by
  norm_num [passportInternalZk, codeRound, powThreshold]

end ArkLibExamples.ReedSolomon.ProveKit
