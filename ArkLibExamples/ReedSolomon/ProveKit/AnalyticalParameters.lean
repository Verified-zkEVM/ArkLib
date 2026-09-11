/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit.Parameters
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Analytical ProveKit retuning

This file records two further parameter changes obtained by exact finite search.  They are
analytical configurations: the measured schedules in `Parameters.lean` remain unchanged.

The sharp first-order list and MCA estimates may use different interpolation supports at the
same `(n, k, agreement)`.  `CodeRound` has one support slot, so an analytical schedule stores
the MCA support that produces its exceptional count, while the list support is recorded by the
separate functions below.
-/

namespace ArkLibExamples.ReedSolomon.ProveKit

/-- A derivative-weighted first-order interpolation support `(m, M, mu)`. -/
structure FirstOrderSupport where
  multiplicity : ℕ
  derivativeCap : ℕ
  jetDegree : ℕ
  deriving DecidableEq, Repr

/-- Extract the single support stored in a measured code-round row. -/
def CodeRound.firstOrderSupport (r : CodeRound) : FirstOrderSupport where
  multiplicity := r.multiplicity
  derivativeCap := r.derivativeCap
  jetDegree := r.jetDegree

/-- MCA supports for the analytical Passport outer schedule. -/
def passportOuterAnalyticalMcaSupport : Fin 6 → FirstOrderSupport := ![
  (passportOuterWitness.row 0).firstOrderSupport,
  (passportOuterWitness.row 1).firstOrderSupport,
  (passportOuterWitness.row 2).firstOrderSupport,
  (passportOuterWitness.row 3).firstOrderSupport,
  { multiplicity := 60, derivativeCap := 60, jetDegree := 1568 },
  (passportOuterWitness.row 5).firstOrderSupport
]

/-- List supports for the analytical Passport outer schedule.  Only the fifth row differs from
the MCA support. -/
def passportOuterAnalyticalListSupport : Fin 6 → FirstOrderSupport := ![
  (passportOuterWitness.row 0).firstOrderSupport,
  (passportOuterWitness.row 1).firstOrderSupport,
  (passportOuterWitness.row 2).firstOrderSupport,
  (passportOuterWitness.row 3).firstOrderSupport,
  { multiplicity := 56, derivativeCap := 53, jetDegree := 1391 },
  (passportOuterWitness.row 5).firstOrderSupport
]

/-- The further analytical Passport outer schedule.  It changes only the fifth row: its
agreement is 394, its query count is 22, and it uses separate sharp MCA/list certificates. -/
def passportOuterAnalytical : Schedule 6 where
  row := ![
    passportOuterWitness.row 0,
    passportOuterWitness.row 1,
    passportOuterWitness.row 2,
    passportOuterWitness.row 3,
    codeRound 16384 16 394 60 60 1568 24 22 1 22342747603335828
      40320140359804306 180429296,
    passportOuterWitness.row 5
  ]
  fieldSize := bn254FieldSize
  security := security
  nonceSpace := nonceSpace

/-- MCA supports for the analytical cubic-Goldilocks lookup schedule. -/
def goldilocksLookupAnalyticalMcaSupport : Fin 4 → FirstOrderSupport := ![
  { multiplicity := 96, derivativeCap := 42, jetDegree := 174 },
  (goldilocksLookupWitness.row 1).firstOrderSupport,
  (goldilocksLookupWitness.row 2).firstOrderSupport,
  (goldilocksLookupWitness.row 3).firstOrderSupport
]

/-- List supports for the analytical cubic-Goldilocks lookup schedule.  Only the first row uses
a support different from the MCA calculation. -/
def goldilocksLookupAnalyticalListSupport : Fin 4 → FirstOrderSupport := ![
  { multiplicity := 63, derivativeCap := 28, jetDegree := 118 },
  (goldilocksLookupWitness.row 1).firstOrderSupport,
  (goldilocksLookupWitness.row 2).firstOrderSupport,
  (goldilocksLookupWitness.row 3).firstOrderSupport
]

/-- The further analytical Goldilocks lookup schedule. It retains the measured query counts and
changes the first row's list size, exceptional count, and OOD count. Its stored support remains
the MCA support. -/
def goldilocksLookupAnalytical : Schedule 4 where
  row := ![
    codeRound 4096 1024 1933 96 42 174 127 109 1 18786624067678312
      12566666451549204 39721253,
    goldilocksLookupWitness.row 1,
    goldilocksLookupWitness.row 2,
    goldilocksLookupWitness.row 3
  ]
  fieldSize := goldilocksCubicFieldSize
  security := security
  nonceSpace := nonceSpace

theorem passportOuterAnalytical_structurallyValid :
    passportOuterAnalytical.StructurallyValid := by
  intro i
  fin_cases i
  · change (passportOuterWitness.row 0).StructurallyValid bn254FieldSize
    exact passportOuterWitness_structurallyValid 0
  · change (passportOuterWitness.row 1).StructurallyValid bn254FieldSize
    exact passportOuterWitness_structurallyValid 1
  · change (passportOuterWitness.row 2).StructurallyValid bn254FieldSize
    exact passportOuterWitness_structurallyValid 2
  · change (passportOuterWitness.row 3).StructurallyValid bn254FieldSize
    exact passportOuterWitness_structurallyValid 3
  · norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid,
      passportOuterAnalytical, passportOuterWitness, codeRound, powThreshold, bn254FieldSize]
  · change (passportOuterWitness.row 5).StructurallyValid bn254FieldSize
    exact passportOuterWitness_structurallyValid 5

theorem goldilocksLookupAnalytical_structurallyValid :
    goldilocksLookupAnalytical.StructurallyValid := by
  intro i
  fin_cases i
  · norm_num [Schedule.StructurallyValid, CodeRound.StructurallyValid,
      goldilocksLookupAnalytical, goldilocksLookupWitness, codeRound, powThreshold,
      goldilocksCubicFieldSize]
  · change (goldilocksLookupWitness.row 1).StructurallyValid goldilocksCubicFieldSize
    exact goldilocksLookupWitness_structurallyValid 1
  · change (goldilocksLookupWitness.row 2).StructurallyValid goldilocksCubicFieldSize
    exact goldilocksLookupWitness_structurallyValid 2
  · change (goldilocksLookupWitness.row 3).StructurallyValid goldilocksCubicFieldSize
    exact goldilocksLookupWitness_structurallyValid 3

/-- The analytical Passport query schedule is `[109, 55, 37, 29, 22, 18]`. -/
theorem passportOuterAnalytical_querySchedule :
    (fun i ↦ (passportOuterAnalytical.row i).revisedQueries) = ![109, 55, 37, 29, 22, 18] := by
  funext i
  fin_cases i <;> rfl

/-- Goldilocks retains the measured witness query schedule `[109, 55, 37, 26]`. -/
theorem goldilocksLookupAnalytical_querySchedule :
    (fun i ↦ (goldilocksLookupAnalytical.row i).revisedQueries) = ![109, 55, 37, 26] := by
  funext i
  fin_cases i <;> rfl

/-- Every Passport row other than the fifth is definitionally inherited from the measured
schedule. -/
theorem passportOuterAnalytical_unchanged_of_ne_four
    (i : Fin 6) (hi : i ≠ 4) :
    passportOuterAnalytical.row i = passportOuterWitness.row i := by
  fin_cases i <;> simp_all [passportOuterAnalytical]

/-- Every Goldilocks row after the first is definitionally inherited from the measured schedule. -/
theorem goldilocksLookupAnalytical_unchanged_of_ne_zero
    (i : Fin 4) (hi : i ≠ 0) :
    goldilocksLookupAnalytical.row i = goldilocksLookupWitness.row i := by
  fin_cases i <;> simp_all [goldilocksLookupAnalytical]

/-- The fifth Passport row uses distinct MCA and list supports. -/
theorem passportOuterAnalytical_supports :
    passportOuterAnalyticalMcaSupport 4 =
        { multiplicity := 60, derivativeCap := 60, jetDegree := 1568 } ∧
      passportOuterAnalyticalListSupport 4 =
        { multiplicity := 56, derivativeCap := 53, jetDegree := 1391 } := by
  constructor <;> rfl

/-- The first Goldilocks row uses distinct MCA and list supports. -/
theorem goldilocksLookupAnalytical_supports :
    goldilocksLookupAnalyticalMcaSupport 0 =
        { multiplicity := 96, derivativeCap := 42, jetDegree := 174 } ∧
      goldilocksLookupAnalyticalListSupport 0 =
        { multiplicity := 63, derivativeCap := 28, jetDegree := 118 } := by
  constructor <;> rfl

end ArkLibExamples.ReedSolomon.ProveKit
