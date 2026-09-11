/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile
import ArkLibExamples.ReedSolomon.Fields
/-!
# Finite parameters for the LambdaVM CPU table

This module records the finite first-order certificates for the selected CPU row at
`32768` trace rows. The first profile certifies the degree-50 powers batching curve on the
full length-`65536` evaluation domain. The remaining eight profiles certify the binary folds,
from length `32768` through length `256`. At every fold, the dimension is half the current
length and the agreement is the ceiling of the initial agreement scaled to that length.

The two-anchor list profile is deliberately separate. Its dimension is `32771`, because
recovering a polynomial of degree at most `32770` requires Reed--Solomon dimension `32771`.
It is therefore not the dimension-`32768` initial powers profile.

All support dimensions, heights, column weights, splits, and exceptional ceilings were generated
by `scripts/tune_first_order_mca.py` and reproduced through
`scripts/check_lambda_table_scope.py` in the paper artifact repository. The proofs below ask Lean
to recompute the finite support and height conditions.
-/

namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU

open _root_.ReedSolomon.CurveProfile

/-- Number of rows in the selected CPU execution trace. -/
def traceRows : ℕ := 32768

/-- Length of the rate-one-half Reed--Solomon evaluation domain. -/
def length : ℕ := 65536

/-- Required agreement on the initial evaluation domain. -/
def agreement : ℕ := 45690

/-- Dimension of the initial polynomial before adding the two anchor degrees. -/
def initialDimension : ℕ := 32768

/-- Dimension used to list-decode degree-at-most-`traceRows + 2` anchored tuples. -/
def listDimension : ℕ := 32771

/-- Degree of the CPU powers-batching curve: 51 values use powers `0` through `50`. -/
def powersDegree : ℕ := 50

/-- Initial powers profile followed by the eight binary-fold profiles. -/
def profiles : Fin 9 → LineProfile := ![
  { n := 65536, k := 32768, agreement := 45690, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 50,
    supportDimension := 271682880, localRank := 4125,
    columnY₀Weight := 3580444920, height := 36670, heightSlots := 9959302447560 },
  { n := 32768, k := 16384, agreement := 22845, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 135847200, localRank := 4125,
    columnY₀Weight := 1790363640, height := 727, heightSlots := 97106397960 },
  { n := 16384, k := 8192, agreement := 11423, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 67935840, localRank := 4125,
    columnY₀Weight := 895451640, height := 703, heightSlots := 46931379720 },
  { n := 8192, k := 4096, agreement := 5712, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 33980160, localRank := 4125,
    columnY₀Weight := 447995640, height := 659, heightSlots := 21978909960 },
  { n := 4096, k := 2048, agreement := 2856, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 16995840, localRank := 4125,
    columnY₀Weight := 224139000, height := 622, heightSlots := 10364269320 },
  { n := 2048, k := 1024, agreement := 1428, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 8503680, localRank := 4125,
    columnY₀Weight := 112210680, height := 561, heightSlots := 4666857480 },
  { n := 1024, k := 512, agreement := 714, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 4257600, localRank := 4125,
    columnY₀Weight := 56246520, height := 470, heightSlots := 1949083080 },
  { n := 512, k := 256, agreement := 357, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 2134560, localRank := 4125,
    columnY₀Weight := 28264440, height := 357, heightSlots := 735908040 },
  { n := 256, k := 128, agreement := 179, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 1079520, localRank := 4125,
    columnY₀Weight := 14402040, height := 185, heightSlots := 186388680 }
]

/-- Splits minimizing the exact exceptional-fiber estimates for the nine curves. -/
def splits : Fin 9 → ℕ := ![32923, 16462, 8231, 4116, 2058, 1029, 514, 257, 128]

/-- Integer ceilings for the actual exceptional sets constructed from the nine profiles. -/
def exceptionalCounts : Fin 9 → ℕ := ![
  2083866315591056321, 10327375567345557, 2495641113148010,
  584404316685816, 137780487841264, 31012724900600,
  6471554467790, 1219691220099, 153308775293
]

/-- Sum of the eight fold exceptional ceilings. -/
def foldExceptionalCount : ℕ :=
  exceptionalCounts 1 + exceptionalCounts 2 + exceptionalCounts 3 + exceptionalCounts 4 +
    exceptionalCounts 5 + exceptionalCounts 6 + exceptionalCounts 7 + exceptionalCounts 8

/-- The generated fold ceilings sum to the paper artifact's fold numerator. -/
theorem foldExceptionalCount_eq : foldExceptionalCount = 13584058764384429 := by
  decide

/-- Initial powers ceiling plus all eight fold ceilings. -/
def totalExceptionalCount : ℕ := exceptionalCounts 0 + foldExceptionalCount

/-- Exact total of the initial and folding exceptional ceilings. -/
theorem totalExceptionalCount_eq : totalExceptionalCount = 2097450374355440750 := by
  decide

/-- Finite profile used for the two-anchor CPU candidate list. -/
def listProfile : LineProfile :=
  { n := 65536, k := 32771, agreement := 45690, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 271653540, localRank := 4125,
    columnY₀Weight := 3579696480, height := 749, heightSlots := 200160458520 }

/-- Split minimizing the exact scalar list expression. -/
def listSplit : ℕ := 32925

/-- Integer ceiling for every finite list at the two-anchor CPU parameters. -/
def listBound : ℕ := 113772416

/-- Cardinality of the cubic Goldilocks challenge field. -/
def fieldSize : ℕ := 6277101731002175853884774869567645561244584131361410908161

/-- The concrete challenge field has the recorded cardinality. -/
theorem fieldSize_eq : Fintype.card ConcreteFields.GoldilocksCubic = fieldSize := by
  rw [ConcreteFields.goldilocksCubic_card]
  rfl

/-- Every powers and fold row passes the complete polynomial-curve finite checks. -/
theorem profiles_verified (i : Fin 9) : (profiles i).CurveVerification := by
  fin_cases i <;> decide +kernel

/-- Every powers and fold row also passes the scalar degree-one finite checks. -/
theorem profiles_scalar_verified (i : Fin 9) : (profiles i).Verification := by
  fin_cases i <;> constructor <;> decide +kernel

/-- The distinct two-anchor list profile passes the complete scalar finite checks. -/
theorem listProfile_verified : listProfile.Verification := by
  constructor <;> decide +kernel

end ArkLibExamples.ReedSolomon.LambdaVM.CPU
