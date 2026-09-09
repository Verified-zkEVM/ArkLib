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
def agreement : ℕ := 45810

/-- Dimension of the initial polynomial before adding the two anchor degrees. -/
def initialDimension : ℕ := 32768

/-- Dimension used to list-decode degree-at-most-`traceRows + 2` anchored tuples. -/
def listDimension : ℕ := 32771

/-- Degree of the CPU powers-batching curve: 51 values use powers `0` through `50`. -/
def powersDegree : ℕ := 50

/-- Initial powers profile followed by the eight binary-fold profiles. -/
def profiles : Fin 9 → LineProfile := ![
  { n := 65536, k := 32768, agreement := 45810, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 50,
    supportDimension := 92023540, localRank := 1400,
    columnY₀Weight := 829800580, height := 42164, heightSlots := 3879342763520 },
  { n := 32768, k := 16384, agreement := 22905, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 46013660, localRank := 1400,
    columnY₀Weight := 414932140, height := 832, heightSlots := 37914446640 },
  { n := 16384, k := 8192, agreement := 11453, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 23010876, localRank := 1400,
    columnY₀Weight := 207527180, height := 787, heightSlots := 17925043108 },
  { n := 8192, k := 4096, agreement := 5727, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 11509484, localRank := 1400,
    columnY₀Weight := 103824700, height := 710, heightSlots := 8079418424 },
  { n := 4096, k := 2048, agreement := 2864, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 5758788, localRank := 1400,
    columnY₀Weight := 51973460, height := 595, heightSlots := 3380264188 },
  { n := 2048, k := 1024, agreement := 1432, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 2881284, localRank := 1400,
    columnY₀Weight := 26018580, height := 518, heightSlots := 1469367816 },
  { n := 1024, k := 512, agreement := 716, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 1442532, localRank := 1400,
    columnY₀Weight := 13041140, height := 413, heightSlots := 584167108 },
  { n := 512, k := 256, agreement := 358, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 723156, localRank := 1400,
    columnY₀Weight := 6552420, height := 296, heightSlots := 208224912 },
  { n := 256, k := 128, agreement := 179, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 363468, localRank := 1400,
    columnY₀Weight := 3308060, height := 193, heightSlots := 67204732 }
]

/-- Splits minimizing the exact exceptional-fiber estimates for the nine curves. -/
def splits : Fin 9 → ℕ := ![32917, 16458, 8230, 4115, 2058, 1029, 514, 257, 128]

/-- Integer ceilings for the actual exceptional sets constructed from the nine profiles. -/
def exceptionalCounts : Fin 9 → ℕ := ![
  3395110257406885729, 16746255074995314, 3958679485474707,
  892165202095663, 186608919184478, 40516184299310,
  8035980474225, 1424226698158, 227108936244
]

/-- Sum of the eight fold exceptional ceilings. -/
def foldExceptionalCount : ℕ :=
  exceptionalCounts 1 + exceptionalCounts 2 + exceptionalCounts 3 + exceptionalCounts 4 +
    exceptionalCounts 5 + exceptionalCounts 6 + exceptionalCounts 7 + exceptionalCounts 8

/-- The generated fold ceilings sum to the paper artifact's fold numerator. -/
theorem foldExceptionalCount_eq : foldExceptionalCount = 21833912182158099 := by
  decide

/-- Initial powers ceiling plus all eight fold ceilings. -/
def totalExceptionalCount : ℕ := exceptionalCounts 0 + foldExceptionalCount

/-- Exact total of the initial and folding exceptional ceilings. -/
theorem totalExceptionalCount_eq : totalExceptionalCount = 3416944169589043828 := by
  decide

/-- Finite profile used for the two-anchor CPU candidate list. -/
def listProfile : LineProfile :=
  { n := 65536, k := 32771, agreement := 45810, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 92013880, localRank := 1400,
    columnY₀Weight := 829631110, height := 873, heightSlots := 79590500010 }

/-- Split minimizing the exact scalar list expression. -/
def listSplit : ℕ := 32917

/-- Integer ceiling for every finite list at the two-anchor CPU parameters. -/
def listBound : ℕ := 165670441

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
