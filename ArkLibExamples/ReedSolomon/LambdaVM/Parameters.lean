/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.CurveProfile
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

open CurveProfile

/-- Number of rows in the selected CPU execution trace. -/
def traceRows : ℕ := 32768

/-- Length of the rate-one-half Reed--Solomon evaluation domain. -/
def length : ℕ := 65536

/-- Required agreement on the initial evaluation domain. -/
def agreement : ℕ := 45880

/-- Dimension of the initial polynomial before adding the two anchor degrees. -/
def initialDimension : ℕ := 32768

/-- Dimension used to list-decode degree-at-most-`traceRows + 2` anchored tuples. -/
def listDimension : ℕ := 32771

/-- Degree of the CPU powers-batching curve: 51 values use powers `0` through `50`. -/
def powersDegree : ℕ := 50

/-- Initial powers profile followed by the eight binary-fold profiles. -/
def profiles : Fin 9 → LineProfile := ![
  { n := 65536, k := 32768, agreement := 45880, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 50,
    supportDimension := 92325380, localRank := 1400,
    columnY₀Weight := 833896980, height := 20461, heightSlots := 1888328028580 },
  { n := 32768, k := 16384, agreement := 22940, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 46164580, localRank := 1400,
    columnY₀Weight := 416980340, height := 406, heightSlots := 18372003720 },
  { n := 16384, k := 8192, agreement := 11470, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 23084180, localRank := 1400,
    columnY₀Weight := 208522020, height := 401, heightSlots := 9071318340 },
  { n := 8192, k := 4096, agreement := 5735, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 11543980, localRank := 1400,
    columnY₀Weight := 104292860, height := 392, heightSlots := 4432491280 },
  { n := 4096, k := 2048, agreement := 2868, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 5776036, localRank := 1400,
    columnY₀Weight := 52207540, height := 355, heightSlots := 2004061276 },
  { n := 2048, k := 1024, agreement := 1434, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 2889908, localRank := 1400,
    columnY₀Weight := 26135620, height := 327, heightSlots := 921754204 },
  { n := 1024, k := 512, agreement := 717, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 1446844, localRank := 1400,
    columnY₀Weight := 13099660, height := 283, heightSlots := 397804036 },
  { n := 512, k := 256, agreement := 359, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 727468, localRank := 1400,
    columnY₀Weight := 6610940, height := 183, heightSlots := 127243172 },
  { n := 256, k := 128, agreement := 180, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 367780, localRank := 1400,
    columnY₀Weight := 3366580, height := 111, heightSlots := 37824780 }
]

/-- Splits minimizing the exact exceptional-fiber estimates for the nine curves. -/
def splits : Fin 9 → ℕ := ![32981, 16490, 8245, 4122, 2061, 1031, 515, 258, 129]

/-- Integer ceilings for the actual exceptional sets constructed from the nine profiles. -/
def exceptionalCounts : Fin 9 → ℕ := ![
  7282126800045324606, 36118739117241122, 8915521376023260,
  2177373653279381, 491977429097369, 112986942868727,
  24308713579560, 3860143755620, 563115442509
]

/-- Sum of the eight fold exceptional ceilings. -/
def foldExceptionalCount : ℕ :=
  exceptionalCounts 1 + exceptionalCounts 2 + exceptionalCounts 3 + exceptionalCounts 4 +
    exceptionalCounts 5 + exceptionalCounts 6 + exceptionalCounts 7 + exceptionalCounts 8

/-- The generated fold ceilings sum to the paper artifact's fold numerator. -/
theorem foldExceptionalCount_eq : foldExceptionalCount = 47845330491287548 := by
  decide

/-- Initial powers ceiling plus all eight fold ceilings. -/
def totalExceptionalCount : ℕ := exceptionalCounts 0 + foldExceptionalCount

/-- Exact total of the initial and folding exceptional ceilings. -/
theorem totalExceptionalCount_eq : totalExceptionalCount = 7329972130536612154 := by
  decide

/-- Finite profile used for the two-anchor CPU candidate list. -/
def listProfile : LineProfile :=
  { n := 65536, k := 32771, agreement := 45880, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 92315720, localRank := 1400,
    columnY₀Weight := 833727510, height := 415, heightSlots := 37569612010 }

/-- Split minimizing the exact scalar list expression. -/
def listSplit : ℕ := 32982

/-- Integer ceiling for every finite list at the two-anchor CPU parameters. -/
def listBound : ℕ := 719093721

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
