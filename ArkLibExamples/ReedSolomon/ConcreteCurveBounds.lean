/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ConcreteCurves
import ArkLibExamples.ReedSolomon.CurveCertificate
import ArkLibExamples.ReedSolomon.LambdaVMTables
import ArkLibExamples.ReedSolomon.ProveKit
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderCurveBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderCurveStageSum
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator

/-!
# Exact exceptional-envelope arithmetic for the concrete curve profiles

The interpolation profiles in `ConcreteCurves` fix the actual equation heights, including
batching degree. Here we evaluate the sharper joint-and-fiber expression at each row's
chosen split threshold. Rational comparisons are checked by the Lean kernel.

These are arithmetic lemmas for the geometric theorem: their conclusions concern the
explicit envelope, not an assumed or independently defined exceptional set.
-/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ConcreteCurveBounds

open CurveProfile ConcreteCurves CurveCertificate

/-! ## Revised ProveKit cubic-Goldilocks row -/

/-- The retained-pair split selected for the revised cubic-Goldilocks row. -/
def proveKitGoldilocksCubicSplit : ℕ := 268399

/-- The shifted finite constructor's challenge height for the revised row. -/
def proveKitGoldilocksCubicHeight : ℕ := 339

/-- The exact common Taylor exponent is `2k - 3 = 524285`. -/
theorem proveKitGoldilocksCubic_taylorExponent :
    2 * ProveKit.goldilocksCubic113.k - 3 = 524285 := by
  norm_num [ProveKit.goldilocksCubic113]

/-- This exponent is sufficient at every derivative order, including the order-one stages. -/
theorem proveKitGoldilocksCubic_taylorExponent_sufficient (r : ℕ) :
    TaylorExponentSufficient r ProveKit.goldilocksCubic113.k 524285 := by
  simpa [ProveKit.goldilocksCubic113] using
    taylorExponentSufficient_two_mul_sub_three r (by norm_num : 2 ≤ 262144)

/-- The revised `λ₁η` envelope at `τ = 2k - 3` lies below the integer ceiling used by
the concrete Goldilocks exceptional-set theorem. -/
theorem proveKitGoldilocksCubic_envelope_le :
    firstOrderCurveBound 1048576 262144 262144 proveKitGoldilocksCubicSplit 508263
        30 7 1 proveKitGoldilocksCubicHeight 524285
          (firstOrderCurveDirectRatio 1048576 262144 508263) ≤
      ProveKit.goldilocksCubic113.exceptionalCount := by
  decide +kernel

/-- Recorded split for each lambdaVM curve profile. -/
def lambdaVMSplit : Fin 35 → ℕ := ![
  2049,
  1024,
  512,
  256,
  128,
  4100,
  2050,
  1025,
  512,
  256,
  128,
  8203,
  4102,
  2050,
  1025,
  512,
  256,
  128,
  16414,
  8206,
  4103,
  2051,
  1025,
  512,
  256,
  128,
  32857,
  16428,
  8214,
  4107,
  2053,
  1026,
  513,
  256,
  128
]

/-- Recorded budget for each lambdaVM curve profile. -/
def lambdaVMBudget : Fin 35 → ℕ := ![
  2838667918225456682,
  26152476131756207,
  4825119969938378,
  570057069639270,
  94988329827464,
  3190530058695456919,
  38969228939296809,
  7272733081218728,
  1203674200402655,
  178769630382866,
  24476673421706,
  4491022007152636908,
  60081858838203217,
  13846956267307992,
  2991478345699776,
  474053555586347,
  87886938824701,
  10415917589511,
  6731596329089244959,
  97224282257790975,
  22586352670121224,
  5297390895244013,
  1178015415342033,
  241083051044712,
  33783144798047,
  5984232404552,
  7121894453107095641,
  104153502459085303,
  25452398473245907,
  6227432721928317,
  1431419079833979,
  332364147255836,
  63717950128569,
  13042232149662,
  1827481659385
]

/-- Every selected split lies in the geometric range. -/
theorem lambdaVM_split_admissible (i : Fin 35) :
    (lambdaVM i).k ≤ lambdaVMSplit i ∧ lambdaVMSplit i ≤ (lambdaVM i).agreement ∧
      (lambdaVM i).agreement ≤ (lambdaVM i).n := by
  fin_cases i <;> decide

/-- The exact rational envelope is below its displayed integer ceiling. -/
theorem lambdaVM_envelope_le (i : Fin 35) :
    envelope (lambdaVM i) (lambdaVMSplit i) ≤ lambdaVMBudget i := by
  fin_cases i <;> decide +kernel

/-- Sum the initial curve and every fold belonging to one table configuration. -/
def lambdaVMTotalBudget : Fin 5 → ℕ := ![
  lambdaVMBudget 0 + lambdaVMBudget 1 + lambdaVMBudget 2 + lambdaVMBudget 3 + lambdaVMBudget 4,
  lambdaVMBudget 5 + lambdaVMBudget 6 + lambdaVMBudget 7 + lambdaVMBudget 8 +
    lambdaVMBudget 9 + lambdaVMBudget 10,
  lambdaVMBudget 11 + lambdaVMBudget 12 + lambdaVMBudget 13 + lambdaVMBudget 14 +
    lambdaVMBudget 15 + lambdaVMBudget 16 + lambdaVMBudget 17,
  lambdaVMBudget 18 + lambdaVMBudget 19 + lambdaVMBudget 20 + lambdaVMBudget 21 +
    lambdaVMBudget 22 + lambdaVMBudget 23 + lambdaVMBudget 24 + lambdaVMBudget 25,
  lambdaVMBudget 26 + lambdaVMBudget 27 + lambdaVMBudget 28 + lambdaVMBudget 29 +
    lambdaVMBudget 30 + lambdaVMBudget 31 + lambdaVMBudget 32 + lambdaVMBudget 33 +
    lambdaVMBudget 34
]

/-- All five total curve budgets equal the integers used in the local error calculation. -/
theorem lambdaVM_total_budget_eq (i : Fin 5) :
    lambdaVMTotalBudget i = (LambdaVMTables.tables i).exceptionalBudget := by
  fin_cases i <;> decide

end ArkLibExamples.ReedSolomon.ConcreteCurveBounds
