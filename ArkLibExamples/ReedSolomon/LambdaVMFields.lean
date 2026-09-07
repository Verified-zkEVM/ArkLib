/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.Fields
import ArkLibExamples.ReedSolomon.LambdaVMInterleaving
import ArkLibExamples.ReedSolomon.LambdaVMTables

/-!
# Concrete cubic Goldilocks consequences for LambdaVM

The field-uniform LambdaVM theorem requires a characteristic large enough for its Taylor and
separant arguments. The paper's probability arithmetic separately records the cardinality of the
cubic Goldilocks challenge field. This module instantiates both facts on the canonical field model
from `Fields`, so neither property remains a supplied numeric premise.

## Reading the statements

The five profiles correspond to trace lengths `2048`, `4096`, `8192`, `16384`, and `32768`.
Their Reed--Solomon domains have twice those lengths, and undoing the DEEP quotient gives degree
bound `T + 1`. `lambda_le` works for every interleaving width. Its width-eighteen corollary is the
original LambdaVM tuple represented by the degree-17 batching curve.

Each conclusion uses the `listBudget` in the matching `LambdaVMTables` row. That value is proved
equal to the sharp bound derived from the first-order interpolation certificate; no list cap is
an assumption. The cardinality lemma identifies LambdaVM’s numeric denominator with the
actual cardinality of the cubic Goldilocks model.

## Mathematical scope

These theorems bound the complete common-agreement list through `Code.Lambda`, uniformly over all
received interleaved words. They do not derive the powers exceptional counts, authenticate query
responses, or compose the complete protocol error. A caller still supplies an embedding of the
evaluation domain into the concrete field.
-/

open Code
open ReedSolomon ReedSolomon.ListDecoding

namespace ArkLibExamples.ReedSolomon.LambdaVMFields

open ConcreteFields LambdaVMLists

/-- The canonical cubic Goldilocks field satisfies the characteristic condition in every row. -/
theorem characteristic_admissible (i : Fin 5) :
    ringChar GoldilocksCubic = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]

/-- The complete interleaved list over cubic Goldilocks obeys the matching table budget, for
every width and each of the five table sizes. -/
theorem lambda_le (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin width)
          (ReedSolomon.code domain (profiles i).k :
            Set (Fin (profiles i).n → GoldilocksCubic)))
        (capacityRadius (LambdaVMInterleaving.gap i) (profiles i).n (profiles i).k) ≤
      ((LambdaVMTables.tables i).listBudget : ℕ∞) := by
  rw [LambdaVMTables.list_budget_eq]
  exact LambdaVMInterleaving.lambda_le i width domain (characteristic_admissible i)

/-- The actual width-eighteen LambdaVM tuple has the same sharp bound in all five rows. -/
theorem widthEighteen_lambda_le (i : Fin 5)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 18)
          (ReedSolomon.code domain (profiles i).k :
            Set (Fin (profiles i).n → GoldilocksCubic)))
        (capacityRadius (LambdaVMInterleaving.gap i) (profiles i).n (profiles i).k) ≤
      ((LambdaVMTables.tables i).listBudget : ℕ∞) :=
  lambda_le i 18 domain

/-- LambdaVM's numeric challenge cardinality is the cardinality of the concrete field model. -/
theorem goldilocksCubic_card_eq_lambdaVM :
    Fintype.card GoldilocksCubic = LambdaVM.challengeCardinality := by
  rw [goldilocksCubic_card]
  norm_num [Goldilocks.fieldSize, LambdaVM.challengeCardinality]

end ArkLibExamples.ReedSolomon.LambdaVMFields
