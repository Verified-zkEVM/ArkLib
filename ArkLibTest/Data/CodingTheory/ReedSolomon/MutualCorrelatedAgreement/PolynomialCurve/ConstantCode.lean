/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode

/-! # Checks for constant-code polynomial-curve agreement -/

namespace ReedSolomon

open Polynomial

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 3 ↪ F) (w : Fin 3 → Fin 3 → F) (z : F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain (powerBatchedWord w z) 1 2) ∧
      list.card ≤ 1 := by
  simpa using exists_constantCode_list domain w z 2 (by norm_num)

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 3 ↪ F) (w : Fin 2 → Fin 3 → F) :
    UniformExactPowerAgreement domain w 1 2 3 := by
  simpa using uniformExactPowerAgreement_constantCode_of_two_le domain w 2 (by norm_num)

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 3 ↪ F) (w : Fin 3 → Fin 3 → F) :
    UniformExactPowerAgreement domain w 1 1 6 := by
  simpa using uniformExactPowerAgreement_constantCode_one domain w

end ReedSolomon
