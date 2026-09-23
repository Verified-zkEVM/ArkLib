/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget

open ReedSolomon

open scoped BigOperators

example : ordinaryFrobeniusMixedDegree 1 1 2 2 ≤ 2 * 2 + ordinaryPsi 1 4 :=
  ordinaryFrobeniusMixedDegree_le_unified 1 1 2 2
