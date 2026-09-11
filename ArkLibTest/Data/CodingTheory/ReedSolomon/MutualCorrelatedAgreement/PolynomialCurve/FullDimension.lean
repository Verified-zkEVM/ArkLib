/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullDimension

/-! # Checks for full-dimension polynomial-curve agreement -/

namespace ReedSolomon

open Polynomial

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 2 ↪ F) (w : Fin 3 → Fin 2 → F) :
    UniformExactPowerAgreement domain w 2 2 0 := by
  exact uniformExactPowerAgreement_fullDimension 2 2 domain w

end ReedSolomon
