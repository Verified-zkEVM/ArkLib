/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Dimension
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Interpolation
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.CertifiedRankBound

/-!
# Global interpolation acceptance case

One concrete point with zero center and received value admits a nonzero interpolant.
-/

open PolynomialDifferential ReedSolomon.HiddenDerivative

private theorem exactSpaceDimension :
    Module.finrank ℚ (exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num)) = 3 := by
  rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount ℚ (by norm_num)]
  decide

private theorem localRankAtZero :
    Module.finrank ℚ (LinearMap.range
      (exactLocalConstraintAt (R := ℚ) (D := 2) (A := 2) (M := 1) (W := 0)
        (d := 1) (by norm_num) 1 (0 : ℚ) (0 : ℚ))) ≤ 2 :=
  (finrank_exactLocalConstraintAt_le_certifiedEnlargedRankBound
    (d := 1) (D := 2) (A := 2) (m := 1) (M := 1) (W := 0)
    (by norm_num) (by norm_num) (0 : ℚ) (0 : ℚ)).trans_eq (by decide)

example : ∃ Q : DifferentialPolynomial ℚ 1, Q ≠ 0 ∧
    Q ∈ exactInterpolationSpace ℚ 2 2 1 1 1 0 (by norm_num) ∧
      ∀ _ : Fin 1, SatisfiesLocalConstraints 1 0 0 Q :=
  exists_nonzero_global_interpolant_of_uniform_local_rank_bound (by norm_num)
    (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 0) 2 (fun _ => localRankAtZero)
    (by rw [exactSpaceDimension]; decide)
