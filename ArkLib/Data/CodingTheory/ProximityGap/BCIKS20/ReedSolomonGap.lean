/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound

namespace ProximityGap

open NNReal Finset Function Code
open scoped BigOperators LinearCode

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Theorem 1.2 (Proximity Gaps for Reed-Solomon codes) in [BCIKS20].
Let `C` be a collection of affine spaces. Then `C` displays a `(δ, ε)`-proximity gap with respect to
a Reed-Solomon code, where `(δ, ε)` are the proximity and error parameters defined up to the
Johnson bound. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
    (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0}
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C)
      δ
      (errorBound δ deg domain) := by
  sorry

end CoreResults

end ProximityGap
