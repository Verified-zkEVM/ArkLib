/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_uniqueDecodingRegime {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementAffineLines
  intro u hprob
  have hprob' :
      Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, ReedSolomon.code domain deg) ≤ δ]
        > (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    simpa [errorBound_eq_n_div_q_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hδ] using
      hprob
  have hS : (RS_goodCoeffs (deg := deg) (domain := domain) u δ).card > Fintype.card ι :=
    card_RS_goodCoeffs_gt_of_prob_gt_n_div_q (deg := deg) (domain := domain) (δ := δ) u hprob'
  exact RS_jointAgreement_of_goodCoeffs_card_gt (deg := deg) (domain := domain) (δ := δ) hδ u hS

end CoreResults

end ProximityGap
