/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Proposition4_20
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.FoldDistance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness

/-!
## Re-exported Binary Basefold Soundness tools

Public entry point for the split Binary Basefold soundness development.
This module packages the central bad-sumcheck probability estimate and re-exports the semantic
soundness submodules:
1. `Soundness.QueryPhasePrelims` for query-phase helper definitions and logical/monadic
   alignment
2. `Soundness.Lift`, `Soundness.Proposition4_20`, `Soundness.Incremental`, and
   `Soundness.FoldDistance` for the folding and distance lemmas behind Lemmas 4.20-4.24, with
   the full Proposition 4.20.2 incremental argument now living in `Soundness.Incremental`
3. `Soundness.BadBlocks` and `Soundness.QueryPhaseSoundness` for bad-block analysis and the
   final query-phase soundness statement

Generic block-index and oracle-index arithmetic used across these files lives upstream in
`ArkLib.ProofSystem.Binius.BinaryBasefold.Basic`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

namespace Binius.BinaryBasefold

open scoped NNReal ProbabilityTheory Polynomial

variable {L : Type} [Field L] [Fintype L]

/-- **Probability bound for the bad sumcheck event** (Schwartz-Zippel).
When the verifier challenge `r_i'` is uniform over `L`, the probability that two distinct
degree-≤2 round polynomials agree at `r_i'` is at most `2 / |L|`. -/
lemma probability_bound_badSumcheckEventProp (h_i h_star : L⦃≤ 2⦄[X]) :
    Pr_{ let r_i' ← $ᵖ L }[ badSumcheckEventProp r_i' h_i h_star ] ≤
      (2 : ℝ≥0) / Fintype.card L := by
  classical
  unfold badSumcheckEventProp
  by_cases h_ne : h_i ≠ h_star
  · simp only [ne_eq, h_ne, not_false_eq_true, true_and, ENNReal.coe_ofNat]
    exact prob_poly_agreement_degree_two (p := h_i) (q := h_star) (h_ne := h_ne)
  · simp only [h_ne, false_and, ENNReal.coe_ofNat]
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

end Binius.BinaryBasefold
