/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhasePrelims
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Proposition4_21
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Incremental
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.FoldDistance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.BadBlocks
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness
import ArkLib.ToMathlib.MvPolynomial.Equiv

/-!
## Re-exported Binary Basefold Soundness tools

Public entry point for the split Binary Basefold soundness development.
This module packages the central bad-sumcheck probability estimate and re-exports the semantic
soundness submodules:
1. `Soundness.QueryPhasePrelims` for query-phase helper definitions and logical/monadic
   alignment
2. `Soundness.Lift`, `Soundness.Proposition4_21`, `Soundness.Incremental`, and
   `Soundness.FoldDistance` for the folding and distance lemmas behind archived-DP24
   Propositions/Lemmas 4.21-4.25, with the full incremental Proposition 4.21.2 argument now
   living in `Soundness.Incremental`
3. `Soundness.BadBlocks` and `Soundness.QueryPhaseSoundness` for bad-block analysis and the
   final query-phase soundness statement

Generic block-index and oracle-index arithmetic used across these files lives upstream in
`ArkLib.ProofSystem.Binius.BinaryBasefold.Basic`.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Statement numbering follows the archived revision of [DP24].
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
    let P := (h_i.val - h_star.val).toMvPolynomial (σ := Fin 1) 0
    have h_nonzero : P ≠ 0 := by
      rw [Polynomial.toMvPolynomial_ne_zero_iff, sub_ne_zero]
      exact fun h => h_ne (Subtype.eq h)
    have h_i_degree : h_i.val.degree ≤ 2 :=
      Polynomial.mem_degreeLE (f := h_i.val) (n := 2).mp (by simp only [SetLike.coe_mem])
    have h_star_degree : h_star.val.degree ≤ 2 :=
      Polynomial.mem_degreeLE (f := h_star.val) (n := 2).mp (by simp only [SetLike.coe_mem])
    have h_degree : P.totalDegree ≤ 2 := by
      apply (Polynomial.toMvPolynomial_totalDegree_le _ _).trans
      apply (Polynomial.natDegree_sub_le _ _).trans
      simp only [max_le_iff]
      constructor <;> apply Polynomial.natDegree_le_of_degree_le <;>
        first | exact h_i_degree | exact h_star_degree
    calc
      Pr_{ let r_i' ← $ᵖ L }[ h_i.val.eval r_i' = h_star.val.eval r_i' ] =
          Pr_{ let r_i' ← $ᵖ L }[ (h_i.val - h_star.val).eval r_i' = 0 ] := by
            apply Probability.Pr_congr
            simp [sub_eq_zero]
      _ = Pr_{ let r_i' ← $ᵖ L }[ MvPolynomial.eval (fun _ ↦ r_i') P = 0 ] := by
            apply Probability.Pr_congr
            intro r_i'
            simp [P, MvPolynomial.eval_toMvPolynomial]
      _ = Pr_{ let f ← $ᵖ (Fin 1 → L) }[ MvPolynomial.eval f P = 0 ] := by
            rw [← Probability.prob_uniform_singleton_finFun_eq]
            congr
            funext f
            simp [P, MvPolynomial.eval_toMvPolynomial]
      _ ≤ _ := Probability.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le P h_nonzero h_degree
  · simp only [h_ne, false_and, ENNReal.coe_ofNat]
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

end Binius.BinaryBasefold
