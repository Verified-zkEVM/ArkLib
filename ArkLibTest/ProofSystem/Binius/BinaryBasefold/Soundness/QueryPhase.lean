/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.QueryPhaseSoundness

/-!
# The acceptance bound of one query repetition

`prob_logicalCheckSingleRepetition_le` bounds the probability that one query repetition accepts
against a noncompliant oracle, with no block bad event, by `1/2 + 1/(2 · 2^𝓡)`. This test

* checks that the bound is not trivial: it is at most `3/4` for every rate `𝓡 ≥ 1`, so the
  query error `(1/2 + 1/(2 · 2^𝓡))^γ` is at most `(3/4)^γ` and below `1` for `γ ≥ 1`;
* pins the axioms of the bound, of the folded-distance lemma ([DP24] Lemma 4.25) and of the
  rejection lemma ([DP24] Lemma 4.26).

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

open OracleSpec OracleComp ProtocolSpec AdditiveNTT Binius.BinaryBasefold
open scoped NNReal ENNReal ProbabilityTheory

namespace ArkLibTest.Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

/-- The single-repetition bound of the query phase is at most `3/4` for every rate `𝓡 ≥ 1`. -/
theorem queryRbrKnowledgeError_singleRepetition_le_three_quarters :
    QueryPhase.queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡) ≤ 3 / 4 := by
  have h2 : (2 : ℝ≥0) ≤ 2 ^ 𝓡 := by
    simpa using pow_le_pow_right₀ (a := (2 : ℝ≥0)) one_le_two
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne 𝓡))
  have h4 : (1 : ℝ≥0) / (2 * 2 ^ 𝓡) ≤ 1 / 4 := by
    gcongr
    calc (4 : ℝ≥0) = 2 * 2 := by norm_num
      _ ≤ 2 * 2 ^ 𝓡 := by gcongr
  calc QueryPhase.queryRbrKnowledgeErrorSingleRepetition (𝓡 := 𝓡)
      = 1 / 2 + 1 / (2 * 2 ^ 𝓡) := rfl
    _ ≤ 1 / 2 + 1 / 4 := by gcongr
    _ = 3 / 4 := by norm_num

omit [DecidableEq 𝔽q] [Fact (Fintype.card 𝔽q = 2)] [Fact (β 0 = 1)] [NeZero ℓ] in
/-- The query error of `γ ≥ 1` repetitions is below `1`. -/
theorem queryRbrKnowledgeError_lt_one {γ : ℕ} (hγ : γ ≠ 0)
    (i : (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) :
    QueryPhase.queryRbrKnowledgeError 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i < 1 :=
  pow_lt_one₀ zero_le ((queryRbrKnowledgeError_singleRepetition_le_three_quarters).trans_lt
    (by norm_num)) hγ

/--
info: 'Binius.BinaryBasefold.prob_logicalCheckSingleRepetition_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prob_logicalCheckSingleRepetition_le

/--
info: 'Binius.BinaryBasefold.not_pairUniqueDecodingClose_iteratedFold_of_not_isCompliant' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_pairUniqueDecodingClose_iteratedFold_of_not_isCompliant

/--
info: 'Binius.BinaryBasefold.not_logicalCheckSingleRepetition_of_mem_disagreementSet' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms not_logicalCheckSingleRepetition_of_mem_disagreementSet

/--
info: 'ArkLibTest.Binius.BinaryBasefold.queryRbrKnowledgeError_lt_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms queryRbrKnowledgeError_lt_one

end ArkLibTest.Binius.BinaryBasefold
