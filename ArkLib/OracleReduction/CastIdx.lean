/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Security.Guarded

/-!
# Casting oracle verifiers and reductions along an index equality

A protocol is often a family of oracle verifiers (or reductions) whose statement, oracle statement
and witness types are functions of an index, such as a round number `i : Fin (ℓ + 1)`. Composing
two members of such a family can produce an index, like `0 * ϑ` or `k * ϑ + ϑ`, that is equal but
not definitionally equal to the one a consumer expects. The casts here move a verifier or a
reduction along equalities `i₁ = i₂` of its input index and `j₁ = j₂` of its output index, in the
given type families, and the security notions move with it. Every transport is `subst` followed
by the hypothesis.

The protocol specification is untouched; casts along an equality of protocol specifications are in
`OracleReduction/Cast.lean`.

## Main definitions and statements

* `OracleVerifier.castIdx`, `OracleReduction.castIdx`: the casts. The verifier of a cast reduction
  is the cast verifier, by definition.
* `OracleVerifier.castIdx_rbrKnowledgeSoundnessWorstCase`: worst-case round-by-round knowledge
  soundness moves along the cast, at the relations of the target indices and the same error.
* `OracleReduction.castIdx_perfectCompleteness`: perfect completeness moves along the cast.
* `OracleVerifier.castIdxGuardedForm`: a guarded form of the verifier moves along the cast.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {pSpec : ProtocolSpec n}
  [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
  {I J : Type} {StmtIn : I → Type} {ιₛᵢ : I → Type} {OStmtIn : (i : I) → ιₛᵢ i → Type}
  [Oₛᵢ : ∀ i k, OracleInterface (OStmtIn i k)]
  {StmtOut : J → Type} {ιₛₒ : J → Type} {OStmtOut : (j : J) → ιₛₒ j → Type}
  [Oₛₒ : ∀ j k, OracleInterface (OStmtOut j k)]
  {WitIn : I → Type} {WitOut : J → Type}
  {i₁ i₂ : I} {j₁ j₂ : J}

namespace OracleVerifier

/-- Cast an oracle verifier along equalities of the indices of its input and output families. -/
def castIdx (hi : i₁ = i₂) (hj : j₁ = j₂)
    (V : OracleVerifier oSpec (StmtIn i₁) (OStmtIn i₁) (StmtOut j₁) (OStmtOut j₁) pSpec) :
    OracleVerifier oSpec (StmtIn i₂) (OStmtIn i₂) (StmtOut j₂) (OStmtOut j₂) pSpec :=
  hi ▸ hj ▸ V

/-- A guarded form of an oracle verifier's induced verifier moves along the cast. -/
def castIdxGuardedForm (hi : i₁ = i₂) (hj : j₁ = j₂)
    {V : OracleVerifier oSpec (StmtIn i₁) (OStmtIn i₁) (StmtOut j₁) (OStmtOut j₁) pSpec}
    (G : V.toVerifier.GuardedForm) : (V.castIdx hi hj).toVerifier.GuardedForm := by
  subst hi hj
  exact G

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Worst-case round-by-round knowledge soundness moves along an index cast, from the relations
at the source indices to those at the target indices, with the same error. -/
theorem castIdx_rbrKnowledgeSoundnessWorstCase
    {relIn : ∀ i, Set ((StmtIn i × ∀ k, OStmtIn i k) × WitIn i)}
    {relOut : ∀ j, Set ((StmtOut j × ∀ k, OStmtOut j k) × WitOut j)}
    (hi : i₁ = i₂) (hj : j₁ = j₂)
    {V : OracleVerifier oSpec (StmtIn i₁) (OStmtIn i₁) (StmtOut j₁) (OStmtOut j₁) pSpec}
    {ε : pSpec.ChallengeIdx → ℝ≥0}
    (h : V.toVerifier.rbrKnowledgeSoundnessWorstCase init impl (relIn i₁) (relOut j₁) ε) :
    (V.castIdx hi hj).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (relIn i₂) (relOut j₂) ε := by
  subst hi hj
  exact h

end OracleVerifier

namespace OracleReduction

/-- Cast an oracle reduction along equalities of the indices of its input and output families.
Its verifier is `OracleVerifier.castIdx` of the verifier. -/
def castIdx (hi : i₁ = i₂) (hj : j₁ = j₂)
    (R : OracleReduction oSpec (StmtIn i₁) (OStmtIn i₁) (WitIn i₁) (StmtOut j₁) (OStmtOut j₁)
      (WitOut j₁) pSpec) :
    OracleReduction oSpec (StmtIn i₂) (OStmtIn i₂) (WitIn i₂) (StmtOut j₂) (OStmtOut j₂)
      (WitOut j₂) pSpec where
  prover := hi ▸ hj ▸ R.prover
  verifier := R.verifier.castIdx hi hj

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Perfect completeness moves along an index cast, from the relations at the source indices to
those at the target indices. -/
theorem castIdx_perfectCompleteness
    {relIn : ∀ i, Set ((StmtIn i × ∀ k, OStmtIn i k) × WitIn i)}
    {relOut : ∀ j, Set ((StmtOut j × ∀ k, OStmtOut j k) × WitOut j)}
    (hi : i₁ = i₂) (hj : j₁ = j₂)
    {R : OracleReduction oSpec (StmtIn i₁) (OStmtIn i₁) (WitIn i₁) (StmtOut j₁) (OStmtOut j₁)
      (WitOut j₁) pSpec}
    (h : R.perfectCompleteness init impl (relIn i₁) (relOut j₁)) :
    (R.castIdx hi hj).perfectCompleteness init impl (relIn i₂) (relOut j₂) := by
  subst hi hj
  exact h

end OracleReduction
