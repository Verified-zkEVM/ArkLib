/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.ZeroCheckRelation
public import ArkLib.ProofSystem.Spartan.Terminal
public import ArkLib.ProofSystem.Component.ZeroCheck

/-!
# Spartan's zero-check challenge

The challenge reduction retains the public input, matrices, and attached witness, samples a
uniform row point, and never evaluates the residual interpolation.
-/

@[expose] public section

namespace Spartan.ZeroCheck

open OracleComp Realization
open scoped NNReal

section Construction

variable {R : Type} [CommRing R] (pp : PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Spartan's first challenge, retaining the attached witness and all matrix oracles. -/
abbrev oracleReduction :=
  _root_.ZeroCheck.oracleReduction oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

/-- The first challenge has an always-true guard. -/
abbrev guardedForm :=
  _root_.ZeroCheck.guardedForm oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

/-- The backward extractor preserves the unique witness. -/
abbrev rbrExtractor :=
  _root_.ZeroCheck.rbrExtractor oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

end Construction

variable {R : Type} [Field R] [Fintype R] [SampleableType R]
    (pp : PublicParams) {ι : Type} (oSpec : OracleSpec ι)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [Fintype R] in
/-- The zero-check challenge is perfectly complete for R1CS satisfaction. -/
theorem challenge_perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  rw [relIn_eq, relOut_eq]
  exact _root_.ZeroCheck.challenge_perfectCompleteness oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)

/-- The first challenge's semantic knowledge predicate. Its polynomial view uses nonconstructive
coefficient equality and is used only in security statements. -/
noncomputable def knowledgeStateFunction :
    (oracleReduction (R := R) pp oSpec).verifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) (rbrExtractor pp oSpec) where
  toFun := (_root_.ZeroCheck.knowledgeStateFunction oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)).toFun
  toFun_empty := fun stmt _ h => (polynomial_zero_iff pp stmt.1 stmt.2).1 h
  toFun_next := (_root_.ZeroCheck.knowledgeStateFunction oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)).toFun_next
  toFun_full := (_root_.ZeroCheck.knowledgeStateFunction oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)).toFun_full

/-- Named-extractor, fixed-prefix RBR knowledge soundness with error `ℓ_m / |R|`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCaseWith :
    (oracleReduction (R := R) pp oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (relIn pp) (relOut pp) (fun _ => Unit) (rbrExtractor pp oSpec)
      (knowledgeStateFunction pp oSpec) (fun _ => (pp.ℓ_m : ℝ≥0) / Fintype.card R) := by
  exact _root_.ZeroCheck.challenge_rbrKnowledgeSoundnessWorstCaseWith oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)
    (polynomial_degree_le_one pp) (init := init) (impl := impl)

/-- Worst-case, fixed-prefix RBR knowledge soundness with error `ℓ_m / |R|`. -/
theorem challenge_rbrKnowledgeSoundnessWorstCase :
    (oracleReduction (R := R) pp oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl (relIn pp) (relOut pp) (fun _ => (pp.ℓ_m : ℝ≥0) / Fintype.card R) :=
  ⟨fun _ => Unit, rbrExtractor pp oSpec, knowledgeStateFunction pp oSpec,
    challenge_rbrKnowledgeSoundnessWorstCaseWith pp oSpec⟩

end Spartan.ZeroCheck
