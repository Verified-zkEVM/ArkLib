/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.ZeroCheck.Relation
public import ArkLib.ProofSystem.Spartan.Terminal
public import ArkLib.ProofSystem.Component.RandomEvaluation

/-!
# Spartan's zero-check challenge

Spartan's zero-check is random evaluation (`RandomQuery` comparing a polynomial with `0`, see
`RandomEvaluation`) applied to the residual interpolation, which is multilinear in the `ℓ_m` row
variables. The challenge reduction
retains the public input, matrices, and attached witness, samples a uniform row point, and never
evaluates the residual interpolation.
-/

@[expose] public section

namespace Spartan.ZeroCheck

open OracleComp Realization
open scoped NNReal

section Construction

variable {R : Type} [CommRing R] (pp : PublicParams) {ι : Type} (oSpec : OracleSpec ι)

/-- Spartan's first challenge, retaining the attached witness and all matrix oracles. -/
abbrev oracleReduction :=
  RandomEvaluation.oracleReduction oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

/-- The first challenge has an always-true guard. -/
abbrev guardedForm :=
  RandomEvaluation.guardedForm oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

/-- The backward extractor preserves the unique witness. -/
abbrev rbrExtractor :=
  RandomEvaluation.rbrExtractor oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
    (OracleStatement (R := R) pp)

/-- The R1CS input relation is the random-evaluation input relation for the residual
interpolation. -/
theorem relIn_eq : relIn (R := R) pp =
    RandomEvaluation.relIn R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
      (OracleStatement (R := R) pp) (polynomial pp) := by
  ext s
  exact (polynomial_zero_iff pp s.1.1 s.1.2).symm

/-- The output relation is the random-evaluation output relation for the residual
interpolation. -/
theorem relOut_eq : relOut (R := R) pp =
    RandomEvaluation.relOut R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
      (OracleStatement (R := R) pp) (polynomial pp) := by
  ext s
  exact (RandomEvaluation.mem_relOut_iff R pp.ℓ_m _ _ (polynomial pp)).symm

end Construction

variable {R : Type} [Field R] [Fintype R] [SampleableType R]
    (pp : PublicParams) {ι : Type} (oSpec : OracleSpec ι)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

omit [Fintype R] in
/-- The zero-check challenge is perfectly complete for R1CS satisfaction. -/
theorem challenge_perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  rw [relIn_eq, relOut_eq]
  exact RandomEvaluation.oracleReduction_completeness oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)

/-- The first challenge's semantic knowledge predicate. Its polynomial view uses nonconstructive
coefficient equality and is used only in security statements. -/
noncomputable def knowledgeStateFunction :
    (oracleReduction (R := R) pp oSpec).verifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) (rbrExtractor pp oSpec) where
  toFun := (RandomEvaluation.knowledgeStateFunction oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)).toFun
  toFun_empty := fun stmt _ h => (polynomial_zero_iff pp stmt.1 stmt.2).1 h
  toFun_next := (RandomEvaluation.knowledgeStateFunction oSpec R pp.ℓ_m
    (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)).toFun_next
  toFun_full := fun stmt tr wit h =>
    (RandomEvaluation.knowledgeStateFunction oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS)
      (OracleStatement (R := R) pp) (polynomial pp) (init := init) (impl := impl)).toFun_full
      stmt tr wit (by rwa [relOut_eq] at h)

/-- Named-extractor, fixed-prefix RBR knowledge soundness with error `ℓ_m / |R|`. -/
theorem challenge_rbrKnowledgeSoundnessWith :
    (oracleReduction (R := R) pp oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn pp) (relOut pp) (fun _ => Unit) (rbrExtractor pp oSpec)
      (knowledgeStateFunction pp oSpec) (fun _ => (pp.ℓ_m : ℝ≥0) / Fintype.card R) := by
  -- The contract reads the knowledge state only through `toFun`, which is the generic one.
  intro stmtIn i tr
  exact RandomEvaluation.oracleVerifier_rbrKnowledgeSoundnessWith_of_degreeOf_le_one
    oSpec R pp.ℓ_m (R1CS.Statement R pp.toSizeR1CS) (OracleStatement (R := R) pp) (polynomial pp)
    (polynomial_degree_le_one pp) (init := init) (impl := impl) stmtIn i tr

/-- Fixed-prefix RBR knowledge soundness with error `ℓ_m / |R|`. -/
theorem challenge_rbrKnowledgeSoundness :
    (oracleReduction (R := R) pp oSpec).verifier.toVerifier.rbrKnowledgeSoundness
      init impl (relIn pp) (relOut pp) (fun _ => (pp.ℓ_m : ℝ≥0) / Fintype.card R) :=
  ⟨fun _ => Unit, rbrExtractor pp oSpec, knowledgeStateFunction pp oSpec,
    challenge_rbrKnowledgeSoundnessWith pp oSpec⟩

end Spartan.ZeroCheck
