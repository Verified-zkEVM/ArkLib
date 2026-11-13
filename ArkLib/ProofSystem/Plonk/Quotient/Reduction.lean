/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Batch.Reduction
public import ArkLib.ProofSystem.Plonk.Quotient.Data
public import ArkLib.OracleReduction.LiftContext.Purity

/-! # Plonk quotient, evaluation and terminal check

The finite-domain quotient zero test is lifted into the retained Plonk context. The quotient
message precedes its evaluation challenge. Its terminal guard checks the multiplication identity,
including at points in the row domain, and returns the retained context only on acceptance.
-/

@[expose] public section

namespace Plonk.Quotient

open OracleSpec OracleComp OracleQuery ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

local instance : ∀ i, OracleInterface.{0, 0} (QuotientZeroTest.OStmtOut i) :=
  fun i => nomatch i

variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}
  (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 2 ≤ n)

/-- The row-domain vanishing polynomial is evaluated by powering. -/
def domain : QuotientZeroTest.Domain F where
  points := Batch.points ω hω
  evalNodal z := z ^ n - 1
  evalNodal_eq z := by
    rw [nodal_eq ω hω (by omega)]
    simp

/-- Quotient first, then one uniform evaluation challenge. -/
abbrev pSpec := QuotientZeroTest.pSpec F (domain ω hω hn) (GrandProduct.residualDegree n)

/-- The input is the vanishing claim on the retained batch polynomial. -/
def relIn := Batch.relOut ω hω

/-- An accepted output retains all earlier oracles, without further obligations. -/
def relOut : Set (((F × F) × ∀ i, Batch.OStmtOut F n i) × Unit) := Set.univ

/-- Project the batch oracle and preserve the complete earlier oracle context on output. -/
def statementLens : OracleStatement.ExecutableLens (F × F) (F × F) Unit Unit
    (Batch.OStmtOut F n) (Batch.OStmtOut F n)
    (QuotientZeroTest.OStmtIn F (GrandProduct.residualDegree n)) QuotientZeroTest.OStmtOut where
  projStmt _ := ()
  materializeInput _ f _ := f (.inr ())
  simulateInput _ q := OracleSpec.query (spec := [Batch.OStmtOut F n]ₒ) ⟨.inr (), q.2⟩
  simulateInput_eq _ _ _ := rfl
  liftStmt s _ := s
  materializeOutput f _ := f
  simulateOutput q := liftM (OracleSpec.query (spec := [Batch.OStmtOut F n]ₒ) q)
  simulateOutput_eq _ _ _ := rfl

/-- Both inner and outer stages have unique witnesses. -/
def contextLens : OracleContext.ExecutableLens (F × F) (F × F) Unit Unit
    (Batch.OStmtOut F n) (Batch.OStmtOut F n)
    (QuotientZeroTest.OStmtIn F (GrandProduct.residualDegree n)) QuotientZeroTest.OStmtOut
    Unit Unit Unit Unit where
  stmt := statementLens (F := F) (n := n)
  wit := ⟨fun _ => (), fun _ _ => ()⟩

/-- Backward extraction preserves the unique witness. -/
def inverseWitness : Witness.InvLens ((F × F) × ∀ i, Batch.OStmtOut F n i)
    Unit Unit Unit Unit := ⟨fun _ => (), fun _ _ => ()⟩

variable {ι : Type} (oSpec : OracleSpec ι)

/-- The lifted output forwards every earlier oracle by its input embedding. -/
def liftOutput :
    (QuotientZeroTest.oracleVerifier F (domain ω hω hn) (GrandProduct.residualDegree n)
      oSpec).LiftContextOutput (statementLens (F := F) (n := n)) where
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq _ := rfl
    outputInterface_heq _ := HEq.rfl }
  materialize_eq _ _ _ _ := rfl

/-- The actual evaluation-only quotient verifier in the retained Plonk context. -/
def oracleVerifier :=
  (QuotientZeroTest.oracleVerifier F (domain ω hω hn) (GrandProduct.residualDegree n)
    oSpec).liftContext (statementLens (F := F) (n := n)) (liftOutput ω hω hn oSpec)

/-- The honest quotient prover and its terminal evaluation guard. -/
def oracleReduction :=
  (QuotientZeroTest.oracleReduction F (domain ω hω hn) (GrandProduct.residualDegree n)
    oSpec).liftContext (contextLens (F := F) (n := n)) (liftOutput ω hω hn oSpec)

instance : (oracleReduction ω hω hn oSpec).prover.OutputIsPure := by
  change (Prover.liftContext (contextLens (F := F) (n := n)).toLens.toContext
    (QuotientZeroTest.oracleProver F (domain ω hω hn) (GrandProduct.residualDegree n)
      oSpec)).OutputIsPure
  infer_instance

/-- The transported guard checks the same multiplication identity as the generic zero test. -/
def guardedForm : (oracleVerifier ω hω hn oSpec).toVerifier.GuardedForm :=
  OracleVerifier.liftContextGuardedForm (statementLens (F := F) (n := n))
    (QuotientZeroTest.oracleVerifier F (domain ω hω hn) (GrandProduct.residualDegree n) oSpec)
    (liftOutput ω hω hn oSpec)
    (QuotientZeroTest.guardedForm F (domain ω hω hn) (GrandProduct.residualDegree n) oSpec)

/-- Materialization checks the quotient identity and returns the exact retained input on success. -/
theorem oracleVerifier_toVerifier (stmt : (F × F) × ∀ i, Batch.OStmtOut F n i)
    (tr : (pSpec ω hω hn).FullTranscript) :
    (oracleVerifier ω hω hn oSpec).toVerifier.verify stmt tr =
      let z : F := tr 1
      if FiniteDomainQuotient.eval (stmt.2 (.inr ())) z =
          FiniteDomainQuotient.eval (tr 0) z * (z ^ n - 1)
      then pure stmt else failure := by
  rw [(guardedForm ω hω hn oSpec).verify_eq]
  change (if decide (FiniteDomainQuotient.eval (stmt.2 (.inr ())) (tr 1) =
      FiniteDomainQuotient.eval (tr 0) (tr 1) * (domain ω hω hn).evalNodal (tr 1)) = true
    then pure stmt else failure) = _
  dsimp only [domain]
  split_ifs with h₁ h₂ h₂
  · simp_all
  · exact (h₂ (of_decide_eq_true h₁)).elim
  · exact (h₁ (decide_eq_true h₂)).elim
  · simp_all

variable [SampleableType F]

instance lensComplete :
    (contextLens (F := F) (n := n)).toLens.toContext.IsComplete
      (relIn ω hω)
      (QuotientZeroTest.relIn F (domain ω hω hn) (GrandProduct.residualDegree n))
      (relOut (F := F) (n := n)) QuotientZeroTest.relOut
      ((QuotientZeroTest.oracleReduction F (domain ω hω hn) (GrandProduct.residualDegree n)
        oSpec).toReduction.compatContext (contextLens (F := F) (n := n)).toLens.toContext) where
  proj_complete _ _ h := (Batch.vanishes_iff_zeroOn ω hω _).mp h
  lift_complete _ _ _ _ _ _ _ := trivial

instance lensKnowledgeSound : Extractor.Lens.IsKnowledgeSound
    (relIn ω hω)
    (QuotientZeroTest.relIn F (domain ω hω hn) (GrandProduct.residualDegree n))
    (relOut (F := F) (n := n)) QuotientZeroTest.relOut
    ((QuotientZeroTest.oracleVerifier F (domain ω hω hn) (GrandProduct.residualDegree n)
      oSpec).toVerifier.compatStatement (statementLens (F := F) (n := n)).toLens)
    (fun _ _ => True)
    ⟨(statementLens (F := F) (n := n)).toLens, inverseWitness (F := F) (n := n)⟩ where
  proj_knowledgeSound _ _ _ _ _ := Or.inl trivial
  lift_knowledgeSound _ _ _ _ h := (Batch.vanishes_iff_zeroOn ω hω _).mpr h

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Completeness of the actual lifted quotient prover and terminal guard. -/
theorem oracleReduction_perfectCompleteness :
    (oracleReduction ω hω hn oSpec).perfectCompleteness init impl
      (relIn ω hω) (relOut (F := F) (n := n)) :=
  OracleReduction.liftContext_perfectCompleteness
    (QuotientZeroTest.oracleReduction_perfectCompleteness F (domain ω hω hn)
      (GrandProduct.residualDegree n) oSpec init impl)

/-- The named extractor is the transported generic zero-test extractor. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    ((F × F) × ∀ i, Batch.OStmtOut F n i) Unit Unit (pSpec ω hω hn)
    (fun _ => Unit × Unit) :=
  (QuotientZeroTest.rbrExtractor F (domain ω hω hn) (GrandProduct.residualDegree n)
    oSpec).liftContext
    ⟨(statementLens (F := F) (n := n)).toLens, inverseWitness (F := F) (n := n)⟩

/-- The named fixed-prefix knowledge state is transported by the executable lens. -/
def knowledgeStateFunction :=
  (QuotientZeroTest.oracleVerifier F (domain ω hω hn) (GrandProduct.residualDegree n)
    oSpec).liftContextKnowledgeStateFunction
    (outerRelIn := relIn ω hω) (outerRelOut := relOut (F := F) (n := n))
    (witLens := inverseWitness (F := F) (n := n)) (liftOutput ω hω hn oSpec)
    (QuotientZeroTest.rbrExtractor F (domain ω hω hn) (GrandProduct.residualDegree n) oSpec)
    (QuotientZeroTest.knowledgeStateFunction F (domain ω hω hn)
      (GrandProduct.residualDegree n) oSpec init impl)

variable [Fintype F]

/-- The quotient/evaluation/terminal stage has exactly `4(n - 1) / |F|` fixed-prefix error. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleVerifier ω hω hn oSpec).toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn ω hω) (relOut (F := F) (n := n)) (fun _ => Unit × Unit)
      (rbrExtractor ω hω hn oSpec) (knowledgeStateFunction ω hω hn oSpec init impl)
      (fun _ => (GrandProduct.residualDegree n : ℝ≥0) / Fintype.card F) := by
  apply OracleVerifier.liftContext_rbrKnowledgeSoundnessWith
  apply QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundnessWith
  change (Batch.points ω hω).card ≤ GrandProduct.residualDegree n
  rw [points_card]
  unfold GrandProduct.residualDegree
  omega

end Plonk.Quotient
