/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Evaluation.Relation
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Sending Spartan's row evaluations

The prover sends three field elements. The verifier checks their equality-weighted residual and
retains the original matrix and witness oracles. True output claims recover the first sumcheck's
terminal relation, giving zero knowledge error without a challenge.
-/

@[expose] public section

namespace Spartan.SendEvaluations

open OracleComp OracleSpec ProtocolSpec Realization

variable {R : Type} [CommRing R] [DecidableEq R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)
  [∀ i, OracleInterface (OracleStatement (R := R) pp i)]

/-- One message containing the three row evaluations. -/
abbrev pSpec (R : Type) : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[R1CS.MatrixIdx → R]⟩

instance : ∀ i, OracleInterface ((pSpec R).Message i) := fun _ => default

instance : IsEmpty (pSpec R).ChallengeIdx := ⟨fun ⟨0, h⟩ => nomatch h⟩

/-- Retain exactly the original matrix and witness oracles. -/
def outputEmbedding : OracleOutputEmbedding (OracleStatement (R := R) pp) (pSpec R).Message
    (OracleStatement (R := R) pp) where
  embed := Function.Embedding.inl
  hEq _ := rfl
  outputInterface_heq _ := HEq.rfl

/-- The verifier reads the three scalar claims and checks their weighted residual. -/
def oracleVerifier : OracleVerifier oSpec (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp)
    ((R1CS.MatrixIdx → R) × Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) (pSpec R) where
  verify stmt _ := do
    let v : R1CS.MatrixIdx → R ← query (spec := [(pSpec R).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard (Evaluation.check pp stmt v)
    return (v, stmt)
  outputOracle := .inl (outputEmbedding pp)

/-- The honest prover computes the row evaluations from its retained input tables. -/
def oracleProver : OracleProver oSpec (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit
    ((R1CS.MatrixIdx → R) × Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (pSpec R) where
  PrvState _ := Evaluation.Statement (R := R) pp × (∀ i, OracleStatement (R := R) pp i)
  input := Prod.fst
  sendMessage | ⟨0, _⟩ => fun s => pure (Evaluation.values pp s.1 s.2, s)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output s := pure (((Evaluation.values pp s.1 s.2, s.1), s.2), ())

/-- The guarded send-evaluations reduction. -/
def oracleReduction : OracleReduction oSpec (Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit
    ((R1CS.MatrixIdx → R) × Evaluation.Statement (R := R) pp)
    (OracleStatement (R := R) pp) Unit (pSpec R) where
  prover := oracleProver pp oSpec
  verifier := oracleVerifier pp oSpec

/-- The semantic first sumcheck terminal relation. -/
def relIn : Set (((Evaluation.Statement (R := R) pp) ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | Evaluation.inputRelation pp s.1.1 s.1.2}

/-- The three claims refer to the same original oracle tables. -/
def relOut : Set ((((R1CS.MatrixIdx → R) × Evaluation.Statement (R := R) pp) ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | Evaluation.outputRelation pp s.1.1.2 s.1.2 s.1.1.1}

@[simp]
theorem materializeOutput (chals : (pSpec R).Challenges)
    (oracles : ∀ i, OracleStatement (R := R) pp i) (msgs : (pSpec R).Messages) :
    (oracleVerifier pp oSpec).materializeOutput chals oracles msgs = oracles := by
  rfl

/-- The verifier accepts precisely when the sent values pass the scalar equation. -/
theorem verifier_run (s : Evaluation.Statement (R := R) pp ×
    (∀ i, OracleStatement (R := R) pp i)) (tr : (pSpec R).FullTranscript) :
    (oracleVerifier pp oSpec).toVerifier.run s tr =
      if Evaluation.check pp s.1 (tr 0) then pure (((tr 0), s.1), s.2) else failure := by
  exact OracleVerifier.toVerifier_verify_of_query_guard (oracleVerifier pp oSpec)
    ⟨⟨0, rfl⟩, ()⟩ (fun stmt v _ => Evaluation.check pp stmt v)
    (hcheck := fun stmt v _ => inferInstanceAs
      (Decidable (eqWeight stmt.τ stmt.r_x * (v .A * v .B - v .C) = stmt.e)))
    (fun stmt v _ => (v, stmt)) (fun _ _ => rfl) s.1 s.2 tr

/-- The deterministic guard and output of the underlying verifier. -/
def guardedForm : (oracleVerifier (R := R) pp oSpec).toVerifier.GuardedForm where
  check s tr := decide (Evaluation.check pp s.1 (tr 0))
  out s tr := ((tr 0, s.1), s.2)
  verify_eq s tr := by
    simpa only [decide_eq_true_eq] using verifier_run pp oSpec s tr

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The input relation is the knowledge invariant both before and after the prover message. -/
def knowledgeStateFunction :
    (oracleVerifier (R := R) pp oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) Extractor.RoundByRound.unit where
  toFun _ s _ _ := Evaluation.inputRelation pp s.1 s.2
  toFun_empty _ _ h := h
  toFun_next _ _ _ _ _ _ h := h
  toFun_full s tr _ h := by
    obtain ⟨hc, hv⟩ := (guardedForm pp oSpec).check_and_of_prEvent_pos h
    let v := ((guardedForm pp oSpec).out s tr).1.1
    have hcheck : Evaluation.check pp s.1 v := of_decide_eq_true hc
    exact Evaluation.inputRelation_of_check pp s.1 s.2 v hcheck hv

/-- Fixed-prefix knowledge soundness with the named unit extractor and zero error. -/
theorem verifier_rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn pp) (relOut pp) (fun _ => Unit) Extractor.RoundByRound.unit
      (knowledgeStateFunction pp oSpec init impl) (fun _ => 0) := by
  intro _ i
  exact isEmptyElim i

/-- Sending and checking row evaluations has zero fixed-prefix knowledge error. -/
theorem verifier_rbrKnowledgeSoundness :
    (oracleVerifier (R := R) pp oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn pp) (relOut pp) (fun _ => 0) :=
  ⟨_, _, knowledgeStateFunction pp oSpec init impl,
    verifier_rbrKnowledgeSoundnessWith pp oSpec init impl⟩

/-- Honest row evaluations pass the scalar check and establish all three output claims. -/
theorem reduction_perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro s w h x hx
  let v := Evaluation.values pp s.1 s.2
  let tr : (pSpec R).FullTranscript := fun | ⟨0, _⟩ => v
  have hp : (oracleProver pp oSpec).run s w = pure (tr, (((v, s.1), s.2), ())) := by
    change (pure _ : OracleComp _ _) = pure _
    congr 1
    dsimp
    congr 1
    funext i
    fin_cases i
    rfl
  have hv : (oracleVerifier pp oSpec).toVerifier.run s tr = pure ((v, s.1), s.2) := by
    rw [verifier_run]
    exact ite_eq_left ((Evaluation.check_values_iff pp s.1 s.2).2 h)
  have hrun : ((oracleReduction pp oSpec).toReduction.run s w).run =
      pure (some ((tr, (((v, s.1), s.2), ())), ((v, s.1), s.2))) := by
    rw [Reduction.run_run_eq_bind]
    change (do
      let p ← (oracleProver pp oSpec).run s w
      let out ← liftComp ((oracleVerifier pp oSpec).toVerifier.run s p.1).run _
      pure (out.map (fun v => (p, v)))) = _
    rw [hp, pure_bind, hv]
    rfl
  rw [hrun, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨_, rfl, Evaluation.values_correct pp s.1 s.2, rfl⟩

end Spartan.SendEvaluations
