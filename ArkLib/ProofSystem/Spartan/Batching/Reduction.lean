/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Batching.Relation
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# Spartan's independent batching challenge

The verifier samples one vector of three independent coefficients and computes the second
sumcheck's claimed sum. It retains every original oracle and makes no oracle queries.
-/

@[expose] public section

namespace Spartan.Batching

open OracleComp OracleSpec ProtocolSpec Realization
open scoped NNReal ENNReal

variable {R : Type} [CommRing R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)
  [∀ i, OracleInterface (OracleStatement (R := R) pp i)]

/-- One challenge containing three independent coefficients. -/
abbrev pSpec (R : Type) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[R1CS.MatrixIdx → R]⟩

instance : VerifierOnly (pSpec R) where
  verifier_first' := by simp

/-- The prover receives the coefficients and computes the same public batched claim. -/
def oracleProver : OracleProver oSpec (InputStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit
    (Statement (R := R) pp) (OracleStatement (R := R) pp) Unit (pSpec R) where
  PrvState
  | 0 => InputStatement (R := R) pp × (∀ i, OracleStatement (R := R) pp i)
  | 1 => Statement (R := R) pp × (∀ i, OracleStatement (R := R) pp i)
  input := Prod.fst
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun s => pure fun ρ => (batch pp s.1 ρ, s.2)
  output s := pure (s, ())

instance : (oracleProver (R := R) pp oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- The verifier forms the claimed sum and retains the original oracle family. -/
def oracleVerifier : OracleVerifier oSpec (InputStatement (R := R) pp)
    (OracleStatement (R := R) pp)
    (Statement (R := R) pp) (OracleStatement (R := R) pp) (pSpec R) where
  verify s challenges := pure (batch pp s (challenges ⟨0, rfl⟩))
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq _ := rfl
    outputInterface_heq _ := HEq.rfl }

/-- The independent batching reduction. -/
def oracleReduction : OracleReduction oSpec (InputStatement (R := R) pp)
    (OracleStatement (R := R) pp) Unit
    (Statement (R := R) pp) (OracleStatement (R := R) pp) Unit (pSpec R) where
  prover := oracleProver pp oSpec
  verifier := oracleVerifier pp oSpec

/-- All three input row claims are true. -/
def relIn : Set ((InputStatement (R := R) pp ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | Evaluation.outputRelation pp s.1.1.2 s.1.2 s.1.1.1}

/-- The second sumcheck's initial claim holds for the retained original tables. -/
def relOut : Set ((Statement (R := R) pp ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | outputRelation pp s.1.1 s.1.2}

@[simp]
theorem materializeOutput (challenges : (pSpec R).Challenges)
    (oracles : ∀ i, OracleStatement (R := R) pp i) (messages : (pSpec R).Messages) :
    (oracleVerifier pp oSpec).materializeOutput challenges oracles messages = oracles := rfl

/-- The underlying verifier always returns the computed batch and unchanged oracle tables. -/
theorem verifier_run (s : InputStatement (R := R) pp ×
    (∀ i, OracleStatement (R := R) pp i)) (tr : (pSpec R).FullTranscript) :
    (oracleVerifier pp oSpec).toVerifier.run s tr = pure (batch pp s.1 (tr 0), s.2) := rfl

/-- Batching has an always-true guard. -/
def guardedForm : (oracleVerifier (R := R) pp oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out s tr := (batch pp s.1 (tr 0), s.2)
  verify_eq _ _ := rfl

/-- The backward extractor retains the unique witness. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (InputStatement (R := R) pp × (∀ i, OracleStatement (R := R) pp i))
    Unit Unit (pSpec R) (fun _ => Unit) where
  extractIn _ w := w
  extractMid _ _ _ _ := ()
  extractOut _ _ _ := ()

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Knowledge is truth of all row claims before sampling and of the batched claim afterwards. -/
def knowledgeStateFunction :
    (oracleVerifier (R := R) pp oSpec).toVerifier.KnowledgeStateFunction init impl
      (relIn pp) (relOut pp) (rbrExtractor pp oSpec) where
  toFun
  | 0 => fun s _ _ => Evaluation.outputRelation pp s.1.2 s.2 s.1.1
  | 1 => fun s tr _ => outputRelation pp (batch pp s.1 (tr ⟨0, by decide⟩)) s.2
  toFun_empty _ _ h := h
  toFun_next | 0 => fun hDir _ _ _ => by simp at hDir
  toFun_full s tr _ h := ((guardedForm pp oSpec).check_and_of_prEvent_pos h).2

variable [SampleableType R]

/-- True row claims establish the second sumcheck claim for every coefficient vector. -/
theorem batch_perfectCompleteness :
    (oracleReduction (R := R) pp oSpec).perfectCompleteness init impl (relIn pp) (relOut pp) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨s, oracles⟩ wit hs x hx
  simp only [OracleReduction.toReduction, oracleReduction, Reduction.run,
    Prover.run_of_verifier_first, oracleProver, oracleVerifier,
    OracleVerifier.toVerifier] at hx
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun y =>
    (pure (some y) : OracleComp _ _) from rfl] at hx
  simp only [Verifier.run, OracleComp.liftComp_pure, ← OracleComp.liftComp_eq_liftM,
    pure_bind, OptionT.run_mk] at hx
  obtain ⟨qSupport, hqSupport, hx⟩ := hx
  obtain ⟨q, rfl⟩ := hqSupport
  simp only [Challenge, ChallengeIdx, FullTranscript.challenges, Option.getM,
    Fin.isValue, Fin.vcons_of_one, MessageIdx, Message] at hx
  subst x
  exact ⟨_, rfl, batchedClaim_complete pp s oracles _ hs, rfl⟩

end Spartan.Batching

namespace Spartan.Batching

open OracleComp OracleSpec ProtocolSpec Realization
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [SampleableType F] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι)
  [∀ i, OracleInterface (OracleStatement (R := F) pp i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Fixed-prefix knowledge soundness for the named extractor, with error exactly `1 / |F|`
for the independent coefficient challenge. -/
theorem batch_rbrKnowledgeSoundnessWith :
    (oracleVerifier (R := F) pp oSpec).toVerifier.rbrKnowledgeSoundnessWith init impl
      (relIn pp) (relOut pp) (fun _ => Unit) (rbrExtractor pp oSpec)
      (knowledgeStateFunction pp oSpec init impl) (fun _ => (1 : ℝ≥0) / Fintype.card F) := by
  rintro ⟨s, oracles⟩ i tr
  have hi : i = ⟨0, by simp⟩ := by
    apply Subtype.ext
    exact Fin.ext (by omega)
  subst i
  have htr : tr = fun j => Fin.elim0 j := by
    funext j
    exact Fin.elim0 j
  rw [htr]
  dsimp [knowledgeStateFunction, rbrExtractor, pSpec]
  simp only [exists_const]
  have hconcat (ρ : R1CS.MatrixIdx → F) :
      @ProtocolSpec.Transcript.concat 1 (pSpec F) (0 : Fin 1) ρ
        (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1) = ρ :=
    ProtocolSpec.Transcript.concat_zero (pSpec := pSpec F) ρ _
  rw [prEvent_congr ($ᵗ (R1CS.MatrixIdx → F)) _ _ fun ρ => by rw [hconcat]]
  by_cases h : Evaluation.outputRelation pp s.2 oracles s.1
  · simp only [h, not_true_eq_false, false_and, prEvent_false]
    exact zero_le
  · simp only [h, not_false_eq_true, true_and]
    rw [independent_batch_collision_eq_inv_card pp s oracles h]
    have hdenom : (Fintype.card F : ℝ≥0) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [ENNReal.coe_div hdenom, ENNReal.coe_one, ENNReal.coe_natCast]

/-- Independent batching has fixed-prefix knowledge error `1 / |F|`. -/
theorem batch_rbrKnowledgeSoundness :
    (oracleVerifier (R := F) pp oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (relIn pp) (relOut pp) (fun _ => (1 : ℝ≥0) / Fintype.card F) :=
  ⟨fun _ => Unit, rbrExtractor pp oSpec, knowledgeStateFunction pp oSpec init impl,
    batch_rbrKnowledgeSoundnessWith pp oSpec init impl⟩

end Spartan.Batching
