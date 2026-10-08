/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationLegacyPremise
public import ArkLib.Interaction.Oracle.FiatShamir.LegacyExecution

/-!
# The canonical legacy knowledge game at a fixed challenge table

The common fragment has an empty ambient source, independent prover-private uniform draws, a pure
verifier observation, and the named native backward extractor. Its canonical logged game equals
an explicit full-table experiment. This is a program-level simplification of the legacy game;
the separate transcript correspondence connects it to native restoration security.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec Interaction.Oracle.TypeTree Interaction.Oracle
open Interaction.TwoParty
open scoped ProbabilityTheory

namespace Interaction.Oracle.FiatShamir

open Security Security.StateRestoration

/-- The common fragment has no ambient base-oracle calls. -/
def emptyLegacyImpl {Input : Type} (rounds : List Round) :
    QueryImpl (OracleSpec.ofPFunctor 0)
      (StateT (QueryImpl (srChallengeOracle Input (legacySpec rounds)) Id) ProbComp) :=
  fun impossible => nomatch impossible

/-- Canonical table-state interpreter with independent private uniform draws. -/
def legacyStateCoinImpl {Input : Type} (rounds : List Round)
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)] :
    QueryImpl (((OracleSpec.ofPFunctor 0) +
      fsChallengeOracle Input (legacySpec rounds)) + unifSpec)
      (StateT (QueryImpl (srChallengeOracle Input (legacySpec rounds)) Id) ProbComp) :=
  (((emptyLegacyImpl (Input := Input) rounds).addLift
    (srChallengeQueryImpl' (Statement := Input) (pSpec := legacySpec rounds)) :
      QueryImpl (OracleSpec.ofPFunctor 0 + fsChallengeOracle Input (legacySpec rounds))
        (StateT (QueryImpl (srChallengeOracle Input (legacySpec rounds)) Id) ProbComp)).addLift
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp))

/-- The canonical interpreter reads its fixed table without changing it. -/
theorem legacyState_run {Input A : Type} (rounds : List Round)
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    (program : OracleComp (((OracleSpec.ofPFunctor 0) +
      fsChallengeOracle Input (legacySpec rounds)) + unifSpec) A)
    (table : LegacyTable Input rounds) :
    (simulateQ (legacyStateCoinImpl rounds) program).run table =
      (fun a => (a, table)) <$> simulateQ (legacyFixedTableCoinImpl rounds table) program := by
  induction program using OracleComp.inductionOn with
  | pure a => simp
  | query_bind query next ih =>
      cases query with
      | inl query =>
          cases query with
          | inl impossible => nomatch impossible
          | inr key =>
              rcases key with ⟨i, key⟩
              simp only [ChallengeIdx, Challenge, ofPFunctor_zero, add_apply_inl, add_apply_inr,
                simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
                id_map, StateT.run_bind, map_bind]
              change (simulateQ (legacyStateCoinImpl rounds)
                (next (table ⟨i, key⟩))).run table = _
              exact ih (table ⟨i, key⟩)
      | inr coin =>
          have h := congrArg (fun k : Fin (coin + 1) → ProbComp (A × LegacyTable Input rounds) =>
            (liftM (unifSpec.query coin) : ProbComp (Fin (coin + 1))) >>= k) (funext ih)
          simpa [legacyStateCoinImpl, QueryImpl.addLift, StateT.run_bind,
            legacyFixedTableCoinImpl] using h

/-- Forgetting the unchanged table gives the explicit fixed-table coin interpreter. -/
theorem legacyState_run' {Input A : Type} (rounds : List Round)
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    (program : OracleComp (((OracleSpec.ofPFunctor 0) +
      fsChallengeOracle Input (legacySpec rounds)) + unifSpec) A)
    (table : LegacyTable Input rounds) :
    (simulateQ (legacyStateCoinImpl rounds) program).run' table =
      simulateQ (legacyFixedTableCoinImpl rounds table) program := by
  simp only [StateT.run'_eq, legacyState_run, Functor.map_map]
  simp

/-- Run the arbitrary coin-bearing prover, then derive the complete canonical transcript. -/
def legacyFixedTableTranscript {Input W : Type} (rounds : List Round)
    (table : LegacyTable Input rounds)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    ProbComp (Input × (legacySpec rounds).FullTranscript × W) := do
  let selected ← simulateQ (legacyFixedTableCoinImpl rounds table) prover
  pure (selected.1, evalWithAnswerFn (legacyTableAnswer rounds table)
    (selected.2.1.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) selected.1), selected.2.2)

universe w

/-- The pure verifier/extractor result on a concrete legacy transcript. -/
def nativeLegacyResult {Input W WitIn StmtOut : Type} (rounds : List Round)
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (selected : Input × (legacySpec rounds).FullTranscript × W) :
    Input × Option WitIn × Option StmtOut × W :=
  let path := legacyToRestorationPath rounds selected.2.1
  (selected.1, some (witnessMap selected.1
    ((extractor selected.1).extractWitness path (seed selected.1 path selected.2.2))),
    observe selected.1 path, selected.2.2)

private theorem logging_bind_fst {ι A B : Type} {spec : OracleSpec ι}
    (program : OracleComp spec A) (next : A → OracleComp spec B) :
    ((simulateQ loggingOracle program).run >>= fun logged => next logged.1) =
      program >>= next := by
  rw [← bind_map_left, loggingOracle.fst_map_run_simulateQ]

/-- A base/challenge computation contains no private draws and reads the fixed table. -/
theorem legacyFixedTableCoinImpl_liftLeft {Input A : Type} (rounds : List Round)
    (table : LegacyTable Input rounds)
    (program : OracleComp (OracleSpec.ofPFunctor 0 +
      fsChallengeOracle Input (legacySpec rounds)) A) :
    simulateQ (legacyFixedTableCoinImpl rounds table)
      (program.liftComp ((OracleSpec.ofPFunctor 0 +
        fsChallengeOracle Input (legacySpec rounds)) + unifSpec)) =
      pure (evalWithAnswerFn (legacyTableAnswer rounds table) program) := by
  induction program using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q next ih =>
    cases q with
    | inl impossible => nomatch impossible
    | inr key =>
      simp only [ChallengeIdx, Challenge, ofPFunctor_zero, add_apply_inr, liftComp_bind,
        liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, simulateQ_bind,
        evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, bind_eq_pure_iff] at *
      refine ⟨table key, ?_, ih (table key)⟩
      change simulateQ (legacyFixedTableCoinImpl rounds table)
        (liftM (((OracleSpec.ofPFunctor 0 + fsChallengeOracle Input (legacySpec rounds)) +
          unifSpec).query (.inl (.inr key)))) = _
      simp [legacyFixedTableCoinImpl]

/-- Unroll the actual canonical coin-bearing knowledge game for the pure native verifier and
backward extractor. Only their unused logs and unchanged table state are erased; prover coins and
the precise relation-failure event remain. No native execution equivalence is assumed. -/
theorem coinKSExperimentProb_eq_fixedTable
    {Input W WitIn StmtOut : Type} (rounds : List Round)
    [∀ i, SampleableType ((legacySpec rounds).Challenge i)]
    (init : ProbComp (LegacyTable Input rounds))
    (state : Input → KnowledgeState.{w})
    (extractor : (z : Input) → RoundExtractor (protocol rounds).tree (state z))
    (seed : (z : Input) → (path : (protocol rounds).tree.ExecutionPath) →
      W → ((extractor z).terminalState path).Witness)
    (witnessMap : (z : Input) → (state z).Witness → WitIn)
    (observe : Input → (protocol rounds).tree.ExecutionPath → Option StmtOut)
    (relIn : Set (Input × WitIn)) (relOut : Set (StmtOut × W))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    Verifier.StateRestoration.coinKSExperimentProb init (emptyLegacyImpl rounds)
      (unifSpec.passthrough : QueryImpl unifSpec ProbComp)
      (nativeBackwardLegacyExtractor (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) state extractor seed witnessMap)
      relIn relOut
      (nativeLegacyVerifier (OracleSpec.ofPFunctor 0) (legacySpec rounds)
        (legacyToRestorationPath rounds) observe) prover =
      Pr{let selected ← (init >>= fun table => legacyFixedTableTranscript rounds table prover)}[
        relationKSFailEvent relIn relOut
          (nativeLegacyResult rounds state extractor seed witnessMap observe selected)] := by
  unfold Verifier.StateRestoration.coinKSExperimentProb
  simp only [nativeBackwardLegacyExtractor_run, nativeLegacyVerifier_run,
    simulateQ_pure, WriterT.run_pure, liftComp_pure, pure_bind]
  simp only [bind_assoc]
  congr 2
  apply bind_congr
  intro table
  change ((simulateQ (legacyStateCoinImpl rounds) _).run' table >>= _) = _
  rw [legacyState_run']
  let next : Input × (legacySpec rounds).Messages × W →
      OracleComp ((OracleSpec.ofPFunctor 0 +
        fsChallengeOracle Input (legacySpec rounds)) + unifSpec)
        (Input × Option WitIn × Option StmtOut × W) := fun selected => do
    let transcript ← (selected.2.1.deriveTranscriptSR
      (oSpec := OracleSpec.ofPFunctor 0) selected.1).liftComp _
    pure (nativeLegacyResult rounds state extractor seed witnessMap observe
      (selected.1, transcript, selected.2.2))
  change (simulateQ (legacyFixedTableCoinImpl rounds table)
    ((simulateQ loggingOracle prover).run >>= fun logged => next logged.1) >>= _) = _
  rw [logging_bind_fst]
  dsimp only [next]
  simp only [simulateQ_bind, simulateQ_pure, legacyFixedTableTranscript, bind_assoc]
  apply bind_congr
  intro selected
  rw [legacyFixedTableCoinImpl_liftLeft]
  simp only [pure_bind]

end Interaction.Oracle.FiatShamir
