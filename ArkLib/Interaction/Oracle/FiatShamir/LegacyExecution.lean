/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyCompletionKeys
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized
public import ArkLib.OracleReduction.FiatShamir.Legacy.KnowledgeGames
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript

/-!
# Operational transport of finite legacy state restoration

The concrete legacy prover has an empty ambient oracle, a Fiat–Shamir challenge oracle, and an
independent private-sampling oracle. This module routes those effects into the native randomized
restoration signature while preserving the prover's arbitrary private draws and query order.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open OracleComp OracleSpec ProtocolSpec Security.StateRestoration

/-- Route an arbitrary legacy prover's challenge queries and private coins into the native
randomized-restoration oracle. The legacy ambient source is empty. -/
def legacyProverRoute {Input : Type} (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds))) :
    QueryImpl (((OracleSpec.ofPFunctor 0) +
        fsChallengeOracle Input (legacySpec rounds)) + unifSpec)
      (OracleComp (unifSpec + oracleSpec Input PUnit rounds)) :=
  fun query => match query with
    | .inl (.inl impossible) => nomatch impossible
    | .inl (.inr key) =>
        simulateQ (restorationQueries Input PUnit rounds) (hashRoute key)
    | .inr coin =>
        liftM ((unifSpec + oracleSpec Input PUnit rounds).query (.inl coin))

/-- The legacy prover always selects a complete message tuple; native `none` is unreachable for
this transported program. -/
def legacySelection {Input W : Type} (rounds : List Round)
    (result : Input × (legacySpec rounds).Messages × W) :
    Option (Input × Messages PUnit rounds × W) :=
  some (result.1, withUnitSalts rounds ((fullLegacyMessagesEquiv rounds).symm result.2.1),
    result.2.2)

/-- Execute any coin-bearing legacy prover inside the native randomized oracle signature.
The route maps each private uniform query to the same uniform query and each challenge query to
its corresponding native typed-prefix key. -/
def simulateLegacyProverWith {Input W : Type} (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    RandomizedRestorationAdversary Input PUnit W rounds :=
  legacySelection rounds <$> simulateQ (legacyProverRoute rounds hashRoute) prover

/-- The concrete transport through the checked equivalence between typed native restoration
keys and alternating legacy Fiat–Shamir queries. -/
noncomputable def simulateLegacyProver {Input W : Type} (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    RandomizedRestorationAdversary Input PUnit W rounds :=
  simulateLegacyProverWith rounds (legacyQueryInNative rounds) prover

/-- Interpret the empty legacy ambient source and each FS challenge from one fixed table. -/
def legacyTableAnswer {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) :
    QueryImpl (OracleSpec.ofPFunctor 0 + srChallengeOracle Input (legacySpec rounds)) Id :=
  fun query => match query with
    | .inl impossible => nomatch impossible
    | .inr key => table key

/-- The challenge tuple selected by a fixed legacy table and a complete message tuple. -/
def legacyTableChallenges {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    (legacySpec rounds).Challenges :=
  fun i => table ⟨i, (z, messages.take i.1.castSucc)⟩

private theorem challenges_take_succ_challenge {n : Nat} {spec : ProtocolSpec n}
    (cs : spec.Challenges) (i : Fin n) (h : spec.dir i = .V_to_P) :
    (cs.take i.castSucc).concat h (cs ⟨i, h⟩) = cs.take i.succ := by
  funext ⟨j, hj⟩
  revert hj
  induction j using Fin.lastCases with
  | last =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.concat_apply_last]
      rfl
  | cast j =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.concat_apply_castSucc]
      rfl

private theorem challenges_take_succ_message {n : Nat} {spec : ProtocolSpec n}
    (cs : spec.Challenges) (i : Fin n) (h : spec.dir i = .P_to_V) :
    (cs.take i.castSucc).extend h = cs.take i.succ := by
  funext ⟨j, hj⟩
  revert hj
  induction j using Fin.lastCases with
  | last =>
      intro hj
      have hc : spec.dir i = .V_to_P := by
        simpa [ProtocolSpec.ChallengeIdxUpTo, SliceLT.sliceLT,
          ProtocolSpec.take, Fin.castLE] using hj
      exact absurd (h.symm.trans hc) (by decide)
  | cast j =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.extend_apply_castSucc]
      rfl

private theorem legacyChalTuple_eval {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages)
    (j : Fin (legacySteps rounds + 1)) :
    evalWithAnswerFn (legacyTableAnswer rounds table)
      (ProtocolSpec.chalTupleUpTo (oSpec := OracleSpec.ofPFunctor 0) z messages j) =
        (legacyTableChallenges rounds table z messages).take j := by
  induction j using Fin.induction with
  | zero =>
      funext i
      exact i.1.elim0
  | succ i ih =>
      change evalWithAnswerFn (legacyTableAnswer rounds table)
        (do
          let cs ← ProtocolSpec.chalTupleUpTo
            (oSpec := OracleSpec.ofPFunctor 0) z messages i.castSucc
          match hDir : (legacySpec rounds).dir i with
          | .V_to_P => do
              let c ← ProtocolSpec.getChallengeSR (oSpec := OracleSpec.ofPFunctor 0)
                ⟨i, hDir⟩ (z, messages.take i.castSucc)
              pure (cs.concat hDir c)
          | .P_to_V => pure (cs.extend hDir)) = _
      rw [evalWithAnswerFn_bind, ih]
      split
      · rename_i hDir
        change evalWithAnswerFn (legacyTableAnswer rounds table)
          (ProtocolSpec.getChallengeSR (oSpec := OracleSpec.ofPFunctor 0)
              ⟨i, hDir⟩ (z, messages.take i.castSucc) >>= fun c =>
                pure ((legacyTableChallenges rounds table z messages).take i.castSucc
                  |>.concat hDir c)) = _
        change ProtocolSpec.ChallengesUpTo.concat
            ((legacyTableChallenges rounds table z messages).take i.castSucc) hDir
            (table ⟨⟨i, hDir⟩, (z, messages.take i.castSucc)⟩) =
          (legacyTableChallenges rounds table z messages).take i.succ
        exact challenges_take_succ_challenge
          (legacyTableChallenges rounds table z messages) i hDir
      · simp only [evalWithAnswerFn_pure]
        exact challenges_take_succ_message
          (legacyTableChallenges rounds table z messages) i ‹_›

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-table evaluation of the concrete legacy transcript program reads exactly each
challenge cell keyed by its input and full prior public-message prefix. -/
theorem legacyDeriveTranscript_eval {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    evalWithAnswerFn (legacyTableAnswer rounds table)
      (messages.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) z) =
        ProtocolSpec.FullTranscript.ofMessagesChallenges messages
          (legacyTableChallenges rounds table z messages) := by
  rw [ProtocolSpec.Messages.deriveTranscriptSR_eq_chalTupleUpTo]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    legacyChalTuple_eval]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same actual derivation records the canonical challenge queries in their execution
order. Each query answer is still taken from the paired fixed table. -/
theorem legacyDeriveTranscript_logged_eval {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    evalWithAnswerFn (legacyTableAnswer rounds table)
      (messages.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) z).withQueryLog =
        (ProtocolSpec.FullTranscript.ofMessagesChallenges messages
            (legacyTableChallenges rounds table z messages),
          QueryLog.inr (ProtocolSpec.canonChalLog z messages
            (Fin.last (legacySteps rounds))
            (legacyTableChallenges rounds table z messages))) := by
  change evalWithAnswerFn (legacyTableAnswer rounds table)
    ((simulateQ loggingOracle
      (ProtocolSpec.MessagesUpTo.deriveTranscriptSRAux
        (oSpec := OracleSpec.ofPFunctor 0) (StmtIn := Input)
        z (Fin.last (legacySteps rounds)) messages.asUpTo
        (Fin.last (legacySteps rounds)))).run) = _
  refine (congrArg (evalWithAnswerFn (legacyTableAnswer rounds table))
    (ProtocolSpec.logged_deriveTranscriptSRAux_eq
      (oSpec := OracleSpec.ofPFunctor 0) z messages
      (Fin.last (legacySteps rounds)))).trans ?_
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    legacyChalTuple_eval]
  rfl

/-- The native path completed from a selected public-message tuple retains that exact tuple. -/
theorem publicPathMessages_completedPath {Input : Type} (rounds : List Round)
    (z : Input) (messages : PublicMessages rounds)
    (table : Table Input PUnit rounds) :
    publicPathMessages rounds (toPublicPath rounds
      (completedPath rounds z (withUnitSalts rounds messages) table)) = messages := by
  induction rounds with
  | nil => cases messages; rfl
  | cons round rounds ih =>
      rcases messages with ⟨message, suffix⟩
      simp only [withUnitSalts, completedPath, toPublicPath,
        publicPathMessages, ih]
      rfl

/-- The actual legacy SR transcript derivation and the native fixed-table completion return
the same alternating transcript after the checked path and message conversions. -/
theorem legacyDeriveTranscript_completedPath {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    evalWithAnswerFn (legacyTableAnswer rounds (nativeTableToLegacy rounds table))
      (messages.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) z) =
        toLegacyTranscript rounds (toPublicPath rounds
          (completedPath rounds z
            (withUnitSalts rounds ((fullLegacyMessagesEquiv rounds).symm messages))
            table)) := by
  rw [legacyDeriveTranscript_eval]
  let publicMessages := (fullLegacyMessagesEquiv rounds).symm messages
  let path := toLegacyTranscript rounds (toPublicPath rounds
    (completedPath rounds z (withUnitSalts rounds publicMessages) table))
  have hm : path.toMessagesChallenges.1 = messages := by
    simp only [path, toLegacyTranscript_messages,
      publicPathMessages_completedPath]
    exact (fullLegacyMessagesEquiv rounds).apply_symm_apply messages
  have hc : path.toMessagesChallenges.2 =
      legacyTableChallenges rounds (nativeTableToLegacy rounds table) z messages := by
    have hraw := completedPath_legacyChallenges rounds z publicMessages table
    have hmsg : fullLegacyMessagesEquiv rounds publicMessages = messages :=
      (fullLegacyMessagesEquiv rounds).apply_symm_apply messages
    rw [hmsg] at hraw
    exact hraw
  apply (ProtocolSpec.FullTranscript.equivMessagesChallenges
    (pSpec := legacySpec rounds)).injective
  change ProtocolSpec.FullTranscript.toMessagesChallenges
      (ProtocolSpec.FullTranscript.ofMessagesChallenges messages
        (legacyTableChallenges rounds (nativeTableToLegacy rounds table) z messages)) =
      path.toMessagesChallenges
  have hpair : path.toMessagesChallenges =
      (messages, legacyTableChallenges rounds (nativeTableToLegacy rounds table)
        z messages) := Prod.ext hm hc
  rw [hpair]
  have hright := (ProtocolSpec.FullTranscript.equivMessagesChallenges
    (pSpec := legacySpec rounds)).apply_symm_apply
      (messages, legacyTableChallenges rounds (nativeTableToLegacy rounds table)
        z messages)
  change ProtocolSpec.FullTranscript.toMessagesChallenges
      (ProtocolSpec.FullTranscript.ofMessagesChallenges messages
        (legacyTableChallenges rounds (nativeTableToLegacy rounds table) z messages)) =
        (messages, legacyTableChallenges rounds (nativeTableToLegacy rounds table)
          z messages) at hright
  exact hright

/-- Interpret native hash queries from a full fixed table while forwarding each private
uniform query as a fresh `ProbComp` draw. -/
def nativeFixedTableCoinImpl {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) :
    QueryImpl (unifSpec + oracleSpec Input PUnit rounds) ProbComp :=
  unifSpec.passthrough + (QueryImpl.ofFn table).liftTarget ProbComp

/-- The corresponding legacy fixed-table interpreter, with private coins left untouched. -/
def legacyFixedTableCoinImpl {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) :
    QueryImpl (((OracleSpec.ofPFunctor 0) +
        fsChallengeOracle Input (legacySpec rounds)) + unifSpec) ProbComp :=
  fun query => match query with
    | .inl (.inl impossible) => nomatch impossible
    | .inl (.inr key) => pure (table key)
    | .inr coin => liftM (unifSpec.query coin)

/-- Reading the native hash side through the randomized signature is exactly fixed-table
evaluation; the uniform side remains available for the prover's independent samples. -/
private theorem nativeFixedTableCoinImpl_comp_restoration {Input : Type}
    (rounds : List Round) (table : Table Input PUnit rounds) :
    QueryImpl.compose (nativeFixedTableCoinImpl rounds table)
      (restorationQueries Input PUnit rounds) =
        (QueryImpl.ofFn table).liftTarget ProbComp := by
  funext key
  simp [QueryImpl.compose, restorationQueries, nativeFixedTableCoinImpl]

/-- One transported legacy challenge query is answered by the matching native table cell,
with no private draw. -/
theorem legacyQueryInNative_at_fixedTable {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (q : (fsChallengeOracle Input (legacySpec rounds)).Domain) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (simulateQ (restorationQueries Input PUnit rounds) (legacyQueryInNative rounds q)) =
        pure (nativeTableToLegacy rounds table q) := by
  rw [← QueryImpl.simulateQ_compose,
    nativeFixedTableCoinImpl_comp_restoration, simulateQ_liftTarget]
  exact congrArg pure (legacyQueryInNative_eval rounds table q)

/-- In the fixed-table probability interpreter, native completion is a pure path read-out.
No private sample is consumed by completion. -/
theorem nativeComplete_at_fixedTable {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) (z : Input)
    (messages : Messages PUnit rounds) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (simulateQ (restorationQueries Input PUnit rounds) (complete rounds z messages)) =
        pure (completedPath rounds z messages table) := by
  rw [← QueryImpl.simulateQ_compose,
    nativeFixedTableCoinImpl_comp_restoration, simulateQ_liftTarget]
  exact congrArg pure (complete_eval rounds z messages table)

/-- Pointwise hash-answer agreement implies equality of the full query interpreters, including
the unchanged private-coin branch. -/
private theorem legacyProverRoute_coinImpl {Input : Type} (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)))
    (nativeTable : Table Input PUnit rounds) (legacyTable : LegacyTable Input rounds)
    (hhash : ∀ q,
      simulateQ (nativeFixedTableCoinImpl rounds nativeTable)
        (simulateQ (restorationQueries Input PUnit rounds) (hashRoute q)) =
          pure (legacyTable q)) :
    QueryImpl.compose (nativeFixedTableCoinImpl rounds nativeTable)
      (legacyProverRoute rounds hashRoute) =
        legacyFixedTableCoinImpl rounds legacyTable := by
  funext query
  cases query with
  | inl source =>
      cases source with
      | inl impossible => exact impossible.elim
      | inr key => exact hhash key
  | inr coin =>
      simp [QueryImpl.compose, legacyProverRoute, legacyFixedTableCoinImpl,
        nativeFixedTableCoinImpl]

/-- Every arbitrary legacy prover has the same output distribution at a paired full table after
translation, with every private sample executed in the same order. -/
theorem simulateLegacyProverWith_at_fixedTable {Input W : Type}
    (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)))
    (nativeTable : Table Input PUnit rounds) (legacyTable : LegacyTable Input rounds)
    (hhash : ∀ q,
      simulateQ (nativeFixedTableCoinImpl rounds nativeTable)
        (simulateQ (restorationQueries Input PUnit rounds) (hashRoute q)) =
          pure (legacyTable q))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    simulateQ (nativeFixedTableCoinImpl rounds nativeTable)
      (simulateLegacyProverWith rounds hashRoute prover) =
        legacySelection rounds <$>
          simulateQ (legacyFixedTableCoinImpl rounds legacyTable) prover := by
  simp only [simulateLegacyProverWith, simulateQ_map,
    ← QueryImpl.simulateQ_compose]
  rw [legacyProverRoute_coinImpl rounds hashRoute nativeTable legacyTable hhash]

/-- Concrete arbitrary-prover table coupling through the checked typed key equivalence. -/
theorem simulateLegacyProver_at_fixedTable {Input W : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (simulateLegacyProver rounds prover) =
    legacySelection rounds <$>
      simulateQ (legacyFixedTableCoinImpl rounds
        (nativeTableToLegacy rounds table)) prover := by
  exact simulateLegacyProverWith_at_fixedTable rounds (legacyQueryInNative rounds)
    table (nativeTableToLegacy rounds table)
    (legacyQueryInNative_at_fixedTable rounds table) prover

/-- Decode one selected legacy prover output into the actual native completed path at a fixed
full table. -/
def legacySelectedNativePath {Input W : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (result : Input × (legacySpec rounds).Messages × W) :
    Option (Input × (protocol rounds).tree.ExecutionPath × W) :=
  some (result.1,
    completedPath rounds result.1
      (withUnitSalts rounds ((fullLegacyMessagesEquiv rounds).symm result.2.1)) table,
    result.2.2)

/-- Decoding a selected native path returns the legacy prover's exact derived transcript,
including every challenge read from the same fixed table. -/
theorem legacySelectedNativePath_transcript {Input W : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (result : Input × (legacySpec rounds).Messages × W) :
    (fun triple =>
      (triple.1, toLegacyTranscript rounds (toPublicPath rounds triple.2.1),
        triple.2.2)) <$> legacySelectedNativePath rounds table result =
      some (result.1,
        evalWithAnswerFn (legacyTableAnswer rounds (nativeTableToLegacy rounds table))
          (result.2.1.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) result.1),
        result.2.2) := by
  simp only [legacySelectedNativePath]
  rw [legacyDeriveTranscript_completedPath]
  rfl

/-- The complete native selected-path output at a full table is exactly the legacy prover's
output followed by deterministic completion. This holds for every adaptive prover and retains
the full sequence of its private uniform draws. -/
theorem simulateLegacyProverWith_complete_at_fixedTable {Input W : Type}
    (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)))
    (nativeTable : Table Input PUnit rounds) (legacyTable : LegacyTable Input rounds)
    (hhash : ∀ q,
      simulateQ (nativeFixedTableCoinImpl rounds nativeTable)
        (simulateQ (restorationQueries Input PUnit rounds) (hashRoute q)) =
          pure (legacyTable q))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    simulateQ (nativeFixedTableCoinImpl rounds nativeTable)
      (randomizedRestoredExecution rounds
        (simulateLegacyProverWith rounds hashRoute prover)) =
    legacySelectedNativePath rounds nativeTable <$>
      simulateQ (legacyFixedTableCoinImpl rounds legacyTable) prover := by
  simp only [randomizedRestoredExecution, simulateQ_bind,
    simulateLegacyProverWith_at_fixedTable rounds hashRoute nativeTable legacyTable hhash]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro result
  rcases result with ⟨z, messages, witness⟩
  simp [legacySelection, legacySelectedNativePath, nativeComplete_at_fixedTable]

/-- Concrete selected native path at the same full challenge table as the legacy prover. -/
theorem simulateLegacyProver_complete_at_fixedTable {Input W : Type}
    (rounds : List Round) (table : Table Input PUnit rounds)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    simulateQ (nativeFixedTableCoinImpl rounds table)
      (randomizedRestoredExecution rounds (simulateLegacyProver rounds prover)) =
    legacySelectedNativePath rounds table <$>
      simulateQ (legacyFixedTableCoinImpl rounds
        (nativeTableToLegacy rounds table)) prover := by
  exact simulateLegacyProverWith_complete_at_fixedTable rounds
    (legacyQueryInNative rounds) table (nativeTableToLegacy rounds table)
    (legacyQueryInNative_at_fixedTable rounds table) prover

/-- The final native selected-path program, after decoding, is the legacy prover followed by
the actual canonical transcript derivation at the same full table. -/
theorem simulateLegacyProver_deriveTranscript_at_fixedTable {Input W : Type}
    (rounds : List Round) (table : Table Input PUnit rounds)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    (fun selected => selected.map fun triple =>
      (triple.1, toLegacyTranscript rounds (toPublicPath rounds triple.2.1),
        triple.2.2)) <$>
      simulateQ (nativeFixedTableCoinImpl rounds table)
        (randomizedRestoredExecution rounds (simulateLegacyProver rounds prover)) =
    (fun result => some (result.1,
      evalWithAnswerFn (legacyTableAnswer rounds (nativeTableToLegacy rounds table))
        (result.2.1.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) result.1),
      result.2.2)) <$>
        simulateQ (legacyFixedTableCoinImpl rounds
          (nativeTableToLegacy rounds table)) prover := by
  rw [simulateLegacyProver_complete_at_fixedTable]
  simp only [Functor.map_map]
  congr 1
  funext result
  exact legacySelectedNativePath_transcript rounds table result

end Interaction.Oracle.FiatShamir
