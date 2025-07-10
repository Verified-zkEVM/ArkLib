import ArkLib.OracleReduction.Basic
import ArkLib.Data.Fin.Basic

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

namespace loggingOracle

universe u

variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

@[simp]
theorem impl_run {i : ι} {t : spec.domain i} :
    (loggingOracle.impl (query i t)).run = (do let u ← query i t; return (u, [⟨i, ⟨t, u⟩⟩])) :=
  rfl

@[simp]
theorem simulateQ_map_fst (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ loggingOracle oa).run = oa := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [simulateQ_bind, ih]
  | failure => simp

@[simp]
theorem simulateQ_bind_fst (oa : OracleComp spec α) (f : α → OracleComp spec β) :
    (do let a ← (simulateQ loggingOracle oa).run; f a.1) = oa >>= f := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [simulateQ_bind, ih]
  | failure => simp

end loggingOracle

section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

/--
Prover's function for processing the next round, given the current result of the previous round.
-/
@[inline, specialize]
def Prover.processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.getDir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := prover.receiveChallenge ⟨j, hDir⟩ state challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩

/-- Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def Prover.runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input (stmt, wit)⟩)
    prover.processRound
    i

/-- Run the prover in an interactive reduction up to round `i`, logging all the queries made by the
  prover. Returns the transcript up to that round, the prover's state after that round, and the log
  of the prover's oracle queries.
-/
@[inline, specialize]
def Prover.runWithLogToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript i × prover.PrvState i × QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ)) := do
  let ⟨⟨transcript, state⟩, proveQueryLog⟩ ←
    (simulateQ loggingOracle (prover.runToRound i stmt wit)).run
  return ⟨transcript, state, proveQueryLog⟩

/-- Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript. See `Prover.runWithLog` for a version that additionally returns the log of the
  prover's oracle queries.
-/
@[inline, specialize]
def Prover.run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ) ((StmtOut × WitOut) × FullTranscript pSpec) := do
  let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
  return ⟨prover.output state, transcript⟩

/-- Run the prover in an interactive reduction, logging all the queries made by the prover. Returns
  the output statement and witness, the transcript, and the log of the prover's oracle queries.
-/
@[inline, specialize]
def Prover.runWithLog (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        ((StmtOut × WitOut) × FullTranscript pSpec × QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ)) := do
  let ⟨transcript, state, proveQueryLog⟩ ← prover.runWithLogToRound (Fin.last n) stmt wit
  return ⟨prover.output state, transcript, proveQueryLog⟩

/-- Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and
  the transcript, and return the output statement along with the log of oracle queries made by the
  veirifer.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : OracleComp oSpec StmtOut :=
  verifier.verify stmt transcript

/-- Running the oracle verifier without reification. Since we do not know the input oracle
  statements nor the prover's messages, we return an oracle computation (with those as oracles) of
  type `StmtOut` together with a simulation strategy for `OStmtOut` in terms of the rest.

  Essentially, we call `verify` and `simulate` on the input statement & the challenges.
-/
@[inline, specialize]
def OracleVerifier.SimulateOnly.run
    (stmt : StmtIn) (challenges : pSpec.Challenges)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ)) StmtOut ×
        QueryImpl [OStmtOut]ₒ (OracleComp (oSpec ++ₒ ([OStmtIn]ₒ ++ₒ [pSpec.Message]ₒ))) :=
  ⟨verifier.verify stmt challenges, verifier.simulate stmt challenges⟩

/-- Run the oracle verifier (with reification) in an (interactive) oracle reduction.

We take in all available information (input statement, input oracle statements, and the full
transcript), and use `verify` and `reify` to compute the output statement (non-oracle & oracle).
-/
@[inline, specialize]
def OracleVerifier.run
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OracleComp oSpec (StmtOut × (∀ i, OStmtOut i)) := do
  let f := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages
  let stmtOut ← simulateQ f (verifier.verify stmt transcript.challenges)
  let oStmtOut ← verifier.reify ⟨stmt, oStmtIn⟩ transcript
  return ⟨stmtOut, oStmtOut⟩

/-- Running an oracle verifier (with reification) is definitionally equal to first converting it to
  a non-oracle verifier, and then running it. -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {transcript : FullTranscript pSpec}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec} :
      verifier.run stmt oStmt transcript =
        verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := rfl

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the output statement and witness, and the
  full transcript.

  See `Reduction.runWithLog` for a version that additionally returns the logs of the prover's and
  the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        ((StmtOut × WitOut) × StmtOut × FullTranscript pSpec) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let ⟨ctxOut, transcript⟩ ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt transcript)
  return (ctxOut, stmtOut, transcript)

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the output statement and witness, the
  full transcript, and the logs of the prover's and the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.runWithLog (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        ((StmtOut × WitOut) × StmtOut × FullTranscript pSpec ×
          QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let ⟨ctxOut, transcript, proveQueryLog⟩ ← reduction.prover.runWithLog stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt transcript)).run
  return (ctxOut, stmtOut, transcript, proveQueryLog, verifyQueryLog)

/-- Logging the queries made by both parties do not change the output of the reduction -/
@[simp]
theorem Reduction.runWithLog_eq_run
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} :
      (fun ⟨prvOutput, witOut, transcript, _, _⟩ => (prvOutput, witOut, transcript)) <$>
        reduction.runWithLog stmt wit = reduction.run stmt wit := by
  simp [run, runWithLog, Verifier.run, Prover.runWithLog, Prover.runWithLogToRound]
  sorry

/-- Run an interactive oracle reduction (where the oracle verifier has reification).

Returns the full transcript, the output statement and witness, the log of all prover's oracle
queries, and the log of all verifier's oracle queries to the prover's messages and to the shared
oracle.
-/
@[inline, specialize]
def OracleReduction.run
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (((StmtOut × ∀ i, OStmtOut i) × WitOut) × (StmtOut × ∀ i, OStmtOut i)
          × FullTranscript pSpec) := do
  let ⟨ctxOut, transcript⟩ ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let stmtOut ← liftM <| reduction.verifier.run stmt oStmt transcript
  return (ctxOut, stmtOut, transcript)

/-- Run an interactive oracle reduction (where the oracle verifier has reification), with logging
  the oracle queries of the prover and the verifier.

Returns the full transcript, the output statement and witness, the log of all prover's oracle
queries, and the log of all verifier's oracle queries to the prover's messages and to the shared
oracle.
-/
@[inline, specialize]
def OracleReduction.runWithLog
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (((StmtOut × ∀ i, OStmtOut i) × WitOut) × (StmtOut × ∀ i, OStmtOut i)
          × FullTranscript pSpec × QueryLog (oSpec ++ₒ [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let ⟨ctxOut, transcript, proveQueryLog⟩ ← reduction.prover.runWithLog ⟨stmt, oStmt⟩ wit
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt oStmt transcript)).run
  return (ctxOut, stmtOut, transcript, proveQueryLog, verifyQueryLog)

/-- Running an oracle reduction (with reification for verifier) is definitionally equal to first
  converting it to a non-oracle reduction, and then running it. -/
@[simp]
theorem OracleReduction.run_eq_run_reduction
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := rfl


/-- Running an oracle reduction (with reification for verifier) with logging is definitionally equal
  to first converting it to a non-oracle reduction, and then running it with logging. -/
@[simp]
theorem OracleReduction.runWithLog_eq_runWithLog_reduction
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.runWithLog stmt oStmt wit =
        oracleReduction.toReduction.runWithLog ⟨stmt, oStmt⟩ wit := rfl

omit Oₘ in
@[simp]
theorem Prover.runToRound_zero_of_prover_first
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 0 stmt wit = (pure (default, prover.input (stmt, wit))) := by
  simp [Prover.runToRound]

end Execution

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}

section SingleMessage

/-! Simplification lemmas for protocols with a single message -/

variable {pSpec : ProtocolSpec 1}

@[simp]
theorem Prover.runToRound_one_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        return (fun i => match i with | ⟨0, _⟩ => msg, state)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : (pSpec 0).1 = .P_to_V := by simp
  split <;> rename_i hDir
  · have : Direction.P_to_V = .V_to_P := by rw [← this, hDir]
    contradiction
  · congr; funext a; congr; simp [default, Transcript.concat]; funext i
    have : i = 0 := by aesop
    rw [this]; simp [Fin.snoc]

@[simp]
theorem Prover.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        let ctxOut := prover.output state
        return (ctxOut, fun i => match i with | ⟨0, _⟩ => msg)) := by
  simp [Prover.run]; rfl

@[simp]
theorem Reduction.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      reduction.run stmt wit = (do
        let state := reduction.prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (reduction.prover.sendMessage ⟨0, by simp⟩ state) _
        let (prvStmtOut, witOut) := reduction.prover.output state
        let transcript : pSpec.FullTranscript := fun i => match i with | ⟨0, _⟩ => msg
        let stmtOut ← reduction.verifier.verify stmt transcript
        return ((prvStmtOut, witOut), stmtOut, transcript)) := by
  simp [Reduction.run, Verifier.run, ← liftComp_map]
  conv =>
    enter [1, 1]
    rw [map_eq_pure_bind]
    simp
  -- conv =>
  --   enter [1, 2, a, 1]
  --   rw [map_eq_pure_bind]
  --   rw [loggingOracle.simulateQ_bind_fst
  --     (reduction.verifier.verify stmt _) (fun a_1_1 => pure (a_1_1, _))]
  -- simp
  sorry

end SingleMessage

section Classes

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    {pSpec : ProtocolSpec 2}

-- /-- Simplification of the prover's execution in a single-round, two-message protocol where the
--   prover speaks first -/
-- theorem Prover.run_of_isSingleRound [IsSingleRound pSpec] (stmt : StmtIn) (wit : WitIn)
--     (prover : Prover pSpec oSpec StmtIn WitIn StmtOut WitOut) :
--       prover.run stmt wit = (do
--         let state ← liftComp (prover.load stmt wit)
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp
--           (simulate loggingOracle ∅ (prover.sendMessage default state emptyTranscript))
--         let challenge ← query (Sum.inr default) ()
--         let state ← liftComp (prover.receiveChallenge default state transcript challenge)
--         let transcript := Transcript.mk2 msg challenge
--         let witOut := prover.output state
--         return (transcript, queryLog, witOut)) := by
--   simp [Prover.run, Prover.runToRound, Fin.reduceFinMk, Fin.val_two,
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, getDir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, getDir_apply, Fin.succ_one_eq_two,
--     Fin.succ_zero_eq_one, queryBind_inj', true_and, exists_const]
--   funext chal; simp [OracleSpec.append] at chal
--   congr; funext state; congr
--   rw [← Transcript.mk2_eq_toFull_snoc_snoc _ _]

-- theorem Reduction.run_of_isSingleRound [IsSingleRound pSpec]
--     (reduction : Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut PrvState)
--     (stmt : StmtIn) (wit : WitIn) :
--       reduction.run stmt wit = do
--         let state := reduction.prover.load stmt wit
--         let ⟨⟨msg, state⟩, queryLog⟩ ← liftComp (simulate loggingOracle ∅
--           (reduction.prover.sendMessage default state))
--         let challenge := reduction.prover.receiveChallenge default state
--         let stmtOut ← reduction.verifier.verify stmt transcript
--         return (transcript, queryLog, stmtOut, reduction.prover.output state) := by sorry

end Classes
