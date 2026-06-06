import ArkLib.OracleReduction.Basic
import ArkLib.Data.Fin.Basic
import ArkLib.ToVCVio.OracleComp.EvalDist

/-!
  # Execution Semantics of Interactive Oracle Reductions

  We define what it means to execute an interactive oracle reduction, and prove some basic
  properties.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v

-- namespace loggingOracle

-- variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

-- @[simp]
-- theorem impl_run {i : ι} {t : spec.domain i} :
--     (loggingOracle.impl (query i t)).run = (do let u ← query i t; return (u, [⟨i, ⟨t, u⟩⟩])) :=
--   rfl

-- @[simp]
-- theorem simulateQ_map_fst (oa : OracleComp spec α) :
--     Prod.fst <$> (simulateQ loggingOracle oa).run = oa := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- @[simp]
-- theorem simulateQ_bind_fst (oa : OracleComp spec α) (f : α → OracleComp spec β) :
--     (do let a ← (simulateQ loggingOracle oa).run; f a.1) = oa >>= f := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- /-- We often have to specify `oa` and `f` for this to be applied -/
-- theorem simulateQ_bind_fst_comp (oa : OracleComp spec α) (f : α → OracleComp spec β) :
--     (do let a ← (simulateQ loggingOracle oa).run; f a.1) = (do let a ← oa; f a) := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- /-- Ideally, this theorem can also compare the logs of the two oracle computations.

-- For this to work, we need an extra function mapping `superSpec.QueryLog` to `spec.QueryLog`.

-- This function always exists if `superSpec` is `spec + something`, and extensions thereof, but may
-- not be guaranteed to exist in general, if we just have the current fields in the type class. -/
-- @[simp]
-- theorem simulateQ_run_liftComp_fst {ι' : Type u} {superSpec : OracleSpec ι'}
--     (oa : OracleComp spec α) [SubSpec spec superSpec] :
--       Prod.fst <$> (simulateQ loggingOracle oa).run.liftComp superSpec =
--         Prod.fst <$> (simulateQ loggingOracle (oa.liftComp superSpec)).run := by
--   induction oa using OracleComp.induction with
--   | pure a => simp
--   | query_bind i t oa ih => simp [simulateQ_bind, ih]
--   | failure => simp

-- end loggingOracle

section Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
 {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

namespace Prover

/--
Prover's function for processing the next round, given the current result of the previous round, and
a function for getting the challenge.
-/
@[inline, specialize]
def processRound (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (pSpec.Transcript j.succ × prover.PrvState j.succ) := do
  let ⟨transcript, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let challenge ← pSpec.getChallenge ⟨j, hDir⟩
    letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
    return ⟨transcript.concat challenge, newState⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨transcript.concat msg, newState⟩

/-- Run the prover in an interactive reduction up to round index `i`, via first inputting the
  statement and witness, and then processing each round up to round `i`. Returns the transcript up
  to round `i`, and the prover's state after round `i`.
-/
@[inline, specialize]
def runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (pSpec.Transcript i × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, prover.input (stmt, wit)⟩)
    (prover.processRound)
    i

/-- Run the prover in an interactive reduction up to round `i`, logging all the queries made by the
  prover. Returns the transcript up to that round, the prover's state after that round, and the
  log of the prover's oracle queries. This basically just wraps `runToRound` with a logging
  oracle.
-/
@[inline, specialize]
def runWithLogToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((pSpec.Transcript i × prover.PrvState i) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  WriterT.run (simulateQ loggingOracle (prover.runToRound i stmt wit))

private lemma fst_map_simulateQ_loggingOracle_run {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> WriterT.run (simulateQ loggingOracle oa) = oa := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_query_bind]
    show Prod.fst <$> (do let u ← liftM (loggingOracle t); simulateQ loggingOracle (oa u)).run =
      liftM (query t) >>= oa
    stop -- This is broken for now until the refactor of `loggingOracle` and `WriterT`
    simp only [WriterT.run_bind, map_bind, Functor.map_map]
    have key : ∀ (w : QueryLog spec), (fun a_1 => (Prod.map id (w * ·) a_1).1) =
        (Prod.fst : α × QueryLog spec → α) :=
      fun w => funext fun ⟨a, b⟩ => rfl
    simp_rw [key, ih]
    rw [← bind_map_left Prod.fst]
    rfl

@[simp]
lemma runWithLogToRound_discard_log_eq_runToRound (i : Fin (n + 1))
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLogToRound i stmt wit =
        prover.runToRound i stmt wit := by
  simp [runWithLogToRound, runToRound]

/-- Run the prover in an interactive reduction. Returns the output statement and witness, and the
  transcript. See `runWithLog` for a version that additionally returns the log of the
  prover's oracle queries.
-/
@[inline, specialize]
def run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (FullTranscript pSpec × StmtOut × WitOut) := do
  let ⟨transcript, state⟩ ← prover.runToRound (Fin.last n) stmt wit
  return ⟨transcript, ← prover.output state⟩

/-- Run the prover in an interactive reduction, logging all the queries made by the prover. Returns
  the transcript, the output statement and witness, and the log of the prover's oracle queries.

Note: this is just a wrapper around `run` that logs the queries made by the prover.
-/
@[inline, specialize]
def runWithLog (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        ((FullTranscript pSpec × StmtOut × WitOut) × QueryLog (oSpec + [pSpec.Challenge]ₒ)) :=
  (simulateQ loggingOracle (prover.run stmt wit)).run

@[simp]
lemma runWithLog_discard_log_eq_run (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      Prod.fst <$> prover.runWithLog stmt wit = prover.run stmt wit := by
  simp [runWithLog]

end Prover

/-- Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and
  the transcript, and return the output statement.
-/
@[inline, specialize, reducible]
def Verifier.run (stmt : StmtIn) (transcript : FullTranscript pSpec)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) : OptionT (OracleComp oSpec) StmtOut :=
  verifier.verify stmt transcript

/-- Run the oracle verifier in the interactive protocol. Returns the verifier's output, including
    both the output statement and oracle statements, and the log of queries made by the verifier.
-/
@[inline, specialize]
def OracleVerifier.run [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmtIn : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
      OptionT (OracleComp oSpec) (StmtOut × (∀ i, OStmtOut i)) := do
  let f := OracleInterface.simOracle2 oSpec oStmtIn transcript.messages
  let stmtOut ← simulateQ f (verifier.verify stmt transcript.challenges)
  let oStmtOut : ∀ i, OStmtOut i := fun i => match h : verifier.embed i with
    | .inl j => (verifier.hEq i ▸ h ▸ oStmtIn j : OStmtOut i)
    | .inr j => (verifier.hEq i ▸ h ▸ transcript.messages j : OStmtOut i)
  return ⟨stmtOut, oStmtOut⟩

/-- Running an oracle verifier then is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleVerifier.run_eq_run_verifier [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {transcript : FullTranscript pSpec}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec} :
      verifier.run stmt oStmt transcript =
        verifier.toVerifier.run ⟨stmt, oStmt⟩ transcript := by
  simp only [OracleVerifier.run, OracleVerifier.toVerifier, Verifier.run]
  rfl

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier.

  See `Reduction.runWithLog` for a version that additionally returns the logs of the prover's and
  the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.run (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let proverResult ← reduction.prover.run stmt wit
  let stmtOut ← liftM (reduction.verifier.run stmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run a reduction and return only the verifier's output statement, discarding the full transcript
  and prover witness. Useful when only the final verdict matters (e.g. for `Proof`s). -/
def Reduction.verdict (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) StmtOut := do
  let ⟨_, stmtOut⟩ ← reduction.run stmt wit
  return stmtOut

/-- Running `Reduction.verdict` is running the reduction and projecting the verdict. -/
lemma Reduction.verdict_run_eq_map_run
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.verdict stmt wit).run =
      Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
        result.2) <$> (reduction.run stmt wit).run := by
  simp [Reduction.verdict, OptionT.run_map]

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  full successful run results. Returns `none` if any instance fails, otherwise returns a function
  from indices to the full run data. -/
def Reduction.allRuns {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ)
        (Option (Fin L → ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut))) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.run (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- Run a reduction on `L` instances and project each successful full run result through `extract`.
  Returns `none` if any instance fails, otherwise returns the indexed extracted outputs. -/
def Reduction.allOutputs {L : ℕ} {α : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → α)) := do
  let results ← reduction.allRuns stmts wits
  return results.map fun resultOf => fun i => extract (resultOf i)

/-- Run a reduction on `L` instances (given by indexed statements and witnesses), and sequence the
  results. Returns `none` if any instance fails, otherwise returns a function from indices to
  the verifier's output statements. -/
def Reduction.allVerdicts {L : ℕ}
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OracleComp (oSpec + [pSpec.Challenge]ₒ) (Option (Fin L → StmtOut)) := do
  let results ← (Vector.ofFn id).mapM fun i => (reduction.verdict (stmts i) (wits i)).run
  return (results.mapM id).map fun v => fun i => v[i]

/-- `allVerdicts` has the same distribution as `allOutputs` with a projection retaining the
  verifier output as the first component; it differs only by a pure post-map. -/
lemma Reduction.allVerdicts_eq_map_allOutputs_fst {L : ℕ} {β : Type}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → β)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
    reduction.allVerdicts stmts wits =
      (Option.map (fun resultOf => fun i => (resultOf i).1)) <$>
        reduction.allOutputs (fun result => (result.2, extract result)) stmts wits := by
  unfold Reduction.allVerdicts Reduction.allOutputs Reduction.allRuns
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  rw [Vector.mapM_bind_map_eq
    (v := Vector.ofFn (id : Fin L → Fin L))
    (f₁ := fun i => (reduction.verdict (stmts i) (wits i)).run)
    (f₂ := fun i => (reduction.run (stmts i) (wits i)).run)
    (g := Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
      result.2))
    (post₁ := fun results =>
      pure ((results.mapM id).map fun v => fun i => v[i]))
    (post₂ := fun results =>
      pure (Option.map (fun resultOf => fun i => (resultOf i).1)
        (Option.map (fun resultOf => fun i => ((resultOf i).2, extract (resultOf i)))
          (Option.map (fun v => fun i => v[i]) (results.mapM id)))))]
  · intro i
    exact Reduction.verdict_run_eq_map_run reduction (stmts i) (wits i)
  · intro results
    congr 1
    rw [Vector.mapM_id_option_map_comm]
    cases h : results.mapM id with
    | none => simp
    | some v =>
        simp only [Option.map_some, Option.some.injEq]
        funext i
        simp

lemma Reduction.support_allOutputs_index
    {StmtIn WitIn StmtOut WitOut α : Type} {n : ℕ} {pSpec : ProtocolSpec n} {L : ℕ}
    (extract : ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) → α)
    (stmts : Fin L → StmtIn) (wits : Fin L → WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    {y : Option (Fin L → α)}
    (hy : y ∈ support (reduction.allOutputs extract stmts wits))
    {resultOf : Fin L → α} (hy_eq : y = some resultOf) (i : Fin L) :
      ∃ result, some result ∈ support (reduction.run (stmts i) (wits i)).run ∧
        extract result = resultOf i := by
  unfold Reduction.allOutputs at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨runsOpt, hrunsOpt, hy_mem⟩ := hy
  rw [mem_support_pure_iff] at hy_mem
  rw [hy_eq] at hy_mem
  cases hruns : runsOpt with
  | none => simp [hruns] at hy_mem
  | some runOf =>
      simp only [hruns, Option.map_some, Option.some.injEq] at hy_mem
      unfold Reduction.allRuns at hrunsOpt
      rw [mem_support_bind_iff] at hrunsOpt
      obtain ⟨results, hresults, hrunsOpt⟩ := hrunsOpt
      rw [mem_support_pure_iff] at hrunsOpt
      cases hseq : results.mapM id with
      | none => simp [hseq, hruns] at hrunsOpt
      | some results' =>
          simp only [hseq, Option.map_some] at hrunsOpt
          rw [hruns] at hrunsOpt
          simp only [Option.some.injEq] at hrunsOpt
          have hidx : results[i] = some results'[i] :=
            Vector.mapM_id_some_index hseq i
          refine ⟨results'[i], ?_, ?_⟩
          · simpa [hidx] using
              OracleComp.support_ofFn_mapM_index
                (fun i => (reduction.run (stmts i) (wits i)).run) hresults i
          · have hrunOf_i := congrFun hrunsOpt i
            have hresult_i := congrFun hy_mem i
            rw [hresult_i, hrunOf_i]

/-- If a reduction's verifier is a pure function `f` of the input statement and full transcript,
    then the verifier output of any complete result in the support of `Reduction.run` equals
    `f stmt td` applied to the input statement and the produced transcript. -/
lemma Reduction.support_run_pure_verifier
    {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (f : StmtIn → FullTranscript pSpec → StmtOut)
    (hf : ∀ stmt td,
      reduction.verifier.verify stmt td =
        (pure (f stmt td) : OptionT (OracleComp oSpec) StmtOut))
    (stmt : StmtIn) (wit : WitIn)
    {y : Option ((FullTranscript pSpec × StmtOut × WitOut) × StmtOut)}
    (hy : y ∈ support (reduction.run stmt wit).run)
    {td : FullTranscript pSpec} {prv : StmtOut × WitOut} {vOut : StmtOut}
    (heq : y = some ((td, prv), vOut)) : vOut = f stmt td := by
  rw [heq] at hy
  unfold Reduction.run at hy
  simp only [OptionT.run_bind, Option.elimM] at hy
  rw [mem_support_bind_iff] at hy
  obtain ⟨proverResultOpt, _hprover, hy⟩ := hy
  cases proverResultOpt with
  | none =>
      exfalso
      simp at hy
  | some proverResult =>
      simp only [Option.elim_some] at hy
      rw [mem_support_bind_iff] at hy
      obtain ⟨stmtOutOpt, hstmtOutOpt, hy⟩ := hy
      simp only [ChallengeIdx, Challenge, Verifier.run, hf, OptionT.run_pure, liftM_pure,
        support_pure, Set.mem_singleton_iff] at hstmtOutOpt
      subst stmtOutOpt
      simp only [Option.elim_some, Option.getM_some, OptionT.run_pure] at hy
      injection hy with hpair
      have htd : td = proverResult.1 := congrArg Prod.fst (congrArg Prod.fst hpair)
      have hvOut : vOut = f stmt proverResult.1 := congrArg Prod.snd hpair
      rw [htd]
      exact hvOut

/-- An execution of an interactive reduction on a given initial statement and witness. Consists of
  first running the prover, and then the verifier. Returns the full transcript, the output statement
  and witness from the prover, and the output statement from the verifier, along with the logs of
  the prover's and the verifier's oracle queries.
-/
@[inline, specialize]
def Reduction.runWithLog (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (((FullTranscript pSpec × StmtOut × WitOut) × StmtOut) ×
          QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  -- `ctxOut` contains both the output statement and witness after running the prover
  let ⟨proverResult, proveQueryLog⟩ ← reduction.prover.runWithLog stmt wit
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt proverResult.1)).run
  return ⟨⟨proverResult, ← stmtOut.getM⟩, proveQueryLog, verifyQueryLog⟩

/-- TODO: figure out a better name for this -/
private lemma Monad.map_of_prod_fst_eq_prod_fst {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β γ : Type u} (ma : m (α × β)) (c : γ) :
    (fun a => (c, a.1)) <$> ma = Prod.mk c <$> Prod.fst <$> ma := by
  simp only [Functor.map_map]

/-- Logging the queries made by both parties do not change the output of the reduction -/
@[simp]
theorem Reduction.runWithLog_discard_logs_eq_run
    {stmt : StmtIn} {wit : WitIn}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec} :
      Prod.fst <$>
        reduction.runWithLog stmt wit = reduction.run stmt wit := by
  simp [runWithLog, run, Prover.runWithLog]
  sorry
  -- calc
  -- _ = (do
  --   let a ← (simulateQ loggingOracle proverRun).run
  --   (fun aFst : (pSpec.FullTranscript × StmtOut × WitOut) => (fun b => (aFst, Prod.fst b)) <$>
  --       (simulateQ loggingOracle (Verifier.run stmt aFst.1 reduction.verifier)).run.liftComp
  --         (oSpec + [pSpec.Challenge]ₒ)) a.1) := rfl
  -- _ = _ := by
    -- rw [loggingOracle.simulateQ_bind_fst_comp proverRun
    --   (fun a => (fun b => (a, Prod.fst b)) <$>
    --     (simulateQ loggingOracle (Verifier.run stmt a.1 reduction.verifier)).run.liftComp
    --       (oSpec + [pSpec.Challenge]ₒ))]
    -- congr
    -- ext proverResult
    -- rw [← Functor.map_map]
    -- simp


/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.run [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i)) := do
  let proverResult ← reduction.prover.run ⟨stmt, oStmt⟩ wit
  let stmtOut ← liftM (reduction.verifier.run stmt oStmt proverResult.1).run
  return ⟨proverResult, ← stmtOut.getM⟩

/-- Run an interactive oracle reduction. Returns the full transcript, the output statement and
  witness, the log of all prover's oracle queries, and the log of all verifier's oracle queries to
  the prover's messages and to the shared oracle.
-/
@[inline, specialize]
def OracleReduction.runWithLog [∀ i, OracleInterface (pSpec.Message i)]
    (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn)
    (reduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        ((FullTranscript pSpec × (StmtOut × ∀ i, OStmtOut i) × WitOut) ×
          (StmtOut × ∀ i, OStmtOut i) ×
            QueryLog (oSpec + [pSpec.Challenge]ₒ) × QueryLog oSpec) := do
  let ⟨proverResult, proveQueryLog⟩ ←
    (simulateQ loggingOracle (reduction.prover.run ⟨stmt, oStmt⟩ wit)).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle (reduction.verifier.run stmt oStmt proverResult.1)).run
  return ⟨proverResult, ← stmtOut.getM, proveQueryLog, verifyQueryLog⟩

/-- Running an oracle reduction is equal to running its non-oracle counterpart -/
@[simp]
theorem OracleReduction.run_eq_run_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

/-- Running an oracle reduction with logging of queries to the shared oracle is equal to running its
  non-oracle counterpart with logging of queries to the shared oracle -/
@[simp]
theorem OracleReduction.runWithLog_eq_runWithLog_reduction [∀ i, OracleInterface (pSpec.Message i)]
    {stmt : StmtIn} {oStmt : ∀ i, OStmtIn i} {wit : WitIn}
    {oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec} :
      oracleReduction.run stmt oStmt wit =
        oracleReduction.toReduction.run ⟨stmt, oStmt⟩ wit := by
  simp only [OracleReduction.run, Reduction.run, OracleVerifier.run_eq_run_verifier,
    OracleReduction.toReduction]

@[simp]
theorem Prover.runToRound_zero_of_prover_first
    (stmt : StmtIn) (wit : WitIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 0 stmt wit = (pure (default, prover.input (stmt, wit))) := by
  simp [Prover.runToRound]

end Execution

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

section Trivial

/-- Running the identity or trivial reduction results in the same input statement and witness, and
  empty transcript. -/
@[simp]
theorem Reduction.id_run (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).run stmt wit =
      pure ⟨⟨default, stmt, wit⟩, stmt⟩ := by
  simp [Reduction.run, Reduction.id, Prover.run, Verifier.run, Prover.id, Verifier.id]
  rfl

/-- Running the identity or trivial reduction, with logging of queries to the shared oracle,
  results in the same input statement and witness, empty transcript, and empty query logs. -/
@[simp]
theorem Reduction.id_runWithLog (stmt : StmtIn) (wit : WitIn) :
    (Reduction.id : Reduction oSpec StmtIn WitIn _ _ _).runWithLog stmt wit =
      pure ⟨⟨⟨default, stmt, wit⟩, stmt⟩, [], []⟩ := by
  simp_all only [ChallengeIdx, Challenge]
  rfl

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_run (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).run stmt oStmt wit =
      pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩⟩ := by
  simp_all only [ChallengeIdx, Challenge, run_eq_run_reduction, id_toReduction, Reduction.id_run]

/-- Running the identity or trivial oracle reduction results in the same input statement, oracle
  statement, and witness. -/
@[simp]
theorem OracleReduction.id_runWithLog (stmt : StmtIn) (oStmt : ∀ i, OStmtIn i) (wit : WitIn) :
    (OracleReduction.id : OracleReduction oSpec StmtIn OStmtIn WitIn _ _ _ _).runWithLog
      stmt oStmt wit = pure ⟨⟨default, ⟨stmt, oStmt⟩, wit⟩, ⟨stmt, oStmt⟩, [], []⟩ := by
  simp only [OracleReduction.runWithLog, OracleVerifier.run, Prover.run, OracleReduction.id,
    OracleProver.id, OracleVerifier.id, Prover.id,
    Prover.runToRound,
    monadLift_pure, pure_bind, Option.getM]
  rfl

end Trivial

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
  have : pSpec.dir 0 = .P_to_V := by simp
  split <;> rename_i hDir
  · have : Direction.P_to_V = .V_to_P := by rw [← this, hDir]
    contradiction
  · congr; funext a; congr; simp [default, Transcript.concat]; funext i
    have : i = 0 := by aesop
    rw [this]; simp [Fin.snoc]

@[simp]
theorem Prover.runToRound_one_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.runToRound 1 stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        letI newState := (← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _) challenge
        return (fun i => match i with | ⟨0, _⟩ => challenge, newState)) := by
  simp [Prover.runToRound, Prover.processRound]
  have : pSpec.dir 0 = .V_to_P := by simp
  split <;> rename_i hDir
  · -- V_to_P case: this is what we want
    congr 1
    funext challenge
    congr 1
    funext f
    simp only [default, Transcript.concat, Prod.mk.injEq]
    constructor
    · funext ⟨i, hi⟩
      have h : i = 0 := by omega
      subst h
      simp [Fin.snoc]
    · trivial
  · -- P_to_V case: contradiction
    have : Direction.V_to_P = .P_to_V := by rw [← this, hDir]
    contradiction

@[simp]
theorem Prover.run_of_verifier_first [VerifierOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let challenge ← liftComp (pSpec.getChallenge ⟨0, by simp⟩) _
        let f ← liftComp (prover.receiveChallenge ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output (f challenge)
        return ((fun i => match i with | ⟨0, _⟩ => challenge), ctxOut)) := by
  simp [Prover.run]; rfl

@[simp]
theorem Prover.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      prover.run stmt wit = (do
        let state := prover.input (stmt, wit)
        let ⟨msg, state⟩ ← liftComp (prover.sendMessage ⟨0, by simp⟩ state) _
        let ctxOut ← prover.output state
        return ((fun i => match i with | ⟨0, _⟩ => msg), ctxOut)) := by
  simp [Prover.run]; rfl

-- @[simp]
theorem Reduction.run_of_prover_first [ProverOnly pSpec] (stmt : StmtIn) (wit : WitIn)
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) :
      reduction.run stmt wit = (do
        let state := reduction.prover.input (stmt, wit)
        let ⟨msg, state⟩ ← (reduction.prover.sendMessage ⟨0, by simp⟩ state)
        let ctxOut ← reduction.prover.output state
        let transcript : pSpec.FullTranscript := fun i => match i with | ⟨0, _⟩ => msg
        let stmtOut ← (reduction.verifier.verify stmt transcript).run
        return (⟨transcript, ctxOut⟩, ← stmtOut.getM)) := by
  simp only [Reduction.run, Verifier.run]
  rw [Prover.run_of_prover_first]
  simp only [liftComp_eq_liftM, bind_assoc, pure_bind, monadLift_bind, monadLift_pure,
    monadLift_liftM_OptionT]

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
--     Fin.val_zero, Fin.coe_castSucc, Fin.val_succ, dir_apply, bind_pure_comp, getType_apply,
--     Fin.induction_two, Fin.val_one, pure_bind, map_bind, liftComp]
--   split <;> rename_i hDir0
--   · exfalso; simp only [prover_first, reduceCtorEq] at hDir0
--   split <;> rename_i hDir1
--   swap
--   · exfalso; simp only [verifier_last_of_two, reduceCtorEq] at hDir1
--   simp only [Functor.map_map, bind_map_left, default]
--   congr; funext x; congr; funext y;
--   simp only [Fin.isValue, map_bind, Functor.map_map, dir_apply, Fin.succ_one_eq_two,
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
