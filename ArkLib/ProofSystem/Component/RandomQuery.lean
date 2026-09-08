/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.LiftContext.OracleReduction

/-!
# Simple Oracle Reduction: Random Query

This describes a one-round oracle reduction to randomly test whether two oracles (of the same type,
with same oracle interface) are equal.

In more details: there is no witness nor public statement. There are two `OStatement`s, `a` and `b`,
of the same type. The relation is `a = b`.
   - The verifier samples random `q : OracleInterface.Query` for that type and sends it to the
     prover.
   - The verifier does not do any checks.
   - The output relation is that `a` and `b` are equal at that query.
   - We also support a variant where it's `a.query q = r` where `r` is the response, discarding `b`.
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [O : OracleInterface OStatement]
  [inst : SampleableType (Query OStatement)]

namespace RandomQuery

@[reducible, simp] def StmtIn := Unit
@[reducible, simp] def StmtOut := Query OStatement

@[reducible, simp] def OStmtIn := fun _ : Fin 2 => OStatement
@[reducible, simp] def OStmtOut := fun _ : Fin 2 => OStatement

@[reducible, simp] def WitIn := Unit
@[reducible, simp] def WitOut := Unit

/-- The input relation is that the two oracles are equal. -/
@[reducible, simp]
def relIn : Set ((StmtIn × ∀ i, OStmtIn OStatement i) × WitIn) :=
  { ⟨⟨(), oracles⟩, ()⟩ | oracles 0 = oracles 1 }

/--
The output relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `answer a q = answer b q`.
-/
@[reducible, simp]
def relOut : Set ((StmtOut OStatement × ∀ i, OStmtOut OStatement i) × WitOut) :=
  { ⟨⟨q, oStmt⟩, ()⟩ | answer (oStmt 0) q = answer (oStmt 1) q }

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Query OStatement]⟩

@[reducible]
def outputEmbed : Fin 2 ↪ Fin 2 ⊕ (pSpec OStatement).MessageIdx :=
  ⟨Sum.inl, Sum.inl_injective⟩

/--
The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`,
and outputs the same `q`.

We keep track of `(a, b)` in the prover's state, along with the single random query `q`.
-/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Unit (fun _ : Fin 2 => OStatement) Unit
    (Query OStatement) (fun _ : Fin 2 => OStatement) Unit (pSpec OStatement) where

  PrvState
  | 0 => ∀ _ : Fin 2, OStatement
  | 1 => (∀ _ : Fin 2, OStatement) × (Query OStatement)

  input := fun x => x.1.2

  sendMessage | ⟨0, h⟩ => nomatch h

  receiveChallenge | ⟨0, _⟩ => fun oracles => pure fun q => (oracles, q)

  output := fun (oracles, q) => pure ((q, oracles), ())

/-- The `RandomQuery` oracle prover has pure output: it repackages the received challenge and
  the oracles, with no oracle query. -/
instance instOutputIsPure : (oracleProver oSpec OStatement).OutputIsPure := ⟨_, fun _ => rfl⟩

/--
The oracle verifier simply returns the challenge, and performs no checks.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Unit (fun _ : Fin 2 => OStatement)
    (Query OStatement) (fun _ : Fin 2 => OStatement) (pSpec OStatement) where

  verify := fun _ chal => do
    let q : Query OStatement := chal ⟨0, rfl⟩
    pure q

  outputOracle := .inl {
    embed := outputEmbed OStatement
    hEq := by intro i; exact rfl
    outputInterface_heq := by
      intro i
      change HEq O O
      rfl }

omit inst in
@[simp]
theorem oracleVerifier_materializeOutput (challenges : (pSpec OStatement).Challenges)
    (oStmt : ∀ i, OStmtIn OStatement i) (messages : (pSpec OStatement).Messages) :
    (oracleVerifier oSpec OStatement).materializeOutput challenges oStmt messages = oStmt := by
  funext i
  change (match outputEmbed OStatement i with
    | Sum.inl j => _
    | Sum.inr j => isEmptyElim j) = oStmt i
  rw [show outputEmbed OStatement i = Sum.inl i from rfl]
  rfl

/--
Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction:
the input oracles are `(a, b)`, and the output oracles are the same `(a, b)`
its output statement also contains the challenge `q`.
-/
@[inline, specialize]
def oracleReduction :
    OracleReduction oSpec Unit (fun _ : Fin 2 => OStatement) Unit
    (Query OStatement) (fun _ : Fin 2 => OStatement) Unit (pSpec OStatement) where
  prover := oracleProver oSpec OStatement
  verifier := oracleVerifier oSpec OStatement

instance : VerifierOnly (pSpec OStatement) where
  verifier_first' := by simp

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `RandomQuery` oracle reduction is perfectly complete. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec OStatement).perfectCompleteness
      init impl (relIn OStatement) (relOut OStatement) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction, relIn, relOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hOStmt
  have hEq : oStmt 0 = oStmt 1 := hOStmt
  simp only [OracleReduction.toReduction, Reduction.run,
    Prover.run_of_verifier_first, oracleProver, oracleVerifier,
    OracleVerifier.toVerifier, Verifier.run]
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  simp only [OracleComp.liftComp_pure, ← OracleComp.liftComp_eq_liftM, pure_bind]
  erw [simulateQ_bind]
  erw [simulateQ_bind]
  simp only [QueryImpl.addLift_def, monadLift_bind, monadLift_pure, simulateQ_pure,
    bind_assoc, pure_bind]
  erw [simulateQ_bind]
  simp only [Challenge, ChallengeIdx, simulateQ_pure, OptionT.run,
    FullTranscript.challenges, map_pure, Option.getM, bind_assoc, pure_bind]
  erw [simulateQ_query]
  simp only [StmtOut, OStmtOut, WitOut, Fin.isValue, Fin.vcons_of_one, ChallengeIdx,
    Challenge, ofPFunctor_toPFunctor, QueryImpl.liftTarget_self, MessageIdx,
    Message, bind_map_left, StateT.run'_eq, StateT.run_bind, map_bind, OptionT.mk_bind,
    Set.mem_ofPred_eq, probEvent_eq_one_iff, probFailure_bind_eq_zero_iff,
    OptionT.probFailure_liftM, probFailure_eq_zero, OptionT.support_liftM,
    Prod.forall, true_and, support_bind, Set.mem_iUnion, OptionT.mem_support_iff,
    OptionT.run_mk, support_map, Set.mem_image, Prod.exists, exists_and_right,
    exists_eq_right, exists_prop, forall_exists_index, and_imp, Prod.mk.injEq]
  constructor <;> intro <;> intro <;> intro <;> intro
  all_goals try erw [simulateQ_bind]
  all_goals simp only [monadLift, MonadLift.monadLift, liftM]
  all_goals simp only [OptionT.run]
  all_goals try erw [simulateQ_pure]
  all_goals try simp_all only [pure_bind, OptionT.probFailure_eq, OptionT.run,
    probFailure_eq_zero]
  · rw [show OptionT.mk = id from rfl]
    simp only [ChallengeIdx, Fin.vcons_of_one, Challenge, Fin.isValue, input_query,
      cont_query, id_eq, zero_add, probOutput_eq_zero_iff, support_map,
      Set.mem_image, Prod.exists, exists_and_right, exists_eq_right, not_exists]
    intro
    erw [simulateQ_pure]
    simp only [Fin.isValue, StmtIn, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and,
      not_false_eq_true, implies_true]
  · intro a b x hx x_1 hx1 x_2 x_3
    erw [simulateQ_bind]
    simp only [OptionT.lift]
    erw [simulateQ_pure]
    simp only [StateT.run, pure_bind]
    rintro ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨?_, rfl, ?_⟩ <;> congr 1

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   answer (oracles 0) q = answer (oracles 1) q

def stateFunction [Inhabited OStatement] : (oracleVerifier oSpec OStatement).StateFunction init impl
    (relIn OStatement).language (relOut OStatement).language where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal => by
    let q := chal ⟨0, by aesop⟩
    change Query OStatement at q
    exact answer (oracles 0) q = answer (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next | 0 => fun hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr h => by
    -- The verifier deterministically returns `(tr 0, oStmt)`. The output is in `relOut.language`
    -- iff `answer (oStmt 0) (tr 0) = answer (oStmt 1) (tr 0)`, but the hypothesis `h` says exactly
    -- the opposite for the last-round state function `toFun 1`.
    rw [probEvent_eq_zero_iff]
    intro x hx
    rw [OptionT.mem_support_iff] at hx
    -- Unfold the verifier-run inside `hx`.
    simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk,
      support_bind, Set.mem_iUnion] at hx
    rw [oracleVerifier_materializeOutput] at hx
    simp only [oracleVerifier] at hx
    obtain ⟨s, _, hx⟩ := hx
    -- The inner `simulateQ (simOracle2 ...) (pure ...)` reduces via `simulateQ_pure` and
    -- absorbs the outer `pure (stmtOut, ...)`.
    erw [simulateQ_pure] at hx
    -- Now hx : some x ∈ support ((pure (some (tr.challenges ⟨0,_⟩, fun i => oStmt i))).run' s)
    -- `pure` in `StateT σ ProbComp` unfolds via `StateT.run_pure`, then `map_pure` and
    -- `support_pure`.
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
      Set.mem_singleton_iff, Option.map_some, Option.some.injEq] at hx
    subst x
    -- Now goal: `(tr.challenges ⟨0, _⟩, oStmt) ∉ relOut.language`. The state function `h` at
    -- last round denies `answer (oStmt 0) (tr 0) = answer (oStmt 1) (tr 0)`, which is what
    -- being in `relOut.language` would require (witness is `Unit`).
    simp only [Set.not_mem_language_iff]
    intro wit hMem
    simp only [relOut, Set.mem_ofPred_eq] at hMem
    exact h hMem

/-- The round-by-round extractor is trivial since the output witness is `Unit`. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (StmtIn × (∀ _ : Fin 2, OStatement)) WitIn WitOut (pSpec OStatement) (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- The knowledge state function for the `RandomQuery` oracle reduction. -/
def knowledgeStateFunction :
    (oracleVerifier oSpec OStatement).KnowledgeStateFunction init impl
    (relIn OStatement) (relOut OStatement) (rbrExtractor oSpec OStatement) where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal _ => by
    let q := chal ⟨0, by aesop⟩
    change Query OStatement at q
    exact answer (oracles 0) q = answer (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next | 0 => fun hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr witOut => by
    -- The verifier deterministically returns `(tr 0, oStmt)`. If the output is in `relOut` for some
    -- witness `witOut : Unit`, then `answer (oStmt 0) (tr 0) = answer (oStmt 1) (tr 0)`, exactly
    -- what `toFun 1 _ tr ()` asserts.
    intro h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hRel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk,
      support_bind, Set.mem_iUnion] at hx
    rw [oracleVerifier_materializeOutput] at hx
    simp only [oracleVerifier] at hx
    obtain ⟨s, _, hx⟩ := hx
    erw [simulateQ_pure] at hx
    simp only [StateT.run'_eq, StateT.run_pure, map_pure, support_pure,
      Set.mem_singleton_iff, Option.map_some, Option.some.injEq] at hx
    subst x
    -- Now `hRel : ((tr.challenges ⟨0, _⟩, oStmt), witOut) ∈ relOut`.
    simp only [relOut, Set.mem_ofPred_eq] at hRel
    exact hRel

variable [Fintype (Query OStatement)] [∀ q, DecidableEq (O.toOC.spec q)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

/-- The `RandomQuery` oracle reduction is round-by-round knowledge sound.

  The key fact governing the soundness of this reduction is a property of the form
  `∀ a b : OStatement, a ≠ b → #{q | oracle a q = oracle b q} ≤ d`.
  In other words, the oracle instance has distance at most `d`.
-/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness [Nonempty (Query OStatement)]
    {d : ℕ} (hDist : distanceLE O d) :
    (oracleVerifier oSpec OStatement).rbrKnowledgeSoundness init impl
      (relIn OStatement)
      (relOut OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  apply Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
  refine ⟨fun _ => Unit, rbrExtractor oSpec OStatement,
    knowledgeStateFunction oSpec OStatement, ?_⟩
  rintro ⟨stmt, oracles⟩ i transcript
  have hi : i = ⟨0, by simp⟩ := by aesop
  subst i
  have htr : transcript = fun j => Fin.elim0 j := by
    funext j
    exact Fin.elim0 j
  rw [htr]
  dsimp [knowledgeStateFunction, rbrExtractor, pSpec]
  simp only [exists_const]
  rcases Classical.em (oracles 0 = oracles 1) with hOracles | hOracles
  · simp [hOracles]
  · simp only [hOracles, not_false_eq_true, true_and]
    let decPred : DecidablePred (fun q : Query OStatement =>
        answer (oracles 0) q = answer (oracles 1) q) := fun q =>
      (inferInstance : DecidableEq (O.toOC.spec q))
        (answer (oracles 0) q) (answer (oracles 1) q)
    have hconcat (challenge : Query OStatement) :
        @ProtocolSpec.Transcript.concat 1 (pSpec OStatement) (0 : Fin 1) challenge
          (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1) = challenge := by
      exact ProtocolSpec.Transcript.concat_zero (pSpec := pSpec OStatement) challenge
        (fun j : Fin 0 => Fin.elim0 j)
    have hpred :
        (fun challenge : Query OStatement =>
          answer (oracles 0) (@ProtocolSpec.Transcript.concat 1 (pSpec OStatement)
            (0 : Fin 1) challenge (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1)) =
          answer (oracles 1) (@ProtocolSpec.Transcript.concat 1 (pSpec OStatement)
            (0 : Fin 1) challenge (fun j : Fin 0 => Fin.elim0 j) (0 : Fin 1))) =
        fun q => answer (oracles 0) q = answer (oracles 1) q := by
      funext challenge
      rw [hconcat]
    rw [hpred]
    rw [@probEvent_uniformSample (Query OStatement) inst _ _ decPred]
    have hfilter : Finset.univ.filter (fun q =>
        answer (oracles 0) q = answer (oracles 1) q) =
        O.agreementQueries (oracles 0) (oracles 1) := by
      ext q
      simp
    rw [hfilter]
    have hdenom : (Fintype.card (Query OStatement) : ℝ≥0) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [ENNReal.coe_div hdenom]
    apply ENNReal.div_le_div_right
    · have hcard := hDist (oracles 0) (oracles 1) hOracles
      exact Nat.cast_le.mpr hcard

end RandomQuery

-- namespace RandomQueryAndReduceClaim

-- /-!
--   Random query where we throw away the second oracle, and replace with the response:
--   - The input relation is `{ ⟨⟨_, 𝒪⟩, _⟩ | 𝒪 0 = 𝒪 1 }`.
--   - The output relation is `{ ⟨⟨q, r⟩, 𝒪⟩, _⟩ | oracle (𝒪 0) q = r }`.
--   - The (oracle) verifier sends a single random query `q` to the prover, queries the oracle
--     `𝒪 1` at `q` to get response `r`, returns `(q, r)` as the output statement, and drops
--     `𝒪 1` from the output oracle statement.

--   This is just the concatenation of `RandomQuery` and `ReduceClaim`.
-- -/

-- @[reducible, simp] def StmtIn := Unit
-- @[reducible, simp] def StmtOut := Query OStatement × Response OStatement

-- @[reducible, simp] def OStmtIn := fun _ : Fin 2 => OStatement
-- @[reducible, simp] def OStmtOut := fun _ : Fin 1 => OStatement

-- @[reducible, simp] def WitIn := Unit
-- @[reducible, simp] def WitOut := Unit

-- @[reducible, simp]
-- def relIn : (StmtIn × ∀ i, OStmtIn OStatement i) → WitIn → Prop := fun ⟨(), oracles⟩ () =>
--   oracles 0 = oracles 1

-- /--
-- The final relation states that the first oracle `oStmt ()` agrees with the response `r` at the
-- query `q`.
-- -/
-- @[reducible, simp]
-- def relOut : (StmtOut OStatement × ∀ i, OStmtOut OStatement i) → WitOut → Prop :=
--   fun ⟨⟨q, r⟩, oStmt⟩ () => answer (oStmt 0) q = r

-- -- @[reducible]
-- -- def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

-- -- instance : ∀ i, OracleInterface ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
-- -- @[reducible, simp] instance : ∀ i, SampleableType ((pSpec OStatement).Challenge i)
-- --   | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

-- -- instance : OracleContext.Lens
-- --     RandomQuery.StmtIn (RandomQuery.StmtOut OStatement)
-- --     StmtIn (StmtOut OStatement)
-- --     (RandomQuery.OStmtIn OStatement) (RandomQuery.OStmtOut OStatement)
-- --     (OStmtIn OStatement) (OStmtOut OStatement)
-- --     RandomQuery.WitIn RandomQuery.WitOut
-- --     WitIn WitOut where
-- --   projStmt := fun () => ()
-- --   liftStmt := fun () => ()
-- --   projOStmt := fun i => fun () => ()
-- --   simulateOutputQuery := fun i => fun () => ()
-- --   liftOStmt := fun i => fun () => ()
-- --   projWit := fun () => ()
-- --   liftWit := fun () => ()

-- end RandomQueryAndReduceClaim
