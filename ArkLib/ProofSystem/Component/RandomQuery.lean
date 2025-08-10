/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.LiftContext.Reduction

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

variable {ι : Type} (oSpec : OracleSpec ι) (OStatement : Type) [OracleInterface OStatement]
  [inst : SelectableType (Query OStatement)]

namespace RandomQuery

@[reducible, simp]
def StmtIn := Unit

@[reducible, simp]
def StmtOut := Query OStatement

@[reducible, simp]
def OStmtIn := fun _ : Fin 2 => OStatement

@[reducible, simp]
def OStmtOut := fun _ : Fin 2 => OStatement

@[reducible, simp]
def WitIn := Unit

@[reducible, simp]
def WitOut := Unit

/-- The input relation is that the two oracles are equal. -/
@[reducible, simp]
def relIn : Set ((StmtIn × ∀ i, OStmtIn OStatement i) × WitIn) :=
  { ⟨⟨(), oracles⟩, ()⟩ | oracles 0 = oracles 1 }

/--
The output relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `oracle a q = oracle b q`.
-/
@[reducible, simp]
def relOut : Set ((StmtOut OStatement × ∀ i, OStmtOut OStatement i) × WitOut) :=
  { ⟨⟨q, oStmt⟩, ()⟩ | oracle (oStmt 0) q = oracle (oStmt 1) q }

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

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

  receiveChallenge | ⟨0, _⟩ => fun oracles q => (oracles, q)

  output := fun (oracles, q) => ((q, oracles), ())

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

  embed := Function.Embedding.inl

  hEq := by simp

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

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `RandomQuery` oracle reduction is perfectly complete. -/
@[simp]
theorem oracleReduction_completeness (hInit : init.neverFails) :
    (oracleReduction oSpec OStatement).perfectCompleteness
      init impl (relIn OStatement) (relOut OStatement) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction, relIn, relOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨stmt, oStmt⟩ wit hOStmt
  simp [Reduction.run, Prover.run, Verifier.run, Prover.runToRound, Prover.processRound,
    OracleReduction.toReduction, OracleVerifier.toVerifier, oracleVerifier, oracleProver,
    Transcript.concat, FullTranscript.challenges, hInit]
  constructor
  -- Soon we won't have to reason about failure of `init` here.
  · intro s hs
    simp [StateT.run]
    unfold SimOracle.append
    simp [challengeQueryImpl, liftM, monadLift, MonadLift.monadLift, StateT.lift]
    have := SelectableType.probFailure_selectElem (β := Query OStatement)
    aesop
  · aesop

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q

def stateFunction [Inhabited OStatement] : (oracleVerifier oSpec OStatement).StateFunction init impl
    (relIn OStatement).language (relOut OStatement).language where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next := fun i hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr h => by
    simp_all only [Fin.reduceLast, Fin.isValue, OStmtIn, Nat.reduceAdd, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, Fin.zero_eta, Fin.castLE_refl, Matrix.cons_val_zero, eq_mp_eq_cast, cast_eq,
      StmtOut, OStmtOut, StmtIn, StateT.run'_eq, Set.language, WitOut, relOut, Set.mem_image,
      Set.mem_setOf_eq, Prod.exists, exists_const, exists_eq_right, probEvent_eq_zero_iff,
      support_bind, support_map, Set.mem_iUnion, exists_and_right, exists_prop, forall_exists_index,
      and_imp, Prod.forall]
    intro a b s hs s' hSupp
    simp [OracleVerifier.toVerifier, Verifier.run, oracleVerifier] at hSupp
    simp [hSupp.1, h]

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
  | 1 => fun ⟨_, oracles⟩ chal _ =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q
  toFun_empty := fun stmt => by simp
  toFun_next := fun i hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr _ h => by
    simp_all [oracleVerifier, OracleVerifier.toVerifier, Verifier.run]

variable [Fintype (Query OStatement)] [DecidableEq (Response OStatement)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

/-- The `RandomQuery` oracle reduction is round-by-round knowledge sound.

  The key fact governing the soundness of this reduction is a property of the form
  `∀ a b : OStatement, a ≠ b → #{q | OracleInterface.oracle a q = OracleInterface.oracle b q} ≤ d`.
  In other words, the oracle instance has distance at most `d`.
-/
@[simp]
theorem oracleVerifier_rbrKnowledgeSoundness [Nonempty (Query OStatement)]
    {d : ℕ} (hDist : OracleInterface.distanceLE OStatement d) :
    (oracleVerifier oSpec OStatement).rbrKnowledgeSoundness init impl
      (relIn OStatement)
      (relOut OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨fun _ => Unit, rbrExtractor oSpec OStatement,
    knowledgeStateFunction oSpec OStatement, ?_⟩
  intro ⟨_, oracles⟩ _ rbrP i
  have : i = ⟨0, by simp⟩ := by aesop
  subst i
  dsimp at oracles
  simp [Prover.runWithLogToRound, Prover.runToRound, rbrExtractor, knowledgeStateFunction]
  unfold SimOracle.append
  simp [challengeQueryImpl]
  classical
  simp only [probEvent_bind_eq_tsum]
  simp [ProtocolSpec.Transcript.concat, Fin.snoc, default]
  unfold Function.comp
  dsimp
  calc
  _ ≤ ((Finset.card
    {x | ¬oracles 0 = oracles 1 ∧ oracle (oracles 0) x = oracle (oracles 1) x} : ENNReal) /
        (Fintype.card (Query OStatement))) := by
    rw [ENNReal.tsum_mul_right]
    grw [OracleComp.tsum_probOutput_le_one]
    simp
  _ ≤ (((d : ℝ≥0) / (Fintype.card (Query OStatement)))) := by
    gcongr
    simp
    by_cases hOracles : oracles 0 = oracles 1
    · simp [hOracles]
    · simp [hOracles]
      exact hDist (oracles 0) (oracles 1) hOracles
  _ = _ := by
    refine (ENNReal.toNNReal_eq_toNNReal_iff' ?_ ?_).mp ?_
    · simp; intro h'; apply ENNReal.div_eq_top.mp at h'; simp at h'
    · simp; intro h'; apply ENNReal.div_eq_top.mp at h'; simp at h'
    · simp

end RandomQuery

namespace RandomQueryWithResponse

/-!
  Random query where we throw away the second oracle, and replace with the response
-/

@[reducible, simp]
def StmtIn := Unit

@[reducible, simp]
def StmtOut := Query OStatement × Response OStatement

@[reducible, simp]
def OStmtIn := fun _ : Fin 2 => OStatement

@[reducible, simp]
def OStmtOut := fun _ : Unit => OStatement

@[reducible, simp]
def WitIn := Unit

@[reducible, simp]
def WitOut := Unit

@[reducible, simp]
def relIn : (StmtIn × ∀ i, OStmtIn OStatement i) → WitIn → Prop := fun ⟨(), oracles⟩ () =>
  oracles 0 = oracles 1

/--
The final relation states that the first oracle `oStmt ()` agrees with the response `r` at the query
`q`.
-/
@[reducible, simp]
def relOut : (StmtOut OStatement × ∀ i, OStmtOut OStatement i) → WitOut → Prop :=
  fun ⟨⟨q, r⟩, oStmt⟩ () => oracle (oStmt ()) q = r

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

instance : ∀ i, OracleInterface ((pSpec OStatement).Message i) | ⟨0, h⟩ => nomatch h
@[reducible, simp] instance : ∀ i, SelectableType ((pSpec OStatement).Challenge i)
  | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

-- Perhaps it's time to test out the liftContext infrastructure

-- instance : OracleContext.Lens
--     RandomQuery.StmtIn (RandomQuery.StmtOut OStatement)
--     StmtIn (StmtOut OStatement)
--     (RandomQuery.OStmtIn OStatement) (RandomQuery.OStmtOut OStatement)
--     (OStmtIn OStatement) (OStmtOut OStatement)
--     RandomQuery.WitIn RandomQuery.WitOut
--     WitIn WitOut where
--   projStmt := fun () => ()
--   liftStmt := fun () => ()
--   projOStmt := fun i => fun () => ()
--   simOStmt := fun i => fun () => ()
--   liftOStmt := fun i => fun () => ()
--   projWit := fun () => ()
--   liftWit := fun () => ()

end RandomQueryWithResponse
