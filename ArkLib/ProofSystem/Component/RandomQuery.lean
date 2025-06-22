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
  [inst : VCVCompatible (Query OStatement)]

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
def relIn : (StmtIn × ∀ i, OStmtIn OStatement i) → WitIn → Prop := fun ⟨(), oracles⟩ () =>
  oracles 0 = oracles 1

/--
The output relation states that if the verifier's single query was `q`, then
`a` and `b` agree on that `q`, i.e. `oracle a q = oracle b q`.
-/
@[reducible, simp]
def relOut : (StmtOut OStatement × ∀ i, OStmtOut OStatement i) → WitOut → Prop :=
  fun ⟨q, oStmt⟩ () => oracle (oStmt 0) q = oracle (oStmt 1) q

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.V_to_P, Query OStatement)]

/--
The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`,
and outputs the same `q`.

We keep track of `(a, b)` in the prover's state, along with the single random query `q`.
-/
@[inline, specialize]
def oracleProver : OracleProver (pSpec OStatement) oSpec Unit Unit
    (Query OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where

  PrvState
  | 0 => ∀ _ : Fin 2, OStatement
  | 1 => (∀ _ : Fin 2, OStatement) × (Query OStatement)

  input := fun ⟨(), oracles⟩ () => oracles

  sendMessage | ⟨0, h⟩ => nomatch h

  receiveChallenge | ⟨0, _⟩ => fun oracles q => (oracles, q)

  output := fun (oracles, q) => ((q, oracles), ())

/--
The oracle verifier simply returns the challenge, and performs no checks.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier (pSpec OStatement) oSpec Unit (Query OStatement)
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where

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
  OracleReduction (pSpec OStatement) oSpec Unit Unit
    (Query OStatement) Unit
    (fun _ : Fin 2 => OStatement) (fun _ : Fin 2 => OStatement) where
  prover := oracleProver oSpec OStatement
  verifier := oracleVerifier oSpec OStatement

variable [oSpec.FiniteRange]

/-- The `RandomQuery` oracle reduction is perfectly complete. -/
@[simp]
theorem oracleReduction_completeness : (oracleReduction oSpec OStatement).perfectCompleteness
    (relIn OStatement) (relOut OStatement) := by
  simp [OracleReduction.perfectCompleteness, oracleReduction, relIn, relOut]
  intro _ oStmt _ hOStmt
  simp [Reduction.run, Prover.run, Verifier.run, Prover.runToRound, Prover.processRound,
    OracleReduction.toReduction, OracleVerifier.toVerifier, oracleVerifier, oracleProver,
    Transcript.concat, FullTranscript.challenges]
  intro q oStmt' q' oStmt'' transcript h1 h2 h3 h4
  apply congrFun at h3
  simp_all [Fin.snoc]
  funext i; fin_cases i <;> simp_all

-- def langIn : Set (Unit × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨(), oracles⟩ =>
--   oracles 0 = oracles 1

-- def langOut : Set ((Query OStatement) × (∀ _ : Fin 2, OStatement)) := setOf fun ⟨q, oracles⟩ =>
--   OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q

def stateFunction : (oracleVerifier oSpec OStatement).StateFunction (pSpec OStatement) oSpec
    (relIn OStatement).language (relOut OStatement).language where
  toFun
  | 0 => fun ⟨_, oracles⟩ _ => oracles 0 = oracles 1
  | 1 => fun ⟨_, oracles⟩ chal =>
    let q : Query OStatement := by simpa [pSpec] using chal ⟨0, by aesop⟩
    OracleInterface.oracle (oracles 0) q = OracleInterface.oracle (oracles 1) q
  toFun_empty := fun stmt hStmt => by simp_all [relIn, Function.language]
  toFun_next := fun i hDir ⟨stmt, oStmt⟩ tr h => by simp_all
  toFun_full := fun ⟨stmt, oStmt⟩ tr h => by
    simp_all [relOut, Function.language]
    intro a b hSupp
    simp [OracleVerifier.toVerifier, Verifier.run, oracleVerifier] at hSupp
    simp [hSupp.1, hSupp.2, h]

/-- The extractor is trivial since the output witness is `Unit`. -/
def extractor : RBRExtractor (pSpec OStatement) oSpec
    (Unit × (∀ _ : Fin 2, OStatement)) Unit :=
  fun _ _ _ _ => ()

/-!
  The key fact governing the soundness of this reduction is a property of the form
  `∀ a b : OStatement, a ≠ b → #{q | OracleInterface.oracle a q = OracleInterface.oracle b q} ≤ d`.
  In other words, the oracle instance has distance at most `d`.
-/

variable [Fintype (Query OStatement)] [DecidableEq (Response OStatement)]

instance : Fintype ((pSpec OStatement).Challenge ⟨0, by simp⟩) := by
  dsimp [pSpec, ProtocolSpec.Challenge]; infer_instance

open NNReal

/-- The `RandomQuery` oracle reduction is knowledge sound. -/
@[simp]
theorem rbr_knowledge_soundness {d : ℕ} (h : OracleInterface.distanceLE OStatement d) :
    (oracleVerifier oSpec OStatement).rbrKnowledgeSoundness
      (relIn OStatement)
      (relOut OStatement)
      (fun _ => (d : ℝ≥0) / (Fintype.card (Query OStatement) : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness Verifier.rbrKnowledgeSoundness
  refine ⟨stateFunction oSpec OStatement, extractor oSpec OStatement, ?_⟩
  intro ⟨_, oracles⟩ _ rbrP i
  have : i = ⟨0, by simp⟩ := by aesop
  subst i
  dsimp at oracles
  simp [Prover.runWithLogToRound, Prover.runToRound, stateFunction]
  classical
  unfold Function.comp
  simp [probEvent_liftM_eq_mul_inv, ProtocolSpec.Transcript.concat, Fin.snoc, default]
  rw [div_eq_mul_inv]
  gcongr
  simp [Finset.filter_and]
  split_ifs with hOracles <;> simp
  exact h (oracles 0) (oracles 1) hOracles

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
@[reducible, simp] instance : ∀ i, VCVCompatible ((pSpec OStatement).Challenge i)
  | ⟨0, _⟩ => by dsimp [pSpec, ProtocolSpec.Challenge]; exact inst

-- Perhaps it's time to test out the liftContext infrastructure

-- instance : OracleContextLens
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
