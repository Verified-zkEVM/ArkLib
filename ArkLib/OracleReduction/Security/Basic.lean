/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Execution

/-!
  # Security Definitions for (Oracle) Reductions

  This file defines basic security notions for (oracle) reductions:

  - (Perfect) Completeness

  - (Straightline) (Knowledge) Soundness

  - (Honest-verifier) Zero-knowledge

  For each security notion, we provide a typeclass for it, so that security can be synthesized
  automatically with verified transformations.

  See other files in the same directory for more refined soundness notions (i.e. state-restoration,
  round-by-round, rewinding, etc.)
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SelectableType (pSpec.Challenge i)]
  -- Note: `σ` may depend on the previous data, like `StmtIn`, `pSpec`, and so on
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-
TODO: the "right" factoring for the security definitions are the following:

- We have a two-layer interpretation approach: first, interpret the oracle queries into some monad
  `m` which admits a monad morphism into `PMF` (i.e. `HasEvalDist`); then we interpret the resulting
  monad into `PMF`.

  This does not preclude `m` from being the same oracle computation type, but more interesting
  possibilities are possible, such as `m = ReaderT ρ` for lazy sampling of the shared oracle.

  Another possibility: given `OracleInterface OStmt`, we have an interpretation map

  `interpOStmt : OracleComp (oSpec + [OStmt]ₒ) →ᵐ ReaderT OStmt (OracleComp oSpec)`

- Relations should be `Stmt → Wit → m Prop`, with `m` being the intermediate monad. When `m` is the
  result of `interpOStmt` above, for instance, we get `Stmt → Wit → OStmt → Prop`, which is what we
  want. Same for when we interpret `oSpec` into `Reader (oSpec.FunctionType)`; we then have
  `Stmt → Wit → oSpec.FunctionType → Prop`, which allows us to define relations that rely
  on the (randomly sampled, at the beginning) values of the shared oracle.
-/

namespace Reduction

section Completeness

/-- A reduction satisfies **completeness** with regards to:
  - an initialization function `init : ProbComp σ` for some ambient state `σ`,
  - a stateful query implementation `impl` (in terms of `StateT σ ProbComp`)
  for the shared oracles `oSpec`,
  - an input relation `relIn` and output relation `relOut` (represented as sets), and
  - an error `completenessError ≥ 0`,

  if for all valid statement-witness pair `(stmtIn, witIn) ∈ relIn`, the execution between the
  honest prover and the honest verifier will result in a tuple `((prvStmtOut, witOut), stmtOut)`
  such that

  - `(stmtOut, witOut) ∈ relOut`, (the output statement-witness pair is valid) and
  - `prvStmtOut = stmtOut`, (the output statements are the same from both prover and verifier)

  except with probability `completenessError`.
-/
def completeness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
    [fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ => (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut
    | do (simulateQ (impl ++ₛₒ challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          <| reduction.run stmtIn witIn).run' (← init)] ≥ 1 - completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0

/-- Type class for completeness for a reduction -/
class IsComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    where
  completenessError : ℝ≥0
  is_complete : completeness init impl relIn relOut reduction completenessError

/-- Type class for perfect completeness for a reduction -/
class IsPerfectComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  is_perfect_complete : perfectCompleteness init impl relIn relOut reduction

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}

instance [reduction.IsPerfectComplete init impl relIn relOut] :
    IsComplete init impl relIn relOut reduction where
  completenessError := 0
  is_complete := IsPerfectComplete.is_perfect_complete

/-- If a reduction satisfies completeness with error `ε₁`, then it satisfies completeness with error
  `ε₂` for all `ε₂ ≥ ε₁`. -/
theorem completeness_error_mono {ε₁ ε₂ : ℝ≥0} (hε : ε₁ ≤ ε₂) :
      completeness init impl relIn relOut reduction ε₁ →
        completeness init impl relIn relOut reduction ε₂ := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hstmtIn
  have := h stmtIn witIn hstmtIn
  refine ge_trans this ?_
  exact tsub_le_tsub_left (by simp [hε]) 1

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relIn'` that is a subset of `relIn`. -/
theorem completeness_relIn_mono {ε : ℝ≥0} {relIn' : Set (StmtIn × WitIn)}
    (hrelIn : relIn' ⊆ relIn) :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn' relOut reduction ε := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hStmtIn
  exact h stmtIn witIn (hrelIn hStmtIn)

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relOut'` that is a superset of `relOut`.
-/
theorem completeness_relOut_mono {ε : ℝ≥0} {relOut' : Set (StmtOut × WitOut)}
    (hrelOut : relOut ⊆ relOut') :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn relOut' reduction ε := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hstmtIn
  refine ge_trans ?_ (h stmtIn witIn hstmtIn)
  refine probEvent_mono ?_
  rintro _ _ ⟨h1, h2⟩
  exact ⟨hrelOut h1, h2⟩

/-- Perfect completeness means that the probability of the reduction outputting a valid
  statement-witness pair is _exactly_ 1 (instead of at least `1 - 0`). -/
@[simp]
theorem perfectCompleteness_eq_prob_one :
    reduction.perfectCompleteness init impl relIn relOut ↔
      ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
        [fun ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ =>
          (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut
        | do (simulateQ (impl ++ₛₒ challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
            <| reduction.run stmtIn witIn).run' (← init)] = 1 := by
  refine forall_congr' fun stmtIn => forall_congr' fun stmtOut => forall_congr' fun _ => ?_
  rw [ENNReal.coe_zero, tsub_zero, ge_iff_le, OracleComp.one_le_probEvent_iff,
    probEvent_eq_one_iff, Prod.forall]

-- /-- For a reduction without shared oracles (i.e. `oSpec = []ₒ`), perfect completeness occurs
--   when the reduction produces satisfying statement-witness pairs for all possible challenges. -/
-- theorem perfectCompleteness_forall_challenge [reduction.IsDeterministic] :
--       reduction.perfectCompleteness relIn relOut ↔
--         ∀ stmtIn witIn, relIn stmtIn witIn → ∀ chals : ∀ i, pSpec.Challenge i,
--           reduction.runWithChallenges stmtIn witIn chals = 1 := by

end Completeness

end Reduction

section Soundness

/-! We define 3 variants each of soundness and knowledge soundness:

  1. (Plain) soundness
  2. Knowledge soundness

  For adaptivity, we may want to seed the definition with a term
    `chooseStmtIn : OracleComp oSpec StmtIn`
  (though this is essentially the same as quantifying over all `stmtIn : StmtIn`).

  Note: all soundness definitions are really defined for the **verifier** only. The (honest)
prover does not feature into the definitions.
-/

namespace Extractor

/- We define different types of extractors here -/

variable (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)

/-- A straightline, deterministic, non-oracle-querying extractor takes in the output witness, the
  initial statement, the IOR transcript, and the query logs from the prover and verifier, and
  returns a corresponding initial witness.

  Note that the extractor does not need to take in the output statement, since it can be derived
  via re-running the verifier on the initial statement, the transcript, and the verifier's query
  log.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def Straightline :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- reduction transcript
  QueryLog oSpec → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OracleComp oSpec WitIn -- input witness

end Extractor

namespace Verifier

/-- A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input
  language `langIn : Set StmtIn` and output language `langOut : Set StmtOut` if:
  - for all (malicious) provers with arbitrary types for `WitIn`, `WitOut`,
  - for all arbitrary `witIn`,
  - for all input statement `stmtIn ∉ langIn`,

  the execution between the prover and the honest verifier will result in an output statement
  `stmtOut` that is in `langOut` is at most `soundnessError`.

  (technical note: since execution may fail, this is _not_ equivalent to saying that
  `stmtOut ∉ langOut` with probability at least `1 - soundnessError`)
-/
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    letI reduction := Reduction.mk prover verifier
    [fun ⟨_, stmtOut⟩ => stmtOut ∈ langOut
    | do (simulateQ (impl ++ₛₒ challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        <| reduction.run stmtIn witIn).run' (← init)] ≤ soundnessError

/-- Type class for soundness for a verifier -/
class IsSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  soundnessError : ℝ≥0
  is_sound : soundness init impl langIn langOut verifier soundnessError

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive challenges and send messages), and be able to observe & simulate the prover's
-- oracle queries

/-- A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and
  with respect to input relation `relIn` and output relation `relOut` if:
  - there exists a straightline extractor `E`, such that
  - for all input statement `stmtIn`, witness `witIn`, and (malicious) prover `prover`,
  - if the execution with the honest verifier results in a pair `(stmtOut, witOut)`,
  - and the extractor produces some `witIn'`,

  then the probability that `(stmtIn, witIn')` is not valid and yet `(stmtOut, witOut)` is valid
  is at most `knowledgeError`.
-/
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    letI reduction := Reduction.mk prover verifier
    [fun ⟨stmtIn, witIn, stmtOut, witOut⟩ =>
      (stmtIn, witIn) ∉ relIn ∧ (stmtOut, witOut) ∈ relOut
    | do
      let s ← init
      (simulateQ (impl ++ₛₒ challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        <| do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩ ←
        reduction.runWithLog stmtIn witIn
      let extractedWitIn ←
        liftComp (extractor stmtIn witOut transcript proveQueryLog.fst verifyQueryLog) _
      return (stmtIn, extractedWitIn, stmtOut, witOut)).run' s] ≤ knowledgeError

/-- Type class for knowledge soundness for a verifier -/
class IsKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  knowledgeError : ℝ≥0
  is_knowledge_sound : knowledgeSoundness init impl relIn relOut verifier knowledgeError

/-- An extractor is **monotone** if its success probability on a given query log is the same as
  the success probability on any extension of that query log. -/
class Extractor.Straightline.IsMonotone
    (relIn : Set (StmtIn × WitIn))
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    [oSpec.FiniteRange]
    where
  is_monotone : ∀ witOut stmtIn transcript, ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder probability for now, probably need to consider the whole game
    [fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₁ verifyQueryLog₁] ≤
    [fun witIn => (stmtIn, witIn) ∈ relIn |
      E stmtIn witOut transcript proveQueryLog₂ verifyQueryLog₂]
    -- Pr[extraction game succeeds on proveQueryLog₁, verifyQueryLog₁]
    -- ≤ Pr[extraction game succeeds on proveQueryLog₂, verifyQueryLog₂]

end Verifier

end Soundness

namespace Reduction

section ZeroKnowledge

/-- A simulator for a reduction needs to produce the same transcript as the prover (but potentially
  all at once, instead of sequentially). We also grant the simulator the power to program the shared
  oracles `oSpec` -/
structure Simulator (oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  SimState : Type
  oracleSim : SimOracle.Stateful oSpec oSpec SimState
  proverSim : StmtIn → StateT SimState (OracleComp oSpec) pSpec.FullTranscript

/-
  We define honest-verifier zero-knowledge as follows:
  There exists a simulator such that for all (malicious) verifier, the distributions of transcripts
  generated by the simulator and the interaction between the verifier and the prover are
  (statistically) indistinguishable.
-/
-- def zeroKnowledge (prover : Prover pSpec oSpec) : Prop :=
--   ∃ simulator : Simulator,
--   ∀ verifier : Verifier pSpec oSpec,
--   ∀ stmtIn : Statement,
--   ∀ witIn : Witness,
--   relIn.isValid stmtIn witIn = true →
--     let result := (Reduction.mk prover verifier).run stmtIn witIn
--     let transcript := Prod.fst <$> Prod.snd <$> result
--     let simTranscript := simulator
--     -- let prob := spec.relOut.isValid' <$> output
--     sorry

end ZeroKnowledge

end Reduction

/-! Completeness and soundness are the same as for non-oracle reductions. Only zero-knowledge is
  different (but we haven't defined it yet) -/

open Reduction

section OracleProtocol

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleReduction

/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
def completeness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness init impl relIn relOut oracleReduction.toReduction completenessError

/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
def perfectCompleteness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Prop :=
  Reduction.perfectCompleteness init impl relIn relOut oracleReduction.toReduction

end OracleReduction

namespace OracleVerifier

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
def soundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn langOut soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
def knowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relIn relOut knowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)] {Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SelectableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

/-! All security notions are inherited from `Reduction`, with the output relation specialized to the
  trivial accept/reject one: `fun accRej _ => accRej`. -/

open Reduction

@[reducible, simp]
def completeness (relation : Set (Statement × Witness)) (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.completeness init impl relation acceptRejectRel proof completenessError

@[reducible, simp]
def perfectCompleteness (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.perfectCompleteness init impl relation acceptRejectRel proof

@[reducible, simp]
def soundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.soundness init impl langIn acceptRejectRel.language soundnessError

@[reducible, simp]
def knowledgeSoundness (relation : Set (Statement × Bool))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.knowledgeSoundness init impl relation acceptRejectRel knowledgeError

end Proof

namespace OracleProof

open OracleReduction

/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def completeness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec)
    (completenessError : ℝ≥0) : Prop :=
  OracleReduction.completeness init impl
    relation acceptRejectOracleRel oracleProof completenessError

/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def perfectCompleteness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec) :
      Prop :=
  OracleReduction.perfectCompleteness init impl relation acceptRejectOracleRel oracleProof

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def soundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn acceptRejectOracleRel.language soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def knowledgeSoundness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleVerifier oSpec Statement OStatement Bool (fun _ : Empty => Unit) pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relation acceptRejectOracleRel knowledgeError

end OracleProof

section Trivial

-- We show that the trivial (oracle) reduction is perfectly complete, sound, and knowledge sound.

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem Reduction.id_perfectCompleteness {rel : Set (StmtIn × WitIn)} (hInit : init.neverFails) :
    (Reduction.id : Reduction oSpec _ _ _ _ _).perfectCompleteness init impl rel rel := by
  simp [hInit]
  aesop

/-- The identity / trivial verifier is perfectly sound. -/
@[simp]
theorem Verifier.id_soundness {lang : Set StmtIn} :
    (Verifier.id : Verifier oSpec _ _ _).soundness init impl lang lang 0 := by
  simp [Verifier.soundness, Verifier.id, Reduction.run, Verifier.run]
  aesop

/-- The straightline extractor for the identity / trivial reduction, which just returns the input
  witness. -/
@[reducible]
def Extractor.Straightline.id : Extractor.Straightline oSpec StmtIn WitIn WitIn !p[] :=
  fun _ witOut _ _ _ => pure witOut

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp]
theorem Verifier.id_knowledgeSoundness {rel : Set (StmtIn × WitIn)} :
    (Verifier.id : Verifier oSpec _ _ _).knowledgeSoundness init impl rel rel 0 := by
  refine ⟨Extractor.Straightline.id, ?_⟩
  simp only [Extractor.Straightline.id, Verifier.id, Reduction.runWithLog, Verifier.run]
  simp only [liftM, monadLift, MonadLift.monadLift, liftComp]
  simp only [simulateQ_pure, WriterT.run, StateT.run']
  simp
  intro stmtIn witIn prover stmtIn' witIn' stmtIn'' witIn'' s hs s' hSupport hRel'
  -- simp only [support_bind]
  -- aesop
  sorry

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem OracleReduction.id_perfectCompleteness
    {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    (hInit : init.neverFails) :
    (OracleReduction.id : OracleReduction oSpec _ _ _ _ _ _ _).perfectCompleteness
      init impl rel rel := by
  simp [perfectCompleteness, hInit]
  aesop

/-- The identity / trivial verifier is perfectly sound. -/
@[simp]
theorem OracleVerifier.id_soundness {lang : Set (StmtIn × ∀ i, OStmtIn i)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).soundness
      init impl lang lang 0 := by
  simp [OracleVerifier.soundness]

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp]
theorem OracleVerifier.id_knowledgeSoundness {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).knowledgeSoundness
      init impl rel rel 0 := by
  simp [OracleVerifier.knowledgeSoundness]

end Trivial

end
