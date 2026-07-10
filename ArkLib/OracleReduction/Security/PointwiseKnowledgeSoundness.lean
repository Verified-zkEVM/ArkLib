/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Pointwise round-by-round knowledge soundness

This file defines a pointwise variant of round-by-round knowledge soundness. The input statement,
round, and partial transcript are fixed universally; probability is taken only over the next fresh
verifier challenge. In particular, the definition does not sample a transcript prefix by running a
prover and does not expose a prover query log.

The existing `Verifier.rbrKnowledgeSoundness` predicate instead averages over the transcript prefix
produced by a prover execution. Neither predicate is claimed here to imply the other.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

/-- The bad knowledge-state transition at a fixed statement, round, partial transcript, and next
challenge. It occurs when some post-round intermediate witness makes the state true after the
challenge, while the witness extracted back across that challenge makes the preceding state false.
-/
def rbrKnowledgeTransitionEvent
    {WitMid : Fin (n + 1) → Type}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (stmtIn : StmtIn) (i : pSpec.ChallengeIdx)
    (transcript : pSpec.Transcript i.1.castSucc) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid,
    ¬kSF i.1.castSucc stmtIn transcript
        (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
      kSF i.1.succ stmtIn (transcript.concat challenge) witMid

/-- A concrete false-to-true knowledge-state transition witnesses the bad transition event. -/
theorem rbrKnowledgeTransitionEvent_of_states
    {WitMid : Fin (n + 1) → Type}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (stmtIn : StmtIn) (i : pSpec.ChallengeIdx)
    (transcript : pSpec.Transcript i.1.castSucc) (challenge : pSpec.Challenge i)
    (witMid : WitMid i.1.succ)
    (hpre : ¬kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid))
    (hpost : kSF i.1.succ stmtIn (transcript.concat challenge) witMid) :
    rbrKnowledgeTransitionEvent init impl extractor kSF stmtIn i transcript challenge :=
  ⟨witMid, hpre, hpost⟩

/-- Pointwise round-by-round knowledge soundness.

There are common intermediate-witness types, an extractor, and a knowledge-state function such
that, for every input statement, challenge round, and fixed partial transcript, the probability of
a false-to-true knowledge-state transition over only the next fresh verifier challenge is bounded
by `rbrKnowledgeError i`.
-/
def rbrKnowledgeSoundnessPointwise
    [∀ i, SampleableType (pSpec.Challenge i)]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : pSpec.Transcript i.1.castSucc,
    Pr[rbrKnowledgeTransitionEvent init impl extractor kSF stmtIn i transcript |
      simulateQ challengeQueryImpl (pSpec.getChallenge i)] ≤ rbrKnowledgeError i

end Verifier
