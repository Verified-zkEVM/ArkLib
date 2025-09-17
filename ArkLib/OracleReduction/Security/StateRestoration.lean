/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # State-Restoration Security Definitions

  This file defines state-restoration security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type}

namespace Prover

/-- The type for the **state-restoration** prover in the soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, and a full transcript of interaction.

This is different from the state-restoration prover type in the knowledge soundness game, which
additionally needs to output an output witness. -/
def StateRestoration.Soundness (oSpec : OracleSpec ι) (StmtIn : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages)

/-- The type for the **state-restoration** prover in the knowledge soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, a full transcript of interaction, and an output witness.

Note that the output witness is an addition compared to the state-restoration soundness prover
type. -/
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι) (StmtIn WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages × WitOut)

end Prover

namespace OracleProver

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the soundness
  game.

This is a wrapper around the state-restoration prover type in the soundness game for the associated
reduction. -/
@[reducible]
def StateRestoration.Soundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.Soundness oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the knowledge
  soundness game.

This is a wrapper around the state-restoration prover type in the knowledge soundness game for the
associated reduction. -/
@[reducible]
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitOut : Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.KnowledgeSoundness oSpec (StmtIn × (∀ i, OStmtIn i)) WitOut pSpec

end OracleProver

namespace Extractor

/-- A straightline extractor for state-restoration. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → -- input statement
  WitOut → -- output witness
  pSpec.FullTranscript → -- transcript
  QueryLog (oSpec ++ₒ (srChallengeOracle StmtIn pSpec)) → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OracleComp oSpec WitIn -- an oracle computation that outputs an input witness

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SelectableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
  (impl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))

/-- The state-restoration game for soundness. Basically a wrapper around the state-restoration
  prover to derive the full transcript from the messages output by the prover, with the challenges
  computed from the state-restoration oracle. -/
def srSoundnessGame (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn) := do
  let ⟨stmtIn, messages⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn⟩

/-- The state-restoration game for knowledge soundness. Basically a wrapper around the
    state-restoration prover (for knowledge soundness) to derive the full transcript from the
    messages output by the prover, with the challenges computed from the state-restoration oracle.
-/
def srKnowledgeSoundnessGame
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn × WitOut) := do
  let ⟨stmtIn, messages, witOut⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn, witOut⟩

namespace Verifier

namespace StateRestoration

/-- State-restoration soundness -/
def soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec,
  [ fun ⟨stmtIn, stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn |
    do
    (simulateQ (impl ++ₛₒ srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
        <| (do
    let ⟨transcript, stmtIn⟩ ← srSoundnessGame srProver
    let stmtOut ← liftComp (verifier.run stmtIn transcript) _
    return (stmtIn, stmtOut))).run' (← init)
  ] ≤ srSoundnessError

/-- State-restoration knowledge soundness (w/ straightline extractor). -/
def knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec,
    [ fun ⟨stmtIn, witIn, stmtOut, witOut⟩ =>
        (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn |
      do
      (simulateQ (impl ++ₛₒ srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
          <| (do
            let ⟨transcript, stmtIn, witOut⟩ ← srKnowledgeSoundnessGame srProver
            let stmtOut ← liftComp (verifier.run stmtIn transcript) _
            let witIn ← srExtractor stmtIn witOut transcript default default
            return (stmtIn, witIn, stmtOut, witOut))).run' (← init)
    ] ≤ srKnowledgeSoundnessError

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
