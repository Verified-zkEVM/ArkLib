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

/-- A **state-restoration** prover in a reduction is a modified prover that has query access to
  challenge oracles that can return the `i`-th challenge, for all `i : pSpec.ChallengeIdx`, given
  the input statement and the transcript up to that point.

  It further takes in the input statement and witness, and outputs a full transcript of interaction,
  along with the output statement and witness. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec))
      (StmtIn × (StmtOut × WitOut) × pSpec.Messages)

end Prover

namespace OracleProver

@[reducible]
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration oSpec
    (StmtIn × (∀ i, OStmtIn i)) (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

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

namespace Prover.StateRestoration

/-- The state-restoration game. Basically a wrapper around the state-restoration prover to
derive the full transcript from the messages output by the prover, with the challenges computed
from the state-restoration oracle. -/
def srGame (P : Prover.StateRestoration oSpec StmtIn StmtOut WitOut pSpec) :
    OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec))
      (StmtIn × WitOut × pSpec.FullTranscript) := do
  let ⟨stmtIn, (_, witOut), messages⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨stmtIn, witOut, transcript⟩

end Prover.StateRestoration

namespace Verifier

namespace StateRestoration

/-- State-restoration soundness -/
def soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration oSpec StmtIn StmtOut WitOut pSpec,
  [ fun ⟨stmtIn, stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn |
    do
    (simulateQ (impl ++ₛₒ srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
        <| (do
    let ⟨stmtIn, _, transcript⟩ ← srProver.srGame
    let stmtOut ← liftComp (verifier.run stmtIn transcript) _
    return (stmtIn, stmtOut))).run' (← init)
  ] ≤ srSoundnessError

-- State-restoration knowledge soundness (w/ straightline extractor)
def knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration oSpec StmtIn StmtOut WitOut pSpec,
    [ fun ⟨stmtIn, witIn, stmtOut, witOut⟩ =>
        (stmtOut, witOut) ∈ relOut ∧ (stmtIn, witIn) ∉ relIn |
      do
      (simulateQ (impl ++ₛₒ srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
          <| (do
            let ⟨stmtIn, witOut, transcript⟩ ← srProver.srGame
            let stmtOut ← liftComp (verifier.run stmtIn transcript) _
            let witIn ← srExtractor stmtIn witOut transcript default default
            return (stmtIn, witIn, stmtOut, witOut))).run' (← init)
    ] ≤ srKnowledgeSoundnessError

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
