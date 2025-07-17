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
      (StmtIn × (StmtOut × WitOut) × pSpec.FullTranscript)

end Prover

namespace OracleProver

def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration oSpec
    (StmtIn × (∀ i, OStmtIn i)) (StmtOut × (∀ i, OStmtOut i)) WitOut pSpec

end OracleProver

namespace Verifier

variable {oSpec : OracleSpec ι} (impl : QueryImpl oSpec ProbComp)
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SelectableType (pSpec.Challenge i)]

namespace StateRestoration

/-- State-restoration soundness -/
def srSoundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration oSpec StmtIn StmtOut WitOut pSpec,
  [ fun ⟨stmtIn, stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn |
    simulateQ (impl ++ₛₒ srChallengeQueryImpl.withCaching : QueryImpl _ ProbComp)
        <| (do
    let ⟨stmtIn, ⟨stmtOut, _⟩, transcript⟩ ← srProver.run
    let stmtOut ← liftComp (verifier.run stmtIn transcript) _
    return ⟨stmtIn, stmtOut⟩)
  ] ≤ srSoundnessError

-- State-restoration knowledge soundness (w/ straightline extractor)

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
