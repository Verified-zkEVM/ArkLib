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

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]

namespace Prover

/-- A **state-restoration** prover in a reduction is a modified prover that has query access to
  challenge oracles that can return the `i`-th challenge, for all `i : pSpec.ChallengeIdx`, given
  the input statement and the transcript up to that point.

  It further takes in the input statement and witness, and outputs a full transcript of interaction,
  along with the output statement and witness. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn WitIn StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → WitIn → OracleComp (oSpec ++ₒ (srChallengeOracle StmtIn pSpec))
      ((StmtOut × WitOut) × pSpec.FullTranscript)

end Prover

namespace Verifier

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [oSpec.FiniteRange] [∀ i, VCVCompatible (pSpec.Challenge i)]

namespace StateRestoration

-- /-- State-restoration soundness -/
-- def srSoundness (verifier : Verifier pSpec oSpec StmtIn StmtOut)
--     (langIn : Set StmtIn) (langOut : Set StmtOut) (SRSoundnessError : ENNReal) : Prop :=
--   ∀ stmtIn ∉ langIn,
--   ∀ witIn : WitIn,
--   ∀ Prover.StateRestoration : Prover.StateRestoration pSpec oSpec StmtIn WitIn StmtOut WitOut,
--     let ⟨_, witOut, transcript, queryLog⟩ ← (simulateQ ... (Prover.StateRestoration.run stmtIn witIn)).run
--     let stmtOut ← verifier.run stmtIn transcript
--     return stmtOut ∉ langOut

-- State-restoration knowledge soundness (w/ straightline extractor)

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
