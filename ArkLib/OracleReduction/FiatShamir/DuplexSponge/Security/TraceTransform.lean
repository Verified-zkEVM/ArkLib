/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead

/-!
# Trace Transformations

This file contains the trace transformations for duplex sponge Fiat-Shamir, following Section 5.5 in
the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasChallengeSize pSpec]

-- def stdTrace

/-- The transformation of basic Fiat-Shamir query-answer traces (from both prover and verifier)
to duplex-sponge Fiat-Shamir query-answer traces (from both prover and verifier)

Note: this goes the opposite direction as the prover transformation -/
def basicToDuplexSpongeFSTrace
    (proveQueryLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))
    (verifyQueryLog : QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) :
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U) :=
  sorry

alias d2STrace := basicToDuplexSpongeFSTrace

end DuplexSpongeFS
