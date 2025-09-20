/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lookahead

/-!
# Prover transformation

This file contains the prover transformation (via query simulation) for the analysis of duplex
sponge Fiat-Shamir, following Section 5.4 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasChallengeSize pSpec]

/-- The query simulation between duplex sponge oracles and basic Fiat-Shamir oracles. This is then
  composed with the duplex-sponge malicious prover to obtain a basic F-S malicious prover -/
def duplexSpongeToBasicFSQueryImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (OracleComp (fsChallengeOracle StmtIn pSpec)) :=
  sorry

alias d2SQueryImpl := duplexSpongeToBasicFSQueryImpl

/-- The transformation of a duplex-sponge Fiat-Shamir malicious prover to a basic Fiat-Shamir one.

Note: this transformation needs to be an oracle computation itself -/
def duplexSpongeToBasicFSAlgo
    (P : OracleComp (oSpec ++ₒ duplexSpongeChallengeOracle StmtIn U)
    (StmtIn × pSpec.Messages)) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages) :=
  sorry

alias d2SAlgo := duplexSpongeToBasicFSAlgo

end DuplexSpongeFS
