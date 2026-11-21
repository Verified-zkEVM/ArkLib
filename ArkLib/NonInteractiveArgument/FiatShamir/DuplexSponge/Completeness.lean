/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Construction
import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Completeness.Perfect

/-!
# Completeness of duplex-sponge Fiat–Shamir

Public completeness theorem for the salt-length-parameterized construction.
The proof lives in `Completeness/Perfect.lean` and uses execution laws from `Security/Proofs/`.

## Main results

* `DuplexSpongeFS.duplex_sponge_fiat_shamir_perfect_completeness` proves perfect completeness with
  a shared fixed sponge realization and a stateless ambient oracle.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

/-- **[CO25, Construction 4.4]** — Perfect completeness of DSFS for interactive proofs.

The ambient handler is stateless; the sampled public sponge realization is shared and fixed.
The interactive premise uses its own initialization. The transformed prover returns `(true, ())`
and omits terminal sponge operations. Any salt sampler over the ambient oracle is allowed. -/
theorem duplex_sponge_fiat_shamir_perfect_completeness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn U σ : Type} [SpongeUnit U] [SpongeSize U] [Codec pSpec U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    (δ : ℕ) (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (P : Proof oSpec StmtIn WitIn pSpec) (sampleSalt : OracleComp oSpec (Vector U δ))
    (relation : Set (StmtIn × WitIn))
    (h : P.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relation) :
    (P.duplexSpongeFiatShamir (U := U) δ sampleSalt).perfectCompleteness
      (D_𝔖.sample StmtIn U) (D_𝔖.withOracle impl) relation acceptRejectRel :=
  ProofExecution.perfectCompleteness δ init impl P sampleSalt relation h

end DuplexSpongeFS
