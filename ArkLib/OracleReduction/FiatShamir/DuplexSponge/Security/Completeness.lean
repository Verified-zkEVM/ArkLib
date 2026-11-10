/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Completeness

/-!
# Completeness of duplex-sponge Fiat–Shamir

Public security endpoint for the salt-length-parameterized construction.
Supporting execution laws and hybrid arguments live in `Security/Proofs/`.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

open ProofExecution

section SaltedCompleteness

set_option backward.isDefEq.respectTransparency false in
/-- **[CO25, Construction 4.4]** — Perfect completeness of DSFS for interactive proofs.

The ambient handler is stateless; the sampled public sponge realization is shared and fixed.
The interactive premise uses its own initialization. The transformed prover returns `(true, ())`
and omits terminal sponge operations. Any salt sampler over the ambient oracle is allowed. -/
theorem duplex_sponge_fiat_shamir_perfect_completeness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn U σ : Type} [SpongeUnit U] [SpongeSize] [Codec pSpec U]
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, SampleableType (pSpec.Challenge i)]
    (δ : ℕ) (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (P : Proof oSpec StmtIn WitIn pSpec) (sampleSalt : OracleComp oSpec (Vector U δ))
    (relation : Set (StmtIn × WitIn))
    (h : P.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relation) :
    (P.duplexSpongeFiatShamir (U := U) δ sampleSalt).perfectCompleteness
      (D_𝔖.sample StmtIn U) (D_𝔖.withOracle impl) relation acceptRejectRel := by
  apply perfectCompleteness_of_fixedOracle _ init impl relation
  intro answer
  apply (Proof.perfectCompleteness_stateless_iff _ init _ relation).mpr
  intro stmt wit hrel result hresult
  have he : challengeQueryImpl (pSpec := (⟨!v[.P_to_V],
      !v[DSFSTypedNARGString (pSpec := pSpec) (U := U) δ]⟩ : ProtocolSpec 1)) =
      (fun q => isEmptyElim q.1) := by
    funext q
    exact isEmptyElim q.1
  simp only [he] at hresult
  rw [proof_run_sample δ P impl answer sampleSalt stmt wit] at hresult
  simp only [mem_support_bind_iff] at hresult
  obtain ⟨salt, _hsalt, hresult⟩ := hresult
  have hc := perfectCompleteness_fixedOracle salt P init impl answer relation h
  have hold := (Proof.perfectCompleteness_stateless_iff _ init _ relation).mp hc stmt wit hrel
  simp only [he] at hold
  exact hold result hresult

end SaltedCompleteness

end DuplexSpongeFS
