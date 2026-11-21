/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Completeness.SingleSalt

/-!
# Completeness of canonical Fiat–Shamir

For both the statement-keyed and single-salt transforms, fixed verifier-message functions
preserve perfect completeness and a shared lazy random oracle preserves the completeness
error bound. The unsalted statements allow a stateful ambient oracle. The single-salt
statements allow an ambient salt sampler under a stateless ambient oracle.

## Main results

* `fiatShamir_perfectCompleteness` proves perfect completeness for a fixed challenge table.
* `fiatShamir_completeness_randomOracle` preserves the completeness bound under a shared lazy
  random oracle.
* `canonicalFiatShamir_perfectCompleteness` and `canonicalFiatShamir_completeness_randomOracle`
  give the corresponding guarantees for the single-salt construction.
* `InteractiveProtocol.compileFiatShamirBytes_completeness` covers serialized proofs.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

/-- Statement-keyed Fiat–Shamir preserves perfect completeness for each fixed challenge table. -/
theorem fiatShamir_perfectCompleteness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    [samples : ∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (hR : R.perfectCompleteness init impl relIn relOut)
    (f : QueryImpl (srVerifierMessageOracle StmtIn pSpec) Id) :
    R.fiatShamir.perfectCompleteness (do return (← init, f))
      (impl.addLift fsChallengeQueryImpl') relIn relOut :=
  fiatShamirWithContext_perfectCompleteness init impl relIn relOut R id hR f

/-- Completeness error is preserved by a lazy random challenge oracle shared by the
transformed prover and verifier. The cache starts empty; distinct round indices make every
honest prover query fresh, and reconstruction replays the cached answers. Decidable equality
of query keys suffices, with no finite statement, message, or base-state assumption. -/
theorem fiatShamir_completeness_randomOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type}
    [samples : ∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    [DecidableEq (srVerifierMessageOracle StmtIn pSpec).Domain]
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) (ε : ℝ≥0)
    (hR : R.completeness init impl relIn relOut ε) :
    R.fiatShamir.completeness
      (do return (← init, (∅ : (srVerifierMessageOracle StmtIn pSpec).QueryCache)))
      (FiatShamir.fsRandomOracleImpl impl) relIn relOut ε :=
  fiatShamirWithContext_completeness_randomOracle init impl relIn relOut R id ε hR

section Salted

section FixedOracle

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}

variable [VCVCompatible Salt]
variable [∀ i, SampleableType (pSpec.Challenge i)]

/-- **Perfect completeness of canonical Fiat–Shamir (CO25, Construction 3.17).**
A perfectly complete interactive reduction remains perfectly complete under a stateless ambient
handler and one fixed, consistently answered verifier-message function sampled at initialization.
The function distribution and the salt sampler need not be uniform. This is a probability-one
result; arbitrary completeness error is preserved under the random-oracle assumptions of
`canonicalFiatShamir_completeness_randomOracle`. -/
theorem canonicalFiatShamir_perfectCompleteness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.compileFiatShamir sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT (QueryImpl (fsVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut :=
  CanonicalFS.perfectCompleteness init impl fsInit R sampleSalt relIn relOut h

/-- Perfect completeness of canonical Fiat-Shamir for every configured salt length.
The private ambient sampler is invoked once per NARG string. -/
theorem fiatShamirSalted_perfectCompleteness {σ U : Type} [VCVCompatible U] (saltLength : ℕ)
    (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
    (fsInit : ProbComp
      (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (h : R.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relIn relOut) :
    (R.fiatShamirSalted saltLength sampleSalt).perfectCompleteness fsInit
      ((impl.liftTarget (StateT
        (QueryImpl (fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp)).addLift fsChallengeQueryImpl') relIn relOut := by
  exact canonicalFiatShamir_perfectCompleteness init impl fsInit R sampleSalt relIn relOut h

end FixedOracle

/-- Single-salt Fiat–Shamir preserves its completeness bound under a shared random oracle.
The salt sampler uses only the stateless ambient oracles and is called once per NARG string. -/
theorem canonicalFiatShamir_completeness_randomOracle
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut Salt : Type} [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (StmtIn × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn) (Salt := Salt) impl)
      relIn relOut ε :=
  CanonicalFS.completeness_randomOracle impl R sampleSalt relIn relOut ε h

/-- Single-salt Fiat–Shamir preserves the completeness bound at every salt length. -/
theorem fiatShamirSalted_completeness
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut U : Type} [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain]
    (impl : QueryImpl oSpec ProbComp)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) (ε : ℝ≥0)
    (h : R.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relIn relOut ε) :
    (R.fiatShamirSalted saltLength sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := StmtIn)
        (Salt := Vector U saltLength) impl) relIn relOut ε :=
  canonicalFiatShamir_completeness_randomOracle impl R sampleSalt relIn relOut ε h

section Application

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U : Type}

/-- The typed single-salt Fiat–Shamir argument preserves the interactive completeness bound. -/
theorem InteractiveProtocol.compileFiatShamir_completeness [VCVCompatible Salt]
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Salt) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec Salt)
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamir sampleSalt).completeness
      (pure ((), (∅ : (srVerifierMessageOracle (Statement × Salt) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement) (Salt := Salt) impl)
      relation ε :=
  CanonicalFS.compileFiatShamir_application_completeness P impl sampleSalt relation ε h

/-- Canonical byte serialization adds no completeness error to single-salt Fiat–Shamir. -/
theorem InteractiveProtocol.compileFiatShamirBytes_completeness [VCVCompatible U] (saltLength : ℕ)
    [∀ i, SampleableType (pSpec.Challenge i)]
    [DecidableEq (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).Domain]
    (P : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (impl : QueryImpl oSpec ProbComp) (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (relation : Set (Statement × Witness)) (ε : ℝ≥0)
    (h : P.completeness (pure ()) (impl.liftTarget (StateT Unit ProbComp)) relation ε) :
    (P.compileFiatShamirBytes saltLength serializer sampleSalt).completeness
      (pure ((),
        (∅ : (srVerifierMessageOracle (Statement × Vector U saltLength) pSpec).QueryCache)))
      (CanonicalFS.randomOracleImpl (pSpec := pSpec) (StmtIn := Statement)
        (Salt := Vector U saltLength) impl) relation ε :=
  CanonicalFS.compileFiatShamirBytes_completeness saltLength P serializer impl sampleSalt
    relation ε h

end Application

end Salted
