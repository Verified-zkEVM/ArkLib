/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù, Quang Dao, Yuxi Zheng
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical.Security.Proofs.Soundness

/-!
# Soundness and knowledge soundness of canonical Fiat–Shamir

These theorems transfer state-restoration security to the construction in
`Canonical/Construction.lean`. The public-coin versions cover families indexed by the
security parameter and by a bound on the statement size.

The proofs are in `Canonical/Security/Proofs/Soundness.lean`.

## Main results

* `canonicalFiatShamir_soundness` derives adaptive NARG soundness from state-restoration soundness.
* `canonicalFiatShamir_knowledgeSoundness` builds a NARG extractor from an SR extractor and
  preserves the error bound at every query budget.
* `CanonicalFS.publicCoin_soundness` and `CanonicalFS.publicCoin_knowledge_soundness`
  specialize these guarantees to the public-coin protocol families.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

section StateRestorationTransfer

open ProtocolSpec OracleComp OracleSpec OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

namespace CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible StmtIn] in
/-- Transport a supplied SR extractor, without choosing it after the query budget.
The conclusion uses the NARG extractor interface documented above. Repackaging preserves all
queries, and the selector implication transfers the same `IsQueryBoundP` budget.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem canonicalFiatShamir_knowledgeSoundness_of_fixedExtractor
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    (h_sr_ks : ∀ P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
        fsInit fsImpl privateImpl E
        relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
        V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
          (Verifier.compileFiatShamir (Salt := Salt) V)
          (fsSRDelegatingNARGExtractor E) P}[nargKSFailEvent relIn langOut out] ≤ ε :=
  CanonicalFS.SoundnessProofs.transferFixedExtractor
    privateSpec privateImpl V relIn langOut fsInit fsImpl E
    queryBoundSelector srQueryBoundSelector hCount t ε h_sr_ks

end CanonicalFS

section CanonicalSecurity

open CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  in
/-- **[CO25, Theorem 3.18]** Single-salt FS soundness from IP SR-soundness.

If `V` has state-restoration soundness for `langIn` in the game with salt space `Salt`, with error
`ε`, then `Verifier.compileFiatShamir V` has adaptive NARG soundness in the ROM with error `ε`.

The premise and conclusion use `IsQueryBoundP` with the same natural-number budget `t`.
The selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`: every query counted in the
SR premise is also counted in the FS conclusion. For the paper-facing formulation, choose
`srQueryBoundSelector = publicQuerySelector Verifier.StateRestoration.isSrChallengeMove` and
`queryBoundSelector = nargPublicQuery`.
To count only queries for verifier messages, choose the move selector on both sides. Repackaging
preserves queries exactly, so neither choice increases the budget or the soundness error.
Adapted from **[snarg-book, Theorem 14.3.1]** to the single-salt construction. -/
theorem canonicalFiatShamir_soundness_withSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : ∀ P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.soundnessFailureProb (Salt := Salt) fsInit fsImpl privateImpl
        langIn langOut V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGSoundnessExp fsInit (fsImpl.addLift srChallengeQueryImpl')
          privateImpl (Verifier.compileFiatShamir (Salt := Salt) V) P}[
            nargSoundFailEvent langIn langOut out] ≤ ε :=
  CanonicalFS.SoundnessProofs.transferSoundnessWithSampler
    privateSpec privateImpl V langIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- **[CO25, Theorem 3.19]** — One SR extractor yields
one NARG extractor for every natural-number query budget, with the same error function.
The query selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`, as in the
soundness theorem.
The NARG extractor interface permits randomness and both logs; it does not establish the
deterministic, prover-trace-only contract of Definition 3.6.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem canonicalFiatShamir_knowledgeSoundness_withSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : ∃ E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt),
      ∀ t, ∀ P : Prover.StateRestoration.KnowledgeSoundness
        oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
        P.IsQueryBoundP srQueryBoundSelector t →
        Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
          fsInit fsImpl privateImpl E
          relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
          V P ≤ ε t) :
    ∃ extractor : StmtIn → FSSaltedNARGString pSpec Salt →
      QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) →
      OptionT (OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))
        WitIn,
      ∀ t, ∀ P : OracleComp ((oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
        (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
        Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
            (fsImpl.addLift srChallengeQueryImpl') privateImpl
            ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
            (Verifier.compileFiatShamir (Salt := Salt) V) extractor P}[
              nargKSFailEvent relIn langOut out] ≤ ε t :=
  CanonicalFS.SoundnessProofs.transferKnowledgeSoundnessWithSampler
    privateSpec privateImpl V relIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount ε hSR

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS soundness with standard private randomness. -/
theorem canonicalFiatShamir_soundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (Verifier.compileFiatShamir (Salt := Salt) V) langIn langOut queryBoundSelector t ε :=
  CanonicalFS.SoundnessProofs.transferSoundness V langIn langOut fsInit fsImpl queryBoundSelector
    srQueryBoundSelector hCount t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS knowledge soundness with standard private randomness. -/
theorem canonicalFiatShamir_knowledgeSoundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Salt)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id)
              ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (Verifier.compileFiatShamir (Salt := Salt) V) relIn langOut queryBoundSelector ε :=
  CanonicalFS.SoundnessProofs.transferKnowledgeSoundness
    V relIn langOut fsInit fsImpl queryBoundSelector
    srQueryBoundSelector hCount ε hSR

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem fiatShamir_soundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp
      (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (V.fiatShamirSalted (U := U) saltLength) langIn langOut queryBoundSelector t ε :=
  CanonicalFS.SoundnessProofs.saltLengthSoundness
    saltLength V langIn langOut fsInit fsImpl queryBoundSelector
    srQueryBoundSelector hCount t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Knowledge soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem fiatShamir_knowledgeSoundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp
      (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id)
        ProbComp))
    (queryBoundSelector :
      (oSpec + fsVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Vector U saltLength) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl
              (srVerifierMessageOracle (StmtIn × Vector U saltLength) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (V.fiatShamirSalted (U := U) saltLength) relIn langOut queryBoundSelector ε :=
  CanonicalFS.SoundnessProofs.saltLengthKnowledgeSoundness saltLength V relIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount ε hSR

end CanonicalSecurity

end StateRestorationTransfer

/-! ## Public-coin protocols without ambient oracles -/

section PublicCoin

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

namespace CanonicalFS

section Families

variable {Statement Witness : Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ sec n, ProtocolSpec (rounds sec n)}
  {Salt : ℕ → ℕ → ℕ → Type} [∀ sec s n, VCVCompatible (Salt sec s n)]
  [∀ sec n i, SampleableType ((pSpec sec n).Challenge i)]
  [∀ sec n i, VCVCompatible ((pSpec sec n).Challenge i)]
  (init : ∀ sec s n, ProbComp
    (QueryImpl (srVerifierMessageOracle (Statement × Salt sec s n) (pSpec sec n)) Id))
  (V : ∀ sec n, IP.Verifier Statement (pSpec sec n))
  (size : Statement → ℕ) (saltSize : ℕ → ℕ → ℕ)

omit [∀ sec n i, VCVCompatible ((pSpec sec n).Challenge i)] in
/-- Canonical Fiat--Shamir soundness with the full public parameters and size-restricted
state-restoration premise. The reduction preserves the error and public-query budget. -/
theorem publicCoin_soundness (language : Set Statement)
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (hSR : ∀ sec, IP.srSoundness (init sec) (fun _ n => V sec n)
      language size (error sec)) :
    NARG.adaptiveSoundness
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      language size (fun sec n t => error sec (saltSize sec n) n t) :=
  CanonicalFS.SoundnessProofs.publicCoinSoundness init V size saltSize language error hSR

/-- The canonical FS extractor constructed from a supplied state-restoration extractor family
satisfies the adaptive knowledge-soundness bound for every parameter and query budget. -/
theorem publicCoin_knowledge_soundness_withExtractor
    [DecidableEq Statement] [∀ sec n i, DecidableEq ((pSpec sec n).Message i)]
    (relation : Set (Statement × Witness))
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (E : ∀ sec s n, IP.SRExtractor Statement Witness (pSpec sec n)
      (Salt := Salt sec s n))
    (hE : ∀ sec, IP.srKnowledgeSoundnessWithExtractor
      (init sec) (fun _ n => V sec n) relation size (E sec) (error sec)) :
    NARG.adaptiveKnowledgeSoundnessWithExtractor
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n => publicCoinExtractor (E sec (saltSize sec n) n))
      (fun sec n t => error sec (saltSize sec n) n t) :=
  CanonicalFS.SoundnessProofs.publicCoinKnowledgeSoundnessWithExtractor
    init V size saltSize relation error E hE

/-- One ordinary state-restoration extractor family gives one canonical FS extractor family
for all public security parameters, instance-size bounds, and query budgets. -/
theorem publicCoin_knowledge_soundness (relation : Set (Statement × Witness))
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (hSR : ∀ sec, IP.srKnowledgeSoundness (init sec) (fun _ n => V sec n)
      relation size (error sec)) :
    NARG.adaptiveKnowledgeSoundness
      (fun sec n => []ₒ +
        fsVerifierMessageOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n t => error sec (saltSize sec n) n t) :=
  CanonicalFS.SoundnessProofs.publicCoinKnowledgeSoundness init V size saltSize relation error hSR

end Families

end CanonicalFS

end PublicCoin
