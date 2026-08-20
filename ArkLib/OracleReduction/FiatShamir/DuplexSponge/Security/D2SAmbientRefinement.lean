/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame

/-!
# Ambient-oracle refinement for the revised Hyb₁ executor

The paper's query budgets count only the duplex-sponge requests of the
malicious prover.  An ambient oracle may therefore be queried arbitrarily often.
This file isolates the semantic fact needed by the live Hyb₀--Hyb₁ coupling:
after a fixed encoded-challenge table has been installed, the revised D2F
interpreter passes ambient queries through the same `oSpecImpl` on both sides.
They are consequently free in the later selective identical-until-bad argument.

No probability bound is proved here.  The results are exact equalities of the
stateful stopping interpreters, including the normal state, memo, and stopping
reason.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : CodecCore pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]

/-- The fixed-table outer implementation for a revised Hyb₁ execution with an arbitrary
ambient oracle.  The ambient branch is exactly `oSpecImpl`; the other three branches are the
same fixed `D_Σ`/unit/uniform implementation as the ambient-free direct executor. -/
noncomputable def hyb1AmbientOuterImpl
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl
      (oSpec + d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      ProbComp
  | .inl q => oSpecImpl q
  | .inr q =>
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec)) q

/-- The lazy-table presentation of the Hyb₁ outer oracle.  Only encoded-challenge queries
thread the `gSpec` cache; ambient, unit, and uniform-sampling queries are executed unchanged in
the base probabilistic monad.  This is the executable H₁ interface used by the H₀--H₁ coupling.
The equality with the eagerly sampled `D_Σ` table is proved below rather than assumed. -/
noncomputable def hyb1LazyOuterImpl
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      (StateT (gSpec (U := U) StmtIn pSpec δ).QueryCache ProbComp) := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _
  letI (q : (gSpec (U := U) StmtIn pSpec δ).Domain) :
      SampleableType ((gSpec (U := U) StmtIn pSpec δ).Range q) := by
    rcases q with ⟨i, key⟩
    change SampleableType (Vector U (challengeSize (pSpec := pSpec) i))
    infer_instance
  exact fun
    | .inl q => StateT.lift (oSpecImpl q)
    | .inr (.inl q) => OracleSpec.randomOracle q
    | .inr (.inr (.inl q)) => StateT.lift (d2sUnitSampleImpl (U := U) q)
    | .inr (.inr (.inr q)) => StateT.lift ((QueryImpl.id' unifSpec) q)

/-- The eager-table continuation corresponding to a lazy H₁ cache.  On a `g` request it reads
the cached answer when present and otherwise the corresponding coordinate of `table`; the other
three oracle families are exactly the same as in `hyb1LazyOuterImpl`. -/
noncomputable def hyb1LazyOverlayOuterImpl
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      ProbComp := by
  classical
  exact fun
    | .inl q => oSpecImpl q
    | .inr (.inl q) => pure (OracleComp.dependentTableExtending cache table q)
    | .inr (.inr (.inl q)) => d2sUnitSampleImpl (U := U) q
    | .inr (.inr (.inr q)) => (QueryImpl.id' unifSpec) q

/-- Extending a lazy `g` cache after a miss is equivalent to updating the one corresponding
coordinate of the eager table.  The equality is over the complete outer handler, so it remains
valid after arbitrary ambient and auxiliary requests interleave with later `g` requests. -/
lemma hyb1LazyOverlayOuterImpl_cacheQuery_eq_update
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache)
    (table : OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))
    [DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain]
    {q : (gSpec (U := U) StmtIn pSpec δ).Domain}
    (hcache : cache q = none) (answer : (gSpec (U := U) StmtIn pSpec δ).Range q) :
    hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) oSpecImpl (cache.cacheQuery q answer) table =
      hyb1LazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl cache (Function.update table q answer) := by
  classical
  apply QueryImpl.ext
  rintro (q' | q' | q' | q')
  · rfl
  · simp only [hyb1LazyOverlayOuterImpl]
    rw [OracleComp.dependentTableExtending_cacheQuery,
      ← OracleComp.dependentTableExtending_update_of_none cache table hcache answer]
  · rfl
  · rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- The lazy H₁ handler passes ambient requests through literally unchanged. -/
@[simp]
lemma hyb1LazyOuterImpl_ambient
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : oSpec.Domain) (cache : (gSpec (U := U) StmtIn pSpec δ).QueryCache) :
    (hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) oSpecImpl (Sum.inl q)).run cache =
      (fun answer => (answer, cache)) <$> oSpecImpl q :=
  rfl

/-- Hyb₁ with its encoded challenge function sampled lazily from an initially empty cache.
This is an executable intermediate game, not a new public hybrid: its forthcoming eager/lazy
refinement theorem identifies it exactly with `hyb1Revised`.  Keeping the cache explicit is what
allows the H₀--H₁ coupling to expose one common encoded value only when its key is first reached.
-/
noncomputable def hyb1RevisedLazy
    {T_H : Type} {T_P : Type}
    [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (Option <| BasicFiatShamirGameOutput
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (Salt := Salt)) := by
  classical
  exact
    hybridGameDistRevised
      (δ := δ) (Salt := Salt)
      (T_H := T_H) (T_P := T_P)
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U)
      (init := pure ∅)
      (impl := hyb1LazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) V
      maliciousProver
      (hyb1Line4Trace
        (δ := δ) (Salt := Salt)
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- Ambient calls are forwarded unchanged.  This is the free-query premise for the selective
identical-until-bad theorem: no bound on ambient calls is required. -/
@[simp]
lemma hyb1AmbientOuterImpl_ambient
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (q : oSpec.Domain) :
    hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) oSpecImpl kSigma (Sum.inl q) = oSpecImpl q :=
  rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [DecidableEq StmtIn] [DecidableEq U] in
/-- The D2S branch is the fixed encoded table together with the common unit and uniform
samplers.  Later coupling lemmas use this equation only on charged D2S requests. -/
@[simp]
lemma hyb1AmbientOuterImpl_d2s
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (q : (d2sQueryOracles (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)).Domain) :
    hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) oSpecImpl kSigma (Sum.inr q) =
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec)) q :=
  rfl

omit [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)] in
/-- Fixing the Hyb₁ challenge table commutes with the lossless inner D2S handler even when the
surrounding execution has an ambient oracle.  The inner handler never issues an ambient request;
this equality makes that syntactic fact explicit instead of treating `[]ₒ` as a hidden premise. -/
lemma hyb1AmbientD2fStoppingD2SInner_mapped_eq_direct
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    QueryImpl.mapStateTExceptTBase
      (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl kSigma)
      (d2fStoppingD2SInner (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)) normal) =
      hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma := by
  apply QueryImpl.ext
  rintro (gq | aux | aux)
  · funext memo
    apply ExceptT.ext
    simpa [QueryImpl.mapStateTExceptTBase, hyb1AmbientOuterImpl,
      hyb1StoppingD2SDirect, hyb1GImpl] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma gq) memo).symm
  · funext memo
    apply ExceptT.ext
    simp only [QueryImpl.mapStateTExceptTBase, hyb1StoppingD2SDirect]
    calc
      (StateT.mk (fun state => ExceptT.mk
          ((fun answer => Except.ok (answer, state)) <$> d2sUnitSampleImpl aux)) memo).run =
          (fun answer => Except.ok (answer, memo)) <$> d2sUnitSampleImpl aux := rfl
      _ = (StateT.lift (ExceptT.lift (d2sUnitSampleImpl aux)) memo).run :=
        (QueryImpl.run_stateT_lift_exceptT_lift
          (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          (d2sUnitSampleImpl (U := U) aux) memo).symm
  · funext memo
    apply ExceptT.ext
    simpa [QueryImpl.mapStateTExceptTBase, hyb1AmbientOuterImpl,
      hyb1StoppingD2SDirect] using
      (QueryImpl.run_stateT_lift_exceptT_lift
        (ε := D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
        ((d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec) (Sum.inr aux)) memo).symm

omit [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Pushing the fixed Hyb₁ table through a complete revised D2F execution is exact with an
arbitrary ambient oracle.  This is the semantic boundary needed by the Hyb₀--Hyb₁ coupling:
the outer interpreter receives every ambient request and every D2S request in its original
order, and no ambient request is charged to the D2S query budget. -/
theorem hyb1AmbientD2fRawRevisedStopping_pushes_outer
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    {StmtOut : Type}
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    simulateQ
      (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) oSpecImpl kSigma)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        residual normal PUnit.unit) =
      (((simulateQ
        (QueryImpl.mapStateTStateTExceptTBase
          (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) oSpecImpl kSigma)
          (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))))
        residual).run normal).run PUnit.unit).run := by
  exact QueryImpl.simulateQ_mapStateTStateTExceptTBase_run
    (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) oSpecImpl kSigma)
    (d2fOuterImplRevisedStopping (T_H := T_H) (T_P := T_P) (oSpec := oSpec)
      (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)))
    residual normal PUnit.unit

end DuplexSpongeFS.KeyLemma
