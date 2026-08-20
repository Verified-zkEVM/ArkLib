/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SAmbientLazySampling
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb2GameCoupling

/-!
# Adaptive eager realization of the H₂ fibre oracle

The H₂ bridge samples an encoded representative from the decoder fibre of a
fixed decoded table on the first visit to a `g` key.  This module exposes the
single global fibre cache needed to show that this is equivalent to sampling
one complete fibre table before an arbitrary adaptive outer computation.

Unlike a per-step reparameterization, the cache here persists across every
ambient, prover, verifier, and auxiliary query.  Thus repeated `g` keys use
one representative throughout the whole execution.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn U : Type}
  [SpongeUnit U] [SpongeSize] [VCVCompatible U] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [∀ i, VCVCompatible (pSpec.Message i)]
  [codec : Codec pSpec U] {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  [Fintype U] [Nonempty U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]

/-- The fixed equality decision used by every H₂ fibre-cache operation.  The
lazy and eager presentations must use the same term here: `QueryCache` stores
the decision procedure in its update expression, so extensionally equivalent
classical choices are not sufficient for the adaptive coupling to unfold. -/
noncomputable def gDomainDecidableEq :
    DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
  Classical.decEq _

/-- The canonical finite representation of one decoder fibre.  Naming this
instance prevents the lazy and eager presentations from accidentally using
different implementation choices for the same uniform fibre distribution. -/
noncomputable def decodedFibreFintype
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
    Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
  rcases q with ⟨i, key⟩
  change Fintype {encoded : Vector U (challengeSize (pSpec := pSpec) i) //
    codec.decode i encoded = decoded ⟨i, key⟩}
  infer_instance

/-- Surjectivity of the codec supplies the canonical nonempty witness for a
decoder fibre. -/
noncomputable def decodedFibreNonempty
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
    Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
  rcases q with ⟨i, key⟩
  change Nonempty {encoded : Vector U (challengeSize (pSpec := pSpec) i) //
    codec.decode i encoded = decoded ⟨i, key⟩}
  exact Preliminaries.preimageNonempty (codec.decode i) (codec.decode_surjective i)
    (decoded ⟨i, key⟩)

/-- The canonical uniform sampler for one witnessed decoder fibre. -/
noncomputable def decodedFibreSampleable
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
    SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
  letI := decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI := decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  exact SampleableType.ofFintype _

/-- The named uniform draw from one decoder fibre.  Both the stateful oracle
and the eager-table proof use this term, so their coupling never depends on
definitional equality between independently inferred sampler instances. -/
noncomputable def decodedFibreUniform
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
    ProbComp ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
  letI := decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI := decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI := decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  exact $ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q

/-- The whole outer H₂ fibre oracle.  Its state is the cache of witnessed
decoder-fibre representatives, not merely a cache of their erased encodings. -/
noncomputable def hyb2FibreLazyOuterImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      (StateT
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp) := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  exact fun
    | .inl q => StateT.lift (oSpecImpl q)
    | .inr (.inl q) => fun cache =>
      match cache q with
      | some (answer : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) =>
          pure (answer.1, cache)
      | none => (fun answer :
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q =>
          (answer.1, cache.cacheQuery q answer)) <$>
          decodedFibreUniform (pSpec := pSpec) (U := U) decoded q
    | .inr (.inr (.inl q)) => StateT.lift (d2sUnitSampleImpl (U := U) q)
    | .inr (.inr (.inr q)) => StateT.lift ((QueryImpl.id' unifSpec) q)

/-- The ordinary H₂ log entry emitted by one request to the fibre-realized encoded
outer oracle.  In particular, every `g` occurrence is logged as the corresponding
decoded `e` occurrence, including a cache hit.  Thus this logger preserves the
insertion order and multiplicity of the actual H₂ `e`-log while retaining the
encoded representative that drives the D2F execution. -/
def hyb2FibreOuterEntryAsE :
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ)).Domain) →
      (oSpec + D2SChallengePlusUnitOracle
        (U := U) (gSpec (U := U) StmtIn pSpec δ)).Range q →
        QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ))
  | .inl q, answer => [⟨.inl q, answer⟩]
  | .inr (.inl q), answer => [⟨.inr (.inl q), codec.decode q.1 answer⟩]
  | .inr (.inr (.inl q)), answer => [⟨.inr (.inr (.inl q)), answer⟩]
  | .inr (.inr (.inr q)), answer => [⟨.inr (.inr (.inr q)), answer⟩]

/-- The adaptive H₂ fibre oracle equipped with the *actual H₂-shaped* outer
log.  This is deliberately response-dependent: the `e` answer recorded for a
`g` request is the decode of the very representative used to continue the
stateful D2F computation. -/
noncomputable def hyb2FibreLazyELoggingOuterImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      (WriterT
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ)))
        (StateT
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp)) :=
  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) decoded oSpecImpl).withTraceAppend
      (hyb2FibreOuterEntryAsE (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ))

/-- The response-dependent fibre log is exactly the ordinary decoded form of
the corresponding encoded outer-oracle occurrence.  This is the local
repeated-key invariant needed by Claim 5.22: it is independent of whether the
encoded answer came from a newly sampled fibre representative or the cache. -/
theorem hyb2FibreOuterEntryAsE_eq_decodeHyb1OuterLog
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ)).Domain)
    (answer : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ)).Range q) :
    hyb2FibreOuterEntryAsE (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) q answer =
      decodeHyb1OuterLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) [⟨q, answer⟩] := by
  rcases q with q | q
  · rfl
  · rcases q with q | q
    · rfl
    · rcases q with q | q <;> rfl

/-- Erasing the response-derived decoded log from the fibre logger recovers the
underlying adaptive fibre computation exactly.  This isolates logging from the
later live-H₂ semantic refinement: the latter must establish only that the
recorded decoded log is the bridge's `e` log. -/
theorem fst_map_simulateQ_hyb2FibreLazyELoggingOuterImpl
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ)) α) :
    Prod.fst <$>
      (simulateQ
        (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl) oa).run =
      simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl) oa := by
  exact QueryImpl.fst_map_run_withTraceAppend _ _ _

/-- Decoding the ordinary raw log of the fibre realization gives precisely its
response-derived H₂ log at one outer occurrence.  This includes a cache hit:
the response is already determined by the fibre cache, but both loggers retain
the new occurrence. -/
theorem map_run_hyb2FibreLazy_withLogging_eq_ELogging
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ)).Domain) :
    (fun output => (output.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.2)) <$>
      ((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging q).run =
      (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl q).run := by
  simp only [hyb2FibreLazyELoggingOuterImpl, QueryImpl.withLogging_apply,
    QueryImpl.withTraceAppend_apply]
  simp only [WriterT.run_bind', WriterT.run_liftM, WriterT.run_tell,
    WriterT.run_pure', map_bind, map_pure, bind_assoc, pure_bind]
  simp [decodeHyb1OuterLog, List.map_append,
    hyb2FibreOuterEntryAsE_eq_decodeHyb1OuterLog]

/-- The response-derived H₂ logger is the decoded raw logger for every finite,
adaptive outer computation.  The statement is intentionally about the whole
writer result, not only its first projection: it preserves the order and
multiplicity of all repeated encoded keys. -/
theorem map_run_simulateQ_hyb2FibreLazy_withLogging_eq_ELogging
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp (oSpec + D2SChallengePlusUnitOracle
      (U := U) (gSpec (U := U) StmtIn pSpec δ)) α) :
    (fun output => (output.1,
      decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        output.2)) <$>
      (simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging oa).run =
      (simulateQ
        (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl) oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind q continuation ih =>
      simp only [simulateQ_bind, WriterT.run_bind', map_bind]
      let decodeOutput : ∀ {β : Type},
          β × QueryLog (oSpec + D2SChallengePlusUnitOracle
            (U := U) (gSpec (U := U) StmtIn pSpec δ)) →
            β × QueryLog (oSpec + D2SChallengePlusUnitOracle
              (U := U) (eSpec (U := U) StmtIn pSpec δ)) := fun {β} output =>
        (output.1, decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) output.2)
      have htail : ∀ output :
          (oSpec + D2SChallengePlusUnitOracle
            (U := U) (gSpec (U := U) StmtIn pSpec δ)).Range q ×
              QueryLog (oSpec + D2SChallengePlusUnitOracle
                (U := U) (gSpec (U := U) StmtIn pSpec δ)),
          decodeOutput <$>
              (Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                  (continuation output.1)).run) =
            Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
              (decodeOutput <$>
                (simulateQ
                  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                  (continuation output.1)).run) := by
        intro output
        rw [← LawfulFunctor.comp_map, ← LawfulFunctor.comp_map]
        congr 1
        funext result
        rcases output with ⟨answer, pref⟩
        rcases result with ⟨value, suffix⟩
        simp [decodeOutput, decodeHyb1OuterLog, List.map_append]
      calc
        (do
          let output ←
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
              (liftM (OracleSpec.query q))).run
          decodeOutput <$>
            (Prod.map id (fun suffix => output.2 ++ suffix) <$>
              (simulateQ
                (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                  (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                (continuation output.1)).run)) =
            (do
              let output ←
                (simulateQ
                  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
                (decodeOutput <$>
                  (simulateQ
                    (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                    (continuation output.1)).run)) := by
              apply bind_congr
              intro output
              exact htail output
        _ = (do
              let output ←
                (simulateQ
                  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => (decodeOutput output).2 ++ suffix) <$>
                (simulateQ
                  (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                  (continuation output.1)).run) := by
              apply bind_congr
              intro output
              rw [← ih output.1]
        _ = (do
              let output ← decodeOutput <$>
                (simulateQ
                  (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                  (continuation output.1)).run) := by
              rw [bind_map_left]
        _ = (do
              let output ←
                (simulateQ
                  (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                  (liftM (OracleSpec.query q))).run
              Prod.map id (fun suffix => output.2 ++ suffix) <$>
                (simulateQ
                  (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                    (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                  (continuation output.1)).run) := by
              have hquery := map_run_hyb2FibreLazy_withLogging_eq_ELogging
                (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
                decoded oSpecImpl q
              simpa only [decodeOutput, simulateQ_query, OracleQuery.cont_query, id_map,
                OracleQuery.input_query] using congrArg
                (fun run => do
                  let output ← run
                  Prod.map id (fun suffix => output.2 ++ suffix) <$>
                    (simulateQ
                      (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                      (continuation output.1)).run) hquery

/-- The eager continuation for `hyb2FibreLazyOuterImpl`.  A cached witnessed
representative overrides the full fibre table; otherwise the table's value is
used.  Non-`g` queries are literal base-monad effects. -/
noncomputable def hyb2FibreLazyOverlayOuterImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      ProbComp := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  exact fun
    | .inl q => oSpecImpl q
    | .inr (.inl q) => pure (OracleComp.dependentTableExtending cache table q).1
    | .inr (.inr (.inl q)) => d2sUnitSampleImpl (U := U) q
    | .inr (.inr (.inr q)) => (QueryImpl.id' unifSpec) q

/-- Sample one complete table of witnessed representatives of the decoder
fibres of `decoded`.  This is the eager endpoint of the adaptive fibre
coupling; its projection is an encoded `g` table with exactly that decoded
view. -/
noncomputable def decodedFibreUniformTable
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    ProbComp (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
    exact decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
    exact decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    ⟨fun q => Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)⟩
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  exact $ᵗ OracleReduction.OracleFamily
    (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)

/-- Backwards-compatible name for the globally sampled fibre representative
table used by the H₂ eager presentation. -/
noncomputable abbrev uniformDecodedFibreTable
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    ProbComp (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
  decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded

/-- A complete table of pointwise decoder-fibre witnesses is exactly a witness that one
encoded challenge table decodes to `decoded`.  This is the joint object needed to connect the
adaptive fibre cache to the whole-table reparameterization in Claim 5.22. -/
noncomputable def decodedFibreTableEquivPreimage
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) ≃
      Preliminaries.Preimage
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ) decoded where
  toFun encoded := ⟨projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded encoded, by
    funext q
    exact decode_projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded encoded q⟩
  invFun witness q := ⟨witness.1 q, congrFun witness.2 q⟩
  left_inv encoded := by
    funext q
    apply Subtype.ext
    rfl
  right_inv witness := by
    apply Subtype.ext
    rfl

/-- Uniform sampling is invariant under a finite equivalence.  Keeping this elementary PMF
fact local avoids importing an unrelated coding-theory layer into the Section 5 proof cone. -/
private theorem PMF.map_uniformOfFintype_equiv
    {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (equiv : α ≃ β) :
    (PMF.uniformOfFintype α).map equiv = PMF.uniformOfFintype β := by
  classical
  letI : DecidableEq β := Classical.decEq _
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply,
    Fintype.card_congr equiv, tsum_fintype]
  have hsum :
      Finset.univ.sum (fun a : α =>
          if b = equiv a then (Fintype.card β : ENNReal)⁻¹ else 0) =
        Finset.univ.sum (fun b' : β =>
          if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) := by
    simpa using
      (Fintype.sum_equiv equiv
        (fun a : α => if b = equiv a then (Fintype.card β : ENNReal)⁻¹ else 0)
        (fun b' : β => if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0)
        (by intro a; rfl))
  have hdelta :
      Finset.univ.sum (fun b' : β =>
          if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) =
        (Fintype.card β : ENNReal)⁻¹ := by
    simp
  exact hsum.trans hdelta

/-- Transporting a uniform finite table through an equivalence to one complete preimage is
exactly the uniform-preimage kernel.  This is the joint, rather than merely pointwise,
decoder-fibre law needed by the H₁--H₂ coupling. -/
private theorem PMF.map_uniformOfFintype_equiv_preimage
    {A B α : Type} [DecidableEq A] [Fintype B] [Nonempty B]
    [Fintype α] [Nonempty α]
    (ψ : B → A) (hψ : Function.Surjective ψ) (a : A)
    (equiv : α ≃ Preliminaries.Preimage ψ a)
    (f : α → B)
    (hf : ∀ x, f x = (equiv x).1) :
    PMF.map f (PMF.uniformOfFintype α) =
      Preliminaries.sampleUniformPreimage ψ hψ a := by
  classical
  letI : Nonempty (Preliminaries.Preimage ψ a) :=
    Preliminaries.preimageNonempty ψ hψ a
  letI : DecidableEq (Preliminaries.Preimage ψ a) := Classical.decEq _
  have hfun : f = Subtype.val ∘ equiv := by
    funext x
    exact hf x
  rw [hfun, ← PMF.map_comp]
  rw [PMF.map_uniformOfFintype_equiv equiv]
  rw [Preliminaries.sampleUniformPreimage]

/-- The eager product of all decoder fibres, after forgetting witnesses, is exactly a uniform
encoded table in the fibre of the fixed decoded table.  This is the complete-table version of
the adaptive H₂ cache law; unlike a cellwise statement, it is valid for a continuation which
adaptively revisits keys. -/
theorem evalDist_project_uniformDecodedFibreTable_eq_uniformPreimage
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    [DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ)]
    [Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ))]
    [Fintype (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))]
    [SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))] :
    𝒟[projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded <$>
      ($ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))] =
      𝒟[Preliminaries.uniformPreimageComp
        (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
        (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
        decoded] := by
  rw [evalDist_map, evalDist_uniformSample]
  rw [Preliminaries.evalDist_uniformPreimageComp]
  rw [← liftM_map]
  apply congrArg liftM
  exact PMF.map_uniformOfFintype_equiv_preimage
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ)
    decoded
    (decodedFibreTableEquivPreimage (StmtIn := StmtIn) (pSpec := pSpec) (U := U) decoded)
    (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded) (by intro; rfl)

/-- Distributional equality of a sampled table survives an arbitrary continuation receiving
that table.  Claim 5.22 applies this to the complete adaptive execution, including its ordered
query log. -/
private theorem evalDist_bind_apply_eq_of_evalDist_map_eq
    {A B α : Type} (sample : ProbComp A) (map : A → B) (target : ProbComp B)
    (continuation : B → ProbComp α)
    (h : 𝒟[map <$> sample] = 𝒟[target]) :
    𝒟[do
      let a ← sample
      continuation (map a)] =
      𝒟[do
        let b ← target
        continuation b] := by
  calc
    𝒟[do
      let a ← sample
      continuation (map a)] =
        𝒟[do
          let b ← map <$> sample
          continuation b] := by
      rw [evalDist_bind, evalDist_bind, evalDist_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    _ = 𝒟[do
      let b ← target
      continuation b] := by
      rw [evalDist_bind, evalDist_bind, h]

/-- Draw one encoded challenge table uniformly from the complete fibre above `decoded`.
This named executable kernel is the table-level endpoint to which the adaptive H₂ cache will be
coupled; it keeps the needed classical finite-table choices local to the sampler. -/
noncomputable def uniformEncodedTableInDecodedFibre
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ)) :
    ProbComp (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) := by
  classical
  letI : DecidableEq (DecodedChallengeTable (U := U) StmtIn pSpec δ) := Classical.decEq _
  letI : Fintype (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    Fintype.ofFinite _
  letI : Nonempty (OracleReduction.OracleFamily (gSpec (U := U) StmtIn pSpec δ)) :=
    ⟨fun ⟨_, _⟩ => Vector.replicate _
      (Classical.choice (show Nonempty U from inferInstance))⟩
  exact Preliminaries.uniformPreimageComp
    (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ)
    (decodeEncodedChallengeTable_surjective (U := U) StmtIn pSpec δ) decoded

/-- Updating the witnessed lazy cache after a miss is exactly the same as
updating the corresponding coordinate of the eager fibre table. -/
lemma hyb2FibreLazyOverlayOuterImpl_cacheQuery_eq_update
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
    [DecidableEq (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain]
    {q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain}
    (hcache : cache q = none)
    (answer : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :
    hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) decoded oSpecImpl (cache.cacheQuery q answer) table =
      hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl cache (Function.update table q answer) := by
  classical
  apply QueryImpl.ext
  rintro (q' | q' | q' | q')
  · rfl
  · simp only [hyb2FibreLazyOverlayOuterImpl]
    rw [OracleComp.dependentTableExtending_cacheQuery,
      ← OracleComp.dependentTableExtending_update_of_none cache table hcache answer]
  · rfl
  · rfl

/-- Ambient queries pass through the fibre-cache interpreter unchanged. -/
@[simp]
lemma hyb2FibreLazyOuterImpl_ambient
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : oSpec.Domain)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache) :
    (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) decoded oSpecImpl (Sum.inl q)).run cache =
      (fun answer => (answer, cache)) <$> oSpecImpl q :=
  rfl

/-- On an uncached `g` key, the outer fibre oracle draws the named uniform
representative and records precisely that witnessed representative. -/
@[simp]
lemma hyb2FibreLazyOuterImpl_g_miss
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (hcache : cache q = none) :
    letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
      gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) decoded oSpecImpl (Sum.inr (Sum.inl q))).run cache =
      (fun answer : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q =>
        (answer.1, cache.cacheQuery q answer)) <$>
        decodedFibreUniform (pSpec := pSpec) (U := U) decoded q := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  unfold hyb2FibreLazyOuterImpl
  simp only [StateT.run, hcache]
  rfl

/-- A cached `g` key returns its prior representative and leaves the fibre
cache unchanged. -/
@[simp]
lemma hyb2FibreLazyOuterImpl_g_hit
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (answer : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)
    (hcache : cache q = some answer) :
    letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
      gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) decoded oSpecImpl (Sum.inr (Sum.inl q))).run cache =
      pure (answer.1, cache) := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  unfold hyb2FibreLazyOuterImpl
  simp only [StateT.run, hcache]
  rfl

/-- The distributional heart of the adaptive H₂ coupling.  Sampling one fibre
representative on a cache miss and overwriting the same coordinate of an
independent full fibre table leaves that table uniformly distributed. -/
private theorem evalDist_decodedFibreUniform_bind_update
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain)
    (ψ : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) → ProbComp α) :
    letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
      gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    𝒟[do
      let answer ← decodedFibreUniform (pSpec := pSpec) (U := U) decoded q
      let table ← decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded
      ψ (Function.update table q answer)] =
    𝒟[do
      let table ← decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded
      ψ table] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    ⟨fun q => Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)⟩
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  change 𝒟[do
    let answer ← $ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q
    let table ← $ᵗ OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
    ψ (Function.update table q answer)] =
    𝒟[do
      let table ← $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
      ψ table]
  exact evalDist_uniformSample_bind_update_dependent_effect q ψ

/-- Sampling a complete fibre table and discarding it is the identity
distribution.  This is the base case of the adaptive outer induction. -/
private theorem evalDist_decodedFibreUniformTable_bind_pure
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (a : α) :
    𝒟[do
      let _table ← decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded
      pure a] =
    𝒟[(pure a : ProbComp α)] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    ⟨fun q => Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)⟩
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  change 𝒟[do
    let _table ← $ᵗ OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
    pure a] = 𝒟[(pure a : ProbComp α)]
  symm
  refine evalDist_ext fun x => ?_
  rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one'
      (mx := $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
      (by simp), one_mul]

/-- One outer request which leaves the witnessed fibre cache unchanged commutes
with moving the single eager fibre-table sample outside its continuation. -/
private theorem evalDist_simulateQ_hyb2FibreLazyOuterImpl_lift_step {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (z : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Domain)
    (base : ProbComp ((oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Range z))
    (k : (oSpec + D2SChallengePlusUnitOracle (U := U)
      (gSpec (U := U) StmtIn pSpec δ)).Range z →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (hLazy :
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl z).run cache =
        (fun answer => (answer, cache)) <$> base)
    (hEager : ∀ table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded),
      hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl cache table z = base)
    (ih : ∀ answer cache,
      𝒟[(simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl) (k answer)).run' cache] =
      𝒟[do
        let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer)]) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl)
      (liftM (OracleSpec.query z) >>= k)).run' cache] =
    𝒟[do
      let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k)] := by
  have hred :
      (simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl)
        (liftM (OracleSpec.query z) >>= k)).run' cache =
        ((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl z).run cache) >>= fun pair =>
          (simulateQ
            (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run' pair.2 := by
    rw [simulateQ_bind, simulateQ_spec_query]
    change Prod.fst <$> (((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl z).run cache) >>= fun pair =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run pair.2) = _
    rw [map_bind]
    rfl
  have heval : ∀ table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded),
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k) =
      base >>= fun answer =>
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer) := by
    intro table
    rw [simulateQ_bind, simulateQ_spec_query, hEager]
  rw [hred, hLazy]
  have hpair :
      (((fun answer => (answer, cache)) <$> base) >>= fun pair =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run' pair.2) =
      base >>= fun answer =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k answer)).run' cache := by
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp
  have hmid :
      𝒟[base >>= fun answer => do
        let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer)] =
      (do
        let answer ← 𝒟[base]
        let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded
        𝒟[simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer)]) := by
    rw [evalDist_bind]
    refine congrArg _ (funext fun answer => ?_)
    rw [evalDist_bind]
  calc
    𝒟[((fun answer => (answer, cache)) <$> base) >>= fun pair =>
      (simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run' pair.2] =
      𝒟[base >>= fun answer =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k answer)).run' cache] :=
      congrArg _ hpair
    _ = (do
      let answer ← 𝒟[base]
      let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      𝒟[simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (k answer)]) := by
      rw [evalDist_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [ih answer cache, evalDist_bind]
    _ = 𝒟[do
      let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query z) >>= k)] := by
      simp_rw [heval]
      simp_rw [evalDist_bind]
      ext x
      exact probOutput_bind_bind_swap
        (𝒟[base])
        (𝒟[uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded])
        (fun answer table =>
          𝒟[simulateQ
            (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
            (k answer)]) x
  rfl

/-- The adaptive cache-miss step for a `g` query.  The induction hypothesis is
used after installing the representative in the lazy cache; the independent
full fibre table is overwritten at that same coordinate, and the preceding
distributional exchange removes the overwrite. -/
private theorem evalDist_simulateQ_hyb2FibreLazyOuterImpl_g_step
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (k : (gSpec (U := U) StmtIn pSpec δ).Range q →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (ih : ∀ answer cache,
      𝒟[(simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl) (k answer)).run' cache] =
      𝒟[do
        let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer)]) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl)
      (liftM (OracleSpec.query (spec := oSpec +
        D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
        (Sum.inr (Sum.inl q))) >>= k)).run' cache] =
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k)] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  have hred :
      (simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k)).run' cache =
        ((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl (Sum.inr (Sum.inl q))).run cache) >>=
          fun pair =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k pair.1)).run' pair.2 := by
    rw [simulateQ_bind, simulateQ_spec_query]
    change Prod.fst <$> (((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl
      (Sum.inr (Sum.inl q))).run cache) >>= fun pair =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run pair.2) = _
    rw [map_bind]
    rfl
  have heval : ∀ table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded),
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k) =
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (k (OracleComp.dependentTableExtending cache table q).1) := by
    intro table
    rw [simulateQ_bind, simulateQ_spec_query]
    rfl
  rw [hred]
  simp_rw [heval]
  rcases hcache : cache q with _ | response
  · rw [hyb2FibreLazyOuterImpl_g_miss decoded oSpecImpl q cache hcache]
    set ψ : OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) → ProbComp α :=
      fun table =>
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k (OracleComp.dependentTableExtending cache table q).1) with hψ
    have hfun : ∀ answer :
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q,
        (fun table : OracleReduction.OracleFamily
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) =>
          simulateQ
            (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl
              (cache.cacheQuery q answer) table)
            (k answer.1)) =
          fun table => ψ (Function.update table q answer) := by
      intro answer
      funext table
      simp only [hψ]
      rw [hyb2FibreLazyOverlayOuterImpl_cacheQuery_eq_update
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        decoded oSpecImpl cache table hcache answer]
      simp [OracleComp.dependentTableExtending, hcache]
    trans 𝒟[do
      let answer ← decodedFibreUniform (pSpec := pSpec) (U := U) decoded q
      let table ← decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded
      ψ (Function.update table q answer)]
    · have hlazy :
        (do
          let pair ← (fun answer :
            (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q =>
            (answer.1, cache.cacheQuery q answer)) <$>
            decodedFibreUniform (pSpec := pSpec) (U := U) decoded q
          (simulateQ
            (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
            (k pair.1)).run' pair.2) =
          (decodedFibreUniform (pSpec := pSpec) (U := U) decoded q >>= fun answer =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k answer.1)).run' (cache.cacheQuery q answer)) := by
        rw [map_eq_bind_pure_comp, bind_assoc]
        simp
      have hafter :
          𝒟[decodedFibreUniform (pSpec := pSpec) (U := U) decoded q >>= fun answer =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k answer.1)).run' (cache.cacheQuery q answer)] =
          𝒟[do
            let answer ← decodedFibreUniform (pSpec := pSpec) (U := U) decoded q
            let table ← decodedFibreUniformTable (pSpec := pSpec) (U := U) decoded
            ψ (Function.update table q answer)] := by
        rw [evalDist_bind, evalDist_bind]
        refine congrArg _ (funext fun answer => ?_)
        rw [ih answer.1 (cache.cacheQuery q answer), evalDist_bind, evalDist_bind]
        refine congrArg _ (funext fun table => ?_)
        exact congrArg (fun comp : ProbComp α => 𝒟[comp]) (congrFun (hfun answer) table)
      exact (congrArg (fun comp : ProbComp α => 𝒟[comp]) hlazy).trans hafter
    · exact evalDist_decodedFibreUniform_bind_update decoded q ψ
  · rw [hyb2FibreLazyOuterImpl_g_hit decoded oSpecImpl q cache response hcache]
    change 𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl) (k response.1)).run' cache] = _
    rw [ih response.1 cache]
    rw [evalDist_bind, evalDist_bind]
    refine congrArg _ (funext fun table => ?_)
    have hlookup : (OracleComp.dependentTableExtending cache table q).1 = response.1 := by
      simp [OracleComp.dependentTableExtending, hcache]
    rw [hlookup]

/-- An arbitrary adaptive computation sees the same distribution whether H₂
samples each fibre representative on its first use or samples one complete
fibre table before the computation begins.  The cache persists throughout the
entire computation, so repeated keys are coupled to the same representative. -/
theorem evalDist_simulateQ_hyb2FibreLazyOuterImpl_run'_eq_eager
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (oa : OracleComp
      (oSpec + D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl) oa).run' cache] =
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table) oa] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain :=
    gDomainDecidableEq (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure a =>
      have hlhs :
          (simulateQ
            (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
            (pure a : OracleComp _ α)).run' cache =
            (pure a : ProbComp α) := by
        rw [simulateQ_pure]
        change (fun x => x.1) <$> (pure (a, cache) : ProbComp (α × _)) = pure a
        rw [map_pure]
      rw [hlhs]
      simp_rw [simulateQ_pure]
      exact (evalDist_decodedFibreUniformTable_bind_pure decoded a).symm
  | query_bind z k ih =>
      rcases z with z | z | z | z
      · exact evalDist_simulateQ_hyb2FibreLazyOuterImpl_lift_step
          decoded oSpecImpl (Sum.inl z) (oSpecImpl z) k cache
          (hyb2FibreLazyOuterImpl_ambient decoded oSpecImpl z cache)
          (fun _ => rfl) ih
      · exact evalDist_simulateQ_hyb2FibreLazyOuterImpl_g_step
          decoded oSpecImpl z k cache ih
      · exact evalDist_simulateQ_hyb2FibreLazyOuterImpl_lift_step
          decoded oSpecImpl (Sum.inr (Sum.inr (Sum.inl z))) (d2sUnitSampleImpl (U := U) z)
          k cache rfl (fun _ => rfl) ih
      · exact evalDist_simulateQ_hyb2FibreLazyOuterImpl_lift_step
          decoded oSpecImpl (Sum.inr (Sum.inr (Sum.inr z))) ((QueryImpl.id' unifSpec) z)
          k cache rfl (fun _ => rfl) ih

/- The distributional cache-miss induction below is being refactored through a
canonical finite-fibre distribution.  The raw samplers used by the stateful
oracle and by the eager table are extensionally uniform but not definitionally
equal, so this bridge must be stated at `evalDist` level.

/-- A fibre-cache miss may sample its representative lazily or expose the
same coordinate of one eager fibre table.  The table is threaded through the
whole continuation, so this is the adaptive repeated-key step of Claim 5.22. -/
private theorem evalDist_simulateQ_hyb2FibreLazyOuterImpl_g_step
    {α : Type}
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (q : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (k : (gSpec (U := U) StmtIn pSpec δ).Range q →
      OracleComp (oSpec + D2SChallengePlusUnitOracle (U := U)
        (gSpec (U := U) StmtIn pSpec δ)) α)
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache)
    (ih : ∀ answer cache,
      𝒟[(simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl) (k answer)).run' cache] =
      𝒟[do
        let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k answer)]) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl)
      (liftM (OracleSpec.query (spec := oSpec +
        D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
        (Sum.inr (Sum.inl q))) >>= k)).run' cache] =
    𝒟[do
      let table ← uniformDecodedFibreTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k)] := by
  classical
  letI : DecidableEq (gSpec (U := U) StmtIn pSpec δ).Domain := Classical.decEq _
  letI : FinEnum StmtIn := VCVCompatible.instFinEnum
  letI : FinEnum U := VCVCompatible.instFinEnum
  letI : FinEnum pSpec.ChallengeIdx := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum (pSpec.EncodedMessagesBefore U i.1.castSucc) := inferInstance
  letI (i : pSpec.ChallengeIdx) :
      FinEnum ((gSpecInterface (U := U) StmtIn pSpec δ i).Query) := by
    change FinEnum (StmtIn × Vector U δ × pSpec.EncodedMessagesBefore U i.1.castSucc)
    infer_instance
  letI : FinEnum (gSpec (U := U) StmtIn pSpec δ).Domain := inferInstance
  letI : Fintype (gSpec (U := U) StmtIn pSpec δ).Domain :=
    Fintype.ofEquiv (Fin (FinEnum.card _)) FinEnum.equiv.symm
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Fintype ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
    exact decodedFibreFintype (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      Nonempty ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) := by
    exact decodedFibreNonempty (pSpec := pSpec) (U := U) decoded q
  letI (q : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Domain) :
      SampleableType ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) :=
    decodedFibreSampleable (pSpec := pSpec) (U := U) decoded q
  letI : Nonempty (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    ⟨fun q => Classical.choice (show Nonempty
      ((decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) from inferInstance)⟩
  letI : SampleableType (OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :=
    SampleableType.ofFintype _
  have hred :
      (simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k)).run' cache =
        ((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl (Sum.inr (Sum.inl q))).run cache) >>=
          fun pair =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k pair.1)).run' pair.2 := by
    rw [simulateQ_bind, simulateQ_spec_query]
    change Prod.fst <$> (((hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl
      (Sum.inr (Sum.inl q))).run cache) >>= fun pair =>
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) decoded oSpecImpl) (k pair.1)).run pair.2) = _
    rw [map_bind]
    rfl
  have heval : ∀ table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded),
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (liftM (OracleSpec.query (spec := oSpec +
          D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
          (Sum.inr (Sum.inl q))) >>= k) =
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (k (OracleComp.dependentTableExtending cache table q).1) := by
    intro table
    rw [simulateQ_bind, simulateQ_spec_query]
    rfl
  rw [hred]
  have hlazyq :
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded oSpecImpl (Sum.inr (Sum.inl q))).run cache =
        (fun pair => (pair.1.1, pair.2)) <$>
          (OracleSpec.randomOracle
            (spec := decodedFibreSpec (pSpec := pSpec) (U := U) decoded) q).run cache :=
    rfl
  rw [hlazyq]
  simp_rw [heval]
  rcases hcache : cache q with _ | response
  · rw [QueryImpl.withCaching_run_none _ hcache]
    rw [Functor.map_map, map_eq_bind_pure_comp]
    simp only [bind_assoc]
    rw [evalDist_bind]
    simp only [uniformSampleImpl, evalDist_bind, evalDist_uniformSample, evalDist_pure, pure_bind]
    set ψ : OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) → ProbComp α :=
      fun table =>
        simulateQ
          (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
          (k (OracleComp.dependentTableExtending cache table q).1) with hψ
    have hfun : ∀ answer :
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q,
        (fun table : OracleReduction.OracleFamily
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded) =>
          simulateQ
            (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
              (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl
              (cache.cacheQuery q answer) table)
            (k answer.1)) =
          fun table => ψ (Function.update table q answer) := by
      intro answer
      funext table
      simp only [hψ]
      rw [hyb2FibreLazyOverlayOuterImpl_cacheQuery_eq_update
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        decoded oSpecImpl cache table hcache answer]
      simp [OracleComp.dependentTableExtending, hcache]
    trans 𝒟[do
      let answer ← $ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q
      let table ← $ᵗ OracleReduction.OracleFamily
        (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)
      ψ (Function.update table q answer)]
    · rw [← evalDist_bind, ← map_eq_bind_pure_comp]
      change 𝒟[((fun answer :
          (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q =>
          (answer.1, cache.cacheQuery q answer)) <$>
          ($ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)) >>=
          fun pair =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k pair.1)).run' pair.2] = _
      rw [show (((fun answer => (answer.1, cache.cacheQuery q answer)) <$>
          ($ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q)) >>=
          fun pair =>
            (simulateQ
              (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
              (k pair.1)).run' pair.2) =
          (($ᵗ (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).Range q) >>=
            fun answer =>
              (simulateQ
                (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
                  (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
                (k answer.1)).run' (cache.cacheQuery q answer)) from by
          rw [map_eq_bind_pure_comp]
          simp [bind_assoc]]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg _ (funext fun answer => ?_)
      rw [ih answer.1 (cache.cacheQuery q answer)]
      refine congrArg _ ?_
      apply bind_congr
      intro table
      exact congrFun (hfun answer) table
    · exact evalDist_uniformSample_bind_update_dependent_effect q ψ
  · rw [QueryImpl.withCaching_run_some _ hcache]
    change
      𝒟[(simulateQ
        (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) decoded oSpecImpl) (k response.1)).run' cache] = _
    rw [ih response.1 cache]
    refine congrArg _ ?_
    refine congrArg _ (funext fun table => ?_)
    congr 1
    have hlookup : (OracleComp.dependentTableExtending cache table q).1 = response.1 := by
      simp [OracleComp.dependentTableExtending, hcache]
    rw [hlookup]

-/

/-- The free encoded-oracle realization used to expose the `g` calls hidden inside the
revised D2F interpreter.  It has no memo of its own: the surrounding H₂ fibre oracle owns the
single cache, so a prover and its subsequent verifier share representatives for repeated keys. -/
noncomputable def d2sFreeGImpl :
    GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) PUnit :=
  fun q _ => OptionT.lift <| do
    let answer ← query
      (spec := D2SChallengePlusUnitOracle (U := U) (gSpec (U := U) StmtIn pSpec δ))
      (Sum.inl q)
    pure (answer, PUnit.unit)

/-- Exposing an encoded query does not change the H₁ handler; it only moves the identical
table lookup to the surrounding oracle interpreter. -/
theorem d2sFreeGImpl_eq_hyb1GImpl :
    d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) =
      hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) := by
  rfl

/-- The whole H₂ fibre execution with an ordinary decoded outer log.  It runs the
same encoded representatives as the fibre realization, but emits one decoded
`e` entry for every encoded `g` request.  The explicit `PUnit` memo is the
free `g` implementation's only local state; the shared fibre cache is owned by
the surrounding outer interpreter and spans both prover and verifier phases. -/
noncomputable def hyb2FibreLazyELoggedPhase
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    StateT
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp
      (HybridGameRevisedPhaseWithLog
        (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
        oSpec (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ)))) :=
  hybridGameRevisedPhaseWithLoggerFrom
    (T_H := T_H) (T_P := T_P)
    (logger := hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
    (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    V maliciousProver PUnit.unit

/-- The same fibre execution with its raw encoded outer log retained.  It is
used only as the common adaptive execution from which the H₂-shaped log is
obtained by deterministic decoding. -/
noncomputable def hyb2FibreLazyRawLoggedPhase
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    StateT
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache ProbComp
      (HybridGameRevisedPhaseWithLog
        (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
        oSpec (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit
        (QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (gSpec (U := U) StmtIn pSpec δ)))) :=
  hybridGameRevisedPhaseWithLoggerFrom
    (T_H := T_H) (T_P := T_P)
    (logger := (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging)
    (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    V maliciousProver PUnit.unit

/-- Change only the log carrier of a legal fibre phase from encoded `g`
occurrences to their decoded H₂ `e` occurrences. -/
def decodeHyb2FibreRawPhase
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (phase : HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit
      (QueryLog (oSpec + D2SChallengePlusUnitOracle
        (U := U) (gSpec (U := U) StmtIn pSpec δ)))) :
    HybridGameRevisedPhaseWithLog
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ)
      oSpec (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit
      (QueryLog (oSpec + D2SChallengePlusUnitOracle
        (U := U) (eSpec (U := U) StmtIn pSpec δ))) :=
  match phase with
  | .proverStopped reason proverLog =>
      .proverStopped reason
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          proverLog)
  | .verifier proverRun verifierResult proverLog verifierLog =>
      .verifier proverRun verifierResult
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          proverLog)
        (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
          verifierLog)

/-- The complete raw fibre phase, after deterministic log decoding, is exactly
the complete H₂-logged fibre phase.  This lifts the one-occurrence equality
through both adaptive phases and their shared fibre cache. -/
theorem map_hyb2FibreLazyRawLoggedPhase_eq_ELoggedPhase
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    decodeHyb2FibreRawPhase (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (oSpec := oSpec) <$>
      hyb2FibreLazyRawLoggedPhase (T_H := T_H) (T_P := T_P)
        decoded oSpecImpl V maliciousProver =
      hyb2FibreLazyELoggedPhase (T_H := T_H) (T_P := T_P)
        decoded oSpecImpl V maliciousProver := by
  simp only [hyb2FibreLazyRawLoggedPhase, hyb2FibreLazyELoggedPhase,
    hybridGameRevisedPhaseWithLoggerFrom]
  let decodeOutput : ∀ {β : Type},
      β × QueryLog (oSpec + D2SChallengePlusUnitOracle
        (U := U) (gSpec (U := U) StmtIn pSpec δ)) →
        β × QueryLog (oSpec + D2SChallengePlusUnitOracle
          (U := U) (eSpec (U := U) StmtIn pSpec δ)) := fun {β} output =>
    (output.1, decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) output.2)
  let proverComp := d2fRawRevisedStopping (T_H := T_H) (T_P := T_P)
    (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    maliciousProver PUnit.unit
  have hProver := map_run_simulateQ_hyb2FibreLazy_withLogging_eq_ELogging
    (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    decoded oSpecImpl proverComp
  rw [← hProver]
  conv_rhs => rw [map_eq_bind_pure_comp]
  rw [map_bind]
  simp only [Function.comp_apply, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨proverResult, proverLog⟩
  cases proverResult with
  | error reason => rfl
  | ok proverRun =>
      simp only [decodeHyb2FibreRawPhase, map_bind, map_pure]
      let verifierComp := d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (runForwardVerifierWide δ V proverRun.1.1.1 proverRun.1.1.2)
        proverRun.1.2 proverRun.2
      have hVerifier := map_run_simulateQ_hyb2FibreLazy_withLogging_eq_ELogging
        (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        decoded oSpecImpl verifierComp
      change
        (simulateQ
          (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl).withLogging
          verifierComp).run >>=
          (pure ∘ fun output => HybridGameRevisedPhaseWithLog.verifier proverRun output.1
            (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) proverLog)
            (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) output.2)) =
        (simulateQ
          (hyb2FibreLazyELoggingOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
            (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
          verifierComp).run >>=
          (pure ∘ fun output => HybridGameRevisedPhaseWithLog.verifier proverRun output.1
            (decodeHyb1OuterLog (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) proverLog) output.2)
      rw [← map_eq_bind_pure_comp]
      rw [← hVerifier]
      conv_rhs => rw [← map_eq_bind_pure_comp]
      rw [← LawfulFunctor.comp_map]
      rfl

/-- The conditional H₂ fibre experiment before the decoded public log is identified with the
ordinary H₂ log.  A uniform encoded table supplies the H₂ decoded table; representatives are
then sampled lazily, once per encoded `g` key, by the outer fibre oracle.  The result retains
the raw encoded log, because it is the common object from which both H₁ and H₂ line-4 views are
obtained. -/
noncomputable def hyb2FibreLazyObservedDist
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let observedTable ← uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  (simulateQ
    (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ)
      (decodeEncodedChallengeTable (U := U) StmtIn pSpec δ observedTable) oSpecImpl)
    (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
      (gImpl := d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      V maliciousProver)).run' ∅

/-- The raw observed H₁ game under the explicit uniform encoded-table sampler used by the fibre
coupling.  This is definitionally the eager H₁ endpoint once the surrounding game wrappers are
normalized; keeping it named avoids hiding a full query log inside that normalization. -/
noncomputable def hyb1EagerObservedDist
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    ProbComp (HybridGameRevisedObservation
      (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)
      (gSpec (U := U) StmtIn pSpec δ) T_H T_P PUnit) := do
  let table ← uniformEncodedChallengeTable
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
  simulateQ
    (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl table)
    (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
      (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      V maliciousProver)

/-- Once a complete fibre table is fixed, the eager H₂ outer implementation is literally the
H₁ fixed-table implementation for its encoded projection.  This is the endpoint which turns the
adaptive fibre-table theorem into an H₁/H₂ whole-execution coupling. -/
theorem hyb2FibreLazyOverlayOuterImpl_empty_eq_hyb1AmbientOuterImpl
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded)) :
    hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
      (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl ∅ table =
      hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
        (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table) := by
  apply QueryImpl.ext
  rintro (q | q | q | q)
  · rfl
  · change pure (OracleComp.dependentTableExtending ∅ table q).1 =
      pure (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table q)
    rw [OracleComp.dependentTableExtending_empty]
    rfl
  · rfl
  · rfl

/-- At a fixed complete fibre table, the exposed D2F execution is the corresponding live H₁
execution, not just an output-equivalent surrogate.  In particular, this preserves adaptive
control flow, the exact normal state, and every encoded-query occurrence needed by the later
logged coupling. -/
theorem simulateQ_hyb2FibreLazyOverlayOuterImpl_empty_freeG_eq_hyb1
    {α : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (table : OracleReduction.OracleFamily
      (decodedFibreSpec (pSpec := pSpec) (U := U) decoded))
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    simulateQ
      (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl ∅ table)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        comp normal PUnit.unit) =
      simulateQ
        (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
          (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table))
        (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
          (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          comp normal PUnit.unit) := by
  rw [hyb2FibreLazyOverlayOuterImpl_empty_eq_hyb1AmbientOuterImpl]
  rw [d2sFreeGImpl_eq_hyb1GImpl]

/-- **Adaptive D2F eager-realization bridge.**  The generic fibre coupling applies to the
actual revised D2F state machine once its internal encoded-oracle calls are exposed through
`d2sFreeGImpl`.  This is the key operational form needed for Claim 5.22: it covers an arbitrary
adaptive residual, preserves the inherited normal state, and keeps one fibre cache across the
complete computation. -/
theorem evalDist_d2fRawRevisedStoppingFrom_freeG_eq_eager
    {α : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (cache : (decodedFibreSpec (pSpec := pSpec) (U := U) decoded).QueryCache) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        comp normal PUnit.unit)).run' cache] =
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb2FibreLazyOverlayOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl cache table)
        (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
          (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          comp normal PUnit.unit)] := by
  exact evalDist_simulateQ_hyb2FibreLazyOuterImpl_run'_eq_eager
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    decoded oSpecImpl _ cache

/-- **Adaptive unlogged Claim-5.22 coupling.**  A live D2F execution whose fresh encoded keys
are sampled from the decoded-table fibres has exactly the distribution of H₁ run with one eager
encoded fibre table.  This covers an arbitrary residual and its inherited normal state; the
remaining Claim-5.22 work is solely to transport the associated public query log. -/
theorem evalDist_d2fRawRevisedStoppingFrom_fibreLazy_eq_hyb1
    {α : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (comp : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
      (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        comp normal PUnit.unit)).run' ∅] =
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
          (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table))
        (d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
          (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          comp normal PUnit.unit)] := by
  rw [evalDist_d2fRawRevisedStoppingFrom_freeG_eq_eager
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    decoded oSpecImpl comp normal ∅]
  rw [evalDist_bind, evalDist_bind]
  apply bind_congr
  intro table
  exact congrArg (fun computation : ProbComp _ => 𝒟[computation])
    (simulateQ_hyb2FibreLazyOverlayOuterImpl_empty_freeG_eq_hyb1
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      decoded oSpecImpl table comp normal)

/-- **Logged adaptive Claim-5.22 core.**  The adaptive fibre realization can be
applied directly to the *observed* revised Figure-4 phase.  The observation already carries the
complete insertion-ordered encoded-query logs of the prover and verifier, so this theorem
preserves not merely the returned stopping result but every occurrence on which line 4 acts.

At the eager endpoint, the fibre representatives form the H₁ encoded table.  The remaining
H₁--H₂ task is therefore only to identify the decoded version of the left-hand log with the
ordinary H₂ `e`-log; no additional adaptive-sampling argument is left. -/
theorem evalDist_hyb2FibreLazyObserved_eq_hyb1EagerObserved
    {StmtOut : Type} {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    (decoded : OracleReduction.OracleFamily (eSpec (U := U) StmtIn pSpec δ))
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ) :
    𝒟[(simulateQ
      (hyb2FibreLazyOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
        (pSpec := pSpec) (U := U) (δ := δ) decoded oSpecImpl)
      (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
        (gImpl := d2sFreeGImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        V maliciousProver)).run' ∅] =
    𝒟[do
      let table ← decodedFibreUniformTable (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) decoded
      simulateQ
        (hyb1AmbientOuterImpl (oSpec := oSpec) (StmtIn := StmtIn)
          (pSpec := pSpec) (U := U) (δ := δ) oSpecImpl
          (projectDecodedFibreTable (pSpec := pSpec) (U := U) decoded table))
        (hybridGameRevisedObserved (T_H := T_H) (T_P := T_P)
          (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          V maliciousProver)] := by
  rw [evalDist_simulateQ_hyb2FibreLazyOuterImpl_run'_eq_eager
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
    decoded oSpecImpl _ ∅]
  rw [evalDist_bind, evalDist_bind]
  apply bind_congr
  intro table
  exact congrArg (fun computation : ProbComp _ => 𝒟[computation]) (by
    rw [hyb2FibreLazyOverlayOuterImpl_empty_eq_hyb1AmbientOuterImpl]
    rw [d2sFreeGImpl_eq_hyb1GImpl])

end DuplexSpongeFS.KeyLemma
