/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SNoAbortRefinement
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Hyb01PrefixUpdate

/-!
# Live common-prefix realization for Claim 5.21

The H₀/H₁ lazy-sampling construction advances both executions over a common raw duplex prefix.
This module packages the executable fact needed at each such prefix.  If the prefix comes from a
real H₀ ideal-sponge execution and the complete H₀ trace has not triggered `E`, then it has the
actual normalized `D2SNormalState`; from that state the complete live H₁ residual cannot take an
unrecorded search/oracle abort.  Its only possible error is the post-occurrence `Monitor` stop
which the coupling charges as its first bad event.

This is deliberately not the H₀/H₁ coupling itself: it does not manufacture a joint distribution
or complete either marginal after a stop.  It is the no-hidden-abort invariant consumed by that
future paired executor.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.TraceTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [∀ i, VCVCompatible (pSpec.Message i)] [CodecCore pSpec U]
  {δ : Nat} {Salt : Type} [VCVCompatible Salt] [SaltCodec U δ Salt]
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The concrete H₁ residual has no reachable `underlyingAbort` from a normal state.  This is a
definition over the executable residual, rather than a premise of the coupling. -/
def Hyb1ResidualNoUnderlyingAbortAt
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  ∀ abortNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
    (.error (.underlyingAbort abortNormal) : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∉ support
      (hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (hyb1AmbientFullResidual V maliciousProver) normal)

/-- Every reachable H₁ residual error from a normal state is the monitored, post-occurrence
error face.  In particular, a paired H₀/H₁ execution may stop at this point without inventing an
unrecorded error branch. -/
def Hyb1ResidualErrorsAreMonitorStopsAt
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  ∀ reason : D2SRevisedStoppingReason
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
    (.error reason : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) ∈ support
      (hyb1AmbientDirectResidualRun (T_H := T_H) (T_P := T_P)
        oSpecImpl kSigma (hyb1AmbientFullResidual V maliciousProver) normal) →
    hyb1AmbientStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
      (α := ((Option StmtOut × D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit))
      (.error reason)

/-- An actual H₀ ideal-sponge source supplies the complete no-hidden-abort invariant for every
common replay prefix.  The returned `normal` is constructed from exactly `processed`, so the
paired H₀/H₁ executor may use it as its H₁ state invariant.  The theorem adds no cryptographic
premise: `hSource` is membership in the real H₀ source distribution and `hGood` is the coupling's
ordinary pre-stop condition. -/
theorem dsfsGame_hyb0_hyb1_commonPrefix_noHiddenAbort_of_support
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    (fam : (D_𝔖 StmtIn U).Carrier)
    {source : DSFSGameOutput (oSpec := oSpec) (StmtIn := StmtIn) (StmtOut := StmtOut)
      (pSpec := pSpec) (U := U) (δ := δ)}
    {state : (D_𝔖 StmtIn U).Carrier}
    (hSource : (some source, state) ∈ support
      ((simulateQ (hyb0Impl oSpecImpl) (dsfsGame V maliciousProver).run).run fam))
    (processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrefix : processed <+: TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged source.2.2.2))
    (hGood : ¬ BadEventDS.E (TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged source.2.2.2)))
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace = processed ∧
        (∀ state : CanonicalSpongeState U,
          Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
            normal.state.trace normal.state.trΔ normal.state.h_inv state ≠ .err) ∧
        Hyb1ResidualNoUnderlyingAbortAt (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma V maliciousProver normal ∧
        Hyb1ResidualErrorsAreMonitorStopsAt (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma V maliciousProver normal := by
  obtain ⟨normal, hTrace, hBacktrack⟩ :=
    dsfsGame_hyb0_source_prefix_backTrack_noAbort_of_support
      (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver fam hSource processed hPrefix hGood
  refine ⟨normal, hTrace, hBacktrack, ?_, ?_⟩
  · exact ProverTransform.hyb1AmbientFullResidualRun_no_underlyingAbort_of_support
      (T_H := T_H) (T_P := T_P) oSpecImpl kSigma V maliciousProver normal
  · exact ProverTransform.hyb1AmbientFullResidualRun_error_isMonitorStop_of_support
      (T_H := T_H) (T_P := T_P) oSpecImpl kSigma V maliciousProver normal

/-- The same no-hidden-abort invariant, now at an actual support point of the public H₀ observed
experiment.  Unlike the source-level theorem, this is directly consumable by the H₀/H₁ joint
executor: it recovers the fixed sampled sponge family and real source support certificate from
the observation before deriving the normal state and H₁ residual facts. -/
theorem hyb0Observed_hyb1_commonPrefix_noHiddenAbort_of_support
    [Section5Nonempty pSpec]
    (oSpecImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver oSpec pSpec StmtIn U δ)
    {observation : Statement.Hyb0Observation (oSpec := oSpec) (StmtIn := StmtIn)
      (StmtOut := StmtOut) (pSpec := pSpec) (U := U) (δ := δ) (Salt := Salt)}
    (hObservation : observation ∈ support
      (Statement.Hyb0Observed (T_H := T_H) (T_P := T_P) (Salt := Salt)
        oSpecImpl V maliciousProver))
    (hSource : observation.sourceOutput ≠ none)
    (processed : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrefix : processed <+: observation.baseTrace)
    (hGood : ¬ BadEventDS.E observation.baseTrace)
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier) :
    ∃ normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U),
      normal.state.trace = processed ∧
        (∀ state : CanonicalSpongeState U,
          Backtrack.backTrack (n := n) (pSpec := pSpec) (δ := δ)
            normal.state.trace normal.state.trΔ normal.state.h_inv state ≠ .err) ∧
        Hyb1ResidualNoUnderlyingAbortAt (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma V maliciousProver normal ∧
        Hyb1ResidualErrorsAreMonitorStopsAt (T_H := T_H) (T_P := T_P)
          oSpecImpl kSigma V maliciousProver normal := by
  rcases hyb0Observed_successfulReplay_of_good (T_H := T_H) (T_P := T_P)
    (Salt := Salt) oSpecImpl V maliciousProver hObservation hSource hGood with ⟨replay⟩
  have hPrefixSource : processed <+: TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged replay.source.2.2.2) := by
    rw [replay.source_baseTrace]
    exact hPrefix
  have hGoodSource : ¬ BadEventDS.E (TraceTransform.dsTraceOfLog
      (TaggedQueryLog.untagged replay.source.2.2.2)) := by
    rw [replay.source_baseTrace]
    exact hGood
  exact dsfsGame_hyb0_hyb1_commonPrefix_noHiddenAbort_of_support
    (T_H := T_H) (T_P := T_P) oSpecImpl V maliciousProver replay.fam replay.source_support
    processed hPrefixSource hGoodSource kSigma

end DuplexSpongeFS.KeyLemma
