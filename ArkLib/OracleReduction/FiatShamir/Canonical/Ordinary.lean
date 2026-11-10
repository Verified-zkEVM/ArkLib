/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng
-/
module

public import ArkLib.InteractiveProof.IP
public import ArkLib.NonInteractiveArgument.Legacy
public import ArkLib.OracleReduction.FiatShamir.Canonical

/-!
# Canonical Fiat-Shamir for ordinary public-coin IPs

The IP has no ambient oracle and accepts exactly on `true`. The compiled NARG uses only its
specified round functions. Extraction reconstructs the full transcript from the NARG string and
verifier log, then invokes the ordinary SR extractor with the prover's SR move-response trace.
The extractor receives the original statement and chosen salt separately, uses private coins,
and makes no new queries to the round functions.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped ProbabilityTheory

namespace CanonicalFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {Statement Witness : Type}
  {Salt : Type} [VCVCompatible Salt]
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- The NARG's public handler answers only the pre-sampled round functions. -/
def publicCoinOracleImpl : QueryImpl ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)
    (StateT (QueryImpl (srChallengeOracle (Statement × Salt) pSpec) Id) ProbComp) :=
  (IP.emptyImpl (σ := QueryImpl
    (srChallengeOracle (Statement × Salt) pSpec) Id)).addLift srChallengeQueryImpl'

private def extractionImpl :
    QueryImpl (([]ₒ + fsChallengeOracle (Statement × Salt) pSpec) + unifSpec)
      (StateT (QueryImpl (srChallengeOracle (Statement × Salt) pSpec) Id) ProbComp) :=
  publicCoinOracleImpl.addLift (QueryImpl.id' unifSpec)

omit [VCVCompatible Salt] [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem publicCoinQuerySelector :
    _root_.Verifier.StateRestoration.isSrChallengeMove
      (StmtIn := Statement) (Salt := Salt) (pSpec := pSpec) (oSpec := []ₒ) =
      (fun _ => True) := by
  funext q
  cases q with
  | inl q => nomatch q
  | inr q => rfl

variable [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]

private def standaloneExtractor
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)) :
    OptionT ProbComp Witness :=
  OptionT.mk (simulateQ (((fun q => nomatch q) : QueryImpl []ₒ ProbComp) +
      QueryImpl.id' unifSpec)
    (fsSRDelegatingExtractor E x π trP trV).run)

/-- Reconstruct the IP transcript from recorded verifier queries and run the SR extractor.
Only the prover's SR move-response trace is supplied as the extractor's query log. -/
def publicCoinExtractor
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt)) :
    NARG.Extractor ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)
      Statement Witness (FSSaltedNARGString pSpec Salt) :=
  fun x π trP trV => E x π.1
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 trV.snd)) trP.snd

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The extractor's observable interface is exactly the ordinary SR interface. -/
theorem publicCoinExtractor_apply
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)) :
    publicCoinExtractor E x π trP trV =
      E x π.1
        (FullTranscript.ofMessagesChallenges π.2
          (Messages.challengesOfLog (x, π.1) π.2 trV.snd)) trP.snd := rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem standaloneExtractor_toReduction
    (E : IP.SRExtractor Statement Witness pSpec (Salt := Salt)) :
    standaloneExtractor E.toReduction = publicCoinExtractor E := by
  funext x π trP trV
  unfold publicCoinExtractor standaloneExtractor fsSRDelegatingExtractor
    IP.SRExtractor.toReduction
  simp only [OptionT.run_mk]
  rw [QueryImpl.simulateQ_add_liftComp_right, simulateQ_id']
  rfl

private theorem standaloneExtractor_simulate
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (x : Statement) (π : FSSaltedNARGString pSpec Salt)
    (trP trV : QueryLog ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)) :
    simulateQ extractionImpl (fsSRDelegatingNARGExtractor E x π trP trV).run =
      StateT.lift (standaloneExtractor E x π trP trV).run := by
  unfold fsSRDelegatingNARGExtractor standaloneExtractor
  simp only [OptionT.run_mk, liftComp_def, ← QueryImpl.simulateQ_compose]
  change _ = liftM (simulateQ (((fun q => nomatch q) : QueryImpl []ₒ ProbComp) +
      QueryImpl.id' unifSpec)
    (fsSRDelegatingExtractor E x π trP trV).run)
  rw [← simulateQ_liftTarget]
  congr 1
  funext q
  cases q with
  | inl q => nomatch q
  | inr q =>
    change simulateQ extractionImpl
      (liftM ((([]ₒ + fsChallengeOracle (Statement × Salt) pSpec) + unifSpec).query
        (.inr q))) = _
    rw [simulateQ_spec_query]
    rfl

private theorem standaloneExtractor_experiment_eq
    (init : ProbComp (QueryImpl (srChallengeOracle (Statement × Salt) pSpec) Id))
    (V : IP.Verifier Statement pSpec)
    (E : Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt))
    (P : NARG.Prover ([]ₒ + fsChallengeOracle (Statement × Salt) pSpec)
      Statement (FSSaltedNARGString pSpec Salt)) :
    adaptiveNARGKnowledgeSoundnessExp init publicCoinOracleImpl (QueryImpl.id' unifSpec)
      ((QueryImpl.id' unifSpec).liftTarget (StateT _ ProbComp))
      (_root_.Verifier.compileFiatShamir (Salt := Salt) V) (standaloneExtractor E) P =
    adaptiveNARGKnowledgeSoundnessExp init publicCoinOracleImpl (QueryImpl.id' unifSpec)
      extractionImpl (_root_.Verifier.compileFiatShamir (Salt := Salt) V)
      (fsSRDelegatingNARGExtractor E) P := by
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq]
  simp only [standaloneExtractor_simulate, simulateQ_liftTarget, simulateQ_id']
  rfl

end CanonicalFS

namespace CanonicalFS

section Families

variable {Statement Witness : Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ sec n, ProtocolSpec (rounds sec n)}
  {Salt : ℕ → ℕ → ℕ → Type} [∀ sec s n, VCVCompatible (Salt sec s n)]
  [∀ sec n i, SampleableType ((pSpec sec n).Challenge i)]
  [∀ sec n i, VCVCompatible ((pSpec sec n).Challenge i)]
  (init : ∀ sec s n, ProbComp
    (QueryImpl (srChallengeOracle (Statement × Salt sec s n) (pSpec sec n)) Id))
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
      (fun sec n => []ₒ + fsChallengeOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      language size (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  intro sec n t P hP
  have hCompile
      (V : IP.Verifier Statement (pSpec sec n)) :
      NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
          (V.restrictSize size n)) =
      (NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) V)).restrictSize
          size n := by
      ext x tr
      apply OptionT.ext
      simp only [NARG.Verifier.ofPublic, NARG.Verifier.restrictSize, _root_.Verifier.liftOracles,
        _root_.Verifier.compileFiatShamir, _root_.Verifier.restrictSize,
        OptionT.run_map]
      simp only [OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, bind_assoc,
        pure_bind, Option.elim_some, liftComp_bind, OptionT.run_mk, map_bind]
      apply bind_congr
      intro derived
      simp only [liftM_map, OptionT.run_map, liftComp_map, bind_map_left]
      apply bind_congr
      intro accepted
      cases accepted with
      | none => rfl
      | some accepted => cases accepted <;> rfl
  rw [← NARG.soundnessExperiment_restrictSize_failureProb_eq, ← hCompile]
  rw [NARG.soundnessExperiment_ofPublic]
  have h := canonicalFiatShamir_soundness ((V sec n).restrictSize size n) language {true}
    (init sec (saltSize sec n) n) IP.emptyImpl
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt sec (saltSize sec n) n))
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt sec (saltSize sec n) n))
    (fun _ h => h) t (error sec (saltSize sec n) n t) (hSR sec (saltSize sec n) n t)
  simpa only [publicCoinOracleImpl, publicCoinQuerySelector, NARG.soundnessFailureEvent] using
    h P (by simpa only [publicCoinQuerySelector] using hP)

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
      (fun sec n => []ₒ + fsChallengeOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n => publicCoinExtractor (E sec (saltSize sec n) n))
      (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  intro sec n t P hP
  have hCompile
      (V : IP.Verifier Statement (pSpec sec n)) :
      NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
          (V.restrictSize size n)) =
      (NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) V)).restrictSize
          size n := by
      ext x tr
      apply OptionT.ext
      simp only [NARG.Verifier.ofPublic, NARG.Verifier.restrictSize, _root_.Verifier.liftOracles,
        _root_.Verifier.compileFiatShamir, _root_.Verifier.restrictSize,
        OptionT.run_map]
      simp only [OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, bind_assoc,
        pure_bind, Option.elim_some, liftComp_bind, OptionT.run_mk, map_bind]
      apply bind_congr
      intro derived
      simp only [liftM_map, OptionT.run_map, liftComp_map, bind_map_left]
      apply bind_congr
      intro accepted
      cases accepted with
      | none => rfl
      | some accepted => cases accepted <;> rfl
  rw [← NARG.knowledgeSoundnessExperiment_restrictSize_failureProb_eq, ← hCompile]
  rw [NARG.knowledgeSoundnessExperiment_ofPublic]
  have hGeneric := IP.srKnowledgeSoundnessQueryBoundedWithExtractor_to_generic
    (init sec (saltSize sec n) n) relation ((V sec n).restrictSize size n)
    (E sec (saltSize sec n) n) t (error sec (saltSize sec n) n t) (hE sec (saltSize sec n) n t)
  have hBound : P.IsQueryBoundP (publicQuerySelector
      (_root_.Verifier.StateRestoration.isSrChallengeMove
        (Salt := Salt sec (saltSize sec n) n) (oSpec := []ₒ))) t := by
    simpa only [publicCoinQuerySelector] using hP
  have h := canonicalFiatShamir_knowledgeSoundness_of_fixedExtractor
    unifSpec (QueryImpl.id' unifSpec) ((V sec n).restrictSize size n) relation {true}
    (init sec (saltSize sec n) n) IP.emptyImpl (E sec (saltSize sec n) n).toReduction
    (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove
      (Salt := Salt sec (saltSize sec n) n)))
    (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove
      (Salt := Salt sec (saltSize sec n) n)))
    (fun _ h => h) t (error sec (saltSize sec n) n t) hGeneric P hBound
  change Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp (init sec (saltSize sec n) n)
      publicCoinOracleImpl (QueryImpl.id' unifSpec) NARG.privateExtractorImpl
      (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
        ((V sec n).restrictSize size n))
      (publicCoinExtractor (E sec (saltSize sec n) n)) P)}[
        nargKSFailEvent relation {true} out] ≤ error sec (saltSize sec n) n t
  rw [← standaloneExtractor_toReduction (E sec (saltSize sec n) n)]
  change Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp (init sec (saltSize sec n) n)
      publicCoinOracleImpl (QueryImpl.id' unifSpec)
      ((QueryImpl.id' unifSpec).liftTarget (StateT _ ProbComp))
      (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n)
        ((V sec n).restrictSize size n))
      (standaloneExtractor (E sec (saltSize sec n) n).toReduction) P)}[
        nargKSFailEvent relation {true} out] ≤ error sec (saltSize sec n) n t
  rw [standaloneExtractor_experiment_eq]
  exact h

/-- One ordinary state-restoration extractor family gives one canonical FS extractor family
for all public security parameters, instance-size bounds, and query budgets. -/
theorem publicCoin_knowledge_soundness (relation : Set (Statement × Witness))
    (error : ℕ → ℕ → ℕ → ℕ → ENNReal)
    (hSR : ∀ sec, IP.srKnowledgeSoundness (init sec) (fun _ n => V sec n)
      relation size (error sec)) :
    NARG.adaptiveKnowledgeSoundness
      (fun sec n => []ₒ + fsChallengeOracle (Statement × Salt sec (saltSize sec n) n) (pSpec sec n))
      (fun sec n => init sec (saltSize sec n) n)
      (fun _ _ => publicCoinOracleImpl)
      (fun sec n => NARG.Verifier.ofPublic
        (_root_.Verifier.compileFiatShamir (Salt := Salt sec (saltSize sec n) n) (V sec n)))
      relation size (fun sec n t => error sec (saltSize sec n) n t) := by
  classical
  choose E hE using hSR
  exact ⟨_, publicCoin_knowledge_soundness_withExtractor init V size saltSize relation error E hE⟩

end Families

end CanonicalFS
