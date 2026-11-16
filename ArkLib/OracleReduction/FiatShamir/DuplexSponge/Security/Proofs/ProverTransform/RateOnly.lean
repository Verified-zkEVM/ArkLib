/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, ArkLib Contributors
-/
module

public import VCVio.OracleComp.SimSemantics.StateT.Measure

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ProverTransform.D2SAlgo

/-!
# Prover transformation: rate-only step normal forms

The executable rate-only transition normal forms used by the hybrid proofs, together with
the exact trace-growth law before and after installing an oracle implementation.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open Backtrack Lookahead DSTraceStorage TraceTransform

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]
  {δ : Nat}

/-! ## Rate-only normal forms used by the stopped Claim 5.24 proof

These are the executable rate-only transition normal forms: their premises and conclusions speak
only about the raw rate-only state.  The cache-hit case is stated separately because it samples one
fresh capacity rather than a full state. -/

section RateOnlyStepNormalForms

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [SpongeSize] in
/-- Running a lifted total query does not change the surrounding `D2SQuery` state.  This is the
small transport needed to expose the lookup that follows the unconditional `gᵢ` query in the
codec-image `BackTrack` branch. -/
private lemma rateOnly_stateT_lift_run_bind {ι' : Type} {spec' : OracleSpec ι'}
    {α β σ' : Type} (x : OracleComp spec' α)
    (k : α → StateT σ' (AbortComp spec') β) (st : σ') :
    ((StateT.lift (OptionT.lift x) >>= k).run st)
      = (OptionT.lift x : AbortComp spec' α) >>= fun a => (k a).run st := by
  change (((OptionT.lift x : AbortComp spec' α) >>= fun a => pure (a, st)) >>=
      fun p => (k p.1).run p.2) = _
  rw [bind_assoc]
  simp only [pure_bind]

omit [SpongeSize] in
/-- Function-application form of `rateOnly_stateT_lift_run_bind`; it matches the executable
`StateT` normal form produced by unfolding the raw handler. -/
private lemma rateOnly_stateT_lift_bind_apply {ι' : Type} {spec' : OracleSpec ι'}
    {α β σ' : Type} (x : OracleComp spec' α)
    (k : α → StateT σ' (AbortComp spec') β) (st : σ') :
    (StateT.lift (OptionT.lift x)).bind k st
      = (OptionT.lift x : AbortComp spec' α) >>= fun a => (k a) st := by
  change (((OptionT.lift x : AbortComp spec' α) >>= fun a => pure (a, st)) >>=
      fun p => (k p.1) p.2) = _
  rw [bind_assoc]
  simp only [pure_bind]

omit [SpongeSize] in
/-- Peel an abort-free `OptionT` head from its underlying oracle computation. -/
private lemma rateOnly_optionT_run_bind_of_run_eq {ι' : Type} {spec' : OracleSpec ι'}
    {α β : Type} (z : OptionT (OracleComp spec') α)
    (k : α → OptionT (OracleComp spec') β) (y : OracleComp spec' α)
    (h : z.run = y >>= fun a => pure (some a)) :
    (z >>= k).run = y >>= fun a => (k a).run := by
  rw [OptionT.run_bind, h]
  simp only [Option.elimM, bind_assoc, pure_bind, Option.elim_some]

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A hash-table hit is a deterministic raw rate-only step: it records a redundant trace
occurrence and leaves all lookup tables and pending rate tails untouched. -/
lemma d2sQueryStep_hash_hit_rateOnly
    (x : StmtIn) (cap : Vector U SpongeSize.C)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (h : TraceTableOps.inlu st.trΔ.h x = some cap) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsHashQuery x)).run st
      = pure (cap,
          { st with
            trace := st.trace ++ [⟨dsHashQuery x, cap⟩],
            h_inv := TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv
              ⟨dsHashQuery x, cap⟩ }) := by
  simp only [d2sQueryStep, d2sHandleHashQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [h]
  rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- An inverse-table hit is likewise deterministic in the raw rate-only oracle wrapper. -/
lemma d2sQueryStep_permInv_hit_rateOnly
    (sOut sIn : CanonicalSpongeState U)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (h : TraceTableOps.outlu st.trΔ.p sOut = some sIn) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermInvQuery sOut)).run st
      = pure (sIn,
          { st with
            trace := st.trace ++ [⟨dsPermInvQuery sOut, sIn⟩],
            h_inv := TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv
              ⟨dsPermInvQuery sOut, sIn⟩ }) := by
  simp only [d2sQueryStep, d2sHandleInversePermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [h]
  rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A cache-miss `BackTrack = err` forward step is the genuine Item-4(b) abort: it emits no
new base-oracle occurrence and returns the raw `AbortComp` failure. -/
lemma d2sQueryStep_perm_err_rateOnly
    (sIn : CanonicalSpongeState U)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .err)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none) :
    ((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st).run
      = pure none := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hbt]
  rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A cache-miss, `BackTrack = noResult` forward-table hit is deterministic.  The explicit
rate-only cache premise prevents this normal form from accidentally covering a lazy-tail draw. -/
lemma d2sQueryStep_perm_noResult_hit_rateOnly
    (sIn sOut : CanonicalSpongeState U)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .noResult)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = some sOut) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = pure (sOut,
          { st with
            trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩],
            h_inv := TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv
              ⟨dsPermQuery sIn, sOut⟩ }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hbt]
  simp only [d2sHandleBacktrackNoResult, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hinlu]
  rfl

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- In the codec-image `BackTrack` branch, the post-`gᵢ` lookup is evaluated in the original
state.  On a miss it exposes the rate blocks, then exactly one capacity for the first block. -/
private lemma d2sHandleBacktrackAfterG_miss_rateOnly
    (sIn : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (verifierMessageSize (pSpec := pSpec) out.roundIdx))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = none) :
    (d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) sIn out rhoHat).run st
      = (OptionT.lift (d2sRateBlocksFromVerifierMessage (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ) (i := out.roundIdx) rhoHat) : AbortComp _ _) >>=
          fun rateBlocks =>
        match rateBlocks.toList with
        | [] => failure
        | firstRate :: remainingRates =>
            (OptionT.lift (d2sSampleCapacity (U := U) (StmtIn := StmtIn)
              (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun capacity =>
            let sOut := d2sSynthesisState (U := U) firstRate capacity
            let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
              match RateOnlyTail.ofBlocks? (U := U) remainingRates with
              | none => st.rateCacheP
              | some tail => st.rateCacheP ++ [⟨sOut, tail⟩]
            pure (sOut,
              { st with
                trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩]
                rateCacheP := rateCache'
                trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sIn sOut }
                h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv sIn sOut }) := by
  simp only [d2sHandleBacktrackAfterG, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  simp only [ChallengeIdx, hinlu]
  rw [rateOnly_stateT_lift_bind_apply]
  refine bind_congr fun rateBlocks => ?_
  cases hblocks : rateBlocks.toList with
  | nil => rfl
  | cons firstRate remainingRates =>
      simp only
      rw [rateOnly_stateT_lift_bind_apply]
      refine bind_congr fun capacity => ?_
      rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A codec-image `BackTrack` hit whose forward lookup misses starts a verifier squeeze.  The
unconditional `gᵢ` query leaves the query state unchanged; the first rate block then receives one
fresh capacity and later blocks are stored as a rate-only tail keyed by the materialized output. -/
lemma d2sQueryStep_perm_some_miss_rateOnly
    (sIn : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .some out)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = none) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = (OptionT.lift (d2sQueryG (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ)
            out.roundIdx out.stmt out.salt out.encodedProverMessages) : AbortComp _ _) >>=
          fun rhoHat =>
        (OptionT.lift (d2sRateBlocksFromVerifierMessage (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ) (i := out.roundIdx) rhoHat) : AbortComp _ _) >>=
          fun rateBlocks =>
        match rateBlocks.toList with
        | [] => failure
        | firstRate :: remainingRates =>
            (OptionT.lift (d2sSampleCapacity (U := U) (StmtIn := StmtIn)
              (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun capacity =>
            let sOut := d2sSynthesisState (U := U) firstRate capacity
            let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
              match RateOnlyTail.ofBlocks? (U := U) remainingRates with
              | none => st.rateCacheP
              | some tail => st.rateCacheP ++ [⟨sOut, tail⟩]
            pure (sOut,
              { st with
                trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩]
                rateCacheP := rateCache'
                trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sIn sOut }
                h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv sIn sOut }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hbt]
  simp only [d2sHandleBacktrackSome, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [himg]
  simp only [ite_true]
  change
    ((StateT.lift (OptionT.lift (d2sQueryG (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ)
          out.roundIdx out.stmt out.salt out.encodedProverMessages)) >>=
      fun rhoHat => d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) sIn out rhoHat).run st) = _
  rw [rateOnly_stateT_lift_run_bind]
  refine bind_congr fun rhoHat => ?_
  exact d2sHandleBacktrackAfterG_miss_rateOnly
    (T_H := T_H) (T_P := T_P) sIn out rhoHat st hinlu

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- The `OptionT.run` form of a rate-only squeeze miss.  This exposes the exact sampling
schedule needed by Claim 5.24: query `gᵢ`, reshape its answer, then sample one capacity only for
the first rate block. -/
lemma d2sQueryStep_perm_some_miss_rateOnly_run
    (sIn : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .some out)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = none) :
    ((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st).run
      = d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          out.roundIdx out.stmt out.salt out.encodedProverMessages >>= fun rhoHat =>
          d2sRateBlocksFromVerifierMessage (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (i := out.roundIdx) rhoHat >>= fun rateBlocks =>
            match rateBlocks.toList with
            | [] => pure none
            | firstRate :: remainingRates =>
                d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
                  fun capacity =>
                    let sOut := d2sSynthesisState (U := U) firstRate capacity
                    let rateCache' : List (RateOnlyCacheEntry (U := U)) :=
                      match RateOnlyTail.ofBlocks? (U := U) remainingRates with
                      | none => st.rateCacheP
                      | some tail => st.rateCacheP ++ [⟨sOut, tail⟩]
                    pure (some (sOut,
                      { st with
                        trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩]
                        rateCacheP := rateCache'
                        trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sIn sOut }
                        h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv
                          sIn sOut })) := by
  rw [d2sQueryStep_perm_some_miss_rateOnly (T_H := T_H) (T_P := T_P)
    sIn out st hbt hcache himg hinlu]
  refine Eq.trans (rateOnly_optionT_run_bind_of_run_eq _ _ _ (OptionT.run_lift _)) ?_
  refine bind_congr fun rhoHat => ?_
  refine Eq.trans (rateOnly_optionT_run_bind_of_run_eq _ _ _ (OptionT.run_lift _)) ?_
  refine bind_congr fun rateBlocks => ?_
  cases rateBlocks.toList with
  | nil => rfl
  | cons _ _ =>
      exact rateOnly_optionT_run_bind_of_run_eq _ _ _ (OptionT.run_lift _)

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A hash-table miss appends one sampled capacity occurrence. -/
lemma d2sQueryStep_hash_miss_rateOnly
    (x : StmtIn)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (h : TraceTableOps.inlu st.trΔ.h x = none) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsHashQuery x)).run st
      = (OptionT.lift (d2sSampleCapacity (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun sampled =>
          pure (sampled,
            { st with
              trace := st.trace ++ [⟨dsHashQuery x, sampled⟩],
              trΔ := { st.trΔ with h := TraceTableOps.insert st.trΔ.h x sampled },
              h_inv := TraceNabla.IsSubsetOfQueryLog_append_hash st.h_inv x sampled }) := by
  simp only [d2sQueryStep, d2sHandleHashQuery,
    StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, pure_bind, h, bind_assoc]

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- An inverse-table miss appends one sampled full permutation occurrence. -/
lemma d2sQueryStep_permInv_miss_rateOnly
    (sOut : CanonicalSpongeState U)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (h : TraceTableOps.outlu st.trΔ.p sOut = none) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermInvQuery sOut)).run st
      = (OptionT.lift (d2sSampleState (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun sampled =>
          pure (sampled,
            { st with
              trace := st.trace ++ [⟨dsPermInvQuery sOut, sampled⟩],
              trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sampled sOut },
              h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm_inv st.h_inv sampled sOut }) := by
  simp only [d2sQueryStep, d2sHandleInversePermQuery,
    StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, pure_bind, h, bind_assoc]

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A codec-image `BackTrack.some` hit follows paper Item 4(e)i–ii exactly: it issues the
unconditional `gᵢ` query, then serves the forward-table entry without deriving rate blocks. -/
lemma d2sQueryStep_perm_some_codec_hit_rateOnly
    (sIn sOut : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .some out)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = true)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = some sOut) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = (OptionT.lift (d2sQueryG (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            out.roundIdx out.stmt out.salt out.encodedProverMessages) : AbortComp _ _) >>= fun _ =>
          pure (sOut,
            { st with
              trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩],
              h_inv := TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv
                ⟨dsPermQuery sIn, sOut⟩ }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hbt]
  simp only [d2sHandleBacktrackSome, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [himg]
  simp only [ite_true]
  change
    ((StateT.lift (OptionT.lift (d2sQueryG (U := U) (StmtIn := StmtIn)
          (pSpec := pSpec) (δ := δ)
          out.roundIdx out.stmt out.salt out.encodedProverMessages)) >>=
      fun rhoHat => d2sHandleBacktrackAfterG (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) sIn out rhoHat).run st) = _
  rw [rateOnly_stateT_lift_run_bind]
  refine bind_congr fun rhoHat => ?_
  simp only [d2sHandleBacktrackAfterG, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hinlu]
  rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A non-codec-image `BackTrack.some` result follows paper Item 4(d): it does not query
`gᵢ`, and a forward-table hit merely records the recovered edge. -/
lemma d2sQueryStep_perm_some_notImage_hit_rateOnly
    (sIn sOut : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .some out)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = false)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = some sOut) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = pure (sOut,
          { st with
            trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩],
            h_inv := TraceNabla.IsSubsetOfQueryLog_append_any st.h_inv
              ⟨dsPermQuery sIn, sOut⟩ }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, StateT.run, bind, StateT.bind, get,
    getThe, MonadStateOf.get, StateT.get, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [hcache, hbt]
  simp only [d2sHandleBacktrackSome, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, pure]
  simp only [OptionT.pure, OptionT.bind, OptionT.mk, pure_bind]
  rw [himg]
  rw [hinlu]
  rfl

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- The non-codec-image miss face of paper Item 4(d) samples one fresh full state, exactly like
the ordinary fresh-forward face, but with the `BackTrack.some` certificate made explicit. -/
lemma d2sQueryStep_perm_some_notImage_fresh_rateOnly
    (sIn : CanonicalSpongeState U)
    (out : BacktrackOutput (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .some out)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (himg : d2sInCodecImagePredicate (StmtIn := StmtIn) (pSpec := pSpec) (U := U) out = false)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = none) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = (OptionT.lift (d2sSampleState (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun sOut =>
          pure (sOut,
            { st with
              trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩],
              trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sIn sOut },
              h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv sIn sOut }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, d2sHandleBacktrackSome,
    StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, pure_bind, hcache, hbt, himg, Bool.false_eq_true, ite_false, hinlu, bind_assoc]

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A forward `BackTrack = noResult` miss with no pending rate-only tail samples one fresh full
state.  The cache premise is a failed rate-only lookup, not an empty-cache assertion. -/
lemma d2sQueryStep_perm_noResult_fresh_rateOnly
    (sIn : CanonicalSpongeState U)
    (st : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (hbt : backTrackFwd (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        st.trace st.trΔ st.h_inv sIn (st.trace.length + 1) = .noResult)
    (hcache : popRateOnlyTailByInput (U := U) st.rateCacheP sIn = none)
    (hinlu : TraceTableOps.inlu st.trΔ.p sIn = none) :
    (d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (dsPermQuery sIn)).run st
      = (OptionT.lift (d2sSampleState (U := U) (StmtIn := StmtIn)
            (pSpec := pSpec) (δ := δ)) : AbortComp _ _) >>= fun sOut =>
          pure (sOut,
            { st with
              trace := st.trace ++ [⟨dsPermQuery sIn, sOut⟩],
              trΔ := { st.trΔ with p := TraceTableOps.insert st.trΔ.p sIn sOut },
              h_inv := TraceNabla.IsSubsetOfQueryLog_append_perm st.h_inv sIn sOut }) := by
  simp only [d2sQueryStep, d2sHandleForwardPermQuery, d2sHandleBacktrackNoResult,
    StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set,
    StateT.run_pure, pure_bind, hcache, hbt, hinlu, bind_assoc]

end RateOnlyStepNormalForms

section Trace

variable [∀ i, VCVCompatible (pSpec.Message i)] [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

local notation "QState" => D2SQueryState StmtIn pSpec U δ T_H T_P

/-- **One `D2SQuery` step appends exactly one occurrence.**  Whatever branch of [CO25, §5.4]
Items 2-4 fires, the post-state's raw trace is the pre-state's trace with the single entry
`⟨dq, answer⟩` appended — at the very query that was dispatched.  This handler-free support
statement also applies under stateful or aborting oracle interpretations. -/
theorem d2sQueryStep_trace_append (dq : (duplexSpongeOracle StmtIn U).Domain)
    (qs : QState) :
    ∀ z ∈ support (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) dq).run qs).run),
      ∀ a st', z = some (a, st') →
        st'.trace = qs.trace ++ [(⟨dq, a⟩ : Sigma (duplexSpongeOracle StmtIn U))] := by
  rcases dq with stmt | sIn | sOut
  all_goals
    simp only [d2sQueryStep, d2sHandleHashQuery, d2sHandleInversePermQuery,
      d2sHandleForwardPermQuery, d2sHandleBacktrackNoResult, d2sHandleBacktrackSome,
      d2sHandleBacktrackAfterG, StateT.run_bind, StateT.run_get, pure_bind]
    repeat' first
      | solve | simp [OptionT.run_bind, Option.elimM]
      | split
    all_goals aesop (add simp [OptionT.run_bind, Option.elimM])

/-- Every successful raw rate-only D2S query records exactly its returned oracle occurrence.
This is the monotonicity bridge needed to compare the ordinary Lemma-5.8 experiment with a
proof-only first-bad stop. -/
lemma d2sQueryStep_rateOnly_success_trace
    (impl : QueryImpl
      (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) ProbComp)
    (q : (duplexSpongeOracle StmtIn U).Domain)
    (st st' : D2SQueryState StmtIn pSpec U δ T_H T_P)
    (answer : (duplexSpongeOracle StmtIn U).Range q)
    (hResult : some (answer, st') ∈ support (simulateQ impl
      ((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st).run)) :
    st'.trace = st.trace ++ [⟨q, answer⟩] := by
  apply d2sQueryStep_trace_append q st _ ?_ answer st' rfl
  exact support_simulateQ_subset impl _ hResult

end Trace

end DuplexSpongeFS.ProverTransform
