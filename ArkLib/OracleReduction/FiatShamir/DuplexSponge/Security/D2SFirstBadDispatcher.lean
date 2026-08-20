/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadGateway
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CacheTraceBridges

/-!
# Whole-dispatcher invariant for revised D2SQuery

This module contains the support-level invariant and absorbing finite-run induction for the
live revised D2SQuery executor.  It depends on the cache-coherence and first-bad gateway
facts in `D2SFirstBadGateway`, but deliberately keeps the live dispatcher proof outside that
cache module.  Lemma 5.8 can therefore import this focused boundary without inheriting the
cache-construction implementation details.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-! ## Whole-dispatcher invariant boundary

The preceding lemmas establish the cache invariant for each concrete continuation.  The following
definitions make the one remaining whole-run obligation exact: it is a support statement about
the *live* `d2sQueryStepRevised` / `d2sQueryRunRevised` executors, not a caller-supplied relation
between arbitrary normal states.  A future proof can therefore induct only on the two recursive
equations of the live runner, carrying one named invariant and the five first-bad gateways.
-/

/-- The result invariant needed by the stopped first-event proof.  A reusable continuation has a
coherent rate-only cache and an `E`-good insertion trace.  A monitor stop retains the coherent
pre-occurrence normal state and the record's canonical first bad index.  An underlying abort is
kept distinct: this structural invariant makes no false claim that a BackTrack/parser failure is
a monitored collision. -/
def D2SRunOutcomeInvariant
    {α : Type}
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) α) : Prop :=
  match result with
  | .continue _ normal =>
      RateOnlyCacheCoherent normal ∧ ¬ BadEventDS.E normal.state.trace
  | .stopped normal record =>
      RateOnlyCacheCoherent normal ∧ BadEventDS.E_first_at record.trace record.firstBadIndex
  | .underlyingAbort => True

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- A continuing revised step is a valid first-bad runner state exactly when its successor has a
coherent rate-only cache.  Its `monitorPassed` field supplies the accompanying `¬ E` fact, so
later handler proofs never need to unpack that proof-carrying field manually. -/
lemma D2SRunOutcomeInvariant.continue
    {α : Type} (answer : α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant (.continue answer normal) :=
  ⟨hCoherent, normal.monitorPassed⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- A monitored terminal record carries the canonical first-bad witness of its own
post-occurrence trace.  This is the only terminal outcome charged by the Lemma 5.8 runner. -/
lemma D2SRunOutcomeInvariant.stopped
    {α : Type}
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (D2SRevisedStepResult.stopped (α := α) normal record) :=
  ⟨hCoherent, record.first_bad_at⟩

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- An underlying parser/search failure is deliberately outside the first-bad probability
charge.  Naming this trivial branch prevents the dispatcher induction from conflating it with a
monitor stop. -/
lemma D2SRunOutcomeInvariant.underlyingAbort
    {α : Type} :
    D2SRunOutcomeInvariant
      (D2SRevisedStepResult.underlyingAbort
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (α := α)) :=
  trivial

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- A deterministic hash-table hit appends its stored occurrence and leaves the permutation
table and rate-only cache unchanged.  Thus it preserves the complete first-bad runner invariant,
not merely hash-table functionality. -/
lemma d2sHandleHashPresentRevised_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sHandleHashPresentRevised normal stmt capacity hLookup) := by
  classical
  unfold d2sHandleHashPresentRevised
  dsimp
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp only [dif_pos hE]
    exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
  · simp only [dif_neg hE]
    apply D2SRunOutcomeInvariant.continue
    apply RateOnlyCacheCoherent.append_same_cache_and_permutation normal _ _ hCoherent <;> rfl

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- A hash-table hit adds only a redundant raw occurrence, hence it cannot trigger `Monitor`
after a monitor-passing normal state. -/
lemma d2sHandleHashPresentRevised_not_monitorStop
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = some capacity) :
    ¬ (d2sHandleHashPresentRevised normal stmt capacity hLookup).isMonitorStop := by
  unfold d2sHandleHashPresentRevised
  dsimp
  have hBase := BadEventDS.getBaseTrace_append_hash_lookup_eq normal.state.h_mirror hLookup
  have hNotE : ¬ BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩]) := by
    intro hE
    exact normal.monitorPassed ((BadEventDS.E_iff_of_getBaseTrace_eq hBase).mp hE)
  simp [hNotE]

/-- A deterministic fresh-hash continuation changes only the hash component of the lookup
structure.  Its permutation table and rate-only cache are unchanged, so it has the same
first-bad invariant as a hash hit. -/
lemma d2sHandleHashFreshRevised_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sHandleHashFreshRevised normal stmt capacity hLookup) := by
  classical
  unfold d2sHandleHashFreshRevised
  dsimp
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp only [dif_pos hE]
    exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
  · simp only [dif_neg hE]
    apply D2SRunOutcomeInvariant.continue
    apply RateOnlyCacheCoherent.append_same_cache_and_permutation normal _ _ hCoherent <;> rfl

/-- The complete live Step-2 hash handler preserves the first-bad runner invariant for every
value in its real `simulateQ` support.  A table hit is deterministic; a miss contributes only its
one sampled capacity, after which the deterministic fresh-hash lemma applies.  This is the hash
case consumed by the whole three-direction dispatcher proof. -/
lemma d2sHandleHashQueryRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hCoherent : RateOnlyCacheCoherent normal)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (Vector U SpongeSize.C))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleHashQueryRevised normal stmt))) :
    D2SRunOutcomeInvariant result := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some capacity =>
      rw [d2sHandleHashQueryRevised_hit normal stmt capacity hLookup,
        simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sHandleHashPresentRevised_maintainsInvariant normal stmt capacity hLookup hCoherent
  | none =>
      rw [d2sHandleHashQueryRevised_miss normal stmt hLookup,
        simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
      rw [simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sHandleHashFreshRevised_maintainsInvariant normal stmt capacity hLookup hCoherent

/-- A reverse-table hit selects an already installed normalized pair.  Its raw inverse
occurrence still passes through `Monitor`, while the reusable permutation table and rate-only
cache stay unchanged. -/
lemma d2sPermResolvedInverseHit_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sPermResolvedStep normal (.inverse stateOut stateIn)) := by
  rw [d2sPermResolvedStep_inverse]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_outlu_eq_some normal stateOut stateIn hLookup
  unfold d2sInstallPermInverseStateRevised
  split
  · rename_i hConflict
    exact False.elim (PermInstallStatus.noConfusion (hConflict.symm.trans hStatus))
  · rename_i hFresh
    exact False.elim (PermInstallStatus.noConfusion (hFresh.symm.trans hStatus))
  · rename_i _hPresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp only [dif_pos hE]
      exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
    · simp only [dif_neg hE]
      apply D2SRunOutcomeInvariant.continue
      apply RateOnlyCacheCoherent.append_same_cache_and_permutation normal _ _ hCoherent <;> rfl

/-- Replaying an installed inverse pair is likewise base-trace redundant and cannot stop at
`Monitor` from a monitor-passing normal state. -/
lemma d2sPermResolvedInverseHit_not_monitorStop
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn) :
    ¬ (d2sPermResolvedStep normal (.inverse stateOut stateIn)).isMonitorStop := by
  rw [d2sPermResolvedStep_inverse]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_outlu_eq_some normal stateOut stateIn hLookup
  unfold d2sInstallPermInverseStateRevised
  split
  · rename_i hConflict
    exact False.elim (PermInstallStatus.noConfusion (hConflict.symm.trans hStatus))
  · rename_i hFresh
    exact False.elim (PermInstallStatus.noConfusion (hFresh.symm.trans hStatus))
  · rename_i _hPresent
    have hBase := BadEventDS.D2SBaseTraceWitness.getBaseTraceAppendPermOutluLookup
      normal.state.h_mirror hLookup
    have hNotE : ¬ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) := by
      intro hE
      exact normal.monitorPassed ((BadEventDS.E_iff_of_getBaseTrace_eq hBase).mp hE)
    simp [hNotE]

/-- A reverse-table miss selects one sampled preimage.  If that fresh insertion continues, the
cache-output provenance rules out installing at a pending tail key; if it conflicts or causes a
bad event, the exact attempted inverse occurrence is retained in the stop record. -/
lemma d2sPermResolvedInverseMiss_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sPermResolvedStep normal (.inverse stateOut stateIn)) := by
  rw [d2sPermResolvedStep_inverse]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict :=
    permInstallStatus_fresh_or_conflict_of_outlu_eq_none normal stateIn stateOut hLookup
  unfold d2sInstallPermInverseStateRevised
  split
  · rename_i _hConflict
    exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
  · rename_i hFresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · simp only [dif_pos hE]
      exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
    · simp only [dif_neg hE]
      apply D2SRunOutcomeInvariant.continue
      apply RateOnlyCacheCoherent.inverse_miss_continue normal stateOut stateIn hCoherent hLookup
      unfold d2sInstallPermInverseStateRevised
      split
      · rename_i hConflict'
        exact False.elim (PermInstallStatus.noConfusion (hConflict'.symm.trans hFresh))
      · rename_i _hFresh'
        simp [hE]
      · rename_i hPresent'
        exact False.elim (PermInstallStatus.noConfusion (hPresent'.symm.trans hFresh))
  · rename_i hPresent
    exact False.elim (by
      rcases hStatus with hFresh | hConflict
      · exact PermInstallStatus.noConfusion (hPresent.symm.trans hFresh)
      · exact PermInstallStatus.noConfusion (hPresent.symm.trans hConflict))

/-- The live Step-3 inverse handler preserves the first-bad runner invariant at every value in
its `simulateQ` support.  The proof exposes exactly one sampled full state on a reverse-table
miss and otherwise uses the installed normalized pair. -/
lemma d2sHandleInversePermQueryRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleInversePermQueryRevised normal stateOut))) :
    D2SRunOutcomeInvariant result := by
  cases hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut with
  | some stateIn =>
      rw [d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup,
        simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sPermResolvedInverseHit_maintainsInvariant normal stateOut stateIn hLookup hCoherent
  | none =>
      rw [d2sHandleInversePermQueryRevised_miss normal stateOut hLookup,
        simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨stateIn, _hStateIn, hResult⟩ := hResult
      rw [simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sPermResolvedInverseMiss_maintainsInvariant normal stateOut stateIn hLookup hCoherent

/-- A forward lookup hit is a deterministic reuse of an already installed normalized pair.  The
raw occurrence still goes through `Monitor`; when it continues, neither the permutation table nor
the rate-only cache changes.  This is the table-hit subcase of Algorithm 5.3 Step 4.c.ii. -/
lemma d2sPermResolvedForwardHit_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  rw [d2sPermResolvedStep_forward]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_inlu_eq_some normal stateIn stateOut hLookup
  unfold d2sInstallPermForwardStateRevised
  split
  · rename_i hConflict
    exact False.elim (PermInstallStatus.noConfusion (hConflict.symm.trans hStatus))
  · rename_i hFresh
    exact False.elim (PermInstallStatus.noConfusion (hFresh.symm.trans hStatus))
  · rename_i _hPresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp only [dif_pos hE]
      exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
    · simp only [dif_neg hE]
      apply D2SRunOutcomeInvariant.continue
      apply RateOnlyCacheCoherent.append_same_cache_and_permutation normal _ _ hCoherent <;> rfl

/-- Replaying an already installed forward mapping cannot create a monitor stop from an
`E`-good normal state.  The added raw occurrence is redundant in the base trace, and
`E_iff_of_getBaseTrace_eq` transports the prior monitor certificate without any dependent-index
rewriting. -/
lemma d2sPermResolvedForwardHit_not_monitorStop
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    ¬ (d2sPermResolvedStep normal (.forward stateIn stateOut)).isMonitorStop := by
  rw [d2sPermResolvedStep_forward]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .present :=
    permInstallStatus_present_of_inlu_eq_some normal stateIn stateOut hLookup
  unfold d2sInstallPermForwardStateRevised
  split
  · rename_i hConflict
    exact False.elim (PermInstallStatus.noConfusion (hConflict.symm.trans hStatus))
  · rename_i hFresh
    exact False.elim (PermInstallStatus.noConfusion (hFresh.symm.trans hStatus))
  · rename_i _hPresent
    have hBase := BadEventDS.D2SBaseTraceWitness.getBaseTraceAppendPermInluLookup
      normal.state.h_mirror hLookup
    have hNotE : ¬ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) := by
      intro hE
      exact normal.monitorPassed ((BadEventDS.E_iff_of_getBaseTrace_eq hBase).mp hE)
    simp [hNotE]

/-- A forward table miss is coherent only after the dispatcher has ruled out a rate-only tail at
the same input.  Under that operational precedence condition, a fresh insertion carries the
cache/table provenance forward; a conflict or a monitored collision instead terminates at its
exact post-occurrence record.  This is Algorithm 5.3 Step 4.c.ii--iii without the sampling
wrapper. -/
lemma d2sPermResolvedForwardMiss_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SRunOutcomeInvariant
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) := by
  rw [d2sPermResolvedStep_forward]
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict :=
    permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal stateIn stateOut hLookup
  unfold d2sInstallPermForwardStateRevised
  split
  · rename_i _hConflict
    exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
  · rename_i hFresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · simp only [dif_pos hE]
      exact D2SRunOutcomeInvariant.stopped normal _ hCoherent
    · simp only [dif_neg hE]
      apply D2SRunOutcomeInvariant.continue
      apply RateOnlyCacheCoherent.forward_miss_continue normal stateIn stateOut hCoherent hPop
        hLookup
      unfold d2sInstallPermForwardStateRevised
      split
      · rename_i hConflict'
        exact False.elim (PermInstallStatus.noConfusion (hConflict'.symm.trans hFresh))
      · rename_i _hFresh'
        simp [hE]
      · rename_i hPresent'
        exact False.elim (PermInstallStatus.noConfusion (hPresent'.symm.trans hFresh))
  · rename_i hPresent
    exact False.elim (by
      rcases hStatus with hFresh | hConflict
      · exact PermInstallStatus.noConfusion (hPresent.symm.trans hFresh)
      · exact PermInstallStatus.noConfusion (hPresent.symm.trans hConflict))

/-- A selected lazy tail has the same whole-step invariant as every other resolved forward
action.  Its cache replacement is performed only after the common transition has continued; a
stop keeps the input normal state and its first-bad record, while the impossible raw abort branch
is preserved explicitly as the non-probabilistic outcome. -/
lemma d2sConsumePoppedRateOnlyTailRevised_maintainsInvariant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest)) :
    D2SRunOutcomeInvariant
      (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity) := by
  unfold d2sConsumePoppedRateOnlyTailRevised
  dsimp
  cases hSource : d2sInstallPermForwardStateRevised normal entry.stateIn
      (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  next stateOut sourceNormal =>
    have hAnswer : stateOut = (materializeRateOnlyCacheEntry (U := U) entry capacity).1 :=
      d2sInstallPermForwardStateRevised_continue_answer_eq normal entry.stateIn
        (materializeRateOnlyCacheEntry (U := U) entry capacity).1 stateOut sourceNormal hSource
    subst stateOut
    simp only [d2sReplaceRateCacheOnContinue_continue]
    apply D2SRunOutcomeInvariant.continue
    apply RateOnlyCacheCoherent.tail_continue normal entry cacheRest capacity hCoherent hPop
    simp [d2sConsumePoppedRateOnlyTailRevised, hSource]
  next sourceNormal record =>
    have hNormal : sourceNormal = normal := by
      apply d2sPermResolvedStep_stopped_normal_eq normal
        (.forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1)
      simpa only [d2sPermResolvedStep_forward] using hSource
    subst sourceNormal
    simp only [d2sReplaceRateCacheOnContinue_stopped]
    exact D2SRunOutcomeInvariant.stopped normal record hCoherent
  next =>
    simp only [d2sReplaceRateCacheOnContinue]
    exact D2SRunOutcomeInvariant.underlyingAbort

/-- The sampling form of a selected tail preserves the invariant at every support value of the
live simulator.  It exposes exactly its one capacity sample and then invokes the deterministic
tail-materialization lemma above; no full state, output capacity, or auxiliary oracle value is
sampled at tail creation time. -/
lemma d2sHandlePoppedRateOnlyTailRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq, simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  rw [simulateQ_pure, mem_support_pure_iff] at hResult
  subst result
  exact d2sConsumePoppedRateOnlyTailRevised_maintainsInvariant normal entry cacheRest capacity
    hCoherent hPop

/-- The non-tail forward path preserves the first-bad invariant.  Once the outer dispatcher has
proved that no rate-only tail begins at `stateIn`, the live handler either reuses the ordinary
forward-table value or samples exactly one full state for the ordinary-table miss. -/
lemma d2sHandleForwardNoResultRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardNoResultRevised normal stateIn))) :
    D2SRunOutcomeInvariant result := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      unfold d2sHandleForwardNoResultRevised at hResult
      rw [hPop, hLookup, simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sPermResolvedForwardHit_maintainsInvariant normal stateIn stateOut hLookup hCoherent
  | none =>
      rw [d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup,
        simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨stateOut, _hStateOut, hResult⟩ := hResult
      rw [simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact d2sPermResolvedForwardMiss_maintainsInvariant normal stateIn stateOut hPop hLookup
        hCoherent

/-- A fixed Program capacity is processed by the same first-bad gateway as every other forward
mapping.  On a continuing mapping, its residual rate blocks become the only newly stored lazy
tail; on a conflict or monitored event, the terminal occurrence is retained instead. -/
lemma d2sProgramFirstRateRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    D2SRunOutcomeInvariant
      (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity) := by
  unfold d2sProgramFirstRateRevised
  dsimp
  cases hSource : d2sInstallPermForwardStateRevised normal stateIn
      (d2sSynthesisState (U := U) firstRate capacity)
  next answer sourceNormal =>
    have hAnswer : answer = d2sSynthesisState (U := U) firstRate capacity :=
      d2sInstallPermForwardStateRevised_continue_answer_eq normal stateIn
        (d2sSynthesisState (U := U) firstRate capacity) answer sourceNormal hSource
    subst answer
    simp only [d2sReplaceRateCacheOnContinue_continue]
    apply D2SRunOutcomeInvariant.continue
    apply RateOnlyCacheCoherent.program_continue normal stateIn firstRate remainingRates capacity
      hCoherent hPop hLookup
    simp [d2sProgramFirstRateRevised, hSource]
  next sourceNormal record =>
    have hNormal : sourceNormal = normal := by
      apply d2sPermResolvedStep_stopped_normal_eq normal
        (.forward stateIn (d2sSynthesisState (U := U) firstRate capacity))
      simpa only [d2sPermResolvedStep_forward] using hSource
    subst sourceNormal
    simp only [d2sReplaceRateCacheOnContinue_stopped]
    exact D2SRunOutcomeInvariant.stopped normal record hCoherent
  next =>
    simp only [d2sReplaceRateCacheOnContinue]
    exact D2SRunOutcomeInvariant.underlyingAbort

/-- The sampling form of a Program first rate preserves the invariant for every sampled capacity.
The preceding parser may choose rate blocks, but it never samples an output capacity for a later
tail block. -/
lemma d2sHandleProgramFirstRateRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleProgramFirstRateRevised_eq, simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  rw [simulateQ_pure, mem_support_pure_iff] at hResult
  subst result
  exact d2sProgramFirstRateRevised_maintainsInvariant normal stateIn firstRate remainingRates
    capacity hCoherent hPop hLookup

/-- Step 4's cache-priority case preserves the invariant without invoking BackTrack. -/
lemma d2sHandleForwardPermQueryRevised_tail_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop] at hResult
  exact d2sHandlePoppedRateOnlyTailRevised_maintainsInvariant normal ⟨stateIn, tail⟩ cacheRest
    hCoherent hPop gImpl result hResult

/-- The BackTrack-error branch remains an underlying search abort, distinct from a monitored
post-occurrence stop. -/
lemma d2sHandleForwardPermQueryRevised_err_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hBacktrack : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
      (normal.state.trace.length + 1) = .err)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleForwardPermQueryRevised_err normal stateIn hPop hBacktrack,
    simulateQ_pure, mem_support_pure_iff] at hResult
  subst result
  exact D2SRunOutcomeInvariant.underlyingAbort

/-- Step 4.c of the outer forward dispatcher is exactly the non-tail handler above. -/
lemma d2sHandleForwardPermQueryRevised_noResult_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hBacktrack : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
      (normal.state.trace.length + 1) = .noResult)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPop hBacktrack] at hResult
  exact d2sHandleForwardNoResultRevised_maintainsInvariant normal stateIn hCoherent hPop
    gImpl result hResult

/-- Algorithm 5.3 Step 4.d follows the ordinary non-tail transition on an out-of-image tuple. -/
lemma d2sHandleBacktrackSomeRevised_notInImage_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : ¬ d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleBacktrackSomeRevised_notInImage normal stateIn backtrackOut hPop hImage] at hResult
  exact d2sHandleForwardNoResultRevised_maintainsInvariant normal stateIn hCoherent hPop
    gImpl result hResult

/-- An in-image tuple with an empty verifier challenge creates neither a `gᵢ` query nor a cache
record, so it has the same ordinary continuation as Step 4.c. -/
lemma d2sHandleBacktrackSomeRevised_emptyChallenge_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (hEmpty : ¬ 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleBacktrackSomeRevised_emptyChallenge normal stateIn backtrackOut hPop hImage hEmpty]
    at hResult
  exact d2sHandleForwardNoResultRevised_maintainsInvariant normal stateIn hCoherent hPop
    gImpl result hResult

/-- Once the `gᵢ` response is fixed, a pre-existing forward mapping wins before codec parsing or
Program capacity sampling. -/
lemma d2sHandleBacktrackAfterGRevised_hit_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat hLookup,
    simulateQ_pure, mem_support_pure_iff] at hResult
  subst result
  exact d2sPermResolvedForwardHit_maintainsInvariant normal stateIn stateOut hLookup hCoherent

/-- On a Program table miss, parser and padding choices are harmless to the transition invariant:
an empty parsed block list is the designated underlying abort, while every nonempty list enters
the already-verified one-capacity Program gateway. -/
lemma d2sHandleBacktrackAfterGRevised_miss_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleBacktrackAfterGRevised_miss normal stateIn backtrackOut rhoHat hLookup,
    simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨rateBlocks, _hRateBlocks, hResult⟩ := hResult
  cases hBlocks : rateBlocks.toList with
  | nil =>
      rw [hBlocks, simulateQ_pure, mem_support_pure_iff] at hResult
      subst result
      exact D2SRunOutcomeInvariant.underlyingAbort
  | cons firstRate remainingRates =>
      rw [hBlocks] at hResult
      exact d2sHandleProgramFirstRateRevised_maintainsInvariant normal stateIn firstRate
        remainingRates hCoherent hPop hLookup gImpl result hResult

/-- The complete post-`gᵢ` Program continuation preserves the invariant.  The ordinary table
lookup occurs before parser work, which is why the hit and miss proofs have disjoint sampling
stories. -/
lemma d2sHandleBacktrackAfterGRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) :
    D2SRunOutcomeInvariant result := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      exact d2sHandleBacktrackAfterGRevised_hit_maintainsInvariant normal stateIn stateOut
        backtrackOut rhoHat hCoherent hLookup gImpl result hResult
  | none =>
      exact d2sHandleBacktrackAfterGRevised_miss_maintainsInvariant normal stateIn backtrackOut
        rhoHat hCoherent hPop hLookup gImpl result hResult

/-- A nonempty in-image successful search makes precisely the encoded `gᵢ` query, then invokes
the complete post-`gᵢ` continuation above. -/
lemma d2sHandleBacktrackSomeRevised_nonemptyChallenge_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) :
    D2SRunOutcomeInvariant result := by
  rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge normal stateIn backtrackOut hPop hImage
    hNonempty, simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨rhoHat, _hRhoHat, hResult⟩ := hResult
  exact d2sHandleBacktrackAfterGRevised_maintainsInvariant normal stateIn backtrackOut rhoHat
    hCoherent hPop gImpl result hResult

/-- The complete live forward handler preserves the first-bad/cache invariant.  This is the
executable case tree of Algorithm 5.3 Step 4: lazy-tail priority; then BackTrack error, no
candidate, out-of-image/empty-challenge ordinary continuation, or nonempty in-image Program. -/
lemma d2sHandleForwardPermQueryRevised_maintainsInvariant
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (CanonicalSpongeState U))
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    D2SRunOutcomeInvariant result := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      exact d2sHandleForwardPermQueryRevised_tail_maintainsInvariant normal stateIn tail cacheRest
        hCoherent hPop gImpl result hResult
  | none =>
      cases hBacktrack : Backtrack.backTrack
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
          (normal.state.trace.length + 1) with
      | err =>
          exact d2sHandleForwardPermQueryRevised_err_maintainsInvariant normal stateIn hPop
            hBacktrack gImpl result hResult
      | noResult =>
          exact d2sHandleForwardPermQueryRevised_noResult_maintainsInvariant normal stateIn
            hCoherent hPop hBacktrack gImpl result hResult
      | some backtrackOut =>
          rw [d2sHandleForwardPermQueryRevised_some normal stateIn backtrackOut hPop hBacktrack]
            at hResult
          by_cases hImage : d2sInCodecImagePredicate
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
          · by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
            · exact d2sHandleBacktrackSomeRevised_nonemptyChallenge_maintainsInvariant normal
                stateIn backtrackOut hCoherent hPop hImage hNonempty gImpl result hResult
            · exact d2sHandleBacktrackSomeRevised_emptyChallenge_maintainsInvariant normal stateIn
                backtrackOut hCoherent hPop hImage hNonempty gImpl result hResult
          · exact d2sHandleBacktrackSomeRevised_notInImage_maintainsInvariant normal stateIn
              backtrackOut hCoherent hPop hImage gImpl result hResult

/-- Support-level preservation contract for one invocation of the actual three-direction revised
dispatcher.  The quantification ranges over the concrete simulation used by Lemma 5.8: a `gᵢ`
implementation, unit-capacity sampler, and uniform full-state oracle.  Thus an implementation
proof cannot accidentally establish the contract only for a hand-picked list of branch results. -/
def D2SQueryStepMaintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) : Prop :=
  ∀ (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
      (result : D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        ((duplexSpongeChallengeOracle StmtIn U).Range q)),
    result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)) →
      D2SRunOutcomeInvariant result

/-- The hash arm of the real three-direction dispatcher satisfies the common support-level
contract.  This is a direct re-keying of the live handler theorem, not a second dispatcher. -/
lemma d2sQueryStepRevised_hash_maintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SQueryStepMaintainsInvariant normal (dsHashQuery stmt) := by
  intro gImpl result hResult
  simpa only [d2sQueryStepRevised_hash] using
    d2sHandleHashQueryRevised_maintainsInvariant normal stmt hCoherent gImpl result hResult

/-- The inverse arm of the real three-direction dispatcher satisfies the common support-level
contract.  The only sampled value on a miss is the one full preimage selected by Step 3. -/
lemma d2sQueryStepRevised_inverse_maintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SQueryStepMaintainsInvariant normal (dsPermInvQuery stateOut) := by
  intro gImpl result hResult
  simpa only [d2sQueryStepRevised_inverse] using
    d2sHandleInversePermQueryRevised_maintainsInvariant normal stateOut hCoherent gImpl result
      hResult

/-- The forward arm of the public three-direction dispatcher satisfies the common contract. -/
lemma d2sQueryStepRevised_forward_maintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SQueryStepMaintainsInvariant normal (dsPermQuery stateIn) := by
  intro gImpl result hResult
  simpa only [d2sQueryStepRevised_forward] using
    d2sHandleForwardPermQueryRevised_maintainsInvariant normal stateIn hCoherent gImpl result
      hResult

/-- Reduce the whole live three-direction dispatcher to its forward arm.  The hash and inverse
arms are discharged above, so the only remaining handler proof for Lemma 5.8 is Algorithm 5.3
Step 4 with its cache-hit, table-hit, fresh-miss, and Program subcases. -/
lemma d2sQueryStepRevised_maintainsInvariant_of_forward
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hForward : ∀ stateIn : CanonicalSpongeState U,
      D2SQueryStepMaintainsInvariant normal (dsPermQuery stateIn)) :
    ∀ q : (duplexSpongeChallengeOracle StmtIn U).Domain,
      D2SQueryStepMaintainsInvariant normal q := by
  intro q
  match q with
  | dsHashQuery stmt =>
      exact d2sQueryStepRevised_hash_maintainsInvariant normal stmt hCoherent
  | dsPermInvQuery stateOut =>
      exact d2sQueryStepRevised_inverse_maintainsInvariant normal stateOut hCoherent
  | dsPermQuery stateIn => exact hForward stateIn

/-- Every concrete query direction of the revised D2SQuery dispatcher preserves the shared
first-bad/cache invariant.  The finite-run induction below can therefore use this theorem as its
single local premise. -/
lemma d2sQueryStepRevised_maintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal) :
    ∀ q : (duplexSpongeChallengeOracle StmtIn U).Domain,
      D2SQueryStepMaintainsInvariant normal q := by
  apply d2sQueryStepRevised_maintainsInvariant_of_forward normal hCoherent
  intro stateIn
  exact d2sQueryStepRevised_forward_maintainsInvariant normal stateIn hCoherent

/-- The deterministic continuation-growth contract for one invocation of the actual revised
dispatcher.  It belongs beside the dispatcher invariant, rather than in the probability layer:
every continuation in the concrete simulation may add at most one base-trace representative.
The first-bad aggregation consumes this contract without reopening any handler branch. -/
def D2SQueryStepContinueBaseLengthLe
    [VCVCompatible U] [Nonempty U] [SampleableType U] : Prop :=
  ∀ (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
    D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)) →
      (getBaseTrace normal'.state.trace).length ≤
        (getBaseTrace normal.state.trace).length + 1
/-- The exact trace counterpart of `D2SQueryStepContinueBaseLengthLe`.  A successful live
dispatcher invocation appends its one actual raw query-answer occurrence; it never merely
promises a cardinality bound.  This is the compositional history fact needed to connect the
stateful prover execution to its verifier continuation without reconstructing a trace from
lengths. -/
def D2SQueryStepContinueTraceExtension
    [VCVCompatible U] [Nonempty U] [SampleableType U] : Prop :=
  ∀ (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
    D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)) →
      ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
        normal'.state.trace = normal.state.trace ++ [occurrence]

/-- The hash arm exposes the actual occurrence selected by its hit or miss branch. -/
lemma d2sQueryStepRevised_hash_continue_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : Vector U SpongeSize.C)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal (dsHashQuery stmt)))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
  | some capacity =>
      rw [d2sQueryStepRevised_hash,
        d2sHandleHashQueryRevised_hit normal stmt capacity hLookup] at hResult
      change D2SRevisedStepResult.continue answer normal' ∈
        support (pure (d2sHandleHashPresentRevised normal stmt capacity hLookup)) at hResult
      rw [mem_support_pure_iff] at hResult
      refine ⟨⟨dsHashQuery stmt, capacity⟩, ?_⟩
      exact d2sHandleHashPresentRevised_continue_trace normal stmt capacity hLookup hResult.symm
  | none =>
      rw [d2sQueryStepRevised_hash,
        d2sHandleHashQueryRevised_miss normal stmt hLookup] at hResult
      change D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
          fun capacity => pure (d2sHandleHashFreshRevised normal stmt capacity hLookup))) at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
      change D2SRevisedStepResult.continue answer normal' ∈
        support (pure (d2sHandleHashFreshRevised normal stmt capacity hLookup)) at hResult
      rw [mem_support_pure_iff] at hResult
      refine ⟨⟨dsHashQuery stmt, capacity⟩, ?_⟩
      exact d2sHandleHashFreshRevised_continue_trace normal stmt capacity hLookup hResult.symm

/-- The inverse arm delegates to the common resolved inverse action, which records the queried
output and recovered preimage as its one raw occurrence. -/
lemma d2sQueryStepRevised_inverse_continue_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal (dsPermInvQuery stateOut)))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut with
  | some stateIn =>
      rw [d2sQueryStepRevised_inverse,
        d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup] at hResult
      change D2SRevisedStepResult.continue answer normal' ∈
        support (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) at hResult
      rw [mem_support_pure_iff] at hResult
      refine ⟨D2SPermResolvedAction.occurrence StmtIn (.inverse stateOut stateIn), ?_⟩
      exact d2sPermResolvedStep_continue_trace normal (.inverse stateOut stateIn) hResult.symm
  | none =>
      rw [d2sQueryStepRevised_inverse,
        d2sHandleInversePermQueryRevised_miss normal stateOut hLookup] at hResult
      change D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
          fun stateIn => pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)))) at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨stateIn, _hStateIn, hResult⟩ := hResult
      change D2SRevisedStepResult.continue answer normal' ∈
        support (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) at hResult
      rw [mem_support_pure_iff] at hResult
      refine ⟨D2SPermResolvedAction.occurrence StmtIn (.inverse stateOut stateIn), ?_⟩
      exact d2sPermResolvedStep_continue_trace normal (.inverse stateOut stateIn) hResult.symm

/-- A lazy-tail hit appends the materialized forward pair and nothing else to the raw trace. -/
lemma d2sHandlePoppedRateOnlyTailRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  rw [d2sHandlePoppedRateOnlyTailRevised_eq normal entry cacheRest] at hResult
  change D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
    (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
    (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
      fun capacity =>
        pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity))) at hResult
  rw [simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  change D2SRevisedStepResult.continue answer normal' ∈
    support (pure (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity)) at hResult
  rw [mem_support_pure_iff] at hResult
  refine ⟨⟨dsPermQuery entry.stateIn,
    (materializeRateOnlyCacheEntry (U := U) entry capacity).1⟩, ?_⟩
  exact d2sConsumePoppedRateOnlyTailRevised_continue_trace normal entry cacheRest capacity
    hResult.symm

/-- The first Program block is the sole raw occurrence of a successful Program transition;
later rate blocks remain latent in `Cache_p`. -/
lemma d2sHandleProgramFirstRateRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  rw [d2sHandleProgramFirstRateRevised_eq normal stateIn firstRate remainingRates] at hResult
  change D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
    (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
    (d2sSampleCapacity (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
      fun capacity =>
        pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity)))
      at hResult
  rw [simulateQ_bind, mem_support_bind_iff] at hResult
  obtain ⟨capacity, _hCapacity, hResult⟩ := hResult
  change D2SRevisedStepResult.continue answer normal' ∈ support
    (pure (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity)) at hResult
  rw [mem_support_pure_iff] at hResult
  refine ⟨⟨dsPermQuery stateIn, d2sSynthesisState (U := U) firstRate capacity⟩, ?_⟩
  exact d2sProgramFirstRateRevised_continue_trace normal stateIn firstRate remainingRates capacity
    hResult.symm

/-- The ordinary Step 4.c continuation is trace-exact in all three operational cases. -/
lemma d2sHandleForwardNoResultRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardNoResultRevised normal stateIn))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardNoResultRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_continue_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl answer normal' hResult
  | none =>
      cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
      | some stateOut =>
          rw [d2sHandleForwardNoResultRevised_table normal stateIn stateOut hPop hLookup]
            at hResult
          change D2SRevisedStepResult.continue answer normal' ∈
            support (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
          rw [mem_support_pure_iff] at hResult
          refine ⟨D2SPermResolvedAction.occurrence StmtIn (.forward stateIn stateOut), ?_⟩
          exact d2sPermResolvedStep_continue_trace normal (.forward stateIn stateOut) hResult.symm
      | none =>
          rw [d2sHandleForwardNoResultRevised_fresh normal stateIn hPop hLookup] at hResult
          change D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
            (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
            (d2sSampleState (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) >>=
              fun stateOut => pure (d2sPermResolvedStep normal (.forward stateIn stateOut))))
              at hResult
          rw [simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨stateOut, _hStateOut, hResult⟩ := hResult
          change D2SRevisedStepResult.continue answer normal' ∈
            support (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
          rw [mem_support_pure_iff] at hResult
          refine ⟨D2SPermResolvedAction.occurrence StmtIn (.forward stateIn stateOut), ?_⟩
          exact d2sPermResolvedStep_continue_trace normal (.forward stateIn stateOut) hResult.symm

/-- After a reissued `gᵢ` value, only the actual first Program block can extend the trace. -/
lemma d2sHandleBacktrackAfterGRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      rw [d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat hLookup]
        at hResult
      change D2SRevisedStepResult.continue answer normal' ∈
        support (pure (d2sPermResolvedStep normal (.forward stateIn stateOut))) at hResult
      rw [mem_support_pure_iff] at hResult
      refine ⟨D2SPermResolvedAction.occurrence StmtIn (.forward stateIn stateOut), ?_⟩
      exact d2sPermResolvedStep_continue_trace normal (.forward stateIn stateOut) hResult.symm
  | none =>
      rw [d2sHandleBacktrackAfterGRevised_miss normal stateIn backtrackOut rhoHat hLookup]
        at hResult
      rw [simulateQ_bind, mem_support_bind_iff] at hResult
      obtain ⟨rateBlocks, _hRateBlocks, hResult⟩ := hResult
      cases hBlocks : rateBlocks.toList with
      | nil =>
          rw [hBlocks] at hResult
          simp at hResult
      | cons firstRate remainingRates =>
          rw [hBlocks] at hResult
          exact d2sHandleProgramFirstRateRevised_continue_trace_extension_of_support normal
            stateIn firstRate remainingRates gImpl answer normal' hResult

/-- A recovered Backtrack candidate has the same trace-exact continuation property as an
ordinary forward miss: a pending tail, a table hit, or the first Program block supplies the
single appended occurrence. -/
lemma d2sHandleBacktrackSomeRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleBacktrackSomeRevised_tail normal stateIn backtrackOut tail cacheRest hPop]
        at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_continue_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl answer normal' hResult
  | none =>
      by_cases hImage : d2sInCodecImagePredicate
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
      · by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
        · rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge normal stateIn backtrackOut hPop
            hImage hNonempty, simulateQ_bind, mem_support_bind_iff] at hResult
          obtain ⟨rhoHat, _hRhoHat, hResult⟩ := hResult
          exact d2sHandleBacktrackAfterGRevised_continue_trace_extension_of_support normal
            stateIn backtrackOut rhoHat gImpl answer normal' hResult
        · rw [d2sHandleBacktrackSomeRevised_emptyChallenge normal stateIn backtrackOut hPop
            hImage hNonempty] at hResult
          exact d2sHandleForwardNoResultRevised_continue_trace_extension_of_support normal
            stateIn gImpl answer normal' hResult
      · rw [d2sHandleBacktrackSomeRevised_notInImage normal stateIn backtrackOut hPop hImage]
          at hResult
        exact d2sHandleForwardNoResultRevised_continue_trace_extension_of_support normal
          stateIn gImpl answer normal' hResult

/-- The full forward dispatcher has no hidden trace effect before its selected continuation.
Search failure is terminal; every successful search result reduces to an already trace-exact
ordinary or Program branch. -/
lemma d2sHandleForwardPermQueryRevised_continue_trace_extension_of_support
    [VCVCompatible U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (answer : CanonicalSpongeState U)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hResult : D2SRevisedStepResult.continue answer normal' ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sHandleForwardPermQueryRevised normal stateIn))) :
    ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
      normal'.state.trace = normal.state.trace ++ [occurrence] := by
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop] at hResult
      exact d2sHandlePoppedRateOnlyTailRevised_continue_trace_extension_of_support normal
        ⟨stateIn, tail⟩ cacheRest gImpl answer normal' hResult
  | none =>
      cases hSearch : Backtrack.backTrack
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
          (normal.state.trace.length + 1) with
      | err =>
          rw [d2sHandleForwardPermQueryRevised_err normal stateIn hPop hSearch] at hResult
          change D2SRevisedStepResult.continue answer normal' ∈ support (pure .underlyingAbort)
            at hResult
          simp at hResult
      | noResult =>
          rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPop hSearch] at hResult
          exact d2sHandleForwardNoResultRevised_continue_trace_extension_of_support normal
            stateIn gImpl answer normal' hResult
      | some backtrackOut =>
          rw [d2sHandleForwardPermQueryRevised_some normal stateIn backtrackOut hPop hSearch]
            at hResult
          exact d2sHandleBacktrackSomeRevised_continue_trace_extension_of_support normal
            stateIn backtrackOut gImpl answer normal' hResult

/-- Every live successful D2SQuery step appends exactly one raw occurrence.  This is stronger
than the first-bad cardinality contract and is the bridge used by the shared prover→verifier
execution to retain the actual global trace history. -/
lemma d2sQueryStepRevised_continue_trace_extension
    [VCVCompatible U] [Nonempty U] [SampleableType U] :
    D2SQueryStepContinueTraceExtension
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) := by
  intro normal q gImpl answer normal' hResult
  cases q with
  | inl stmt =>
      exact d2sQueryStepRevised_hash_continue_trace_extension normal stmt gImpl answer normal'
        hResult
  | inr q =>
      cases q with
      | inl stateIn =>
          simpa only [d2sQueryStepRevised_forward] using
            d2sHandleForwardPermQueryRevised_continue_trace_extension_of_support normal
              stateIn gImpl answer normal' hResult
      | inr stateOut =>
          simpa only [d2sQueryStepRevised_inverse] using
            d2sQueryStepRevised_inverse_continue_trace_extension normal stateOut gImpl answer
              normal' hResult

/-- The first-bad cardinality contract is now a one-line consequence of exact raw-history
extension.  This is intentionally stated after the stronger theorem so later proofs never need
to reopen the seven dispatcher branches merely to recover a length bound. -/
lemma d2sQueryStepRevised_continue_baseTrace_length_le
    [VCVCompatible U] [Nonempty U] [SampleableType U] :
    D2SQueryStepContinueBaseLengthLe
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) := by
  intro normal q gImpl answer normal' hResult
  obtain ⟨occurrence, hTrace⟩ :=
    d2sQueryStepRevised_continue_trace_extension normal q gImpl answer normal' hResult
  rw [hTrace]
  exact getBaseTrace_append_singleton_length_le_succ normal.state.trace occurrence

end DuplexSpongeFS.ProverTransform
