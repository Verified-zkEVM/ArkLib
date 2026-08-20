/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CacheTraceBridges

/-!
# First-bad gateway interface for revised D2SQuery

The revised D2SQuery branches all end in the same `Install → append one occurrence → Monitor`
transition.  This module exposes that fact through a small, answer-independent interface:

* `D2SRevisedStepResult.isMonitorStop` is the only terminal outcome charged by the first-bad-event
  proof; it is distinct from a reusable continuation and from a search/parser abort.
* `D2SPermResolvedAction.occurrence` gives the one actual forward or inverse oracle occurrence
  selected before that common tail.
* a resolved forward/inverse action stops at `Monitor` **iff** appending exactly that occurrence to
  its E-good normal prefix makes `E` hold.

Consequently the probability proof never destructs the dependent stop record.  A sampling gateway
only has to normalize the one-occurrence `E` event to a finite capacity target, then invoke the
uniform-sample lemma.  This is the core compression needed to keep the revised Lemma 5.8 proof
small and branch-neutral.
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

omit [DecidableEq StmtIn] [DecidableEq U] in
@[simp] lemma D2SPermResolvedAction.occurrence_forward
    (stateIn stateOut : CanonicalSpongeState U) :
    D2SPermResolvedAction.occurrence StmtIn (.forward stateIn stateOut) =
      ⟨dsPermQuery stateIn, stateOut⟩ := rfl

omit [DecidableEq StmtIn] [DecidableEq U] in
@[simp] lemma D2SPermResolvedAction.occurrence_inverse
    (stateOut stateIn : CanonicalSpongeState U) :
    D2SPermResolvedAction.occurrence StmtIn (.inverse stateOut stateIn) =
      ⟨dsPermInvQuery stateOut, stateIn⟩ := rfl

/-- A fresh hash-table miss has a monitor stop exactly when its one appended hash occurrence
makes the bad event true.  This is the hash analogue of the resolved permutation gateway below;
it lets the first-event proof treat all three sampled directions uniformly. -/
lemma d2sHandleHashFreshRevised_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    (d2sHandleHashFreshRevised normal stmt capacity hLookup).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩]) := by
  classical
  by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
  · simp [d2sHandleHashFreshRevised, hE]
  · simp [d2sHandleHashFreshRevised, hE]

/-- A resolved forward action has a monitor stop exactly when its one appended forward occurrence
makes the bad event true.  The `conflict` case is already certified by the conflict crux; the
`fresh` and `present` cases expose the same test performed by the executable transition. -/
lemma d2sInstallPermForwardStateRevised_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U) :
    (d2sInstallPermForwardStateRevised normal stateIn stateOut).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) := by
  classical
  unfold d2sInstallPermForwardStateRevised
  split
  · rename_i hConflict
    change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    exact (iff_true_intro (install_conflict_fwd_imp_E normal hConflict)).symm
  · rename_i _hFresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · rw [dif_pos hE]
      change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      exact (iff_true_intro hE).symm
    · rw [dif_neg hE]
      change False ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      exact (iff_false_intro hE).symm
  · rename_i _hPresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    · rw [dif_pos hE]
      change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      exact (iff_true_intro hE).symm
    · rw [dif_neg hE]
      change False ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      exact (iff_false_intro hE).symm

/-- The inverse counterpart of
`d2sInstallPermForwardStateRevised_isMonitorStop_iff`, retaining the actual inverse occurrence in
the raw trace. -/
lemma d2sInstallPermInverseStateRevised_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U) :
    (d2sInstallPermInverseStateRevised normal stateOut stateIn).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) := by
  classical
  unfold d2sInstallPermInverseStateRevised
  split
  · rename_i hConflict
    change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    exact (iff_true_intro (install_conflict_inv_imp_E normal hConflict)).symm
  · rename_i _hFresh
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · rw [dif_pos hE]
      change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      exact (iff_true_intro hE).symm
    · rw [dif_neg hE]
      change False ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      exact (iff_false_intro hE).symm
  · rename_i _hPresent
    by_cases hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    · rw [dif_pos hE]
      change True ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      exact (iff_true_intro hE).symm
    · rw [dif_neg hE]
      change False ↔ BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      exact (iff_false_intro hE).symm

/-- The branch-neutral first-bad gateway.  Once a branch has selected its exact direction-tagged
pair, the monitor-stop event is precisely `E` on the normal trace extended by that pair's actual
oracle occurrence.  No dependent record equality or separate conflict case remains for later
probability proofs. -/
lemma d2sPermResolvedStep_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (action : D2SPermResolvedAction U) :
    (d2sPermResolvedStep normal action).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++ [action.occurrence StmtIn]) := by
  cases action with
  | forward stateIn stateOut =>
      simpa using d2sInstallPermForwardStateRevised_isMonitorStop_iff normal stateIn stateOut
  | inverse stateOut stateIn =>
      simpa using d2sInstallPermInverseStateRevised_isMonitorStop_iff normal stateOut stateIn

/-- The execution invariant required when a rate-only tail is selected: its materialization key
is not already a reusable forward-table input.  It is deliberately a property of a *realized
run*, not a property of an arbitrary `D2SNormalState`: the bare state stores a cache list but not
the history showing why each key was created.  The first-event runner will establish and preserve
this invariant from dispatcher order, Program creation, tail removal/re-keying, and the
monitor-passing inverse branch.  In particular, it must not be inferred from `¬ E` alone. -/
def RateOnlyCacheKeysAreTableMissesAt
    (trΔ : TraceNabla T_H T_P StmtIn U)
    (cache : List (RateOnlyCacheEntry (U := U))) : Prop :=
  ∀ entry : RateOnlyCacheEntry (U := U), entry ∈ cache →
    TraceTableOps.inlu trΔ.p entry.stateIn = none

/-- The table-miss component of the realized rate-only cache invariant, specialized to a normal
D2SQuery state.  The table/cache-separated form `RateOnlyCacheKeysAreTableMissesAt` is also used
when a Program or tail transition has recovered its underlying common `Install` successor. -/
def RateOnlyCacheKeysAreTableMisses
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  ∀ entry : RateOnlyCacheEntry (U := U), entry ∈ normal.state.rateCacheP →
    TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none

/-- A rate-only cache key is not arbitrary state: it is the output of a normalized permutation
pair already recorded in the insertion trace.  The witness is intentionally retained in its real
direction-tagged form.  A prior forward occurrence and a prior inverse occurrence both represent
the same normalized pair, and both are needed when an inverse query is checked against a pending
tail key. -/
def RateOnlyCacheKeyHasOutputWitness
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (entry : RateOnlyCacheEntry (U := U)) : Prop :=
  ∃ source : CanonicalSpongeState U,
    (⟨dsPermQuery source, entry.stateIn⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
      (⟨dsPermInvQuery entry.stateIn, source⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace

/-- Trace-realized provenance for every pending rate-only cache key.  Unlike a bare table miss,
this survives appending any later query by ordinary list monotonicity and records exactly why an
inverse insertion at a cache key would trigger `Monitor`. -/
def RateOnlyCacheKeysHaveOutputWitnesses
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (cache : List (RateOnlyCacheEntry (U := U))) : Prop :=
  ∀ entry : RateOnlyCacheEntry (U := U), entry ∈ cache →
    RateOnlyCacheKeyHasOutputWitness trace entry

/-- The execution invariant for the real rate-only cache.  Every key has a trace-level output
origin, is absent from the reusable forward table, and occurs at most once in the pending cache.
The last property is essential because `popRateOnlyTailByInput` removes one record.  None of
these facts is inferred from `¬ E` for an arbitrary normal state: the revised whole-run
refinement establishes them from the empty cache and preserves them branch by branch. -/
structure RateOnlyCacheCoherent
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop where
  outputWitnesses : RateOnlyCacheKeysHaveOutputWitnesses normal.state.trace normal.state.rateCacheP
  tableMisses : RateOnlyCacheKeysAreTableMisses normal
  keyNodup : RateOnlyCacheKeysNodup normal.state.rateCacheP

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- The monitored D2SQuery initial state has no pending rate-only tail, hence satisfies cache
coherence without any protocol-side condition.  This is the base case for the future whole-run
first-bad induction. -/
lemma RateOnlyCacheCoherent.initial :
    RateOnlyCacheCoherent
      (D2SNormalState.initial
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  constructor
  · intro entry hEntry
    change entry ∈ ([] : List (RateOnlyCacheEntry (U := U))) at hEntry
    simp at hEntry
  · intro entry hEntry
    change entry ∈ ([] : List (RateOnlyCacheEntry (U := U))) at hEntry
    simp at hEntry
  · change RateOnlyCacheKeysNodup ([] : List (RateOnlyCacheEntry (U := U)))
    simp [RateOnlyCacheKeysNodup]

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- Existing cache-output witnesses survive any newly appended insertion occurrence. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.append
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (cache : List (RateOnlyCacheEntry (U := U)))
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses trace cache)
    (occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    RateOnlyCacheKeysHaveOutputWitnesses (trace ++ [occurrence]) cache := by
  intro entry hEntry
  rcases hWitnesses entry hEntry with ⟨source, hForward | hInverse⟩
  · exact ⟨source, Or.inl (List.mem_append_left _ hForward)⟩
  · exact ⟨source, Or.inr (List.mem_append_left _ hInverse)⟩

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- A continuing Program materialization gives the newly scheduled tail a direct forward-output
witness, while transporting all older cache witnesses over that one appended occurrence. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.programResidual
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (remainingRates : List (Vector U SpongeSize.R))
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses normal.state.trace normal.state.rateCacheP) :
    RateOnlyCacheKeysHaveOutputWitnesses
      (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      (programResidualRateCache normal stateOut remainingRates) := by
  unfold programResidualRateCache
  cases hTail : RateOnlyTail.ofBlocks? (U := U) remainingRates with
  | none =>
      exact RateOnlyCacheKeysHaveOutputWitnesses.append _ _ hWitnesses
        (⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
  | some tail =>
      intro entry hEntry
      change entry ∈ (⟨stateOut, tail⟩ :: normal.state.rateCacheP) at hEntry
      rcases List.mem_cons.mp hEntry with hEntry | hEntry
      · subst entry
        exact ⟨stateIn, Or.inl (by simp)⟩
      · exact RateOnlyCacheKeysHaveOutputWitnesses.append _ _ hWitnesses
          (⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          entry hEntry

omit [DecidableEq StmtIn] in
/-- A continuing tail materialization transports the witnesses of every retained cache record and
creates a direct forward-output witness for its residual record, when one exists.  The proof uses
only the exact cache pop and re-key operations; it does not pre-sample any later capacity. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.tailResidual
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (cache : List (RateOnlyCacheEntry (U := U)))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses trace cache)
    (hPop : popRateOnlyTailByInput cache entry.stateIn = some (entry.tail, cacheRest)) :
    RateOnlyCacheKeysHaveOutputWitnesses
      (trace ++ [⟨dsPermQuery entry.stateIn,
        (materializeRateOnlyCacheEntry (U := U) entry capacity).1⟩])
      (rateOnlyTailResidualCache entry cacheRest capacity) := by
  let stateOut := (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  have hRest : ∀ retained : RateOnlyCacheEntry (U := U), retained ∈ cacheRest → retained ∈ cache :=
    popRateOnlyTailByInput_rest_subset cache entry.stateIn entry.tail cacheRest hPop
  unfold rateOnlyTailResidualCache
  cases hSuccessor : (materializeRateOnlyCacheEntry (U := U) entry capacity).2 with
  | none =>
      intro retained hRetained
      exact RateOnlyCacheKeysHaveOutputWitnesses.append _ _ hWitnesses
        (⟨dsPermQuery entry.stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
        retained (hRest retained hRetained)
  | some successor =>
      intro retained hRetained
      rcases List.mem_cons.mp (by simpa [hSuccessor] using hRetained) with hRetained | hRetained
      · subst retained
        have hKey : successor.stateIn = stateOut :=
          materializeRateOnlyCacheEntry_some_stateIn entry capacity successor hSuccessor
        exact ⟨entry.stateIn, Or.inl (by simp [hKey, stateOut])⟩
      · exact RateOnlyCacheKeysHaveOutputWitnesses.append _ _ hWitnesses
          (⟨dsPermQuery entry.stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          retained (hRest retained hRetained)

omit [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Apply the named cache-key invariant to the tail selected by the dispatcher. -/
lemma RateOnlyCacheKeysAreTableMisses.lookup_miss
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    {entry : RateOnlyCacheEntry (U := U)}
    (hEntry : entry ∈ normal.state.rateCacheP) :
    TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none :=
  hKeys entry hEntry

/-- A fresh inverse installation can never return a pending cache key as its preimage on a
continuing path.  The cache provenance supplies a prior normalized output; the failed reverse
lookup makes the new inverse occurrence a fresh base entry; and the cache-trace bridge therefore
forces `E_{p^{-1}}`.  This is the inverse half of cache/table separation.

The lemma intentionally says nothing about an inverse **table hit**: that occurrence is
redundant and leaves the table unchanged.  Only a reverse-table miss could introduce a cache key
as a new table input, and that is the case ruled out here. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.inverse_miss_not_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses normal.state.trace normal.state.rateCacheP)
    (hEntry : entry ∈ normal.state.rateCacheP)
    (hInput : stateIn = entry.stateIn)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermInverseStateRevised normal stateOut stateIn =
      .continue stateIn normal') :
    False := by
  subst stateIn
  have hPriorRaw := hWitnesses entry hEntry
  have hPrior :
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inl priorIn), entry.stateIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace normal.state.trace) ∨
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inr entry.stateIn), priorIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace normal.state.trace) := by
    rcases hPriorRaw with ⟨source, hForward | hInverse⟩
    · rcases normalizedPermPair_mem_getBaseTrace_of_mem normal.state.trace
          source entry.stateIn (Or.inl hForward) with hBase | hBase
      · exact Or.inl ⟨source, hBase⟩
      · exact Or.inr ⟨source, hBase⟩
    · rcases normalizedPermPair_mem_getBaseTrace_of_mem normal.state.trace
          source entry.stateIn (Or.inr hInverse) with hBase | hBase
      · exact Or.inl ⟨source, hBase⟩
      · exact Or.inr ⟨source, hBase⟩
  have hOutputWf : BadEventDS.D2SBaseTraceWitness.PermOutputWellformed
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) normal.state.trΔ :=
    ⟨normal.permutationNodup, normal.table_outputFunctional⟩
  have hBase : getBaseTrace
      (normal.state.trace ++ [⟨dsPermInvQuery stateOut, entry.stateIn⟩]) =
      getBaseTrace normal.state.trace ++ [⟨dsPermInvQuery stateOut, entry.stateIn⟩] :=
    BadEventDS.D2SBaseTraceWitness.getBaseTraceAppendPermOutluMiss hOutputWf
      normal.state.h_mirror hLookup
  have hPinv : BadEventDS.E_pinv_at
      (normal.state.trace ++ [⟨dsPermInvQuery stateOut, entry.stateIn⟩])
      (getBaseTrace normal.state.trace).length :=
    BadEventDS.E_pinv_at_append_inverse_of_prior_output_capacity normal.state.trace stateOut
      entry.stateIn hPrior hBase
  have hBad : BadEventDS.E
      (normal.state.trace ++ [⟨dsPermInvQuery stateOut, entry.stateIn⟩]) :=
    (BadEventDS.E_iff_exists_E_at _).mpr
      ⟨(getBaseTrace normal.state.trace).length, Or.inr (Or.inr (Or.inl hPinv))⟩
  have hStop :=
    (d2sInstallPermInverseStateRevised_isMonitorStop_iff normal stateOut entry.stateIn).mpr hBad
  rw [hContinue] at hStop
  simp at hStop

/-- Adding one fresh table pair preserves a forward lookup miss at every other input.  This is
the table-only half of rate-cache preservation; the D2S-specific lemmas supply the fact that a
re-keyed output is different from the just-added input. -/
lemma inlu_add_preserves_miss_away_from_input
    (table : T_P)
    (addedInput addedOutput lookupInput : CanonicalSpongeState U)
    (hNodup : (LawfulTraceTable.toMultiSet table).Nodup)
    (hFunctional : TraceTableOps.InputFunctional table)
    (hMiss : TraceTableOps.inlu table lookupInput = none)
    (hDistinct : lookupInput ≠ addedInput) :
    TraceTableOps.inlu (TraceTableOps.add table addedInput addedOutput) lookupInput = none := by
  cases hNew : TraceTableOps.inlu
      (TraceTableOps.add table addedInput addedOutput) lookupInput with
  | none => rfl
  | some priorOutput =>
      have hMem : (lookupInput, priorOutput) ∈
          TraceTableOps.entries (TraceTableOps.add table addedInput addedOutput) :=
        TraceTableOps.mem_entries_of_inlu_eq_some hNew
      rw [TraceTableOps.mem_entries_add_iff] at hMem
      rcases hMem with hAdded | hOld
      · have hEq : lookupInput = addedInput := congrArg Prod.fst hAdded
        exact False.elim (hDistinct hEq)
      · have hOldMs : (lookupInput, priorOutput) ∈ LawfulTraceTable.toMultiSet table := by
          rw [← LawfulTraceTable.toMultiSet_ofEntries]
          exact Multiset.mem_coe.mpr hOld
        exact False.elim
          (TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
            hNodup hFunctional hMiss priorOutput hOldMs)

/-- A continuing forward installation cannot leave its freshly returned state as a reusable
forward-table input.  An old pair at that input would make the new output capacity duplicate a
prior query capacity; the self-input case makes it duplicate the current query capacity.  Either
one creates `E_p` at the appended base entry, contradicting the successor's passed `Monitor`.

This is the cache-rekey separation fact: a Program or consumed-tail residual may be keyed by the
new output state without pre-sampling a capacity or carrying a separate no-alias premise. -/
lemma d2sInstallPermForwardStateRevised_continue_output_is_table_miss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut normal') :
    TraceTableOps.inlu normal'.state.trΔ.p stateOut = none := by
  let hInputWf : BadEventDS.D2SBaseTraceWitness.PermInputWellformed
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) normal.state.trΔ :=
    ⟨normal.permutationNodup, normal.table_inputFunctional⟩
  have hBase : getBaseTrace
      (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) =
      getBaseTrace normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] :=
    BadEventDS.D2SBaseTraceWitness.getBaseTraceAppendPermInluMiss hInputWf
      normal.state.h_mirror hLookup
  have hTrace : normal'.state.trace =
      normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] :=
    d2sInstallPermForwardStateRevised_continue_trace normal stateIn stateOut hContinue
  have hOldOutputInput : TraceTableOps.inlu normal.state.trΔ.p stateOut = none := by
    cases hOld : TraceTableOps.inlu normal.state.trΔ.p stateOut with
    | none => rfl
    | some priorOut =>
        have hPriorRaw := BadEventDS.D2SBaseTraceWitness.permInluPairMemBaseTrace
          normal.state.h_mirror hOld
        have hPrior :
            (∃ priorOut : CanonicalSpongeState U,
              (⟨.inr (.inl stateOut), priorOut⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
                getBaseTrace normal.state.trace) ∨
            (∃ priorOut : CanonicalSpongeState U,
              (⟨.inr (.inr priorOut), stateOut⟩ :
                Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
                getBaseTrace normal.state.trace) := by
          rcases hPriorRaw with hForward | hInverse
          · exact Or.inl ⟨priorOut, hForward⟩
          · exact Or.inr ⟨priorOut, hInverse⟩
        have hEp : BadEventDS.E_p_at
            (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
            (getBaseTrace normal.state.trace).length :=
          BadEventDS.E_p_at_append_forward_of_prior_query_capacity
            normal.state.trace stateIn stateOut hPrior hBase
        have hBad : BadEventDS.E
            (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) :=
          (BadEventDS.E_iff_exists_E_at _).mpr
            ⟨(getBaseTrace normal.state.trace).length, Or.inr (Or.inl hEp)⟩
        exact False.elim (normal'.monitorPassed (by rwa [hTrace]))
  have hDistinct : stateIn ≠ stateOut := by
    intro hEq
    have hEp : BadEventDS.E_p_at
        (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
        (getBaseTrace normal.state.trace).length :=
      BadEventDS.E_p_at_append_forward_of_current_query_capacity normal.state.trace
        stateIn stateOut (by subst stateOut; rfl) hBase
    have hBad : BadEventDS.E
        (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) :=
      (BadEventDS.E_iff_exists_E_at _).mpr
        ⟨(getBaseTrace normal.state.trace).length, Or.inr (Or.inl hEp)⟩
    exact normal'.monitorPassed (by rwa [hTrace])
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh := by
    rcases permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal stateIn stateOut hLookup with
      hFresh | hConflict
    · exact hFresh
    · have hStop :=
        (d2sInstallPermForwardStateRevised_isMonitorStop_iff normal stateIn stateOut).mpr
          (install_conflict_fwd_imp_E normal hConflict)
      rw [hContinue] at hStop
      simp at hStop
  have hTable : normal'.state.trΔ.p =
      TraceTableOps.add normal.state.trΔ.p stateIn stateOut :=
    d2sInstallPermForwardStateRevised_continue_table_fresh normal stateIn stateOut
      hStatus hContinue
  rw [hTable]
  exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p stateIn stateOut stateOut
    normal.permutationNodup normal.table_inputFunctional hOldOutputInput
    (fun hEq => hDistinct hEq.symm)

/-- A continuing fresh forward installation cannot re-key a pending tail at a state that is
already a pending-tail key.  Cache provenance turns such an equality into a prior permutation
output with the same full state, hence into `E_p` at the newly appended occurrence.  This gives
the Program and tail-rekey branches their cache-key freshness from `Monitor`, rather than from an
unstated scheduler side condition. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.forward_output_not_cache_key_on_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses normal.state.trace normal.state.rateCacheP)
    (hEntry : entry ∈ normal.state.rateCacheP)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut normal') :
    entry.stateIn ≠ stateOut := by
  intro hEq
  subst stateOut
  have hPriorRaw := hWitnesses entry hEntry
  have hPrior :
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inl priorIn), entry.stateIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace normal.state.trace) ∨
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inr entry.stateIn), priorIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace normal.state.trace) := by
    rcases hPriorRaw with ⟨source, hForward | hInverse⟩
    · rcases normalizedPermPair_mem_getBaseTrace_of_mem normal.state.trace
          source entry.stateIn (Or.inl hForward) with hBase | hBase
      · exact Or.inl ⟨source, hBase⟩
      · exact Or.inr ⟨source, hBase⟩
    · rcases normalizedPermPair_mem_getBaseTrace_of_mem normal.state.trace
          source entry.stateIn (Or.inr hInverse) with hBase | hBase
      · exact Or.inl ⟨source, hBase⟩
      · exact Or.inr ⟨source, hBase⟩
  have hInputWf : BadEventDS.D2SBaseTraceWitness.PermInputWellformed
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) normal.state.trΔ :=
    ⟨normal.permutationNodup, normal.table_inputFunctional⟩
  have hBase : getBaseTrace
      (normal.state.trace ++ [⟨dsPermQuery stateIn, entry.stateIn⟩]) =
      getBaseTrace normal.state.trace ++ [⟨dsPermQuery stateIn, entry.stateIn⟩] :=
    BadEventDS.D2SBaseTraceWitness.getBaseTraceAppendPermInluMiss hInputWf
      normal.state.h_mirror hLookup
  have hEp : BadEventDS.E_p_at
      (normal.state.trace ++ [⟨dsPermQuery stateIn, entry.stateIn⟩])
      (getBaseTrace normal.state.trace).length := by
    rcases hPrior with hForward | hInverse
    · rcases hForward with ⟨priorIn, hForward⟩
      exact BadEventDS.E_p_at_append_forward_of_prior_same_output normal.state.trace stateIn
        priorIn entry.stateIn (Or.inl hForward) hBase
    · rcases hInverse with ⟨priorIn, hInverse⟩
      exact BadEventDS.E_p_at_append_forward_of_prior_same_output normal.state.trace stateIn
        priorIn entry.stateIn (Or.inr hInverse) hBase
  have hBad : BadEventDS.E
      (normal.state.trace ++ [⟨dsPermQuery stateIn, entry.stateIn⟩]) :=
    (BadEventDS.E_iff_exists_E_at _).mpr
      ⟨(getBaseTrace normal.state.trace).length, Or.inr (Or.inl hEp)⟩
  have hTrace : normal'.state.trace =
      normal.state.trace ++ [⟨dsPermQuery stateIn, entry.stateIn⟩] :=
    d2sInstallPermForwardStateRevised_continue_trace normal stateIn entry.stateIn hContinue
  exact normal'.monitorPassed (by rwa [hTrace])

/-- The Program residual cache satisfies the table-miss invariant after its underlying forward
installation continues.  The explicitly supplied cache-pop miss is a dispatcher fact: Program
may run only when the current input is not a pending tail key.  It is kept visible here so the
whole-run refinement must prove it from the stateful schedule, rather than treating it as a
property of an arbitrary normal state. -/
lemma RateOnlyCacheKeysAreTableMissesAt.program_residual
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (remainingRates : List (Vector U SpongeSize.R))
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {source : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hForward : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut source) :
    RateOnlyCacheKeysAreTableMissesAt source.state.trΔ
      (programResidualRateCache normal stateOut remainingRates) := by
  have hNoCache : ∀ entry ∈ normal.state.rateCacheP, entry.stateIn ≠ stateIn :=
    (popRateOnlyTailByInput_eq_none_iff normal.state.rateCacheP stateIn).mp hPop
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh := by
    rcases permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal stateIn stateOut hLookup with
      hFresh | hConflict
    · exact hFresh
    · have hStop :=
        (d2sInstallPermForwardStateRevised_isMonitorStop_iff normal stateIn stateOut).mpr
          (install_conflict_fwd_imp_E normal hConflict)
      rw [hForward] at hStop
      simp at hStop
  have hTable : source.state.trΔ.p =
      TraceTableOps.add normal.state.trΔ.p stateIn stateOut :=
    d2sInstallPermForwardStateRevised_continue_table_fresh normal stateIn stateOut hStatus hForward
  unfold RateOnlyCacheKeysAreTableMissesAt programResidualRateCache
  cases hTail : RateOnlyTail.ofBlocks? (U := U) remainingRates with
  | none =>
      change ∀ entry ∈ normal.state.rateCacheP,
        TraceTableOps.inlu source.state.trΔ.p entry.stateIn = none
      rw [hTable]
      intro entry hEntry
      exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p stateIn stateOut
        entry.stateIn normal.permutationNodup normal.table_inputFunctional (hKeys entry hEntry)
        (hNoCache entry hEntry)
  | some tail =>
      change ∀ entry ∈ (⟨stateOut, tail⟩ :: normal.state.rateCacheP),
        TraceTableOps.inlu source.state.trΔ.p entry.stateIn = none
      intro entry hEntry
      rcases List.mem_cons.mp hEntry with hEntry | hEntry
      · subst entry
        exact d2sInstallPermForwardStateRevised_continue_output_is_table_miss normal stateIn
          stateOut hLookup hForward
      · rw [hTable]
        exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p stateIn stateOut
          entry.stateIn normal.permutationNodup normal.table_inputFunctional (hKeys entry hEntry)
          (hNoCache entry hEntry)

/-- A continuing Program materialization preserves unique pending-tail keys.  The possible new
key is its just-produced state; `Monitor` rules out equality with every earlier cache output via
the trace-level cache provenance invariant. -/
lemma RateOnlyCacheKeysNodup.program_residual
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (remainingRates : List (Vector U SpongeSize.R))
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses
      normal.state.trace normal.state.rateCacheP)
    (hNodup : RateOnlyCacheKeysNodup normal.state.rateCacheP)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {source : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hForward : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut source) :
    RateOnlyCacheKeysNodup (programResidualRateCache normal stateOut remainingRates) := by
  unfold programResidualRateCache
  cases hTail : RateOnlyTail.ofBlocks? (U := U) remainingRates with
  | none =>
      simpa [hTail] using hNodup
  | some tail =>
      unfold RateOnlyCacheKeysNodup at hNodup ⊢
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hNodup⟩
      intro hMem
      rcases List.mem_map.mp hMem with ⟨entry, hEntry, hState⟩
      exact RateOnlyCacheKeysHaveOutputWitnesses.forward_output_not_cache_key_on_continue normal
        entry stateIn stateOut hWitnesses hEntry hLookup hForward hState

/-- The cache left by a continuing selected-tail materialization satisfies the table-miss
invariant.  Retained keys differ from the consumed input by cache-key uniqueness; a residual
key, when present, is the just-produced forward output and is a table miss by `Monitor`. -/
lemma RateOnlyCacheKeysAreTableMissesAt.tail_residual
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hNodup : RateOnlyCacheKeysNodup normal.state.rateCacheP)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest))
    {source : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hForward : d2sInstallPermForwardStateRevised normal entry.stateIn
      (materializeRateOnlyCacheEntry (U := U) entry capacity).1 =
      .continue (materializeRateOnlyCacheEntry (U := U) entry capacity).1 source) :
    RateOnlyCacheKeysAreTableMissesAt source.state.trΔ
      (rateOnlyTailResidualCache entry cacheRest capacity) := by
  let stateOut := (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  have hEntry : entry ∈ normal.state.rateCacheP := by
    rcases popRateOnlyTailByInput_some_mem normal.state.rateCacheP entry.stateIn entry.tail
      cacheRest hPop with ⟨prior, hPrior, hState, hTail⟩
    have hEq : prior = entry := by
      cases prior
      cases entry
      simp_all
    simpa [hEq] using hPrior
  have hLookup : TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none :=
    hKeys entry hEntry
  have hStatus : permInstallStatus normal.state.trΔ.p entry.stateIn stateOut = .fresh := by
    rcases permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal entry.stateIn stateOut
        hLookup with hFresh | hConflict
    · exact hFresh
    · have hStop :=
        (d2sInstallPermForwardStateRevised_isMonitorStop_iff normal entry.stateIn stateOut).mpr
          (install_conflict_fwd_imp_E normal hConflict)
      rw [hForward] at hStop
      simp at hStop
  have hTable : source.state.trΔ.p =
      TraceTableOps.add normal.state.trΔ.p entry.stateIn stateOut :=
    d2sInstallPermForwardStateRevised_continue_table_fresh normal entry.stateIn stateOut hStatus
      hForward
  have hRestInputNe : ∀ retained ∈ cacheRest, retained.stateIn ≠ entry.stateIn :=
    popRateOnlyTailByInput_rest_key_ne normal.state.rateCacheP entry.stateIn entry.tail cacheRest
      hNodup hPop
  have hRestMem : ∀ retained : RateOnlyCacheEntry (U := U), retained ∈ cacheRest →
      retained ∈ normal.state.rateCacheP :=
    popRateOnlyTailByInput_rest_subset normal.state.rateCacheP entry.stateIn entry.tail
      cacheRest hPop
  unfold RateOnlyCacheKeysAreTableMissesAt rateOnlyTailResidualCache
  cases hSuccessor : (materializeRateOnlyCacheEntry (U := U) entry capacity).2 with
  | none =>
      change ∀ retained ∈ cacheRest,
        TraceTableOps.inlu source.state.trΔ.p retained.stateIn = none
      rw [hTable]
      intro retained hRetained
      exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p entry.stateIn stateOut
        retained.stateIn normal.permutationNodup normal.table_inputFunctional
        (hKeys retained (hRestMem retained hRetained)) (hRestInputNe retained hRetained)
  | some successor =>
      change ∀ retained ∈ (successor :: cacheRest),
        TraceTableOps.inlu source.state.trΔ.p retained.stateIn = none
      intro retained hRetained
      rcases List.mem_cons.mp hRetained with hRetained | hRetained
      · subst retained
        have hKey : successor.stateIn = stateOut :=
          materializeRateOnlyCacheEntry_some_stateIn entry capacity successor hSuccessor
        rw [hKey]
        exact d2sInstallPermForwardStateRevised_continue_output_is_table_miss normal entry.stateIn
          stateOut hLookup hForward
      · rw [hTable]
        exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p entry.stateIn stateOut
          retained.stateIn normal.permutationNodup normal.table_inputFunctional
          (hKeys retained (hRestMem retained hRetained)) (hRestInputNe retained hRetained)

/-- A continuing selected-tail materialization preserves unique pending-tail keys.  The popped
cache rest remains key-nodup; if a residual tail exists, its new key is the fresh forward output
and cannot coincide with a retained trace-realized cache key. -/
lemma RateOnlyCacheKeysNodup.tail_residual
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses
      normal.state.trace normal.state.rateCacheP)
    (hNodup : RateOnlyCacheKeysNodup normal.state.rateCacheP)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none)
    {source : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hForward : d2sInstallPermForwardStateRevised normal entry.stateIn
      (materializeRateOnlyCacheEntry (U := U) entry capacity).1 =
      .continue (materializeRateOnlyCacheEntry (U := U) entry capacity).1 source) :
    RateOnlyCacheKeysNodup (rateOnlyTailResidualCache entry cacheRest capacity) := by
  let stateOut := (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  have hRestNodup : RateOnlyCacheKeysNodup cacheRest :=
    popRateOnlyTailByInput_rest_keys_nodup normal.state.rateCacheP entry.stateIn entry.tail
      cacheRest hNodup hPop
  have hRestMem : ∀ retained : RateOnlyCacheEntry (U := U), retained ∈ cacheRest →
      retained ∈ normal.state.rateCacheP :=
    popRateOnlyTailByInput_rest_subset normal.state.rateCacheP entry.stateIn entry.tail
      cacheRest hPop
  unfold rateOnlyTailResidualCache
  cases hSuccessor : (materializeRateOnlyCacheEntry (U := U) entry capacity).2 with
  | none =>
      simpa [hSuccessor] using hRestNodup
  | some successor =>
      unfold RateOnlyCacheKeysNodup at hRestNodup ⊢
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, hRestNodup⟩
      intro hMem
      rcases List.mem_map.mp hMem with ⟨retained, hRetained, hState⟩
      have hKey : successor.stateIn = stateOut :=
        materializeRateOnlyCacheEntry_some_stateIn entry capacity successor hSuccessor
      exact RateOnlyCacheKeysHaveOutputWitnesses.forward_output_not_cache_key_on_continue normal
        retained entry.stateIn stateOut hWitnesses (hRestMem retained hRetained) hLookup hForward
        (hState.trans hKey)

/-- On the ordinary Step 4.c fresh path, a failed cache pop means the sampled installation input
is not any pending-tail key.  Thus a continuing fresh install preserves the table-miss invariant
for every existing tail without inspecting any latent capacity. -/
lemma RateOnlyCacheKeysAreTableMisses.forward_miss_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut normal') :
    RateOnlyCacheKeysAreTableMisses normal' := by
  have hNoCache : ∀ entry ∈ normal.state.rateCacheP, entry.stateIn ≠ stateIn :=
    (popRateOnlyTailByInput_eq_none_iff normal.state.rateCacheP stateIn).mp hPop
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh := by
    rcases permInstallStatus_fresh_or_conflict_of_inlu_eq_none normal stateIn stateOut hLookup with
      hFresh | hConflict
    · exact hFresh
    · have hStop :=
        (d2sInstallPermForwardStateRevised_isMonitorStop_iff normal stateIn stateOut).mpr
          (install_conflict_fwd_imp_E normal hConflict)
      rw [hContinue] at hStop
      simp at hStop
  have hTable : normal'.state.trΔ.p =
      TraceTableOps.add normal.state.trΔ.p stateIn stateOut :=
    d2sInstallPermForwardStateRevised_continue_table_fresh normal stateIn stateOut
      hStatus hContinue
  have hCache : normal'.state.rateCacheP = normal.state.rateCacheP :=
    d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue
  intro entry hEntry
  rw [hCache] at hEntry
  rw [hTable]
  exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p stateIn stateOut entry.stateIn
    normal.permutationNodup normal.table_inputFunctional (hKeys entry hEntry)
    (hNoCache entry hEntry)

/-- On an inverse-table miss, a continuing sampled preimage cannot be any pending tail key: the
cache provenance would make that inverse occurrence a first `E_{p^{-1}}` witness.  Consequently
the fresh inverse installation preserves the table-miss invariant for the unchanged cache. -/
lemma RateOnlyCacheKeysAreTableMisses.inverse_miss_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses
      normal.state.trace normal.state.rateCacheP)
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermInverseStateRevised normal stateOut stateIn =
      .continue stateIn normal') :
    RateOnlyCacheKeysAreTableMisses normal' := by
  have hNoCache : ∀ entry ∈ normal.state.rateCacheP, entry.stateIn ≠ stateIn := by
    intro entry hEntry hEq
    exact RateOnlyCacheKeysHaveOutputWitnesses.inverse_miss_not_continue normal entry stateOut
      stateIn hWitnesses hEntry hEq.symm hLookup hContinue
  have hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh := by
    rcases permInstallStatus_fresh_or_conflict_of_outlu_eq_none normal stateIn stateOut hLookup with
      hFresh | hConflict
    · exact hFresh
    · have hStop :=
        (d2sInstallPermInverseStateRevised_isMonitorStop_iff normal stateOut stateIn).mpr
          (install_conflict_inv_imp_E normal hConflict)
      rw [hContinue] at hStop
      simp at hStop
  have hTable : normal'.state.trΔ.p =
      TraceTableOps.add normal.state.trΔ.p stateIn stateOut :=
    d2sInstallPermInverseStateRevised_continue_table_fresh normal stateOut stateIn
      hStatus hContinue
  have hCache : normal'.state.rateCacheP = normal.state.rateCacheP :=
    d2sInstallPermInverseStateRevised_continue_cache normal stateOut stateIn hContinue
  intro entry hEntry
  rw [hCache] at hEntry
  rw [hTable]
  exact inlu_add_preserves_miss_away_from_input normal.state.trΔ.p stateIn stateOut entry.stateIn
    normal.permutationNodup normal.table_inputFunctional (hKeys entry hEntry)
    (hNoCache entry hEntry)

/-- Existing cache-output witnesses survive an ordinary forward continuation because that branch
does not change the cache and appends exactly one forward occurrence. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.forward_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses
      normal.state.trace normal.state.rateCacheP)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut normal') :
    RateOnlyCacheKeysHaveOutputWitnesses normal'.state.trace normal'.state.rateCacheP := by
  rw [d2sInstallPermForwardStateRevised_continue_trace normal stateIn stateOut hContinue,
    d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue]
  exact RateOnlyCacheKeysHaveOutputWitnesses.append normal.state.trace normal.state.rateCacheP
    hWitnesses (⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))

/-- Existing cache-output witnesses likewise survive a continuing inverse installation.  The
inverse branch never reads or writes the rate-only cache; it only appends the actual inverse
occurrence to the trace. -/
lemma RateOnlyCacheKeysHaveOutputWitnesses.inverse_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hWitnesses : RateOnlyCacheKeysHaveOutputWitnesses
      normal.state.trace normal.state.rateCacheP)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermInverseStateRevised normal stateOut stateIn =
      .continue stateIn normal') :
    RateOnlyCacheKeysHaveOutputWitnesses normal'.state.trace normal'.state.rateCacheP := by
  rw [d2sInstallPermInverseStateRevised_continue_trace normal stateOut stateIn hContinue,
    d2sInstallPermInverseStateRevised_continue_cache normal stateOut stateIn hContinue]
  exact RateOnlyCacheKeysHaveOutputWitnesses.append normal.state.trace normal.state.rateCacheP
    hWitnesses (⟨dsPermInvQuery stateOut, stateIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))

/-- Any continuing step that appends one actual occurrence while leaving both the reusable
permutation table and the pending rate-only cache unchanged preserves cache coherence.  This
isolates the no-cache-mutation routes (hash transitions and `Install = present` forward/inverse
table hits) from the four routes that need the stronger cache-specific lemmas below. -/
lemma RateOnlyCacheCoherent.append_same_cache_and_permutation
    (normal normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hTrace : normal'.state.trace = normal.state.trace ++ [occurrence])
    (hTable : normal'.state.trΔ.p = normal.state.trΔ.p)
    (hCache : normal'.state.rateCacheP = normal.state.rateCacheP) :
    RateOnlyCacheCoherent normal' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hTrace, hCache]
    exact RateOnlyCacheKeysHaveOutputWitnesses.append normal.state.trace normal.state.rateCacheP
      hCoherent.outputWitnesses occurrence
  · intro entry hEntry
    rw [hCache] at hEntry
    rw [hTable]
    exact hCoherent.tableMisses entry hEntry
  · rw [hCache]
    exact hCoherent.keyNodup

/-- The ordinary true-miss forward continuation preserves the complete rate-only cache
invariant.  This is the direct `4.c.iii` transition consumed by the whole first-bad runner. -/
lemma RateOnlyCacheCoherent.forward_miss_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermForwardStateRevised normal stateIn stateOut =
      .continue stateOut normal') :
    RateOnlyCacheCoherent normal' :=
  ⟨RateOnlyCacheKeysHaveOutputWitnesses.forward_continue normal stateIn stateOut
      hCoherent.outputWitnesses hContinue,
    RateOnlyCacheKeysAreTableMisses.forward_miss_continue normal stateIn stateOut
      hCoherent.tableMisses hPop hLookup hContinue,
    by
      rw [d2sInstallPermForwardStateRevised_continue_cache normal stateIn stateOut hContinue]
      exact hCoherent.keyNodup⟩

/-- The continuing inverse-miss transition preserves the complete rate-only cache invariant.
Its table-miss component uses the cache provenance proof, so the inverse branch cannot silently
install a mapping at a pending tail key. -/
lemma RateOnlyCacheCoherent.inverse_miss_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sInstallPermInverseStateRevised normal stateOut stateIn =
      .continue stateIn normal') :
    RateOnlyCacheCoherent normal' :=
  ⟨RateOnlyCacheKeysHaveOutputWitnesses.inverse_continue normal stateOut stateIn
      hCoherent.outputWitnesses hContinue,
    RateOnlyCacheKeysAreTableMisses.inverse_miss_continue normal stateOut stateIn
      hCoherent.outputWitnesses hCoherent.tableMisses hLookup hContinue,
    by
      rw [d2sInstallPermInverseStateRevised_continue_cache normal stateOut stateIn hContinue]
      exact hCoherent.keyNodup⟩

/-- A continuing Program materialization preserves the complete rate-only cache invariant.  The
only branch-specific premise is the failed cache pop at the Program input; it is deliberately
exposed as the stateful-replay/dispatcher obligation that prevents Program from bypassing an
already scheduled verifier-tail continuation. -/
lemma RateOnlyCacheCoherent.program_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity =
      .continue (d2sSynthesisState (U := U) firstRate capacity) normal') :
    RateOnlyCacheCoherent normal' := by
  let stateOut := d2sSynthesisState (U := U) firstRate capacity
  have hReplace : d2sReplaceRateCacheOnContinue
      (programResidualRateCache normal stateOut remainingRates)
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) =
      .continue stateOut normal' := by
    simpa [d2sProgramFirstRateRevised, stateOut] using hContinue
  obtain ⟨source, hSource, hNormalTrace, hNormalTable⟩ :=
    d2sReplaceRateCacheOnContinue_continue_source
      (programResidualRateCache normal stateOut remainingRates)
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) hReplace
  rw [d2sPermResolvedStep_forward] at hSource
  have hNormalCache : normal'.state.rateCacheP =
      programResidualRateCache normal stateOut remainingRates :=
    d2sReplaceRateCacheOnContinue_continue_cache
      (programResidualRateCache normal stateOut remainingRates)
      (d2sPermResolvedStep normal (.forward stateIn stateOut)) hReplace
  have hSourceTrace : source.state.trace =
      normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] :=
    d2sInstallPermForwardStateRevised_continue_trace normal stateIn stateOut hSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hNormalTrace, hSourceTrace, hNormalCache]
    exact RateOnlyCacheKeysHaveOutputWitnesses.programResidual normal stateIn stateOut
      remainingRates hCoherent.outputWitnesses
  · change RateOnlyCacheKeysAreTableMissesAt normal'.state.trΔ normal'.state.rateCacheP
    rw [hNormalTable, hNormalCache]
    exact RateOnlyCacheKeysAreTableMissesAt.program_residual normal stateIn stateOut
      remainingRates hCoherent.tableMisses hPop hLookup hSource
  · rw [hNormalCache]
    exact RateOnlyCacheKeysNodup.program_residual normal stateIn stateOut remainingRates
      hCoherent.outputWitnesses hCoherent.keyNodup hLookup hSource

/-- A cache-tail selection performed by the real pop operation certifies that the exact entry
passed to the tail handler was present in the pre-step cache. -/
lemma rateOnlyCacheEntry_mem_of_pop
    (cache : List (RateOnlyCacheEntry (U := U)))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hPop : popRateOnlyTailByInput cache entry.stateIn = some (entry.tail, cacheRest)) :
    entry ∈ cache := by
  rcases popRateOnlyTailByInput_some_mem cache entry.stateIn entry.tail cacheRest hPop with
    ⟨entry', hEntry', hState, hTail⟩
  cases entry
  cases entry'
  simp_all

/-- A continuing selected-tail materialization preserves the complete rate-only-cache
invariant.  This is the cache-hit half of Algorithm 5.3 Step 4.c: the selected record is removed,
one capacity materializes its next rate block, and only the residual rate tail is re-keyed at the
new forward output.  The proof deliberately recovers the common forward
`Install → append → Monitor` successor before applying the three cache components, so this route
shares the exact same first-bad gateway as ordinary and Program forward installations. -/
lemma RateOnlyCacheCoherent.tail_continue
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest))
    {normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hContinue : d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity =
      .continue (materializeRateOnlyCacheEntry (U := U) entry capacity).1 normal') :
    RateOnlyCacheCoherent normal' := by
  let stateOut := (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  have hReplace : d2sReplaceRateCacheOnContinue
      (rateOnlyTailResidualCache entry cacheRest capacity)
      (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)) =
      .continue stateOut normal' := by
    simpa [d2sConsumePoppedRateOnlyTailRevised, stateOut] using hContinue
  obtain ⟨source, hSource, hNormalTrace, hNormalTable⟩ :=
    d2sReplaceRateCacheOnContinue_continue_source
      (rateOnlyTailResidualCache entry cacheRest capacity)
      (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)) hReplace
  rw [d2sPermResolvedStep_forward] at hSource
  have hNormalCache : normal'.state.rateCacheP =
      rateOnlyTailResidualCache entry cacheRest capacity :=
    d2sReplaceRateCacheOnContinue_continue_cache
      (rateOnlyTailResidualCache entry cacheRest capacity)
      (d2sPermResolvedStep normal (.forward entry.stateIn stateOut)) hReplace
  have hSourceTrace : source.state.trace =
      normal.state.trace ++ [⟨dsPermQuery entry.stateIn, stateOut⟩] :=
    d2sInstallPermForwardStateRevised_continue_trace normal entry.stateIn stateOut hSource
  have hEntry : entry ∈ normal.state.rateCacheP :=
    rateOnlyCacheEntry_mem_of_pop normal.state.rateCacheP entry cacheRest hPop
  have hLookup : TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none :=
    hCoherent.tableMisses entry hEntry
  refine ⟨?_, ?_, ?_⟩
  · rw [hNormalTrace, hSourceTrace, hNormalCache]
    exact RateOnlyCacheKeysHaveOutputWitnesses.tailResidual normal.state.trace
      normal.state.rateCacheP entry cacheRest capacity hCoherent.outputWitnesses hPop
  · change RateOnlyCacheKeysAreTableMissesAt normal'.state.trΔ normal'.state.rateCacheP
    rw [hNormalTable, hNormalCache]
    exact RateOnlyCacheKeysAreTableMissesAt.tail_residual normal entry cacheRest capacity
      hCoherent.tableMisses hCoherent.keyNodup hPop hSource
  · rw [hNormalCache]
    exact RateOnlyCacheKeysNodup.tail_residual normal entry cacheRest capacity
      hCoherent.outputWitnesses hCoherent.keyNodup hPop hLookup hSource

/-- A selected rate-only tail only changes the cache on a continuing result.  It cannot change
whether the common forward occurrence is the first monitored bad event.  This isolates the
rate-only-cache policy from the first-event probability proof. -/
lemma d2sConsumePoppedRateOnlyTailRevised_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) :
    (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++
        [⟨dsPermQuery entry.stateIn,
          (materializeRateOnlyCacheEntry (U := U) entry capacity).1⟩]) := by
  let action : D2SPermResolvedAction U :=
    .forward entry.stateIn (materializeRateOnlyCacheEntry (U := U) entry capacity).1
  have hGateway := d2sPermResolvedStep_isMonitorStop_iff normal action
  change (d2sReplaceRateCacheOnContinue (rateOnlyTailResidualCache entry cacheRest capacity)
      (d2sPermResolvedStep normal action)).isMonitorStop ↔
    BadEventDS.E (normal.state.trace ++ [action.occurrence StmtIn])
  cases hStep : d2sPermResolvedStep normal action <;>
    simpa [d2sReplaceRateCacheOnContinue, hStep] using hGateway

/-- Program's first materialized rate block likewise has exactly the common forward first-bad
event.  The residual tail is installed only after `Monitor` passes, so it is irrelevant to this
one-occurrence gateway. -/
lemma d2sProgramFirstRateRevised_isMonitorStop_iff
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (capacity : Vector U SpongeSize.C) :
    (d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity).isMonitorStop ↔
      BadEventDS.E (normal.state.trace ++
        [⟨dsPermQuery stateIn, d2sSynthesisState (U := U) firstRate capacity⟩]) := by
  let action : D2SPermResolvedAction U :=
    .forward stateIn (d2sSynthesisState (U := U) firstRate capacity)
  have hGateway := d2sPermResolvedStep_isMonitorStop_iff normal action
  change (d2sReplaceRateCacheOnContinue
      (programResidualRateCache normal (d2sSynthesisState (U := U) firstRate capacity)
        remainingRates)
      (d2sPermResolvedStep normal action)).isMonitorStop ↔
    BadEventDS.E (normal.state.trace ++ [action.occurrence StmtIn])
  cases hStep : d2sPermResolvedStep normal action <;>
    simpa [d2sReplaceRateCacheOnContinue, hStep] using hGateway

end DuplexSpongeFS.ProverTransform
