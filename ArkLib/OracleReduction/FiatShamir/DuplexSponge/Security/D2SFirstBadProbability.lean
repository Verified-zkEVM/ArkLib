/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadDispatcher
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SRevisedForward
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SampleProduct

/-!
# One-sample first-bad bounds for revised D2SQuery

This file is the probability-facing companion to `D2SFirstBadGateway`.  It proves all five
direct sampling charges used by the revised Lemma 5.8 first-event argument:

* a fresh hash capacity hits at most `2j` prior capacity targets;
* a forward-table miss samples a full state whose capacity hits at most `2j + 1` targets; and
* an inverse-table miss, selected rate-only tail, or Program first-rate block has the same
  `2j + 1` capacity charge.

The proofs deliberately stop at one gateway.  They neither inspect cache internals nor perform a
whole-execution union bound.  Thus the eventual Lemma 5.8 proof needs one generic first-event
aggregation over these local charges, rather than three handler-specific inductions.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U] [SampleableType U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible U] [DecidableEq StmtIn] [Fintype U] [Nonempty U] [SampleableType U] in
/-- Adding one selected capacity to the prior `2j` targets leaves at most `2j + 1` targets. -/
lemma priorCapacityTargetFinset_union_singleton_card_le
    (bt : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (j : ℕ)
    (capacity : Vector U SpongeSize.C) :
    (BadEventDS.priorCapacityTargetFinset bt j ∪ {capacity}).card ≤ 2 * j + 1 := by
  calc
    (BadEventDS.priorCapacityTargetFinset bt j ∪ {capacity}).card ≤
        (BadEventDS.priorCapacityTargetFinset bt j).card + ({capacity} : Finset _).card :=
      Finset.card_union_le _ _
    _ ≤ 2 * j + 1 := by
      simpa using Nat.add_le_add
        (BadEventDS.priorCapacityTargetFinset_card_le bt j) (by simp : 1 ≤ 1)

/-- The uniform interface consumed by the revised Lemma 5.8 first-witness aggregation.  A value
packages one *actual* one-sample handler together with its already-proved monitor-stop charge;
it does not hide a synthetic distribution or a caller-supplied probability predicate.  The
whole-execution proof will select these values adaptively from a monitor-passing normal state. -/
structure D2SOneSampleGateway
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) where
  Answer : Type
  execute : OracleComp (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
    (D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Answer)
  numerator : ℝ≥0∞
  monitorStop_le (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec)) execute] ≤
      numerator / BadEventDS.capacitySpaceSize (U := U)

omit [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- A monitor-stop bound survives arbitrary preceding oracle work when every reached
continuation has the same bound.  This is the only probability rule needed to lift a one-capacity
Program bound through `gᵢ` lookup and challenge parsing; it makes no independence assumption. -/
lemma simulateQ_bind_monitorStop_le
    {A B : Type}
    (impl : QueryImpl
      (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) ProbComp)
    (pre : OracleComp
      (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) A)
    (next : A → OracleComp
      (d2sQueryOracles (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
      (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) B))
    (ε : ℝ≥0∞)
    (hNext : ∀ a ∈ support (simulateQ impl pre),
      Pr[ fun result => result.isMonitorStop | simulateQ impl (next a)] ≤ ε) :
    Pr[ fun result => result.isMonitorStop | simulateQ impl (pre >>= next)] ≤ ε := by
  rw [simulateQ_bind]
  exact probEvent_bind_le_of_forall_le hNext

/-- A revised Step 2 hash-table miss stops with probability at most `2j / |Σ|^c`, where `j` is
the number of preceding base entries. -/
lemma d2sHandleHashQueryRevised_miss_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleHashQueryRevised normal stmt)] ≤
      (2 * (getBaseTrace normal.state.trace).length : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleHashQueryRevised_miss_simulateQ_probEvent_eq
    gImpl normal stmt hLookup (fun result => result.isMonitorStop)]
  calc
    Pr[ fun capacity =>
        (d2sHandleHashFreshRevised normal stmt capacity hLookup).isMonitorStop |
      ($ᵗ (Vector U SpongeSize.C)) ] ≤
        Pr[ fun capacity =>
            capacity ∈ BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
              (getBaseTrace normal.state.trace).length |
          ($ᵗ (Vector U SpongeSize.C)) ] := by
      apply probEvent_mono''
      intro capacity hStop
      have hE := (d2sHandleHashFreshRevised_isMonitorStop_iff normal stmt capacity hLookup).mp hStop
      exact hash_monitor_failure_in_capacity_target normal stmt capacity hE
    _ ≤
        ((BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
          (getBaseTrace normal.state.trace).length).card : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) :=
      BadEventDS.probEvent_uniformCapacity_mem_finset_le (U := U) _
    _ ≤ (2 * (getBaseTrace normal.state.trace).length : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast BadEventDS.priorCapacityTargetFinset_card_le
        (getBaseTrace normal.state.trace) (getBaseTrace normal.state.trace).length

/-- A revised Step 4.c true forward miss stops with probability at most
`(2j + 1) / |Σ|^c`.  The full-state sample is charged only through its capacity projection. -/
lemma d2sHandleForwardNoResultRevised_fresh_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleForwardNoResultRevised normal stateIn)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleForwardNoResultRevised_fresh_simulateQ_probEvent_eq
    gImpl normal stateIn hPop hLookup (fun result => result.isMonitorStop)]
  calc
    Pr[ fun stateOut =>
        (d2sPermResolvedStep normal (.forward stateIn stateOut)).isMonitorStop |
      ($ᵗ (CanonicalSpongeState U)) ] ≤
        Pr[ fun stateOut =>
            stateOut.capacitySegment ∈
              BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
                (getBaseTrace normal.state.trace).length ∪ {stateIn.capacitySegment} |
          ($ᵗ (CanonicalSpongeState U)) ] := by
      apply probEvent_mono''
      intro stateOut hStop
      have hE := (d2sPermResolvedStep_isMonitorStop_iff normal
        (.forward stateIn stateOut)).mp hStop
      exact forward_input_miss_monitor_failure_in_capacity_target normal stateIn stateOut hLookup hE
    _ ≤
        ((BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
          (getBaseTrace normal.state.trace).length ∪ {stateIn.capacitySegment}).card : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) :=
      BadEventDS.probEvent_uniformState_capacitySegment_mem_finset_le (U := U) _
    _ ≤ (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast priorCapacityTargetFinset_union_singleton_card_le
        (getBaseTrace normal.state.trace) (getBaseTrace normal.state.trace).length
        stateIn.capacitySegment

/-- A revised Step 3 inverse-table miss stops with probability at most
`(2j + 1) / |Σ|^c`.  The uniform preimage state is again charged only through its capacity. -/
lemma d2sHandleInversePermQueryRevised_miss_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleInversePermQueryRevised normal stateOut)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleInversePermQueryRevised_miss_simulateQ_probEvent_eq
    gImpl normal stateOut hLookup (fun result => result.isMonitorStop)]
  calc
    Pr[ fun stateIn =>
        (d2sPermResolvedStep normal (.inverse stateOut stateIn)).isMonitorStop |
      ($ᵗ (CanonicalSpongeState U)) ] ≤
        Pr[ fun stateIn =>
            stateIn.capacitySegment ∈
              BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
                (getBaseTrace normal.state.trace).length ∪ {stateOut.capacitySegment} |
          ($ᵗ (CanonicalSpongeState U)) ] := by
      apply probEvent_mono''
      intro stateIn hStop
      have hE := (d2sPermResolvedStep_isMonitorStop_iff normal
        (.inverse stateOut stateIn)).mp hStop
      exact inverse_output_miss_monitor_failure_in_capacity_target
        normal stateOut stateIn hLookup hE
    _ ≤
        ((BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
          (getBaseTrace normal.state.trace).length ∪ {stateOut.capacitySegment}).card : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) :=
      BadEventDS.probEvent_uniformState_capacitySegment_mem_finset_le (U := U) _
    _ ≤ (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast priorCapacityTargetFinset_union_singleton_card_le
        (getBaseTrace normal.state.trace) (getBaseTrace normal.state.trace).length
        stateOut.capacitySegment

/-- A selected Step 4.c.i rate-only tail stops with probability at most
`(2j + 1) / |Σ|^c`.  The dispatcher-selected entry is accompanied by the run-level
`RateOnlyCacheKeysAreTableMisses` invariant; this is the precise fact that lets the common
forward finite-target lemma apply without pre-sampling any latent capacity. -/
lemma d2sHandlePoppedRateOnlyTailRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest)) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandlePoppedRateOnlyTailRevised_simulateQ_probEvent_eq
    gImpl normal entry cacheRest (fun result => result.isMonitorStop)]
  let target :=
    BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
      (getBaseTrace normal.state.trace).length ∪ {entry.stateIn.capacitySegment}
  have hEntry : entry ∈ normal.state.rateCacheP :=
    rateOnlyCacheEntry_mem_of_pop normal.state.rateCacheP entry cacheRest hPop
  have hLookup : TraceTableOps.inlu normal.state.trΔ.p entry.stateIn = none :=
    hKeys.lookup_miss hEntry
  calc
    Pr[ fun capacity =>
        (d2sConsumePoppedRateOnlyTailRevised normal entry cacheRest capacity).isMonitorStop |
      ($ᵗ (Vector U SpongeSize.C)) ] ≤
        Pr[ fun capacity => capacity ∈ target | ($ᵗ (Vector U SpongeSize.C)) ] := by
      apply probEvent_mono''
      intro capacity hStop
      have hE :=
        (d2sConsumePoppedRateOnlyTailRevised_isMonitorStop_iff normal entry cacheRest capacity).mp
          hStop
      have hTarget := forward_input_miss_monitor_failure_in_capacity_target normal entry.stateIn
        (materializeRateOnlyCacheEntry (U := U) entry capacity).1 hLookup hE
      simpa only [target, materializeRateOnlyCacheEntry_capacitySegment] using hTarget
    _ ≤ (target.card : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U) :=
      BadEventDS.probEvent_uniformCapacity_mem_finset_le (U := U) target
    _ ≤ (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast priorCapacityTargetFinset_union_singleton_card_le
        (getBaseTrace normal.state.trace) (getBaseTrace normal.state.trace).length
        entry.stateIn.capacitySegment

/-- A Program first-rate materialization stops with probability at most
`(2j + 1) / |Σ|^c`.  Its caller has already tested the forward table (Step 4.e.ii), so the
one capacity sample is charged by the same forward-miss target as an ordinary fresh mapping. -/
lemma d2sHandleProgramFirstRateRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleProgramFirstRateRevised_simulateQ_probEvent_eq
    gImpl normal stateIn firstRate remainingRates (fun result => result.isMonitorStop)]
  let programResult := fun capacity : Vector U SpongeSize.C =>
    d2sProgramFirstRateRevised normal stateIn firstRate remainingRates capacity
  let target :=
    BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
      (getBaseTrace normal.state.trace).length ∪ {stateIn.capacitySegment}
  calc
    Pr[ fun capacity => (programResult capacity).isMonitorStop |
      ($ᵗ (Vector U SpongeSize.C)) ] ≤
        Pr[ fun capacity => capacity ∈ target | ($ᵗ (Vector U SpongeSize.C)) ] := by
      apply probEvent_mono''
      intro capacity hStop
      have hE := (d2sProgramFirstRateRevised_isMonitorStop_iff normal stateIn firstRate
        remainingRates capacity).mp hStop
      have hTarget := forward_input_miss_monitor_failure_in_capacity_target normal stateIn
        (d2sSynthesisState (U := U) firstRate capacity) hLookup hE
      simpa only [target, d2sSynthesisState_capacitySegment] using hTarget
    _ ≤ (target.card : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U) :=
      BadEventDS.probEvent_uniformCapacity_mem_finset_le (U := U) target
    _ ≤ (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast priorCapacityTargetFinset_union_singleton_card_le
        (getBaseTrace normal.state.trace) (getBaseTrace normal.state.trace).length
        stateIn.capacitySegment

/-- A post-`gᵢ` Program continuation on a forward-table miss has the same one-capacity charge as
the first-rate Program gateway.  Challenge parsing and final-block padding may occur first, but
the bind rule above conditions on those choices and samples no later-tail capacity. -/
lemma d2sHandleBacktrackAfterGRevised_miss_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  rw [d2sHandleBacktrackAfterGRevised_miss normal stateIn backtrackOut rhoHat hLookup]
  apply simulateQ_bind_monitorStop_le
  intro rateBlocks _hRateBlocks
  cases rateBlocks.toList with
  | nil =>
      simp only [simulateQ_pure]
      rw [probEvent_pure]
      simp only [D2SRevisedStepResult.isMonitorStop_underlyingAbort, ↓reduceIte]
      exact bot_le
  | cons firstRate remainingRates =>
      simpa using d2sHandleProgramFirstRateRevised_monitorStop_le gImpl normal stateIn firstRate
        remainingRates hLookup

omit [VCVCompatible U] [Fintype U] [Nonempty U] in
/-- A post-`gᵢ` table hit is a redundant replay and has zero monitor-stop probability. -/
lemma d2sHandleBacktrackAfterGRevised_hit_monitorStop_eq_zero
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat)] = 0 := by
  classical
  rw [d2sHandleBacktrackAfterGRevised_hit normal stateIn stateOut backtrackOut rhoHat hLookup,
    simulateQ_pure, probEvent_pure]
  have hNoStop := d2sPermResolvedForwardHit_not_monitorStop normal stateIn stateOut hLookup
  simp only [hNoStop, ↓reduceIte]

/-- Every post-`gᵢ` continuation has the same `2j+1` charge: the table-hit branch contributes
zero, and the table-miss branch delegates to the one-capacity Program factorization. -/
lemma d2sHandleBacktrackAfterGRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (rhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx)) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleBacktrackAfterGRevised normal stateIn backtrackOut rhoHat)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      rw [d2sHandleBacktrackAfterGRevised_hit_monitorStop_eq_zero gImpl normal stateIn stateOut
        backtrackOut rhoHat hLookup]
      exact bot_le
  | none =>
      exact d2sHandleBacktrackAfterGRevised_miss_monitorStop_le gImpl normal stateIn backtrackOut
        rhoHat hLookup

/-- Step 4.c after a failed tail pop has the standard `2j+1` charge: a table hit is a redundant
replay, while a table miss draws one uniform full state. -/
lemma d2sHandleForwardNoResultRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleForwardNoResultRevised normal stateIn)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  cases hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn with
  | some stateOut =>
      unfold d2sHandleForwardNoResultRevised
      rw [hPop, hLookup, simulateQ_pure, probEvent_pure]
      have hNoStop := d2sPermResolvedForwardHit_not_monitorStop normal stateIn stateOut hLookup
      simp only [hNoStop, ↓reduceIte]
      exact bot_le
  | none =>
      exact d2sHandleForwardNoResultRevised_fresh_monitorStop_le gImpl normal stateIn hPop hLookup

/-- A nonempty in-image BackTrack result reissues its `gᵢ` key, but every possible answer enters
the uniformly bounded post-`gᵢ` continuation. -/
lemma d2sHandleBacktrackSomeRevised_nonemptyChallenge_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut)
    (hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleBacktrackSomeRevised_nonemptyChallenge normal stateIn backtrackOut hPop hImage
    hNonempty]
  apply simulateQ_bind_monitorStop_le
  intro rhoHat _hRhoHat
  exact d2sHandleBacktrackAfterGRevised_monitorStop_le gImpl normal stateIn backtrackOut rhoHat

/-- The cache-priority branch consumes one selected tail block, so it has the same one-capacity
charge as a forward-table miss.  The coherence invariant supplies the exact table-miss premise
for its selected cache key. -/
lemma d2sHandleForwardPermQueryRevised_tail_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = some (tail, cacheRest)) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleForwardPermQueryRevised normal stateIn)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  rw [d2sHandleForwardPermQueryRevised_tail normal stateIn tail cacheRest hPop]
  exact d2sHandlePoppedRateOnlyTailRevised_monitorStop_le gImpl normal ⟨stateIn, tail⟩ cacheRest
    hCoherent.tableMisses hPop

/-- Every successful BackTrack result has the same local charge.  A pending tail still wins;
otherwise the out-of-image and empty-challenge cases are ordinary, and the nonempty in-image
case is covered by the conditional post-`gᵢ` bound. -/
lemma d2sHandleBacktrackSomeRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleBacktrackSomeRevised normal stateIn backtrackOut)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  by_cases hImage : d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut
  · by_cases hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx
    · exact d2sHandleBacktrackSomeRevised_nonemptyChallenge_monitorStop_le gImpl normal stateIn
        backtrackOut hPop hImage hNonempty
    · rw [d2sHandleBacktrackSomeRevised_emptyChallenge normal stateIn backtrackOut hPop hImage
        hNonempty]
      exact d2sHandleForwardNoResultRevised_monitorStop_le gImpl normal stateIn hPop
  · rw [d2sHandleBacktrackSomeRevised_notInImage normal stateIn backtrackOut hPop hImage]
    exact d2sHandleForwardNoResultRevised_monitorStop_le gImpl normal stateIn hPop

/-- Complete Algorithm 5.3 Step 4 local monitor-stop bound.  All control branches are now
subsumed by one `2j+1` charge, and the only random capacity contributing to it is sampled at the
selected forward miss, lazy-tail materialization, or Program first block. -/
lemma d2sHandleForwardPermQueryRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hCoherent : RateOnlyCacheCoherent normal) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sHandleForwardPermQueryRevised normal stateIn)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  cases hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn with
  | some tailAndCache =>
      rcases tailAndCache with ⟨tail, cacheRest⟩
      exact d2sHandleForwardPermQueryRevised_tail_monitorStop_le gImpl normal stateIn tail
        cacheRest hCoherent hPop
  | none =>
      cases hBacktrack : Backtrack.backTrack
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          normal.state.trace normal.state.trΔ normal.state.h_inv stateIn
          (normal.state.trace.length + 1) with
      | err =>
          rw [d2sHandleForwardPermQueryRevised_err normal stateIn hPop hBacktrack,
            simulateQ_pure, probEvent_pure]
          simp only [D2SRevisedStepResult.isMonitorStop_underlyingAbort, ↓reduceIte]
          exact bot_le
      | noResult =>
          rw [d2sHandleForwardPermQueryRevised_noResult normal stateIn hPop hBacktrack]
          exact d2sHandleForwardNoResultRevised_monitorStop_le gImpl normal stateIn hPop
      | some backtrackOut =>
          rw [d2sHandleForwardPermQueryRevised_some normal stateIn backtrackOut hPop hBacktrack]
          exact d2sHandleBacktrackSomeRevised_monitorStop_le gImpl normal stateIn backtrackOut
            hPop

/-- One complete revised D2SQuery step has the uniform `2j+1` local monitor-stop bound.  Hash
misses have the tighter `2j` charge, but are widened here so the finite runner can use one
branch-free coefficient; all table-hit paths are zero by base-trace redundancy. -/
lemma d2sQueryStepRevised_monitorStop_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hCoherent : RateOnlyCacheCoherent normal) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sQueryStepRevised normal q)] ≤
      (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  match q with
  | dsHashQuery stmt =>
      cases hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt with
      | some capacity =>
          rw [d2sQueryStepRevised_hash,
            d2sHandleHashQueryRevised_hit normal stmt capacity hLookup]
          have hSim :
              simulateQ
                (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
                (pure (d2sHandleHashPresentRevised normal stmt capacity hLookup)) =
                pure (d2sHandleHashPresentRevised normal stmt capacity hLookup) :=
            simulateQ_pure _ _
          have hNoStop := d2sHandleHashPresentRevised_not_monitorStop normal stmt capacity hLookup
          calc
            Pr[ fun result => result.isMonitorStop |
              simulateQ
                (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
                (pure (d2sHandleHashPresentRevised normal stmt capacity hLookup)) ] =
                Pr[ fun result => result.isMonitorStop |
                  pure (d2sHandleHashPresentRevised normal stmt capacity hLookup) ] :=
              congrArg (fun comp => Pr[ fun result => result.isMonitorStop | comp ]) hSim
            _ = 0 := by
              rw [probEvent_pure]
              simp only [hNoStop, ↓reduceIte]
            _ ≤ _ := bot_le
      | none =>
          rw [d2sQueryStepRevised_hash]
          calc
            Pr[ fun result => result.isMonitorStop |
              simulateQ
                (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
                (d2sHandleHashQueryRevised normal stmt)] ≤
                (2 * (getBaseTrace normal.state.trace).length : ℝ≥0∞) /
                  BadEventDS.capacitySpaceSize (U := U) :=
              d2sHandleHashQueryRevised_miss_monitorStop_le gImpl normal stmt hLookup
            _ ≤ (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
                  BadEventDS.capacitySpaceSize (U := U) := by
              gcongr
              exact le_add_of_nonneg_right bot_le
  | dsPermInvQuery stateOut =>
      cases hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut with
      | some stateIn =>
          rw [d2sQueryStepRevised_inverse,
            d2sHandleInversePermQueryRevised_hit normal stateOut stateIn hLookup]
          have hSim :
              simulateQ
                (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
                (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) =
                pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)) :=
            simulateQ_pure _ _
          have hNoStop := d2sPermResolvedInverseHit_not_monitorStop normal stateOut stateIn hLookup
          calc
            Pr[ fun result => result.isMonitorStop |
              simulateQ
                (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
                (pure (d2sPermResolvedStep normal (.inverse stateOut stateIn))) ] =
                Pr[ fun result => result.isMonitorStop |
                  pure (d2sPermResolvedStep normal (.inverse stateOut stateIn)) ] :=
              congrArg (fun comp => Pr[ fun result => result.isMonitorStop | comp ]) hSim
            _ = 0 := by
              rw [probEvent_pure]
              simp only [hNoStop, ↓reduceIte]
            _ ≤ _ := bot_le
      | none =>
          rw [d2sQueryStepRevised_inverse]
          exact d2sHandleInversePermQueryRevised_miss_monitorStop_le gImpl normal stateOut hLookup
  | dsPermQuery stateIn =>
      rw [d2sQueryStepRevised_forward]
      exact d2sHandleForwardPermQueryRevised_monitorStop_le gImpl normal stateIn hCoherent

/-! ## Branch-free finite-run aggregation

The five gateway lemmas above are intentionally one-step facts.  The following small interface is
the *only* additional fact needed to aggregate them over the real absorbing
`d2sQueryRunRevised` recursion: every continuing step can add at most one base-trace entry.  In
particular, it does not ask later Lemma 5.8 proofs to reopen the hash, inverse, tail, ordinary,
or Program branches.

The charge is indexed by an upper bound `j` on the current base-trace length.  It is recursive in
the actual query list, rather than a rounded sponge-block budget: a stopped or underlying-abort
branch never evaluates the recursive suffix. -/

/-- The branch-free first-bad charge for a finite actual D2SQuery run.  At a state whose base
trace has length at most `j`, one attempted query costs `(2j+1)/|Σ|ᶜ`; a continuing attempt moves
to the `j+1` upper bound. -/
noncomputable def d2sQueryRunFirstBadCharge (j : ℕ) :
    List (duplexSpongeChallengeOracle StmtIn U).Domain → ℝ≥0∞
  | [] => 0
  | _ :: queries =>
      ((2 * j + 1 : ℕ) : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U) +
        d2sQueryRunFirstBadCharge (j + 1) queries

/-- Widen the exact one-step bound to any supplied base-trace-length upper bound.  This is a
monotone arithmetic wrapper around `d2sQueryStepRevised_monitorStop_le`, not a second sampling
argument. -/
lemma d2sQueryStepRevised_monitorStop_le_of_baseLength_le
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hCoherent : RateOnlyCacheCoherent normal)
    (j : ℕ)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j) :
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sQueryStepRevised normal q)] ≤
      ((2 * j + 1 : ℕ) : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U) := by
  calc
    Pr[ fun result => result.isMonitorStop |
      simulateQ
        (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
        (d2sQueryStepRevised normal q)] ≤
        (2 * (getBaseTrace normal.state.trace).length + 1 : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) :=
      d2sQueryStepRevised_monitorStop_le gImpl normal q hCoherent
    _ ≤ ((2 * j + 1 : ℕ) : ℝ≥0∞) /
          BadEventDS.capacitySpaceSize (U := U) := by
      gcongr
      exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hBaseLength) 1

/-! ## Five concrete gateway packages -/

/-- The Step 2 fresh-hash gateway, with its exact `2j` charge. -/
noncomputable def D2SOneSampleGateway.hashMiss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.h stmt = none) :
    D2SOneSampleGateway normal where
  Answer := Vector U SpongeSize.C
  execute := d2sHandleHashQueryRevised normal stmt
  numerator := 2 * (getBaseTrace normal.state.trace).length
  monitorStop_le := fun gImpl =>
    d2sHandleHashQueryRevised_miss_monitorStop_le gImpl normal stmt hLookup

/-- The Step 3 fresh-inverse gateway, with its exact `2j + 1` charge. -/
noncomputable def D2SOneSampleGateway.inverseMiss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    D2SOneSampleGateway normal where
  Answer := CanonicalSpongeState U
  execute := d2sHandleInversePermQueryRevised normal stateOut
  numerator := 2 * (getBaseTrace normal.state.trace).length + 1
  monitorStop_le := fun gImpl =>
    d2sHandleInversePermQueryRevised_miss_monitorStop_le gImpl normal stateOut hLookup

/-- The Step 4.c true forward-miss gateway, with its exact `2j + 1` charge. -/
noncomputable def D2SOneSampleGateway.forwardMiss
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    D2SOneSampleGateway normal where
  Answer := CanonicalSpongeState U
  execute := d2sHandleForwardNoResultRevised normal stateIn
  numerator := 2 * (getBaseTrace normal.state.trace).length + 1
  monitorStop_le := fun gImpl =>
    d2sHandleForwardNoResultRevised_fresh_monitorStop_le gImpl normal stateIn hPop hLookup

/-- The Step 4.c.i selected-tail gateway.  Its `hPop` is the exact cache selection and `hKeys`
is the run-history invariant that makes the selected key a forward-table miss. -/
noncomputable def D2SOneSampleGateway.tail
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (entry : RateOnlyCacheEntry (U := U))
    (cacheRest : List (RateOnlyCacheEntry (U := U)))
    (hKeys : RateOnlyCacheKeysAreTableMisses normal)
    (hPop : popRateOnlyTailByInput normal.state.rateCacheP entry.stateIn =
      some (entry.tail, cacheRest)) :
    D2SOneSampleGateway normal where
  Answer := CanonicalSpongeState U
  execute := d2sHandlePoppedRateOnlyTailRevised normal entry cacheRest
  numerator := 2 * (getBaseTrace normal.state.trace).length + 1
  monitorStop_le := fun gImpl =>
    d2sHandlePoppedRateOnlyTailRevised_monitorStop_le gImpl normal entry cacheRest hKeys hPop

/-- The Step 4.e first-rate Program gateway.  The preceding Step 4.e.ii table-miss test is kept
in its constructor, rather than becoming an implicit global assumption. -/
noncomputable def D2SOneSampleGateway.program
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn : CanonicalSpongeState U)
    (firstRate : Vector U SpongeSize.R)
    (remainingRates : List (Vector U SpongeSize.R))
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    D2SOneSampleGateway normal where
  Answer := CanonicalSpongeState U
  execute := d2sHandleProgramFirstRateRevised normal stateIn firstRate remainingRates
  numerator := 2 * (getBaseTrace normal.state.trace).length + 1
  monitorStop_le := fun gImpl =>
    d2sHandleProgramFirstRateRevised_monitorStop_le gImpl normal stateIn firstRate
      remainingRates hLookup

end DuplexSpongeFS.ProverTransform
