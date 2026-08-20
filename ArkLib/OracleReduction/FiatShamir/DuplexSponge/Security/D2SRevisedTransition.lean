/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Core
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SPermInstall
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.MonitoredD2SQuery

/-!
# Revised D2SQuery transition: the `Install = conflict` crux family

This module formalizes the gating obligation of the revised (stateful) D2SQuery state boundary of
Section 5.4.  For a `D2SNormalState normal` whose
trace `tr` has passed `Monitor` (`¬ E tr`) and obeys the exact trace/table mirror, an attempted
table-only `Install` of a forced permutation occurrence that is classified `.conflict` forces
`E (tr ++ [occ])` — i.e. the occurrence produced by the conflicting mapping is the first bad
occurrence that the revised transition surfaces as a `D2SPostOccurrenceStopRecord`.

The proof has four stages, all trace/table level (no probability space):

1. **Extract the conflict witness.** `permInstallStatus = .conflict` ↔ `permPairConflicts =
   true`, which provides an entry of the forward table reusing `stateIn` with a different output
   (same-input) or `stateOut` with a different input (same-output).
2. **Non-redundancy of the appended occurrence.** By mirror + input/output functionality of the
   normal table (which `normal.monitorPassed` provides), `(stateIn, stateOut) ∉ entries p`, so the
   raw occurrence is not in `tr`, hence not in `getBaseTrace tr`: the appended occurrence survives
   into the base trace at its final index.
3. **First-bad routing.** The same-input witness is charged to `E_func` (Case 1, forward); the
   same-output witness is charged to `E_p` (capacity duplication on the output side).
4. **Base-trace transport.** The prior witness persists as a strict-prefix base index of the
   appended base trace, so the constructed per-index event fires at the appended index.

Specification note: these lemmas never assert that the attempted occurrence is an installed
partial-bijection mapping; they only show `E` of the extended trace, which is exactly what lets the
migrated transition stop at a post-occurrence record.
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

/-! ## Forward occurrence: `Install = conflict` forces `E` -/

/-- A successful normalized forward lookup is a `present` `Install` on every reusable state.

The lookup supplies the recorded pair.  `Monitor` has already established input and output
functionality of the normal table, so no different pair can conflict with it.  This is the small
selection bridge used when an Item 4 dispatcher turns its actual `inlu` guard into the
statement-layer table-hit branch; it adds no new premise beyond the reusable normal state. -/
lemma permInstallStatus_present_of_inlu_eq_some
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .present := by
  classical
  have hPair : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
    TraceTableOps.mem_entries_of_inlu_eq_some hLookup
  have hNoConflict : ¬ permPairConflicts normal.state.trΔ.p stateIn stateOut = true := by
    rw [permPairConflicts_eq_true_iff]
    rintro ⟨entry, hEntry, (hInput | hOutput)⟩
    · have hEntryMul : (entry.1, entry.2) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact hEntry
      have hPairMul : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact hPair
      have hEq : entry.2 = stateOut :=
        (D2SNormalState.table_inputFunctional
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)
          stateIn entry.2 stateOut (by simpa [hInput.1] using hEntryMul) hPairMul |>.symm
      exact hInput.2 hEq
    · have hEntryMul : (entry.1, entry.2) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact hEntry
      have hPairMul : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact hPair
      have hEq : entry.1 = stateIn :=
        (D2SNormalState.table_outputFunctional
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)
          entry.1 stateIn stateOut (by simpa [hOutput.1] using hEntryMul) hPairMul |>.symm
      exact hOutput.2 hEq
  have hConflict : permPairConflicts normal.state.trΔ.p stateIn stateOut = false := by
    cases h : permPairConflicts normal.state.trΔ.p stateIn stateOut <;> simp_all
  simp [permInstallStatus, hConflict, hPair]

/-- The inverse-direction form of `permInstallStatus_present_of_inlu_eq_some`.  A successful
output lookup supplies the same normalized pair; input functionality of the reusable table then
recovers the forward lookup needed by the common `Install = present` classifier.  Keeping this
bridge explicit prevents every inverse-handler proof from reconstructing the table-pair argument.
-/
lemma permInstallStatus_present_of_outlu_eq_some
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .present := by
  have hPair : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
    TraceTableOps.mem_entries_of_outlu_eq_some hLookup
  have hForwardLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut :=
    TraceTableOps.inlu_eq_some_of_nodup_of_inputFunctional normal.permutationNodup
      normal.table_inputFunctional hPair
  exact permInstallStatus_present_of_inlu_eq_some normal stateIn stateOut hForwardLookup

/-- On a reusable normal state, a failed forward lookup rules out only the `present` case of
`Install`: a newly sampled output is therefore either genuinely `fresh` or an output-side/input-side
`conflict`.  This is the exact classification needed by ordinary Step 4.c.iii; it deliberately
does **not** turn a sampled collision into an impossible branch. -/
lemma permInstallStatus_fresh_or_conflict_of_inlu_eq_none
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict := by
  cases hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | fresh => exact Or.inl rfl
  | conflict => exact Or.inr rfl
  | present =>
      have hMember : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
        permInstallStatus_present_mem normal.state.trΔ.p stateIn stateOut hStatus
      have hSome : TraceTableOps.inlu normal.state.trΔ.p stateIn = some stateOut :=
        TraceTableOps.inlu_eq_some_of_nodup_of_inputFunctional normal.permutationNodup
          (D2SNormalState.table_inputFunctional normal) hMember
      rw [hLookup] at hSome
      simp at hSome

/-- A failed forward lookup also rules out every prior **normalized** permutation representative
with that input in the base trace.  This is the trace-facing form of
`forward_input_miss_excludes_same_input_conflict`: it is used to eliminate `E_func` at the final
entry of a sampled ordinary miss, before reducing the stop to an `E_p` capacity hit. -/
lemma forward_input_miss_excludes_prior_normalized_pair
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none) :
    ¬ ((⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          getBaseTrace normal.state.trace ∨
        ⟨dsPermInvQuery stateOut, stateIn⟩ ∈ getBaseTrace normal.state.trace) := by
  intro hBase
  have hRaw :
      (⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          normal.state.trace ∨
        ⟨dsPermInvQuery stateOut, stateIn⟩ ∈ normal.state.trace := by
    rcases hBase with hForward | hInverse
    · exact Or.inl (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hForward)
    · exact Or.inr (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hInverse)
  have hPair : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
    (normal.state.h_mirror.2 stateIn stateOut).mp hRaw
  have hPairMs : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hPair
  have hNoMem := TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
    normal.permutationNodup (D2SNormalState.table_inputFunctional normal) hLookup stateOut
  exact hNoMem hPairMs

/-- The inverse dual of `permInstallStatus_fresh_or_conflict_of_inlu_eq_none`: an inverse-table
miss excludes `present`, while a sampled preimage can still conflict and must be monitored as a
terminal occurrence. -/
lemma permInstallStatus_fresh_or_conflict_of_outlu_eq_none
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    permInstallStatus normal.state.trΔ.p stateIn stateOut = .fresh ∨
      permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict := by
  cases hStatus : permInstallStatus normal.state.trΔ.p stateIn stateOut with
  | fresh => exact Or.inl rfl
  | conflict => exact Or.inr rfl
  | present =>
      have hMember : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
        permInstallStatus_present_mem normal.state.trΔ.p stateIn stateOut hStatus
      have hSome : TraceTableOps.outlu normal.state.trΔ.p stateOut = some stateIn :=
        TraceTableOps.outlu_eq_some_of_nodup_of_outputFunctional normal.permutationNodup
          (D2SNormalState.table_outputFunctional normal) hMember
      rw [hLookup] at hSome
      simp at hSome

/-- The trace-facing form of an inverse output miss.  A base representative with the queried
output would mirror to a table entry, contradicting the failed `outlu` lookup.  This excludes the
backward `E_func` clause at a freshly sampled inverse answer before probability is considered. -/
lemma inverse_output_miss_excludes_prior_normalized_pair
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none) :
    ¬ ((⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          getBaseTrace normal.state.trace ∨
        ⟨dsPermInvQuery stateOut, stateIn⟩ ∈ getBaseTrace normal.state.trace) := by
  intro hBase
  have hRaw :
      (⟨dsPermQuery stateIn, stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
          normal.state.trace ∨
        ⟨dsPermInvQuery stateOut, stateIn⟩ ∈ normal.state.trace := by
    rcases hBase with hForward | hInverse
    · exact Or.inl (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hForward)
    · exact Or.inr (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hInverse)
  have hPair : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
    (normal.state.h_mirror.2 stateIn stateOut).mp hRaw
  have hPairMs : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hPair
  have hNoMem := TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
    normal.permutationNodup (D2SNormalState.table_outputFunctional normal) hLookup stateIn
  exact hNoMem hPairMs

/-- A same-input conflict witness forces the attempted pair out of the forward table: if
`(stateIn, stateOut)` were present, input functionality would force `stateOut` to equal the
witness's second component. -/
lemma install_conflict_fwd_same_input_pair_not_in_entries
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hInputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.1 = stateIn ∧ entry.2 ≠ stateOut) :
    (stateIn, stateOut) ∉ TraceTableOps.entries normal.state.trΔ.p := by
  classical
  intro hPair
  obtain ⟨entry, hMem, hIn, hOut⟩ := hInputSide
  have hInL : entry.1 = stateIn := hIn
  have hOut : entry.2 ≠ stateOut := hOut
  -- Lift both memberships to the lawful multiset where `InputFunctional` lives.
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hMemMul : (stateIn, entry.2) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    simpa [hInL] using hMemPair
  have hPairMul : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hPair
  have heq : stateOut = entry.2 :=
    (D2SNormalState.table_inputFunctional
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)
      stateIn entry.2 stateOut hMemMul hPairMul
  exact hOut heq.symm

/-- A same-output conflict witness likewise forces `(stateIn, stateOut)` out of the forward table,
this time by output functionality. -/
lemma install_conflict_fwd_same_output_pair_not_in_entries
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hOutputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.2 = stateOut ∧ entry.1 ≠ stateIn) :
    (stateIn, stateOut) ∉ TraceTableOps.entries normal.state.trΔ.p := by
  classical
  intro hPair
  obtain ⟨entry, hMem, hOut, hIn⟩ := hOutputSide
  have hOutEq : entry.2 = stateOut := hOut
  have hInNe : entry.1 ≠ stateIn := hIn
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hMemMul : (entry.1, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    simpa [hOutEq] using hMemPair
  have hPairMul : (stateIn, stateOut) ∈ LawfulTraceTable.toMultiSet normal.state.trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hPair
  have heq : stateIn = entry.1 :=
    (D2SNormalState.table_outputFunctional
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal)
      entry.1 stateIn stateOut hMemMul hPairMul
  exact hInNe heq.symm

/-- The attempted forward occurrence is not redundant in the base trace of a normal state: since
`(stateIn, stateOut) ∉ entries p`, the mirror rules out both raw directions in `tr`, hence in
`getBaseTrace tr`. -/
lemma install_conflict_fwd_occ_not_redundant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hNotInEntries : (stateIn, stateOut) ∉ TraceTableOps.entries normal.state.trΔ.p) :
    ¬ isRedundantEntryOfPrefix (getBaseTrace normal.state.trace)
      (⟨.inr (.inl stateIn), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
  classical
  have hRawNotInTr :
      ¬ ((⟨.inr (.inl stateIn), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ normal.state.trace ∨
        ⟨.inr (.inr stateOut), stateIn⟩ ∈ normal.state.trace) := by
    intro hRaw
    have hInEntries : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
      (normal.state.h_mirror.2 stateIn stateOut).mp hRaw
    exact hNotInEntries hInEntries
  intro hRed
  unfold isRedundantEntryOfPrefix at hRed
  rcases hRed with hF | hI
  · apply hRawNotInTr
    left
    exact (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hF)
  · apply hRawNotInTr
    right
    exact (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hI)

/-- The appended forward occurrence is not redundant in the base trace.  The conflict witness
together with the normal state's functionality rules `(stateIn, stateOut)` out of the forward
table (via `install_conflict_fwd_same_input_pair_not_in_entries`), so
`install_conflict_fwd_occ_not_redundant` applies. -/
lemma install_conflict_fwd_same_input_occ_not_redundant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hInputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.1 = stateIn ∧ entry.2 ≠ stateOut) :
    ¬ isRedundantEntryOfPrefix (getBaseTrace normal.state.trace)
      (⟨.inr (.inl stateIn), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) :=
  install_conflict_fwd_occ_not_redundant normal
    (install_conflict_fwd_same_input_pair_not_in_entries normal hInputSide)

/-- **Forward, same-input conflict → `E_func`.**  A conflict witness reusing `stateIn` with a
different output `entry.2 ≠ stateOut` forces the *prior* occurrence `⟨p, stateIn, entry.2⟩` (or its
inverse representative) to sit strictly before the appended `⟨p, stateIn, stateOut⟩` in the base
trace.  That is exactly `E_func` Case 1 at the appended index. -/
lemma install_conflict_fwd_same_input_imp_E_func
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hInputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.1 = stateIn ∧ entry.2 ≠ stateOut) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermQuery stateIn, stateOut⟩
  let j := (getBaseTrace tr).length
  -- 1. Non-redundancy of the appended occurrence (survives into the base trace).
  have hNotRed : ¬ isRedundantEntryOfPrefix (getBaseTrace tr) occ := by
    simpa [tr, occ] using
      (install_conflict_fwd_same_input_occ_not_redundant normal hInputSide)
  have hbt : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] :=
    getBaseTrace_append_singleton_of_not_redundant_base tr occ hNotRed
  -- 2. The conflict witness is a prior trace/base occurrence sharing `stateIn`.
  obtain ⟨entry, hMem, hIn, hOut⟩ := hInputSide
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hRawPrior :
      (⟨.inr (.inl stateIn), entry.2⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ tr ∨
        ⟨.inr (.inr entry.2), stateIn⟩ ∈ tr := by
    exact ((normal.state.h_mirror.2 stateIn entry.2).mpr (by simpa [tr, hIn] using hMemPair))
  have hBasePrior :
      (⟨.inr (.inl stateIn), entry.2⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ getBaseTrace tr ∨
        ⟨.inr (.inr entry.2), stateIn⟩ ∈ getBaseTrace tr :=
    normalizedPermPair_mem_getBaseTrace_of_mem tr stateIn entry.2 hRawPrior
  -- 3. Construct the forward functionality event at the appended base index `j`.
  have hFwdAt : BadEventDS.E_func_fwd_at (tr ++ [occ]) j := by
    unfold BadEventDS.E_func_fwd_at
    dsimp
    refine ⟨?_, stateIn, stateOut, ?_, ?_⟩
    · -- `j < (getBaseTrace (tr ++ [occ])).length`
      rw [hbt]
      simp [j]
    · -- the appended occurrence occupies the final base index
      simpa [occ, j, hbt]
    · rcases hBasePrior with hF | hI
      · -- forward prior `⟨p, stateIn, entry.2⟩` at base index `i < j`
        rw [List.mem_iff_get] at hF
        obtain ⟨⟨i, hi⟩, hgi⟩ := hF
        simp only [List.get_eq_getElem] at hgi
        let hiNew : i < (getBaseTrace (tr ++ [occ])).length := by
          rw [hbt]
          simp only [List.length_append]
          omega
        refine ⟨⟨i, hiNew⟩, ?_, Or.inl ⟨entry.2, ?_, hOut⟩⟩
        · -- `i < j` as `Fin` comparison
          simpa [j] using hi
        · have hTrans : (getBaseTrace (tr ++ [occ]))[i]'hiNew = (getBaseTrace tr)[i]'hi :=
            BadEventDS.getBaseTrace_getElem_eq_of_append_eq hbt hi hiNew
          simpa [hgi] using hTrans
      · -- inverse prior `⟨p⁻¹, entry.2, stateIn⟩` at base index `i < j`
        rw [List.mem_iff_get] at hI
        obtain ⟨⟨i, hi⟩, hgi⟩ := hI
        simp only [List.get_eq_getElem] at hgi
        let hiNew : i < (getBaseTrace (tr ++ [occ])).length := by
          rw [hbt]
          simp only [List.length_append]
          omega
        refine ⟨⟨i, hiNew⟩, ?_, Or.inr ⟨entry.2, ?_, hOut⟩⟩
        · -- `i < j` as `Fin` comparison
          simpa [j] using hi
        · have hTrans : (getBaseTrace (tr ++ [occ]))[i]'hiNew = (getBaseTrace tr)[i]'hi :=
            BadEventDS.getBaseTrace_getElem_eq_of_append_eq hbt hi hiNew
          simpa [hgi] using hTrans
  -- 4. Lift to `E_func` then `E`.
  have hFuncAt : BadEventDS.E_func_at (tr ++ [occ]) j :=
    (BadEventDS.E_func_at_iff_fwd_or_bwd (tr ++ [occ])).mpr (Or.inl hFwdAt)
  have hFunc : BadEventDS.E_func (tr ++ [occ]) :=
    (BadEventDS.E_func_iff_exists_at (tr ++ [occ])).mpr ⟨j, hFuncAt⟩
  exact Or.inr hFunc

/-! ## Reusable prior-index transport -/

/-- Given a prior entry `e` of the old base trace, lift it into the appended base trace at the
same index, recovering a strict-before-`j` index comparison and the transported getElem equality.
This factors out the `List.mem_iff_get`/`getElem`/proof-irrelevance boilerplate shared by all the
per-index event constructions. -/
lemma getBaseTrace_append_prior_mem_idx
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (occ : Sigma (duplexSpongeChallengeOracle StmtIn U))
    (hbt : getBaseTrace (trace ++ [occ]) = getBaseTrace trace ++ [occ])
    {e : Sigma (duplexSpongeChallengeOracle StmtIn U)}
    (hmem : e ∈ getBaseTrace trace) :
    ∃ (i : ℕ) (hiNew : i < (getBaseTrace (trace ++ [occ])).length),
      i < (getBaseTrace trace).length ∧ (getBaseTrace (trace ++ [occ]))[i]'hiNew = e := by
  rw [List.mem_iff_get] at hmem
  obtain ⟨⟨i, hi⟩, hgi⟩ := hmem
  simp only [List.get_eq_getElem] at hgi
  let hiNew : i < (getBaseTrace (trace ++ [occ])).length := by
    rw [hbt]
    simp only [List.length_append]
    omega
  refine ⟨i, hiNew, hi, ?_⟩
  have hTrans : (getBaseTrace (trace ++ [occ]))[i]'hiNew = (getBaseTrace trace)[i]'hi :=
    BadEventDS.getBaseTrace_getElem_eq_of_append_eq hbt hi hiNew
  simpa [hgi] using hTrans

/-! ## Forward occurrence: same-output conflict → `E_dup` -/

/-- **Forward, same-output conflict → `E_dup`.**  A conflict witness reusing `stateOut` with a
different input `entry.1 ≠ stateIn` forces a *prior* occurrence carrying `stateOut.capacitySegment`
to sit strictly before (or at) the appended `⟨p, stateIn, stateOut⟩` in the base trace.  That is
exactly `E_p` at the appended index (the forward witness charges `E_p`'s branch 2, the inverse
witness charges branch 5, both via `isDuplicatedPriorCapacity`). -/
lemma install_conflict_fwd_same_output_imp_E_p_at
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hOutputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.2 = stateOut ∧ entry.1 ≠ stateIn) :
    BadEventDS.E_p_at (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      (getBaseTrace normal.state.trace).length := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermQuery stateIn, stateOut⟩
  let j := (getBaseTrace tr).length
  -- 1. Non-redundancy of the appended occurrence.
  have hNotRed : ¬ isRedundantEntryOfPrefix (getBaseTrace tr) occ := by
    simpa [tr, occ] using
      (install_conflict_fwd_occ_not_redundant normal
        (install_conflict_fwd_same_output_pair_not_in_entries normal hOutputSide))
  have hbt : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] :=
    getBaseTrace_append_singleton_of_not_redundant_base tr occ hNotRed
  -- 2. The conflict witness is a prior trace/base occurrence sharing `stateOut`.
  obtain ⟨entry, hMem, hOut, hIn⟩ := hOutputSide
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hRawPrior :
      (⟨.inr (.inl entry.1), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ tr ∨
        ⟨.inr (.inr stateOut), entry.1⟩ ∈ tr := by
    exact ((normal.state.h_mirror.2 entry.1 stateOut).mpr (by simpa [tr, hOut] using hMemPair))
  have hBasePrior :
      (⟨.inr (.inl entry.1), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ getBaseTrace tr ∨
        ⟨.inr (.inr stateOut), entry.1⟩ ∈ getBaseTrace tr :=
    normalizedPermPair_mem_getBaseTrace_of_mem tr entry.1 stateOut hRawPrior
  -- 3. Construct the capacity-duplication event at the appended base index `j`.
  have hPAt : BadEventDS.E_p_at (tr ++ [occ]) j := by
    unfold BadEventDS.E_p_at
    dsimp
    refine ⟨?hj, stateOut.capacitySegment, ?now, ?dup⟩
    · rw [hbt]
      simp [j]
    · refine ⟨stateIn, stateOut, ?_, rfl⟩
      simpa [occ, j, hbt]
    · rcases hBasePrior with hF | hI
      · -- Forward prior at index `i`: `isDuplicatedPriorCapacity` branch 2.
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hF
        unfold BadEventDS.isDuplicatedPriorCapacity
        right; left
        refine ⟨⟨i, hiNew⟩, ?_, entry.1, stateOut, ?_, rfl⟩
        · simpa [j] using hi
        · simpa [heq]
      · -- Inverse prior at index `i`: `isDuplicatedPriorCapacity` branch 5.
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hI
        unfold BadEventDS.isDuplicatedPriorCapacity
        right; right; right; right
        refine ⟨⟨i, hiNew⟩, ?_, stateOut, entry.1, ?_, rfl⟩
        · simpa [j] using (Nat.le_of_lt hi)
        · simpa [heq]
  simpa [tr, occ, j] using hPAt

/-- The public conflict gate used by the transition.  The stronger companion
`install_conflict_fwd_same_output_imp_E_p_at` retains the exact first-event clause for the
capacity proof; this wrapper is the unchanged `Monitor`-level consequence. -/
lemma install_conflict_fwd_same_output_imp_E_dup
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hOutputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.2 = stateOut ∧ entry.1 ≠ stateIn) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) := by
  let j := (getBaseTrace normal.state.trace).length
  have hP := install_conflict_fwd_same_output_imp_E_p_at normal hConfigH hOutputSide
  exact (BadEventDS.E_iff_exists_E_at _).mpr ⟨j, Or.inr (Or.inl (by simpa [j] using hP))⟩

/-! ## Forward occurrence: combined conflict → `E` -/

/-- **Forward combined.**  Any `.conflict` classification, whether from a same-input or a
same-output witness, forces `E` of the extended trace.  This is the gating obligation consumed by
the revised transition's forward `Install`. -/
lemma install_conflict_fwd_imp_E
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩]) := by
  classical
  have hpc : permPairConflicts normal.state.trΔ.p stateIn stateOut = true :=
    (permInstallStatus_conflict_iff normal.state.trΔ.p stateIn stateOut).mp hConfigH
  rw [permPairConflicts_eq_true_iff] at hpc
  rcases hpc with ⟨entry, hMem, hSide⟩
  rcases hSide with hIn | hOut
  · exact install_conflict_fwd_same_input_imp_E_func normal hConfigH ⟨entry, hMem, hIn⟩
  · exact install_conflict_fwd_same_output_imp_E_dup normal hConfigH ⟨entry, hMem, hOut⟩

/-! ## Inverse occurrence: `Install = conflict` forces `E` -/

/-- The attempted inverse occurrence is not redundant in the base trace of a normal state: since
`(stateIn, stateOut) ∉ entries p`, the mirror rules out both raw directions in `tr`, hence in
`getBaseTrace tr`.  Inverse-analogue of `install_conflict_fwd_occ_not_redundant`. -/
lemma install_conflict_inv_occ_not_redundant
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hNotInEntries : (stateIn, stateOut) ∉ TraceTableOps.entries normal.state.trΔ.p) :
    ¬ isRedundantEntryOfPrefix (getBaseTrace normal.state.trace)
      (⟨.inr (.inr stateOut), stateIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
  classical
  have hRawNotInTr :
      ¬ ((⟨.inr (.inl stateIn), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ normal.state.trace ∨
        ⟨.inr (.inr stateOut), stateIn⟩ ∈ normal.state.trace) := by
    intro hRaw
    have hInEntries : (stateIn, stateOut) ∈ TraceTableOps.entries normal.state.trΔ.p :=
      (normal.state.h_mirror.2 stateIn stateOut).mp hRaw
    exact hNotInEntries hInEntries
  intro hRed
  unfold isRedundantEntryOfPrefix at hRed
  rcases hRed with hI | hF
  · apply hRawNotInTr
    right
    exact (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hI)
  · apply hRawNotInTr
    left
    exact (List.Sublist.subset (getBaseTrace_sublist normal.state.trace) hF)

/-- **Inverse, same-output conflict → `E_func` (Case 2 / backward).**  A conflict witness reusing
`stateOut` (the inverse-query side) with a different input `entry.1 ≠ stateIn` forces a *prior*
occurrence carrying `stateOut` with a different answer (inverse prior, sub-branch A) or as a forward
output with a different input (forward prior, sub-branch B) to sit strictly before the appended
`⟨p⁻¹, stateOut, stateIn⟩` in the base trace.  That is exactly `E_func_bwd` at the appended
index. -/
lemma install_conflict_inv_same_output_imp_E_func
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hOutputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.2 = stateOut ∧ entry.1 ≠ stateIn) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermInvQuery stateOut, stateIn⟩
  let j := (getBaseTrace tr).length
  have hNotRed : ¬ isRedundantEntryOfPrefix (getBaseTrace tr) occ := by
    simpa [tr, occ] using
      (install_conflict_inv_occ_not_redundant normal
        (install_conflict_fwd_same_output_pair_not_in_entries normal hOutputSide))
  have hbt : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] :=
    getBaseTrace_append_singleton_of_not_redundant_base tr occ hNotRed
  obtain ⟨entry, hMem, hOut, hIn⟩ := hOutputSide
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hRawPrior :
      (⟨.inr (.inl entry.1), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ tr ∨
        ⟨.inr (.inr stateOut), entry.1⟩ ∈ tr := by
    exact ((normal.state.h_mirror.2 entry.1 stateOut).mpr (by simpa [tr, hOut] using hMemPair))
  have hBasePrior :
      (⟨.inr (.inl entry.1), stateOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ getBaseTrace tr ∨
        ⟨.inr (.inr stateOut), entry.1⟩ ∈ getBaseTrace tr :=
    normalizedPermPair_mem_getBaseTrace_of_mem tr entry.1 stateOut hRawPrior
  have hBwdAt : BadEventDS.E_func_bwd_at (tr ++ [occ]) j := by
    unfold BadEventDS.E_func_bwd_at
    dsimp
    refine ⟨?hj, stateIn, stateOut, ?_, ?_⟩
    · rw [hbt]
      simp [j]
    · simpa [occ, j, hbt]
    · rcases hBasePrior with hF | hI
      · -- forward prior `⟨p, entry.1, stateOut⟩` → sub-branch B (`stateOut` as forward output)
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hF
        refine ⟨⟨i, hiNew⟩, ?_, Or.inr ⟨entry.1, ?_, hIn⟩⟩
        · simpa [j] using hi
        · simpa [heq]
      · -- inverse prior `⟨p⁻¹, stateOut, entry.1⟩` → sub-branch A (`stateOut` as inverse query)
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hI
        refine ⟨⟨i, hiNew⟩, ?_, Or.inl ⟨entry.1, ?_, hIn⟩⟩
        · simpa [j] using hi
        · simpa [heq]
  have hFuncAt : BadEventDS.E_func_at (tr ++ [occ]) j :=
    (BadEventDS.E_func_at_iff_fwd_or_bwd (tr ++ [occ])).mpr (Or.inr hBwdAt)
  have hEat : BadEventDS.E_at (tr ++ [occ]) j := Or.inr (Or.inr (Or.inr hFuncAt))
  exact (BadEventDS.E_iff_exists_E_at (tr ++ [occ])).mpr ⟨j, hEat⟩

/-- **Inverse, same-input conflict → `E_pinv` (`E_dup`).**  A conflict witness reusing `stateIn`
(the inverse-answer side) with a different output `entry.2 ≠ stateOut` forces a *prior* occurrence
carrying `stateIn.capacitySegment` (as a forward input, branch 4, or as an inverse answer,
branch 3) to sit strictly before (or at) the appended `⟨p⁻¹, stateOut, stateIn⟩` in the base trace.
That is exactly `E_pinv` at the appended index. -/
lemma install_conflict_inv_same_input_imp_E_pinv_at
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hInputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.1 = stateIn ∧ entry.2 ≠ stateOut) :
    BadEventDS.E_pinv_at (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      (getBaseTrace normal.state.trace).length := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermInvQuery stateOut, stateIn⟩
  let j := (getBaseTrace tr).length
  have hNotRed : ¬ isRedundantEntryOfPrefix (getBaseTrace tr) occ := by
    simpa [tr, occ] using
      (install_conflict_inv_occ_not_redundant normal
        (install_conflict_fwd_same_input_pair_not_in_entries normal hInputSide))
  have hbt : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] :=
    getBaseTrace_append_singleton_of_not_redundant_base tr occ hNotRed
  obtain ⟨entry, hMem, hIn, hOut⟩ := hInputSide
  have hMemPair : (entry.1, entry.2) ∈ TraceTableOps.entries normal.state.trΔ.p := by
    simpa using hMem
  have hRawPrior :
      (⟨.inr (.inl stateIn), entry.2⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ tr ∨
        ⟨.inr (.inr entry.2), stateIn⟩ ∈ tr := by
    exact ((normal.state.h_mirror.2 stateIn entry.2).mpr (by simpa [tr, hIn] using hMemPair))
  have hBasePrior :
      (⟨.inr (.inl stateIn), entry.2⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U))
          ∈ getBaseTrace tr ∨
        ⟨.inr (.inr entry.2), stateIn⟩ ∈ getBaseTrace tr :=
    normalizedPermPair_mem_getBaseTrace_of_mem tr stateIn entry.2 hRawPrior
  have hPInvAt : BadEventDS.E_pinv_at (tr ++ [occ]) j := by
    unfold BadEventDS.E_pinv_at
    dsimp
    refine ⟨?hj, stateIn.capacitySegment, ?now, ?dup⟩
    · rw [hbt]
      simp [j]
    · refine ⟨stateOut, stateIn, ?_, rfl⟩
      simpa [occ, j, hbt]
    · rcases hBasePrior with hF | hI
      · -- Forward prior: branch 4 (`stateIn` as forward input, `j' ≤ j`).
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hF
        unfold BadEventDS.isDuplicatedPriorCapacity
        right; right; right; left
        refine ⟨⟨i, hiNew⟩, ?_, stateIn, entry.2, ?_, rfl⟩
        · simpa [j] using (Nat.le_of_lt hi)
        · simpa [heq]
      · -- Inverse prior: branch 3 (`stateIn` as inverse answer, `j' < j`).
        have ⟨i, hiNew, hi, heq⟩ := getBaseTrace_append_prior_mem_idx tr occ hbt hI
        unfold BadEventDS.isDuplicatedPriorCapacity
        right; right; left
        refine ⟨⟨i, hiNew⟩, ?_, entry.2, stateIn, ?_, rfl⟩
        · simpa [j] using hi
        · simpa [heq]
  simpa [tr, occ, j] using hPInvAt

/-- The public inverse conflict gate.  The stronger companion
`install_conflict_inv_same_input_imp_E_pinv_at` retains the exact clause and index needed by the
inverse fresh-capacity kernel; this wrapper preserves the original `Monitor`-level API. -/
lemma install_conflict_inv_same_input_imp_E_pinv
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict)
    (hInputSide : ∃ entry ∈ TraceTableOps.entries normal.state.trΔ.p,
      entry.1 = stateIn ∧ entry.2 ≠ stateOut) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) := by
  let j := (getBaseTrace normal.state.trace).length
  have hP := install_conflict_inv_same_input_imp_E_pinv_at normal hConfigH hInputSide
  exact (BadEventDS.E_iff_exists_E_at _).mpr ⟨j, Or.inr (Or.inr (Or.inl (by
    simpa [j] using hP)))⟩

/-- **Inverse combined.**  Any `.conflict` classification, whether from a same-input or a
same-output witness, forces `E` of the trace extended by the inverse occurrence.  This is the gating
obligation consumed by the revised transition's inverse `Install`. -/
lemma install_conflict_inv_imp_E
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {stateIn stateOut : CanonicalSpongeState U}
    (hConfigH : permInstallStatus normal.state.trΔ.p stateIn stateOut = .conflict) :
    BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩]) := by
  classical
  have hpc : permPairConflicts normal.state.trΔ.p stateIn stateOut = true :=
    (permInstallStatus_conflict_iff normal.state.trΔ.p stateIn stateOut).mp hConfigH
  rw [permPairConflicts_eq_true_iff] at hpc
  rcases hpc with ⟨entry, hMem, hSide⟩
  rcases hSide with hIn | hOut
  · exact install_conflict_inv_same_input_imp_E_pinv normal hConfigH ⟨entry, hMem, hIn⟩
  · exact install_conflict_inv_same_output_imp_E_func normal hConfigH ⟨entry, hMem, hOut⟩

/-! ## Every monitored stop is a first bad base occurrence

The `Install = conflict` lemmas above explain one important *cause* of a monitor failure.  The
first-event probability proof, however, must work for **every** `D2SPostOccurrenceStopRecord`:
the last occurrence may have been selected by a hash, a cache-tail materialization, a fresh
permutation sample, or a conflict.  This short trace-level interface is deliberately independent
of that cause.

It proves three facts which eliminate the usual stopped-trace bookkeeping from the probability
argument:

1. the monitored final occurrence is nonredundant relative to its reusable normal prefix;
2. the final base trace is the prefix base trace followed by exactly that occurrence; and
3. the corresponding base index is the **first** index satisfying `E_at`.

The key observation is semantic rather than probabilistic.  If the final occurrence were
redundant, its base trace would equal the `E`-good normal prefix's base trace.  Any `E_at` witness
of the monitor failure would then reflect to that prefix, contradicting `normal.monitorPassed`.
Thus a stopped result always has one canonical fresh base position; it never leaves a hidden bad
event inside a redundant raw occurrence.
-/

/-- The canonical base-trace index of the final occurrence recorded by a monitored stop.  It is
the length of the normal prefix's base trace, hence the index at which the appended occurrence
will occur once nonredundancy is established below. -/
noncomputable def D2SPostOccurrenceStopRecord.firstBadIndex
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (_record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) : ℕ :=
  (getBaseTrace normal.state.trace).length

/-- `Monitor` cannot first fail on a redundant occurrence.  Otherwise the base trace would be
unchanged, and its `E_at` witness would reflect to `normal.state.trace`, contradicting the normal
state's `monitorPassed` invariant. -/
lemma D2SPostOccurrenceStopRecord.occ_not_redundant
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    ¬ isRedundantEntryOfPrefix (getBaseTrace normal.state.trace)
      (⟨record.query, record.answer⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
  classical
  intro hRed
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨record.query, record.answer⟩
  have hBaseEq : getBaseTrace (tr ++ [occ]) = getBaseTrace tr :=
    getBaseTrace_append_singleton_of_redundant_base tr occ (by simpa [tr, occ] using hRed)
  have hTerminalBad : BadEventDS.E (tr ++ [occ]) := by
    simpa [tr, occ] using record.monitorFails
  obtain ⟨j, hAt⟩ := (BadEventDS.E_iff_exists_E_at (tr ++ [occ])).mp hTerminalBad
  have hjFinal : j < (getBaseTrace (tr ++ [occ])).length :=
    BadEventDS.E_at_lt_length (tr ++ [occ]) hAt
  have hjPrefix : j < (getBaseTrace tr).length := by
    simpa [hBaseEq] using hjFinal
  have hBaseAppendNil : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [] := by
    simpa [hBaseEq]
  have hAtPrefix : BadEventDS.E_at tr j :=
    BadEventDS.E_at_of_getBaseTrace_append_eq_of_lt hBaseAppendNil hjPrefix hAt
  exact normal.monitorPassed ((BadEventDS.E_iff_exists_E_at tr).mpr ⟨j, hAtPrefix⟩)

/-- A monitored stop extends the normal prefix's base trace by exactly its retained final
occurrence.  This is the direct raw-trace-to-base-trace accounting equation for first-event
probability sums. -/
lemma D2SPostOccurrenceStopRecord.getBaseTrace_append
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    getBaseTrace record.trace =
      getBaseTrace normal.state.trace ++ [⟨record.query, record.answer⟩] := by
  exact getBaseTrace_append_singleton_of_not_redundant_base normal.state.trace
    ⟨record.query, record.answer⟩ record.occ_not_redundant

/-- The single final base entry of a monitored stop is a first `E_at` witness.  All strictly
earlier base indices belong to the normal prefix and are `E`-good; the terminal record supplies
the bad event at the appended entry.  This is the exact stopping-time fact consumed by the revised
Lemma 5.8 proof. -/
lemma D2SPostOccurrenceStopRecord.first_bad_at
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
    BadEventDS.E_first_at record.trace record.firstBadIndex := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨record.query, record.answer⟩
  let j := (getBaseTrace tr).length
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [tr, occ] using record.getBaseTrace_append
  have hTerminalBad : BadEventDS.E (tr ++ [occ]) := by
    simpa [tr, occ] using record.monitorFails
  obtain ⟨i, hFirst⟩ := (BadEventDS.E_iff_exists_E_first_at (tr ++ [occ])).mp hTerminalBad
  have hiFinal : i < (getBaseTrace (tr ++ [occ])).length :=
    BadEventDS.E_at_lt_length (tr ++ [occ]) hFirst.1
  have hiLe : i ≤ j := by
    rw [hBase] at hiFinal
    exact Nat.le_of_lt_succ (by simpa [j] using hiFinal)
  have hNotLt : ¬ i < j := by
    intro hij
    have hAtPrefix : BadEventDS.E_at tr i :=
      BadEventDS.E_at_of_getBaseTrace_append_eq_of_lt hBase (by simpa [j] using hij) hFirst.1
    exact normal.monitorPassed ((BadEventDS.E_iff_exists_E_at tr).mpr ⟨i, hAtPrefix⟩)
  have hij : i = j := by omega
  simpa [D2SPostOccurrenceStopRecord.firstBadIndex, tr, j, hij] using hFirst

/-- A `Monitor` failure after a newly recorded hash occurrence is necessarily `E_h` at the new
final base entry.  The other three components of `E_at` require a forward or inverse permutation
entry at that position, so they are excluded by the terminal hash shape. -/
lemma hash_monitor_failure_imp_E_h_at
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])) :
    BadEventDS.E_h_at (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
      (getBaseTrace normal.state.trace).length := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsHashQuery stmt, capacity⟩
  let j := (getBaseTrace tr).length
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsHashQuery stmt, capacity, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hFirst : BadEventDS.E_first_at (tr ++ [occ]) j := by
    simpa [record, tr, occ, j, D2SPostOccurrenceStopRecord.firstBadIndex,
      D2SPostOccurrenceStopRecord.trace] using record.first_bad_at
  have hFinalIndex : j < (getBaseTrace (tr ++ [occ])).length := by
    rw [hBase]
    simp [j]
  have hFinalAppendIndex : j < (getBaseTrace tr ++ [occ]).length := by
    simp [j]
  have hFinal : (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex = occ := by
    calc
      (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex =
          (getBaseTrace tr ++ [occ])[j]'hFinalAppendIndex :=
        getElem_congr hBase rfl hFinalIndex
      _ = occ := by simp [j]
  rcases hFirst.1 with hHash | hPerm | hInv | hFunc
  · simpa [tr, occ, j] using hHash
  · rcases hPerm with ⟨_, _, ⟨sIn, sOut, hEntry, _⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · rcases hInv with ⟨_, _, ⟨sOut, sIn, hEntry, _⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · rcases (BadEventDS.E_func_at_iff_fwd_or_bwd (tr ++ [occ])).mp hFunc with hFwd | hBwd
    · rcases hFwd with ⟨_, _, _, hEntry, _⟩
      exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
    · rcases hBwd with ⟨_, _, _, hEntry, _⟩
      exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)

/-- The hash-direction normal form consumed by the adaptive uniform-capacity kernel.  The sampled
hash capacity must hit one of the at most `2j` capacity coordinates exposed by the preceding base
trace; no permutation-side input coordinate is added. -/
lemma hash_monitor_failure_in_capacity_target
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stmt : StmtIn) (capacity : Vector U SpongeSize.C)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])) :
    capacity ∈ BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
      (getBaseTrace normal.state.trace).length := by
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsHashQuery stmt, capacity⟩
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsHashQuery stmt, capacity, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hAt := hash_monitor_failure_imp_E_h_at normal stmt capacity hE
  have hHit := BadEventDS.E_h_at_imp_hashFreshHitAt
    (normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩])
    (getBaseTrace normal.state.trace).length hAt
  rw [show normal.state.trace ++ [⟨dsHashQuery stmt, capacity⟩] = tr ++ [occ] by rfl,
    hBase] at hHit
  exact (BadEventDS.hashFreshHitAt_append_hash_length_iff
    (getBaseTrace tr) stmt capacity).mp hHit

/-- A `Monitor` failure after **any** ordinary forward-table miss is necessarily `E_p` at the
new final base entry.  The terminal occurrence is forward, excluding `E_h` and `E_pinv`; and the
miss excludes every prior normalized pair with its input, excluding `E_func`.  Therefore both a
fresh sampled stop and an output-side `Install` conflict share one exact `E_p` target route.

This is the key first-event normalization for Algorithm 5.3 Step 4.c.iii: after it, the
probabilistic proof need only expose the sampled capacity and apply the finite-target bound. -/
lemma forward_input_miss_monitor_failure_imp_E_p_at
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])) :
    BadEventDS.E_p_at (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
      (getBaseTrace normal.state.trace).length := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermQuery stateIn, stateOut⟩
  let j := (getBaseTrace tr).length
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsPermQuery stateIn, stateOut, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hFirst : BadEventDS.E_first_at (tr ++ [occ]) j := by
    simpa [record, tr, occ, j, D2SPostOccurrenceStopRecord.firstBadIndex,
      D2SPostOccurrenceStopRecord.trace] using record.first_bad_at
  have hFinalIndex : j < (getBaseTrace (tr ++ [occ])).length := by
    rw [hBase]
    simp [j]
  have hFinalAppendIndex : j < (getBaseTrace tr ++ [occ]).length := by
    simp [j]
  have hFinal : (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex = occ := by
    calc
      (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex =
          (getBaseTrace tr ++ [occ])[j]'hFinalAppendIndex :=
        getElem_congr hBase rfl hFinalIndex
      _ = occ := by simp [j]
  rcases hFirst.1 with hHash | hPerm | hInv | hFunc
  · rcases hHash with ⟨_, _, ⟨stmt, hEntry⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · simpa [tr, occ, j] using hPerm
  · rcases hInv with ⟨_, _, ⟨sOut, sIn, hEntry, _⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · rcases (BadEventDS.E_func_at_iff_fwd_or_bwd (tr ++ [occ])).mp hFunc with hFwd | hBwd
    · rcases hFwd with ⟨hj, sIn, sOut, hEntry, j', hj', hPrior⟩
      have hCurrent :
          (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) = occ :=
        hEntry.symm.trans hFinal
      have hCurrent' : sIn = stateIn ∧ sOut = stateOut := by
        simpa [occ] using hCurrent
      rcases hCurrent' with ⟨hIn, _⟩
      have hjPrefix : (j' : ℕ) < (getBaseTrace tr).length := by
        simpa [j] using (Fin.lt_def.mp hj')
      have hPriorPrefix :
          (getBaseTrace tr)[j'.1]'hjPrefix =
            (getBaseTrace (tr ++ [occ]))[j'.1]'j'.2 :=
        (BadEventDS.getBaseTrace_getElem_eq_of_append_eq hBase hjPrefix j'.2).symm
      rcases hPrior with ⟨priorOut, hPriorEntry, _⟩ | ⟨priorOut, hPriorEntry, _⟩
      · apply False.elim
        apply forward_input_miss_excludes_prior_normalized_pair normal stateIn priorOut hLookup
        left
        have hPriorEntry' :
            (getBaseTrace tr)[j'.1]'hjPrefix =
              (⟨.inr (.inl sIn), priorOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
          simpa using hPriorPrefix.trans hPriorEntry
        rw [← hIn, ← hPriorEntry']
        exact List.getElem_mem _
      · apply False.elim
        apply forward_input_miss_excludes_prior_normalized_pair normal stateIn priorOut hLookup
        right
        have hPriorEntry' :
            (getBaseTrace tr)[j'.1]'hjPrefix =
              (⟨.inr (.inr priorOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
          simpa using hPriorPrefix.trans hPriorEntry
        rw [← hIn, ← hPriorEntry']
        exact List.getElem_mem _
    · rcases hBwd with ⟨_, _, _, hEntry, _⟩
      exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)

/-- The preceding first-event normal form in the exact finite-set form consumed by the uniform
capacity kernel.  It treats a sampled `.fresh` stop and an output-side `Install` conflict
uniformly: once an ordinary forward lookup missed, *any* `Monitor` stop makes the sampled output
capacity hit the pre-step forward target set of cardinality at most `2j + 1`. -/
lemma forward_input_miss_monitor_failure_in_capacity_target
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateIn stateOut : CanonicalSpongeState U)
    (hLookup : TraceTableOps.inlu normal.state.trΔ.p stateIn = none)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])) :
    stateOut.capacitySegment ∈
      BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
        (getBaseTrace normal.state.trace).length ∪ {stateIn.capacitySegment} := by
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermQuery stateIn, stateOut⟩
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsPermQuery stateIn, stateOut, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hAt := forward_input_miss_monitor_failure_imp_E_p_at normal stateIn stateOut hLookup hE
  have hHit := BadEventDS.E_p_at_imp_permFwdFreshHitAt
    (normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩])
    (getBaseTrace normal.state.trace).length hAt
  rw [show normal.state.trace ++ [⟨dsPermQuery stateIn, stateOut⟩] = tr ++ [occ] by rfl,
    hBase] at hHit
  exact (BadEventDS.permFwdFreshHitAt_append_fwd_length_iff
    (getBaseTrace tr) stateIn stateOut).mp hHit

/-- A `Monitor` failure after an inverse-table miss is necessarily `E_pinv` at the new final base
entry.  The terminal occurrence is inverse, excluding `E_h` and `E_p`; the output miss excludes
the prior normalized pairs needed by the backward `E_func` clause.  Thus every sampled inverse
stop has one precise capacity-target cause. -/
lemma inverse_output_miss_monitor_failure_imp_E_pinv_at
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])) :
    BadEventDS.E_pinv_at (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
      (getBaseTrace normal.state.trace).length := by
  classical
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermInvQuery stateOut, stateIn⟩
  let j := (getBaseTrace tr).length
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsPermInvQuery stateOut, stateIn, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hFirst : BadEventDS.E_first_at (tr ++ [occ]) j := by
    simpa [record, tr, occ, j, D2SPostOccurrenceStopRecord.firstBadIndex,
      D2SPostOccurrenceStopRecord.trace] using record.first_bad_at
  have hFinalIndex : j < (getBaseTrace (tr ++ [occ])).length := by
    rw [hBase]
    simp [j]
  have hFinalAppendIndex : j < (getBaseTrace tr ++ [occ]).length := by
    simp [j]
  have hFinal : (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex = occ := by
    calc
      (getBaseTrace (tr ++ [occ]))[j]'hFinalIndex =
          (getBaseTrace tr ++ [occ])[j]'hFinalAppendIndex :=
        getElem_congr hBase rfl hFinalIndex
      _ = occ := by simp [j]
  rcases hFirst.1 with hHash | hPerm | hInv | hFunc
  · rcases hHash with ⟨_, _, ⟨stmt, hEntry⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · rcases hPerm with ⟨_, _, ⟨sIn, sOut, hEntry, _⟩, _⟩
    exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
  · simpa [tr, occ, j] using hInv
  · rcases (BadEventDS.E_func_at_iff_fwd_or_bwd (tr ++ [occ])).mp hFunc with hFwd | hBwd
    · rcases hFwd with ⟨_, _, _, hEntry, _⟩
      exact False.elim (by simpa [occ] using hFinal.symm.trans hEntry)
    · rcases hBwd with ⟨hj, sIn, sOut, hEntry, j', hj', hPrior⟩
      have hCurrent :
          (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) = occ :=
        hEntry.symm.trans hFinal
      have hCurrent' : sOut = stateOut ∧ sIn = stateIn := by
        simpa [occ] using hCurrent
      rcases hCurrent' with ⟨hOut, _⟩
      have hjPrefix : (j' : ℕ) < (getBaseTrace tr).length := by
        simpa [j] using (Fin.lt_def.mp hj')
      have hPriorPrefix :
          (getBaseTrace tr)[j'.1]'hjPrefix =
            (getBaseTrace (tr ++ [occ]))[j'.1]'j'.2 :=
        (BadEventDS.getBaseTrace_getElem_eq_of_append_eq hBase hjPrefix j'.2).symm
      rcases hPrior with ⟨priorIn, hPriorEntry, _⟩ | ⟨priorIn, hPriorEntry, _⟩
      · apply False.elim
        apply inverse_output_miss_excludes_prior_normalized_pair normal stateOut priorIn hLookup
        right
        have hPriorEntry' :
            (getBaseTrace tr)[j'.1]'hjPrefix =
              (⟨.inr (.inr sOut), priorIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
          simpa using hPriorPrefix.trans hPriorEntry
        rw [← hOut, ← hPriorEntry']
        exact List.getElem_mem _
      · apply False.elim
        apply inverse_output_miss_excludes_prior_normalized_pair normal stateOut priorIn hLookup
        left
        have hPriorEntry' :
            (getBaseTrace tr)[j'.1]'hjPrefix =
              (⟨.inr (.inl priorIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
          simpa using hPriorPrefix.trans hPriorEntry
        rw [← hOut, ← hPriorEntry']
        exact List.getElem_mem _

/-- The inverse miss normal form in the finite-set shape consumed by the uniform full-state
kernel.  Projecting the sampled preimage to its capacity gives a target family of size at most
`2j + 1`, with no separate functionality charge. -/
lemma inverse_output_miss_monitor_failure_in_capacity_target
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (stateOut stateIn : CanonicalSpongeState U)
    (hLookup : TraceTableOps.outlu normal.state.trΔ.p stateOut = none)
    (hE : BadEventDS.E (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])) :
    stateIn.capacitySegment ∈
      BadEventDS.priorCapacityTargetFinset (getBaseTrace normal.state.trace)
        (getBaseTrace normal.state.trace).length ∪ {stateOut.capacitySegment} := by
  let tr := normal.state.trace
  let occ : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermInvQuery stateOut, stateIn⟩
  let record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal :=
    ⟨dsPermInvQuery stateOut, stateIn, hE⟩
  have hBase : getBaseTrace (tr ++ [occ]) = getBaseTrace tr ++ [occ] := by
    simpa [record, tr, occ] using record.getBaseTrace_append
  have hAt := inverse_output_miss_monitor_failure_imp_E_pinv_at normal stateOut stateIn hLookup hE
  have hHit := BadEventDS.E_pinv_at_imp_permBwdFreshHitAt
    (normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩])
    (getBaseTrace normal.state.trace).length hAt
  rw [show normal.state.trace ++ [⟨dsPermInvQuery stateOut, stateIn⟩] = tr ++ [occ] by rfl,
    hBase] at hHit
  exact (BadEventDS.permBwdFreshHitAt_append_bwd_length_iff
    (getBaseTrace tr) stateOut stateIn).mp hHit

end DuplexSpongeFS.ProverTransform
