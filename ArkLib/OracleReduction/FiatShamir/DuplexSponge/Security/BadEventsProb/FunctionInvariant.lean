/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SpongeTrace
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.Representatives
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.PrefixEvents

/-!
# Operational prefix invariants for the functional bad event

This module contains the deterministic D2S handler facts behind the sigma-side `E_func`
arguments.  It deliberately stops at one-handler support points: the later combined-runner lift
is responsible only for threading this invariant through `StateT (OptionT ProbComp)`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ}
  {T_H : Type} {T_P : Type}
  [DecidableEq StmtIn] [DecidableEq U]
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section LocalTraceBridges

variable
  (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
  (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))

/-- A successful `Option.elimM` computation came from a successful sample.  This small
support-unwinding lemma is shared by the BackTrack `.some` operational cases below. -/
private lemma mem_support_option_elimM_some {α β : Type} {sample : ProbComp (Option α)}
    {body : α → ProbComp (Option β)} {b : β}
    (h : some b ∈ support (Option.elimM sample (pure none) body)) :
    ∃ a, some a ∈ support sample ∧ some b ∈ support (body a) := by
  simp only [Option.elimM] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨o, ho, hb⟩ := h
  cases o with
  | none =>
      simp at hb
  | some a =>
      exact ⟨a, ho, by simp at hb; exact hb⟩

/-- A successful nested-`Option` map witnesses a successful source value and its exact image. -/
private lemma mem_support_map_nested_option_some {α β : Type}
    {sample : ProbComp (Option (Option α))} {f : α → β} {b : β}
    (h : some (some b) ∈ support (Option.map (Option.map f) <$> sample)) :
    ∃ a, some (some a) ∈ support sample ∧ f a = b := by
  rw [support_map] at h
  obtain ⟨ooa, hoo, hmap⟩ := h
  cases ooa with
  | none =>
      simp only [Option.map_none] at hmap
      cases hmap
  | some oa =>
      cases oa with
      | none =>
          simp only [Option.map_some, Option.map_none] at hmap
          cases hmap
      | some a =>
          simp only [Option.map_some, Option.some.injEq] at hmap
          subst hmap
          exact ⟨a, hoo, rfl⟩

/-- Output functionality of the mirrored simulator table rules out every backward functional
conflict in its current trace: both conflicting normalized pairs would occupy the same table
output key with unequal preimages. -/
lemma not_E_func_bwd_at_of_permOutput_wf_mirror
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace) (j : ℕ) :
    ¬ E_func_bwd_at trace j := by
  rintro ⟨hj, sIn, sOut, hNow, j', hj'lt, hPrior⟩
  have hNowRaw :
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace := by
    apply (getBaseTrace_sublist trace).subset
    rw [← hNow]
    exact List.getElem_mem _
  have hNowEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
    (hMirror.2 sIn sOut).mp (Or.inr hNowRaw)
  have hNowTable : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hNowEntry
  rcases hPrior with ⟨sIn', hPrior, hne⟩ | ⟨sIn', hPrior, hne⟩
  · have hPriorRaw :
        (⟨.inr (.inr sOut), sIn'⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace := by
      apply (getBaseTrace_sublist trace).subset
      rw [← hPrior]
      exact List.getElem_mem _
    have hPriorEntry : (sIn', sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn' sOut).mp (Or.inr hPriorRaw)
    have hPriorTable : (sIn', sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact hPriorEntry
    exact hne (hwf.p_outputFunctional sIn sIn' sOut hNowTable hPriorTable)
  · have hPriorRaw :
        (⟨.inr (.inl sIn'), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace := by
      apply (getBaseTrace_sublist trace).subset
      rw [← hPrior]
      exact List.getElem_mem _
    have hPriorEntry : (sIn', sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn' sOut).mp (Or.inl hPriorRaw)
    have hPriorTable : (sIn', sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact hPriorEntry
    exact hne (hwf.p_outputFunctional sIn sIn' sOut hNowTable hPriorTable)

/-- The chronological property required by the backward part of Lemma 5.8. -/
def BwdHasPriorBad (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ j, E_func_bwd_at trace j → ∃ j' < j, E_at trace j'

/-- Output functionality plus mirroring establishes the backward chronological property outright. -/
lemma BwdHasPriorBad.of_permOutput_wf_mirror
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace) :
    BwdHasPriorBad trace := by
  intro j hbwd
  exact False.elim (not_E_func_bwd_at_of_permOutput_wf_mirror
    (T_H := T_H) (T_P := T_P) trace hwf hMirror j hbwd)

/-- An old backward witness can be read back through a base-trace suffix extension as long as its
index remains in the old prefix. -/
lemma E_func_bwd_at_of_getBaseTrace_append_eq
    {trace trace' : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {extra : QueryLog (duplexSpongeChallengeOracle StmtIn U)} {j : ℕ}
    (hbt : getBaseTrace trace' = getBaseTrace trace ++ extra)
    (hj : j < (getBaseTrace trace).length)
    (h : E_func_bwd_at trace' j) :
    E_func_bwd_at trace j := by
  rcases h with ⟨hj', sIn, sOut, hNow, j', hj'lt, hPrior⟩
  have hjNew : j < (getBaseTrace trace').length := hj'
  have hNowOld : (getBaseTrace trace)[j] = ⟨.inr (.inr sOut), sIn⟩ := by
    exact (getBaseTrace_getElem_eq_of_append_eq hbt hj hjNew).symm.trans hNow
  have hjpOld : j'.1 < (getBaseTrace trace).length := by
    exact Nat.lt_trans (Fin.lt_def.mp hj'lt) hj
  let jOld : Fin (getBaseTrace trace).length := ⟨j'.1, hjpOld⟩
  have hjOldLt : jOld < ⟨j, hj⟩ := by
    exact Fin.lt_def.mpr (Fin.lt_def.mp hj'lt)
  refine ⟨hj, sIn, sOut, hNowOld, jOld, hjOldLt, ?_⟩
  rcases hPrior with ⟨sIn', hPrior, hne⟩ | ⟨sIn', hPrior, hne⟩
  · left
    refine ⟨sIn', ?_, hne⟩
    exact (getBaseTrace_getElem_eq_of_append_eq hbt hjpOld j'.2).symm.trans hPrior
  · right
    refine ⟨sIn', ?_, hne⟩
    exact (getBaseTrace_getElem_eq_of_append_eq hbt hjpOld j'.2).symm.trans hPrior

/-- Appending a forward query cannot introduce a backward functional witness: if it is retained,
its sole new base position is visibly forward; all earlier backward witnesses are inherited. -/
lemma BwdHasPriorBad.append_forward
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrior : BwdHasPriorBad trace)
    (sIn sOut : CanonicalSpongeState U) :
    BwdHasPriorBad (trace ++ [⟨dsPermQuery sIn, sOut⟩]) := by
  classical
  let entry : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨dsPermQuery sIn, sOut⟩
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry
  · have hbt : getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ [] := by
      rw [DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace entry hred]
      rw [List.append_nil]
    intro j hbwd
    have hOld := E_func_bwd_at_of_getBaseTrace_append_eq hbt
      (j := j) (by
        have hjNew := hbwd.1
        rw [hbt, List.length_append, List.length_nil] at hjNew
        exact hjNew) hbwd
    obtain ⟨j', hj'lt, hBad⟩ := hPrior j hOld
    exact ⟨j', hj'lt, E_at_of_getBaseTrace_append_eq hbt hBad⟩
  · have hbt : getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ [entry] :=
      DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace entry hred
    intro j hbwd
    by_cases hjOld : j < (getBaseTrace trace).length
    · have hOld := E_func_bwd_at_of_getBaseTrace_append_eq hbt hjOld hbwd
      obtain ⟨j', hj'lt, hBad⟩ := hPrior j hOld
      exact ⟨j', hj'lt, E_at_of_getBaseTrace_append_eq hbt hBad⟩
    · rcases hbwd with ⟨hj, sIn', sOut', hNow, _j', _hjlt, _hConflict⟩
      have hlen : (getBaseTrace (trace ++ [entry])).length =
          (getBaseTrace trace).length + 1 := by
        rw [hbt, List.length_append, List.length_singleton]
      have hjGe : (getBaseTrace trace).length ≤ j := Nat.le_of_not_gt hjOld
      have hjLe : j < (getBaseTrace trace).length + 1 := by
        rw [← hlen]
        exact hj
      have hjEq : j = (getBaseTrace trace).length := by omega
      have hInv : (getBaseTrace (trace ++ [entry]))[j]? =
          some ⟨.inr (.inr sOut'), sIn'⟩ := by
        rw [List.getElem?_eq_getElem hj]
        exact congrArg some hNow
      rw [hjEq, hbt, getElem?_append_singleton_length] at hInv
      simp [entry] at hInv

/-- Once an older canonical bad event exists, it witnesses the required strict predecessor for
any newly retained base entry; old backward witnesses are transported unchanged. -/
lemma BwdHasPriorBad.append_of_E
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (hPrior : BwdHasPriorBad trace) (hE : E trace)
    (entry : Sigma (duplexSpongeChallengeOracle StmtIn U)) :
    BwdHasPriorBad (trace ++ [entry]) := by
  classical
  by_cases hred : isRedundantEntryOfPrefix (getBaseTrace trace) entry
  · have hbt : getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ [] := by
      rw [DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace entry hred]
      rw [List.append_nil]
    intro j hbwd
    have hOld := E_func_bwd_at_of_getBaseTrace_append_eq hbt
      (j := j) (by
        have hjNew := hbwd.1
        rw [hbt, List.length_append, List.length_nil] at hjNew
        exact hjNew) hbwd
    obtain ⟨j', hj'lt, hBad⟩ := hPrior j hOld
    exact ⟨j', hj'lt, E_at_of_getBaseTrace_append_eq hbt hBad⟩
  · have hbt : getBaseTrace (trace ++ [entry]) = getBaseTrace trace ++ [entry] :=
      DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace entry hred
    intro j hbwd
    by_cases hjOld : j < (getBaseTrace trace).length
    · have hOld := E_func_bwd_at_of_getBaseTrace_append_eq hbt hjOld hbwd
      obtain ⟨j', hj'lt, hBad⟩ := hPrior j hOld
      exact ⟨j', hj'lt, E_at_of_getBaseTrace_append_eq hbt hBad⟩
    · obtain ⟨jBad, hBad⟩ := (E_iff_exists_E_at trace).mp hE
      have hjBadLt : jBad < (getBaseTrace trace).length := E_at_lt_length trace hBad
      have hlen : (getBaseTrace (trace ++ [entry])).length =
          (getBaseTrace trace).length + 1 := by
        rw [hbt, List.length_append, List.length_singleton]
      have hjGe : (getBaseTrace trace).length ≤ j := Nat.le_of_not_gt hjOld
      have hjLe : j < (getBaseTrace trace).length + 1 := by
        rw [← hlen]
        exact hbwd.1
      have hjEq : j = (getBaseTrace trace).length := by omega
      refine ⟨jBad, ?_, E_at_of_getBaseTrace_append_eq hbt hBad⟩
      rw [hjEq]
      exact hjBadLt

/-- A new forward base representative whose output state was already represented is charged by
`E_p` at precisely its appended base index.  Handler-specific proofs obtain the base-trace-growth
premise from an `inlu` miss plus the no-prior-bad table invariant. -/
lemma E_p_at_append_forward_of_prior_same_output
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sIn' sOut : CanonicalSpongeState U)
    (hPrior : (⟨.inr (.inl sIn'), sOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace ∨
      (⟨.inr (.inr sOut), sIn'⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace)
    (hbase : getBaseTrace (trace ++ [⟨.inr (.inl sIn), sOut⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩]) :
    E_p_at (trace ++ [⟨.inr (.inl sIn), sOut⟩]) (getBaseTrace trace).length := by
  unfold E_p_at
  rw [hbase]
  dsimp only
  refine ⟨by
    simp only [List.length_append, List.length_cons, List.length_nil]
    exact Nat.le_refl _, sOut.capacitySegment, ?_, ?_⟩
  · exact ⟨sIn, sOut, by simp, rfl⟩
  unfold isDuplicatedPriorCapacity
  rcases hPrior with hFwd | hBwd
  · rw [List.mem_iff_get] at hFwd
    obtain ⟨j', hprior⟩ := hFwd
    simp only [List.get_eq_getElem] at hprior
    refine Or.inr (Or.inl ⟨⟨j', by
      simp only [List.length_append, List.length_cons, List.length_nil]
      exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩, ?_, sIn', sOut, ?_, rfl⟩)
    · exact j'.isLt
    · change (getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩])[j'.val]'_ = _
      rw [List.getElem_append_left (bs := [⟨.inr (.inl sIn), sOut⟩]) j'.isLt]
      exact hprior
  · rw [List.mem_iff_get] at hBwd
    obtain ⟨j', hprior⟩ := hBwd
    simp only [List.get_eq_getElem] at hprior
    refine Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨j', by
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩,
      ?_, sOut, sIn', ?_, rfl⟩)))
    · exact Nat.le_of_lt j'.isLt
    · change (getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩])[j'.val]'_ = _
      rw [List.getElem_append_left (bs := [⟨.inr (.inl sIn), sOut⟩]) j'.isLt]
      exact hprior

/-- Set-semantic cache insertion preserves output functionality when the output key was absent.
This is the cache-pop counterpart of `TracePermOutputWellformed.add_perm_outlu`. -/
lemma TracePermOutputWellformed.insert_perm_outlu
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    {sIn sOut : CanonicalSpongeState U}
    (hLookup : TraceTableOps.outlu trΔ.p sOut = none) :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      ({ trΔ with p := TraceTableOps.insert trΔ.p sIn sOut } :
        TraceNabla T_H T_P StmtIn U) := by
  have hFresh :
      (sIn, sOut) ∉ LawfulTraceTable.toMultiSet trΔ.p :=
    TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.p_nodup hwf.p_outputFunctional hLookup sIn
  have hEntry : (sIn, sOut) ∉ TraceTableOps.entries trΔ.p := by
    intro hMem
    apply hFresh
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact Multiset.mem_coe.mpr hMem
  rw [TraceTableOps.insert, if_neg hEntry]
  exact TracePermOutputWellformed.add_perm_outlu
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
    (sIn := sIn) hwf hLookup

/-- If an output-side lookup already represents `sIn' ↦ sOut` with `sIn' ≠ sIn`, then under
output functionality the normalized pair `sIn ↦ sOut` cannot already occur in the mirrored base
trace.  Thus appending it creates a genuinely new forward representative, which the preceding
`E_p` bridge can charge. -/
lemma perm_base_not_mem_of_outlu_some_of_ne
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sIn' sOut : CanonicalSpongeState U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = some sIn')
    (hNe : sIn' ≠ sIn) :
    (⟨.inr (.inl sIn), sOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉ getBaseTrace trace ∧
      (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉ getBaseTrace trace := by
  have hOld : (sIn', sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact Multiset.mem_coe.mpr (TraceTableOps.mem_entries_of_outlu_eq_some hLookup)
  constructor
  · intro hBase
    have hRaw : (⟨.inr (.inl sIn), sOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hNewEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inl hRaw)
    have hNew : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hNewEntry
    exact hNe (hwf.p_outputFunctional sIn sIn' sOut hNew hOld)
  · intro hBase
    have hRaw : (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hNewEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inr hRaw)
    have hNew : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hNewEntry
    exact hNe (hwf.p_outputFunctional sIn sIn' sOut hNew hOld)

/-! ## Forward fresh-sampling step -/

/- A forward `inlu` miss either preserves output-table wellformedness or appends a new
representative whose output collides with a represented permutation output, which is immediately
charged by `E_p`.  The only use of `¬ E` is to recover input functionality from the mirror so
that the forward append is known to create a base representative. -/
set_option maxHeartbeats 400000 in
-- This finite table-and-base-trace case split is reused by the StateT runner invariant.
lemma forward_miss_permOutput_wf_or_E
    {st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {stateIn a : CanonicalSpongeState U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    (hIn : TraceTableOps.inlu st.trΔ.p stateIn = none) :
    E (st.trace ++ [⟨.inr (.inl stateIn), a⟩]) ∨
      TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U)
        ({ st.trΔ with p := TraceTableOps.add st.trΔ.p stateIn a } :
          TraceNabla T_H T_P StmtIn U) := by
  cases hOut : TraceTableOps.outlu st.trΔ.p a with
  | none =>
      exact Or.inr (TracePermOutputWellformed.add_perm_outlu
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        (sIn := stateIn) hwf hOut)
  | some sIn' =>
      let hInput : TracePermInputWellformed (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (U := U) st.trΔ :=
        ⟨hwf.p_nodup,
          table_inputFunctional_of_mirror_of_not_E (trace := st.trace) st.h_mirror hNoE⟩
      have hbase : getBaseTrace (st.trace ++ [⟨.inr (.inl stateIn), a⟩]) =
          getBaseTrace st.trace ++ [⟨.inr (.inl stateIn), a⟩] :=
        getBaseTrace_append_perm_inlu_miss_eq_of_input_wf
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
          hInput st.h_mirror hIn
      have hPrior := perm_outlu_pair_mem_baseTrace_of_mirror
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        st.h_mirror hOut
      have hEp := E_p_at_append_forward_of_prior_same_output
        (StmtIn := StmtIn) (U := U) st.trace stateIn sIn' a hPrior hbase
      exact Or.inl ((E_iff_exists_E_at _).mpr
        ⟨(getBaseTrace st.trace).length, Or.inr (Or.inl hEp)⟩)

/- The cache-pop branch has the same output-functional dichotomy as a fresh forward step.
Set insertion is harmless when its output is fresh or when it repeats the exact represented pair;
otherwise it appends a new output collision, hence `E_p`. -/
set_option maxHeartbeats 400000 in
-- The cached-pair branch needs the same finite output-lookup split as a fresh permutation answer.
lemma cache_insert_permOutput_wf_or_E
    {st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    {stateIn a : CanonicalSpongeState U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ) :
    E (st.trace ++ [⟨.inr (.inl stateIn), a⟩]) ∨
      TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U)
        ({ st.trΔ with p := TraceTableOps.insert st.trΔ.p stateIn a } :
          TraceNabla T_H T_P StmtIn U) := by
  cases hOut : TraceTableOps.outlu st.trΔ.p a with
  | none =>
      exact Or.inr (TracePermOutputWellformed.insert_perm_outlu
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        (sIn := stateIn) hwf hOut)
  | some sIn' =>
      by_cases hEq : sIn' = stateIn
      · subst sIn'
        have hMem : (stateIn, a) ∈ TraceTableOps.entries st.trΔ.p :=
          TraceTableOps.mem_entries_of_outlu_eq_some hOut
        have hp : TraceTableOps.insert st.trΔ.p stateIn a = st.trΔ.p := by
          rw [TraceTableOps.insert, if_pos hMem]
        exact Or.inr ⟨by rw [hp]; exact hwf.p_nodup,
          by rw [hp]; exact hwf.p_outputFunctional⟩
      · have hnot := perm_base_not_mem_of_outlu_some_of_ne
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
          hwf st.h_mirror hOut hEq
        have hbase : getBaseTrace (st.trace ++ [⟨.inr (.inl stateIn), a⟩]) =
            getBaseTrace st.trace ++ [⟨.inr (.inl stateIn), a⟩] :=
          DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base st.trace
            ⟨.inr (.inl stateIn), a⟩ (by
              simp only [isRedundantEntryOfPrefix]
              intro hred
              rcases hred with hFwd | hBwd
              · exact hnot.1 hFwd
              · exact hnot.2 hBwd)
        have hPrior := perm_outlu_pair_mem_baseTrace_of_mirror
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
          st.h_mirror hOut
        have hEp := E_p_at_append_forward_of_prior_same_output
          (StmtIn := StmtIn) (U := U) st.trace stateIn sIn' a hPrior hbase
        exact Or.inl ((E_iff_exists_E_at _).mpr
          ⟨(getBaseTrace st.trace).length, Or.inr (Or.inl hEp)⟩)

/-! ## The `.noResult` forward handler -/

/- The three operational branches of Item 4(c) preserve output functionality unless the newly
recorded forward pair itself raises `E_p`.  This is the local preservation component that the
combined-runner invariant needs; it does not perform any probability reasoning. -/
set_option maxHeartbeats 400000 in
-- The handler unfolds to cache-pop, genuine forward miss, and successful forward-table-hit cases.
lemma d2sHandleBacktrackNoResult_support_permOutput_wf_or_E
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleBacktrackNoResult at hi
  cases hCache : ProverTransform.popCacheEntryByInput (U := U) st.cacheP stateIn with
  | some cached =>
      rcases cached with ⟨cachedEntry, cacheTail⟩
      simp [hCache] at hi
      rcases hi with ⟨ha, hst⟩
      subst a
      subst st'
      exact cache_insert_permOutput_wf_or_E
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) hwf
  | none =>
      by_cases hIn : TraceTableOps.inlu st.trΔ.p stateIn = none
      · simp [hCache, hIn] at hi
        rcases hi with ⟨_, hst⟩
        subst st'
        exact forward_miss_permOutput_wf_or_E
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) hwf hNoE hIn
      · simp [hCache, hIn] at hi
        obtain ⟨ha, hst⟩ := hi
        subst a
        subst st'
        exact Or.inr hwf

/-! ## The `.some` forward handler -/

/- Item 4(d)/4(e) ultimately either answers from `inlu` or installs one new forward pair.  The
oracle and state plumbing is unwound here only far enough to expose that common table operation. -/
set_option maxHeartbeats 400000 in
-- This shares the no-result result theorem rather than duplicating any base-trace collision logic.
lemma d2sHandleBacktrackSome_support_permOutput_wf_or_E
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleBacktrackSome
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        stateIn backtrackOut).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleBacktrackSome at hi
  have rebuild (hp : st'.trΔ.p = st.trΔ.p) :
      E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
    exact Or.inr ⟨by rw [hp]; exact hwf.p_nodup,
      by rw [hp]; exact hwf.p_outputFunctional⟩
  split at hi
  · simp at hi
    obtain ⟨rhoHat, _hrhoHat, hi⟩ := mem_support_option_elimM_some hi
    split at hi
    · exact rebuild (by aesop)
    · simp at hi
      obtain ⟨rateBlocks, _hrateBlocks, hi⟩ := mem_support_option_elimM_some hi
      obtain ⟨synth, _hsynth, hsynth⟩ := mem_support_map_nested_option_some hi
      injection hsynth with _ha hstEq
      subst st'
      exact forward_miss_permOutput_wf_or_E
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) hwf hNoE (by assumption)
  · simp at hi
    split at hi
    · exact rebuild (by aesop)
    · simp at hi
      rcases hi with ⟨_ha, hstEq⟩
      subst st'
      exact forward_miss_permOutput_wf_or_E
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) hwf hNoE (by assumption)

/-! ## The forward wrapper -/

/- A successful forward handler preserves output functionality unless its newly installed
representative itself raises an already-defined bad event.  The abort branch has no support point. -/
set_option maxHeartbeats 400000 in
-- The generated BackTrack term needs bounded extra reduction to expose its three branches.
lemma d2sHandleForwardPermQuery_support_permOutput_wf_or_E
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleForwardPermQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleForwardPermQuery at hi
  cases hbt : Backtrack.backTrack
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
  | err =>
      simp [hbt] at hi
  | noResult =>
      exact d2sHandleBacktrackNoResult_support_permOutput_wf_or_E
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl st hwf hNoE (by
          simp [hbt] at hi
          exact hi) rfl
  | some backtrackOut =>
      exact d2sHandleBacktrackSome_support_permOutput_wf_or_E
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl backtrackOut st hwf hNoE (by
          simp [hbt] at hi
          exact hi) rfl

/-! ## The non-forward handlers -/

/-- A hash query never changes the permutation table. -/
lemma d2sHandleHashQuery_support_permOutput_wf
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {i : Option (Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleHashQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run)
    {a : Vector U SpongeSize.C}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleHashQuery at hi
  cases hLookup : TraceTableOps.inlu st.trΔ.h stmt with
  | none =>
      simp [hLookup] at hi
      have hp : st'.trΔ.p = st.trΔ.p := by aesop
      exact ⟨by rw [hp]; exact hwf.p_nodup,
        by rw [hp]; exact hwf.p_outputFunctional⟩
  | some capSeg =>
      simp [hLookup] at hi
      have hp : st'.trΔ.p = st.trΔ.p := by aesop
      exact ⟨by rw [hp]; exact hwf.p_nodup,
        by rw [hp]; exact hwf.p_outputFunctional⟩

/-- An inverse query installs only a pair with a fresh output key, so it preserves output
functionality unconditionally. -/
lemma d2sHandleInversePermQuery_support_permOutput_wf
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleInversePermQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleInversePermQuery at hi
  cases hLookup : TraceTableOps.outlu st.trΔ.p stateOut with
  | none =>
      simp [hLookup] at hi
      have hp : st'.trΔ.p = TraceTableOps.add st.trΔ.p a stateOut := by aesop
      have hNew := TracePermOutputWellformed.add_perm_outlu
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        (sIn := a) hwf hLookup
      exact ⟨by rw [hp]; exact hNew.p_nodup,
        by rw [hp]; exact hNew.p_outputFunctional⟩
  | some recovered =>
      simp [hLookup] at hi
      have hp : st'.trΔ.p = st.trΔ.p := by aesop
      exact ⟨by rw [hp]; exact hwf.p_nodup,
        by rw [hp]; exact hwf.p_outputFunctional⟩

/-! ## One D2S dispatch step -/

/- Under a good prefix, one successful D2S step either retains output functionality or creates
the first bad event in its new representative. -/
set_option maxHeartbeats 400000 in
-- The sum-dispatch branches expose generated dependent OptionT terms.
lemma d2sQueryStep_support_permOutput_wf_or_E
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    {i : Option (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sQueryStep
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run)
    {a : (duplexSpongeChallengeOracle StmtIn U).Range q}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  cases q with
  | inl stmt =>
      exact Or.inr (d2sHandleHashQuery_support_permOutput_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl st hwf hi hiEq)
  | inr q' =>
      cases q' with
      | inl stateIn =>
          exact d2sHandleForwardPermQuery_support_permOutput_wf_or_E
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl st hwf hNoE hi hiEq
      | inr stateOut =>
          exact Or.inr (d2sHandleInversePermQuery_support_permOutput_wf
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl st hwf hi hiEq)

/- The public D2S wrapper has the same local invariant: an abort has no successful support
point, while a successful step is exactly the corresponding `d2sQueryStep` support point. -/
set_option maxHeartbeats 400000 in
-- Unfolding `OptionT.run` once exposes the dispatcher support point.
lemma d2sQueryImpl_support_permOutput_wf_or_E
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    (hNoE : ¬ E st.trace)
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run)) :
    ∀ a st', r = some (a, st') →
      E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
  intro a₀ st₀ hrEq
  rw [ProverTransform.d2sQueryImpl] at hr
  simp only [Option.elimM, OptionT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨i, hi, hr⟩ := hr
  cases hiEq : i with
  | none =>
      have hr' : r ∈ support (pure none : ProbComp
          (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        rw [hiEq] at hr
        exact hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      cases hr'
  | some i' =>
      cases i' with
      | none =>
          have hr' : r ∈ support
              ((failure : OptionT ProbComp
                ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                  ProverTransform.D2SQueryState
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run) := by
            rw [hiEq] at hr
            exact hr
          rw [hrEq] at hr'
          simp at hr'
      | some pair =>
          rcases pair with ⟨a, st'⟩
          have hi' : some (some (a, st')) ∈ support
              (simulateQ (gImpl + auxImpl)
                (OptionT.run ((ProverTransform.d2sQueryStep
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run := by
            rw [hiEq] at hi
            exact hi
          have hstep : E st'.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (U := U) st'.trΔ :=
            d2sQueryStep_support_permOutput_wf_or_E
              (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) gImpl auxImpl q st hwf hNoE hi' rfl
          have hr' : r = some (a, st') := by
            have hrPure : r ∈ support (pure (some (a, st')) : ProbComp
              (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                ProverTransform.D2SQueryState
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
              rw [hiEq] at hr
              exact hr
            rw [mem_support_pure_iff] at hrPure
            exact hrPure
          have hpair : (a₀, st₀) = (a, st') := by
            rw [hrEq] at hr'
            exact Option.some.inj hr'
          injection hpair with ha hs
          subst ha
          subst hs
          exact hstep

/-- Generic successful-result eliminator for the public `d2sQueryImpl` wrapper.  It isolates the
single `OptionT`/simulation peel shared by every state invariant from the query-step-specific
argument. -/
private lemma d2sQueryImpl_support_of_step
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {Q : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) → Prop}
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hStep : ∀ (a : (duplexSpongeChallengeOracle StmtIn U).Range q)
        (st' : ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
        (some (some (a, st')) ∈ support (simulateQ (gImpl + auxImpl)
          (OptionT.run ((ProverTransform.d2sQueryStep
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run) → Q st')
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run)) :
    ∀ a st', r = some (a, st') → Q st' := by
  intro a₀ st₀ hrEq
  rw [ProverTransform.d2sQueryImpl] at hr
  simp only [Option.elimM, OptionT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨i, hi, hr⟩ := hr
  cases hiEq : i with
  | none =>
      have hr' : r ∈ support (pure none : ProbComp
          (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        rw [hiEq] at hr
        exact hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      cases hr'
  | some i' =>
      cases i' with
      | none =>
          have hr' : r ∈ support
              ((failure : OptionT ProbComp
                ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                  ProverTransform.D2SQueryState
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run) := by
            rw [hiEq] at hr
            exact hr
          rw [hrEq] at hr'
          simp at hr'
      | some pair =>
          rcases pair with ⟨a, st'⟩
          have hi' : some (some (a, st')) ∈ support
              (simulateQ (gImpl + auxImpl)
                (OptionT.run ((ProverTransform.d2sQueryStep
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run := by
            rw [hiEq] at hi
            exact hi
          have hQ : Q st' := hStep a st' hi'
          have hr' : r = some (a, st') := by
            have hrPure : r ∈ support (pure (some (a, st')) : ProbComp
              (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                ProverTransform.D2SQueryState
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
              rw [hiEq] at hr
              exact hr
            rw [mem_support_pure_iff] at hrPure
            exact hrPure
          have hpair : (a₀, st₀) = (a, st') := by
            rw [hrEq] at hr'
            exact Option.some.inj hr'
          injection hpair with ha hs
          subst ha
          subst hs
          exact hQ

/-- The public wrapper preserves output functionality on a hash query, which does not touch the
permutation table. -/
lemma d2sQueryImpl_hash_support_permOutput_wf
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (stmt : StmtIn)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {r : Option (Vector U SpongeSize.C ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsHashQuery stmt) st).run)) :
    ∀ a st', r = some (a, st') →
      TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
  apply d2sQueryImpl_support_of_step
    (Q := fun st' => TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ)
    gImpl auxImpl (dsHashQuery stmt) st ?_ hr
  intro a st' hi
  exact d2sHandleHashQuery_support_permOutput_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hwf hi rfl

/-- The public wrapper preserves output functionality on an inverse query. -/
lemma d2sQueryImpl_inverse_support_permOutput_wf
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (stateOut : CanonicalSpongeState U)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {r : Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl (dsPermInvQuery stateOut) st).run)) :
    ∀ a st', r = some (a, st') →
      TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
  apply d2sQueryImpl_support_of_step
    (Q := fun st' => TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ)
    gImpl auxImpl (dsPermInvQuery stateOut) st ?_ hr
  intro a st' hi
  exact d2sHandleInversePermQuery_support_permOutput_wf
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl st hwf hi rfl

/-- State invariant that is strong enough to retain the chronology of backward conflicts while
still allowing the simulator to record a forward bad event when it first loses output
functionality. -/
def D2SFuncInvariant
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) : Prop :=
  BwdHasPriorBad st.trace ∧
    (E st.trace ∨ TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)

/- One successful D2S query preserves the chronological backward-conflict invariant. -/
set_option maxHeartbeats 400000 in
-- This proof combines the exact raw one-entry trace contract with the handler Wf facts.
lemma d2sQueryImpl_support_funcInvariant
    [VCVCompatible StmtIn]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hI : D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st)
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run)) :
    ∀ a st', r = some (a, st') →
      D2SFuncInvariant (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st' := by
  intro a st' hrEq
  have htrace := d2sQueryImpl_support_trace_append
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) gImpl auxImpl q st hr a st' hrEq
  constructor
  · cases q with
    | inl stmt =>
        rcases hI.2 with hE | hwf
        · rw [htrace]
          exact BwdHasPriorBad.append_of_E st.trace hI.1 hE ⟨dsHashQuery stmt, a⟩
        · have hwf' := d2sQueryImpl_hash_support_permOutput_wf
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl stmt st hwf hr a st' hrEq
          exact BwdHasPriorBad.of_permOutput_wf_mirror st'.trace hwf' st'.h_mirror
    | inr q' =>
        cases q' with
        | inl stateIn =>
            rw [htrace]
            exact BwdHasPriorBad.append_forward st.trace hI.1 stateIn a
        | inr stateOut =>
            rcases hI.2 with hE | hwf
            · rw [htrace]
              exact BwdHasPriorBad.append_of_E st.trace hI.1 hE ⟨dsPermInvQuery stateOut, a⟩
            · have hwf' := d2sQueryImpl_inverse_support_permOutput_wf
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl stateOut st hwf hr a st' hrEq
              exact BwdHasPriorBad.of_permOutput_wf_mirror st'.trace hwf' st'.h_mirror
  · by_cases hE : E st.trace
    · left
      obtain ⟨extra, hbase⟩ :=
        getBaseTrace_append_singleton_exists_suffix (StmtIn := StmtIn) st.trace ⟨q, a⟩
      rw [htrace]
      exact E_of_getBaseTrace_append_eq hbase hE
    · rcases hI.2 with hOld | hwf
      · exact False.elim (hE hOld)
      · exact d2sQueryImpl_support_permOutput_wf_or_E
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) gImpl auxImpl q st hwf hE hr a st' hrEq

/-- The default simulator state satisfies the chronological functional-conflict invariant. -/
lemma default_d2s_funcInvariant :
    D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (default : ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := by
  let st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) := default
  have hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ := by
    change TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ : TraceNabla T_H T_P StmtIn U)
    exact TracePermOutputWellformed.empty
  exact ⟨BwdHasPriorBad.of_permOutput_wf_mirror st.trace hwf st.h_mirror, Or.inr hwf⟩

/- The generic combined simulator runner preserves the full chronological backward invariant. -/
set_option maxHeartbeats 400000 in
-- This is a direct instantiation of the generic combined state-invariant induction.
lemma sigma_combinedImpl_support_funcInvariant
    [VCVCompatible StmtIn]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {α : Type}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hst : D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st)
    {r : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hr : r ∈ support (((simulateQ (lemma5_8CombinedImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift
          ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) +
            QueryImpl.id' unifSpec) aux))))
      oa).run).run (st, []))) :
    D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) r.2.1 := by
  refine combinedImpl_support_state_invariant
    (StmtIn := StmtIn) (U := U)
    (spongeImpl := ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (gImpl := fun q => OptionT.lift
        ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
      (auxImpl := fun aux => OptionT.lift
        ((ProverTransform.d2sUnitSampleImpl (U := U) +
          QueryImpl.id' unifSpec) aux)))
    (I := D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    ?_ (st, []) hst hr
  intro q s r hs hrStep
  cases r with
  | none => trivial
  | some pair =>
      rcases pair with ⟨a, s'⟩
      exact d2sQueryImpl_support_funcInvariant
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ)
        (gImpl := fun q => OptionT.lift
          ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) +
            QueryImpl.id' unifSpec) aux))
        q s hs hrStep a s' rfl

/- The two runner specializations below deliberately mirror the trace-bridge API in
`SpongeTrace`.  Keeping the large `simulateQ` support types behind these names prevents each
consumer of the chronological invariant from re-elaborating the full prover/verifier runner. -/
set_option maxHeartbeats 400000 in
lemma sigma_prover_run_support_funcInvariant
    [VCVCompatible StmtIn]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    {proverResult : Option (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ) ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    (hpr : proverResult ∈ support (((simulateQ (lemma5_8CombinedImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift
          ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) +
            QueryImpl.id' unifSpec) aux))))
      maliciousProver).run).run (default, []))) :
    D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) proverResult.2.1 := by
  exact sigma_combinedImpl_support_funcInvariant
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g default default_d2s_funcInvariant hpr

set_option maxHeartbeats 400000 in
lemma sigma_verifier_run_support_funcInvariant
    [VCVCompatible StmtIn]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hst : D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) st)
    {α : Type}
    {verifierResult : Option α ×
      (ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) ×
        QueryLog ([]ₒ + duplexSpongeChallengeOracle StmtIn U))}
    {oa : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α}
    (hvr : verifierResult ∈ support (((simulateQ (lemma5_8CombinedImpl
      (ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift
          ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) +
            QueryImpl.id' unifSpec) aux))))
      oa).run).run (st, []))) :
    D2SFuncInvariant (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) verifierResult.2.1 := by
  exact sigma_combinedImpl_support_funcInvariant
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hst hvr

/- Every complete sigma experiment support trace satisfies the chronological backward property.
The proof is a genuine runner lift: it obtains the prover/verifier internal states from the
projected-trace support factorization and applies `sigma_combinedImpl_support_funcInvariant` to
each executed segment. -/
set_option maxHeartbeats 400000 in
-- Support factorization elaborates the full abortable prover/verifier execution type.
lemma sigma_support_bwdHasPriorBad
    {StmtOut : Type}
    [VCVCompatible StmtIn]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    [VCVCompatible U] [SampleableType U]
    [Fintype U] [Nonempty U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U) ×
      QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (htr : tr ∈ support (lemma5_8SigmaTraceDist (T_H := T_H) (T_P := T_P)
      (δ := δ) (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n)
      (pSpec := pSpec) (U := U) V maliciousProver)) :
    BwdHasPriorBad (tr.1 ++ tr.2) := by
  classical
  obtain ⟨k_g, hk_g, hproj⟩ :=
    sigma_mem_support_factor (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (StmtOut := StmtOut) (n := n) (pSpec := pSpec)
      (U := U) (δ := δ) V maliciousProver tr htr
  obtain ⟨s₀, hs₀, proverResult, hpr, hcases⟩ :=
    projectedTraceDistAbortable_mem_support_cases
      (StmtIn := StmtIn) (StmtOut := StmtOut) (pSpec := pSpec)
      (U := U) (δ := δ)
      (init := pure (default :
        ProverTransform.D2SQueryState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))
      (spongeImpl := ProverTransform.d2sQueryImpl
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (gImpl := fun q => OptionT.lift
          ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q))
        (auxImpl := fun aux => OptionT.lift
          ((ProverTransform.d2sUnitSampleImpl (U := U) +
            QueryImpl.id' unifSpec) aux)))
      V maliciousProver tr hproj
  rw [mem_support_pure_iff] at hs₀
  subst s₀
  obtain ⟨proverOut, stP, trPWide⟩ := proverResult
  have hPI := sigma_prover_run_support_funcInvariant
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g maliciousProver hpr
  have hPTrace :
      stP.trace = lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trPWide :=
    sigma_prover_run_support_d2sTrace_bridge
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) k_g maliciousProver hpr
  cases proverOut with
  | none =>
      have htrEq : tr =
          (lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trPWide, []) := hcases
      subst tr
      rw [← hPTrace, List.append_nil]
      exact hPI.1
  | some stmtProof =>
      obtain ⟨stmtIn, proof⟩ := stmtProof
      obtain ⟨verifierResult, hvr, htrEq⟩ := hcases
      obtain ⟨verifierOut, stV, trVWide⟩ := verifierResult
      have hVI := sigma_verifier_run_support_funcInvariant
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) k_g stP hPI hvr
      have hVTrace :
          stV.trace = stP.trace ++
            lemma5_8ProjectTraceLog (StmtIn := StmtIn) (U := U) trVWide :=
        sigma_verifier_run_support_d2sTrace_bridge
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
          (U := U) (δ := δ) k_g stP hvr
      subst tr
      rw [← hPTrace, ← hVTrace]
      exact hVI.1

end LocalTraceBridges

end BadEventDS

end DuplexSpongeFS
