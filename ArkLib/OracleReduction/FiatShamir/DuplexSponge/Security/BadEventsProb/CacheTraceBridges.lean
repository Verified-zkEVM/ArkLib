/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets

/-!
# Cache trace bridges for stateful D2SQuery

The revised rate-only cache stores a continuation at a state that was produced by a prior
permutation query, while `E_p` and `E_pinv` are defined over the normalized base trace.  This
small module is the sole bridge between those two views.  Its lemmas say exactly when a newly
appended permutation occurrence is already bad because a cache-related capacity has appeared
before.  It deliberately contains no handler or probability argument.

Keeping these bridges separate from `FunctionInvariant` prevents the stateful-cache proof from
growing the legacy functional-invariant module, and gives the whole-run cache proof a single
dependency with no simulator control flow.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : CodecCore pSpec U] {δ : ℕ}
  {T_H : Type} {T_P : Type}
  [DecidableEq StmtIn] [DecidableEq U]
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- A successful hash-table lookup has an identical hash occurrence in the normalized base
trace.  This deterministic table/trace bridge is shared by the live dispatcher and the legacy
representative development, so it lives below either proof architecture. -/
lemma hash_lookup_mem_baseTrace_of_mirror
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.h stmt = some cap) :
    (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
      getBaseTrace trace := by
  have hEntry : (stmt, cap) ∈ TraceTableOps.entries trΔ.h :=
    TraceTableOps.mem_entries_of_inlu_eq_some hLookup
  have hRaw : (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
    (hMirror.1 stmt cap).mpr hEntry
  exact DuplexSpongeFS.hash_pair_mem_getBaseTrace_of_mem trace hRaw

/-- Replaying a hash-table hit appends only a redundant raw occurrence, so the normalized base
trace remains unchanged. -/
lemma getBaseTrace_append_hash_lookup_eq
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.h stmt = some cap) :
    getBaseTrace (trace ++ [⟨.inl stmt, cap⟩]) = getBaseTrace trace := by
  have hBase := hash_lookup_mem_baseTrace_of_mirror
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) hMirror hLookup
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace
    ⟨.inl stmt, cap⟩ (by
      simp only [isRedundantEntryOfPrefix]
      exact hBase)

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A new forward base representative whose output capacity was already used as the input
capacity of a prior permutation representative is charged by `E_p` at its appended base index.

The prior pair may be represented by either the query of `p` or the answer of `p⁻¹`; these are
the two direction-tagged forms retained by the rate-only-cache provenance invariant. -/
lemma E_p_at_append_forward_of_prior_query_capacity
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sOut : CanonicalSpongeState U)
    (hPrior :
      (∃ priorOut : CanonicalSpongeState U,
        (⟨.inr (.inl sOut), priorOut⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace) ∨
      (∃ priorOut : CanonicalSpongeState U,
        (⟨.inr (.inr priorOut), sOut⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace))
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
  · obtain ⟨priorOut, hFwd⟩ := hFwd
    rw [List.mem_iff_get] at hFwd
    obtain ⟨j', hprior⟩ := hFwd
    simp only [List.get_eq_getElem] at hprior
    apply Or.inr
    apply Or.inr
    apply Or.inr
    left
    refine ⟨⟨j', by
      simp only [List.length_append, List.length_cons, List.length_nil]
      exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩,
      ?_, sOut, priorOut, ?_, rfl⟩
    · exact Nat.le_of_lt j'.isLt
    · change (getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩])[j'.val]'_ = _
      rw [List.getElem_append_left (bs := [⟨.inr (.inl sIn), sOut⟩]) j'.isLt]
      exact hprior
  · obtain ⟨priorOut, hBwd⟩ := hBwd
    rw [List.mem_iff_get] at hBwd
    obtain ⟨j', hprior⟩ := hBwd
    simp only [List.get_eq_getElem] at hprior
    apply Or.inr
    apply Or.inr
    left
    refine ⟨⟨j', by
      simp only [List.length_append, List.length_cons, List.length_nil]
      exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩,
      ?_, priorOut, sOut, ?_, rfl⟩
    · exact j'.isLt
    · change (getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩])[j'.val]'_ = _
      rw [List.getElem_append_left (bs := [⟨.inr (.inl sIn), sOut⟩]) j'.isLt]
      exact hprior

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A newly appended forward representative is charged by `E_p` when its output capacity equals
the capacity of its own query state.  This is the current-entry (`j' = j`) input case of
Definition 5.7. -/
lemma E_p_at_append_forward_of_current_query_capacity
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sIn sOut : CanonicalSpongeState U)
    (hCap : sIn.capacitySegment = sOut.capacitySegment)
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
  · unfold isDuplicatedPriorCapacity
    apply Or.inr
    apply Or.inr
    apply Or.inr
    left
    refine ⟨⟨(getBaseTrace trace).length, by
      simp only [List.length_append, List.length_cons, List.length_nil]
      exact Nat.lt_succ_self _⟩, ?_, sIn, sOut, ?_, hCap⟩
    · exact Nat.le_refl _
    · have hEntry :
          (getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩])[getBaseTrace trace |>.length]? =
            some ⟨.inr (.inl sIn), sOut⟩ :=
        getElem?_append_singleton_length (getBaseTrace trace) ⟨.inr (.inl sIn), sOut⟩
      rw [List.getElem?_eq_getElem (by
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact Nat.lt_succ_self _)] at hEntry
      exact Option.some.inj hEntry

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A new inverse base representative whose returned input was already the output of a prior
normalized permutation pair is charged by `E_{p^{-1}}` at its appended base index.  The prior pair
may have been recorded forward or inverse. -/
lemma E_pinv_at_append_inverse_of_prior_output_capacity
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (sOut sIn : CanonicalSpongeState U)
    (hPrior :
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inl priorIn), sIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace) ∨
      (∃ priorIn : CanonicalSpongeState U,
        (⟨.inr (.inr sIn), priorIn⟩ :
          Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ getBaseTrace trace))
    (hbase : getBaseTrace (trace ++ [⟨.inr (.inr sOut), sIn⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inr sOut), sIn⟩]) :
    E_pinv_at (trace ++ [⟨.inr (.inr sOut), sIn⟩]) (getBaseTrace trace).length := by
  unfold E_pinv_at
  rw [hbase]
  dsimp only
  refine ⟨by
    simp only [List.length_append, List.length_cons, List.length_nil]
    exact Nat.le_refl _, sIn.capacitySegment, ?_, ?_⟩
  · exact ⟨sOut, sIn, by simp, rfl⟩
  · unfold isDuplicatedPriorCapacity
    rcases hPrior with hForward | hInverse
    · obtain ⟨priorIn, hForward⟩ := hForward
      rw [List.mem_iff_get] at hForward
      obtain ⟨j', hprior⟩ := hForward
      simp only [List.get_eq_getElem] at hprior
      apply Or.inr
      left
      refine ⟨⟨j', by
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩,
        ?_, priorIn, sIn, ?_, rfl⟩
      · exact j'.isLt
      · change (getBaseTrace trace ++ [⟨.inr (.inr sOut), sIn⟩])[j'.val]'_ = _
        rw [List.getElem_append_left (bs := [⟨.inr (.inr sOut), sIn⟩]) j'.isLt]
        exact hprior
    · obtain ⟨priorIn, hInverse⟩ := hInverse
      rw [List.mem_iff_get] at hInverse
      obtain ⟨j', hprior⟩ := hInverse
      simp only [List.get_eq_getElem] at hprior
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      refine ⟨⟨j', by
        simp only [List.length_append, List.length_cons, List.length_nil]
        exact Nat.lt_trans j'.isLt (Nat.lt_succ_self _)⟩,
        ?_, sIn, priorIn, ?_, rfl⟩
      · exact Nat.le_of_lt j'.isLt
      · change (getBaseTrace trace ++ [⟨.inr (.inr sOut), sIn⟩])[j'.val]'_ = _
        rw [List.getElem_append_left (bs := [⟨.inr (.inr sOut), sIn⟩]) j'.isLt]
        exact hprior

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A new forward base representative whose full output state was already represented is charged
by `E_p` at its appended base index.  This is the state-level companion of the capacity bridges
above: it is used solely to prove that a continuing residual tail receives a fresh cache key.
The previous representative may have been recorded in either permutation direction. -/
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

/-! ## Deterministic table-miss witnesses

These are the tiny table-side facts consumed by the revised first-bad gateway.  They live here,
below all handler code, rather than in the legacy `Representatives` module. -/

namespace D2SBaseTraceWitness

/-- The forward-lookup fragment of a normalized permutation table. -/
structure PermInputWellformed (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  nodup : (LawfulTraceTable.toMultiSet trΔ.p).Nodup
  inputFunctional : TraceTableOps.InputFunctional trΔ.p

/-- The inverse-lookup dual of `PermInputWellformed`. -/
structure PermOutputWellformed (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  nodup : (LawfulTraceTable.toMultiSet trΔ.p).Nodup
  outputFunctional : TraceTableOps.OutputFunctional trΔ.p

/-- A forward lookup miss excludes both raw orientations of a normalized permutation pair from
the base trace. -/
lemma permBaseNotMemOfInluNone
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : PermInputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = none) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉
        getBaseTrace trace ∧
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉
        getBaseTrace trace := by
  constructor
  · intro hBase
    have hRaw : (⟨.inr (.inl sIn), sOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inl hRaw)
    have hMem : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      hwf.nodup hwf.inputFunctional hLookup sOut hMem
  · intro hBase
    have hRaw : (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inr hRaw)
    have hMem : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      hwf.nodup hwf.inputFunctional hLookup sOut hMem

/-- Appending the answer of a genuine forward-table miss adds exactly one base representative. -/
lemma getBaseTraceAppendPermInluMiss
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : PermInputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = none) :
    getBaseTrace (trace ++ [⟨.inr (.inl sIn), sOut⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩] := by
  apply getBaseTrace_append_singleton_of_not_redundant_base
  simp only [isRedundantEntryOfPrefix]
  have hAbsent := permBaseNotMemOfInluNone (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (U := U) (sOut := sOut) hwf hMirror hLookup
  intro hRedundant
  rcases hRedundant with hForward | hInverse
  · exact hAbsent.1 hForward
  · exact hAbsent.2 hInverse

/-- An inverse lookup miss excludes both raw orientations of a normalized permutation pair from
the base trace. -/
lemma permBaseNotMemOfOutluNone
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : PermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = none) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉
        getBaseTrace trace ∧
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉
        getBaseTrace trace := by
  constructor
  · intro hBase
    have hRaw : (⟨.inr (.inl sIn), sOut⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inl hRaw)
    have hMem : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.nodup hwf.outputFunctional hLookup sIn hMem
  · intro hBase
    have hRaw : (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inr hRaw)
    have hMem : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.nodup hwf.outputFunctional hLookup sIn hMem

/-- Appending the answer of a genuine inverse-table miss adds exactly one base representative. -/
lemma getBaseTraceAppendPermOutluMiss
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : PermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = none) :
    getBaseTrace (trace ++ [⟨.inr (.inr sOut), sIn⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inr sOut), sIn⟩] := by
  apply getBaseTrace_append_singleton_of_not_redundant_base
  simp only [isRedundantEntryOfPrefix]
  have hAbsent := permBaseNotMemOfOutluNone (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (U := U) (sIn := sIn) hwf hMirror hLookup
  intro hRedundant
  rcases hRedundant with hInverse | hForward
  · exact hAbsent.2 hInverse
  · exact hAbsent.1 hForward

/-- A successful forward lookup has an existing normalized permutation representative in the
base trace, whether the original raw occurrence was forward or inverse. -/
lemma permInluPairMemBaseTrace
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = some sOut) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        getBaseTrace trace ∨
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        getBaseTrace trace := by
  have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
    TraceTableOps.mem_entries_of_inlu_eq_some hLookup
  have hRaw :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
    (hMirror.2 sIn sOut).mpr hEntry
  exact normalizedPermPair_mem_getBaseTrace_of_mem trace sIn sOut hRaw

/-- A successful inverse lookup has an existing normalized permutation representative in the
base trace, in either raw orientation. -/
lemma permOutluPairMemBaseTrace
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = some sIn) :
    (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        getBaseTrace trace ∨
      (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈
        getBaseTrace trace := by
  have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
    TraceTableOps.mem_entries_of_outlu_eq_some hLookup
  have hRaw :
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace ∨
        (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
    (hMirror.2 sIn sOut).mpr hEntry
  exact normalizedPermPair_mem_getBaseTrace_of_mem trace sIn sOut hRaw

/-- Replaying an established forward lookup appends only a redundant raw occurrence. -/
lemma getBaseTraceAppendPermInluLookup
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = some sOut) :
    getBaseTrace (trace ++ [⟨.inr (.inl sIn), sOut⟩]) = getBaseTrace trace := by
  have hBase := permInluPairMemBaseTrace
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) hMirror hLookup
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace
    ⟨.inr (.inl sIn), sOut⟩ (by
      simp only [isRedundantEntryOfPrefix]
      exact hBase)

/-- Replaying an established inverse lookup appends only a redundant raw occurrence. -/
lemma getBaseTraceAppendPermOutluLookup
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = some sIn) :
    getBaseTrace (trace ++ [⟨.inr (.inr sOut), sIn⟩]) = getBaseTrace trace := by
  have hBase := permOutluPairMemBaseTrace
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) hMirror hLookup
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace
    ⟨.inr (.inr sOut), sIn⟩ (by
      simp only [isRedundantEntryOfPrefix]
      exact hBase.symm)

end D2SBaseTraceWitness

end DuplexSpongeFS.BadEventDS
