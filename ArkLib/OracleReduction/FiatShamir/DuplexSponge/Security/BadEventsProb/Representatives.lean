/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CapacityTargets
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.CacheTraceBridges
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsProb.SampleProduct

/-!
# Base-trace representatives for D2S table hits

These lemmas isolate the deterministic part of the paper statement that consistency responses are
not new base-trace representatives.  If `D2SQuery` answers from `tr_∇` (rather than from a fresh
sample or from `Cache_p`), the answered pair already occurs in the raw trace by the mirror
invariant, hence it already has a representative in `getBaseTrace`.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS

namespace BadEventDS

open DuplexSpongeFS.DSTraceStorage

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : ℕ}

variable {T_H : Type} {T_P : Type}
  [DecidableEq StmtIn] [DecidableEq U]
  [LawfulTraceNablaImpl T_H T_P StmtIn U]

section TableHitRepresentatives

variable
  (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) (OptionT ProbComp))
  (auxImpl : QueryImpl ((Unit →ₒ U) + unifSpec) (OptionT ProbComp))

/-- Table well-formedness invariant for the D2S simulator's `tr_∇` index.  Lookup failure in the
lawful table API only means true absence under these nodup/functionality hypotheses; without them,
duplicates or conflicting entries can also force `inlu/outlu = none`. -/
structure TraceNablaTablesWellformed
    (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  h_nodup : (LawfulTraceTable.toMultiSet trΔ.h).Nodup
  h_inputFunctional : TraceTableOps.InputFunctional trΔ.h
  p_nodup : (LawfulTraceTable.toMultiSet trΔ.p).Nodup
  p_inputFunctional : TraceTableOps.InputFunctional trΔ.p
  p_outputFunctional : TraceTableOps.OutputFunctional trΔ.p

/-- Hash-table fragment of `TraceNablaTablesWellformed`.

Sigma hash freshness only needs the `tr_∇.h` table to be nodup and input-functional; separating
this avoids threading irrelevant permutation-table invariants through the hash miss branch. -/
structure TraceHashTableWellformed
    (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  h_nodup : (LawfulTraceTable.toMultiSet trΔ.h).Nodup
  h_inputFunctional : TraceTableOps.InputFunctional trΔ.h

/-- Forward-lookup fragment of permutation-table well-formedness.

This is the invariant needed for a `p.inlu = none` forward miss: no pair with that input is
already represented.  We deliberately do not require output-functionality here, since adding a
fresh forward sample with an already-used output is exactly an `E_func`-style situation. -/
structure TracePermInputWellformed
    (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  p_nodup : (LawfulTraceTable.toMultiSet trΔ.p).Nodup
  p_inputFunctional : TraceTableOps.InputFunctional trΔ.p

/-- Backward-lookup fragment of permutation-table well-formedness.

This is the invariant needed for a `p.outlu = none` inverse miss.  It is dual to
`TracePermInputWellformed` and intentionally avoids assuming input-functionality. -/
structure TracePermOutputWellformed
    (trΔ : TraceNabla T_H T_P StmtIn U) : Prop where
  p_nodup : (LawfulTraceTable.toMultiSet trΔ.p).Nodup
  p_outputFunctional : TraceTableOps.OutputFunctional trΔ.p

/-- The empty trace table is nodup. -/
lemma traceTable_empty_nodup
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V] :
    (LawfulTraceTable.toMultiSet (TraceTableOps.empty : T)).Nodup := by
  rw [LawfulTraceTable.toMultiSet_empty]
  simp only [Multiset.nodup_zero]

/-- The empty trace table is input-functional. -/
lemma traceTable_empty_inputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V] :
    TraceTableOps.InputFunctional (TraceTableOps.empty : T) := by
  intro k v v' hmem _hmem'
  rw [LawfulTraceTable.toMultiSet_empty] at hmem
  cases hmem

/-- The empty trace table is output-functional. -/
lemma traceTable_empty_outputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V] :
    TraceTableOps.OutputFunctional (TraceTableOps.empty : T) := by
  intro k k' v hmem _hmem'
  rw [LawfulTraceTable.toMultiSet_empty] at hmem
  cases hmem

/-- The empty `tr_∇` index carried by the default D2S state is wellformed. -/
lemma TraceNablaTablesWellformed.empty :
    TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ :
        TraceNabla T_H T_P StmtIn U) := by
  exact
    ⟨traceTable_empty_nodup, traceTable_empty_inputFunctional,
      traceTable_empty_nodup, traceTable_empty_inputFunctional,
      traceTable_empty_outputFunctional⟩

lemma TraceHashTableWellformed.empty :
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ :
        TraceNabla T_H T_P StmtIn U) := by
  exact ⟨traceTable_empty_nodup, traceTable_empty_inputFunctional⟩

lemma TracePermInputWellformed.empty :
    TracePermInputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ :
        TraceNabla T_H T_P StmtIn U) := by
  exact ⟨traceTable_empty_nodup, traceTable_empty_inputFunctional⟩

lemma TracePermOutputWellformed.empty :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ :
        TraceNabla T_H T_P StmtIn U) := by
  exact ⟨traceTable_empty_nodup, traceTable_empty_outputFunctional⟩

lemma TraceNablaTablesWellformed.hash
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ) :
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ :=
  ⟨hwf.h_nodup, hwf.h_inputFunctional⟩

lemma TraceNablaTablesWellformed.permInput
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ) :
    TracePermInputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ :=
  ⟨hwf.p_nodup, hwf.p_inputFunctional⟩

lemma TraceNablaTablesWellformed.permOutput
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ) :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ :=
  ⟨hwf.p_nodup, hwf.p_outputFunctional⟩

/-- Hash-table well-formedness is preserved by adding a pair on a genuine hash miss. -/
lemma TraceHashTableWellformed.add_hash
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hLookup : TraceTableOps.inlu trΔ.h stmt = none) :
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      ({ trΔ with h := TraceTableOps.add trΔ.h stmt cap } :
        TraceNabla T_H T_P StmtIn U) := by
  have hFreshInput :
      ∀ cap' : Vector U SpongeSize.C,
        (stmt, cap') ∉ LawfulTraceTable.toMultiSet trΔ.h :=
    TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      hwf.h_nodup hwf.h_inputFunctional hLookup
  constructor
  · exact TraceTableOps.nodup_add hwf.h_nodup (hFreshInput cap)
  · exact TraceTableOps.inputFunctional_add hwf.h_inputFunctional hFreshInput

/-- Full-table well-formedness is preserved by adding a pair on a genuine hash miss. -/
lemma TraceNablaTablesWellformed.add_hash
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hLookup : TraceTableOps.inlu trΔ.h stmt = none) :
    TraceNablaTablesWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      ({ trΔ with h := TraceTableOps.add trΔ.h stmt cap } :
        TraceNabla T_H T_P StmtIn U) := by
  have hHash := hwf.hash.add_hash
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
    (cap := cap) hLookup
  exact ⟨hHash.h_nodup, hHash.h_inputFunctional, hwf.p_nodup,
    hwf.p_inputFunctional, hwf.p_outputFunctional⟩

/-- Inverse permutation output-well-formedness is preserved by `p.add` on a genuine `outlu` miss. -/
lemma TracePermOutputWellformed.add_perm_outlu
    {trΔ : TraceNabla T_H T_P StmtIn U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    {sIn sOut : CanonicalSpongeState U}
    (hLookup : TraceTableOps.outlu trΔ.p sOut = none) :
    TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U)
      ({ trΔ with p := TraceTableOps.add trΔ.p sIn sOut } :
        TraceNabla T_H T_P StmtIn U) := by
  have hFreshOutput :
      ∀ sIn' : CanonicalSpongeState U,
        (sIn', sOut) ∉ LawfulTraceTable.toMultiSet trΔ.p :=
    TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.p_nodup hwf.p_outputFunctional hLookup
  constructor
  · exact TraceTableOps.nodup_add hwf.p_nodup (hFreshOutput sIn)
  · exact TraceTableOps.outputFunctional_add hwf.p_outputFunctional hFreshOutput

/-- Under table well-formedness, a failed hash lookup means that no base-trace representative for
that hash statement/capacity pair already exists. -/
lemma hash_base_not_mem_of_inlu_none_of_hash_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.h stmt = none) :
    (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∉
      getBaseTrace trace := by
  intro hBase
  have hRaw : (⟨.inl stmt, cap⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
    (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
  have hEntry : (stmt, cap) ∈ TraceTableOps.entries trΔ.h :=
    (hMirror.1 stmt cap).mp hRaw
  have hMs : (stmt, cap) ∈ LawfulTraceTable.toMultiSet trΔ.h := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact Multiset.mem_coe.mpr hEntry
  exact TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
    hwf.h_nodup hwf.h_inputFunctional hLookup cap hMs

/-- Under table well-formedness, appending the answer of a genuine hash miss appends a new
base-trace representative. -/
lemma getBaseTrace_append_hash_miss_eq_of_hash_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.h stmt = none) :
    getBaseTrace (trace ++ [⟨.inl stmt, cap⟩]) =
      getBaseTrace trace ++ [⟨.inl stmt, cap⟩] := by
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace
    ⟨.inl stmt, cap⟩ (by
      simp only [isRedundantEntryOfPrefix]
      exact hash_base_not_mem_of_inlu_none_of_hash_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        hwf hMirror hLookup)

/-- Under table well-formedness, a failed forward permutation lookup means that no normalized
base-trace representative with that input state already exists, in either orientation. -/
lemma perm_base_not_mem_of_inlu_none_of_input_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : TracePermInputWellformed (T_H := T_H) (T_P := T_P)
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
    have hMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      hwf.p_nodup hwf.p_inputFunctional hLookup sOut hMs
  · intro hBase
    have hRaw : (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inr hRaw)
    have hMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
      hwf.p_nodup hwf.p_inputFunctional hLookup sOut hMs

/-- Under table well-formedness, appending the answer of a genuine forward-permutation miss
appends a new base-trace representative. -/
lemma getBaseTrace_append_perm_inlu_miss_eq_of_input_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : TracePermInputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = none) :
    getBaseTrace (trace ++ [⟨.inr (.inl sIn), sOut⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inl sIn), sOut⟩] := by
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace
    ⟨.inr (.inl sIn), sOut⟩ (by
      simp only [isRedundantEntryOfPrefix]
      have hnot := perm_base_not_mem_of_inlu_none_of_input_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        (sOut := sOut) hwf hMirror hLookup
      intro hred
      rcases hred with hFwd | hInv
      · exact hnot.1 hFwd
      · exact hnot.2 hInv)

/-- Under table well-formedness, a failed inverse permutation lookup means that no normalized
base-trace representative with that output state already exists, in either orientation. -/
lemma perm_base_not_mem_of_outlu_none_of_output_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
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
    have hMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.p_nodup hwf.p_outputFunctional hLookup sIn hMs
  · intro hBase
    have hRaw : (⟨.inr (.inr sOut), sIn⟩ :
        Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace :=
      (getBaseTrace_sublist (StmtIn := StmtIn) (U := U) trace).subset hBase
    have hEntry : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p :=
      (hMirror.2 sIn sOut).mp (Or.inr hRaw)
    have hMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet trΔ.p := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hEntry
    exact TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
      hwf.p_nodup hwf.p_outputFunctional hLookup sIn hMs

/-- Under table well-formedness, appending the answer of a genuine inverse-permutation miss
appends a new base-trace representative. -/
lemma getBaseTrace_append_perm_outlu_miss_eq_of_output_wf
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hwf : TracePermOutputWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) trΔ)
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = none) :
    getBaseTrace (trace ++ [⟨.inr (.inr sOut), sIn⟩]) =
      getBaseTrace trace ++ [⟨.inr (.inr sOut), sIn⟩] := by
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_not_redundant_base trace
    ⟨.inr (.inr sOut), sIn⟩ (by
      simp only [isRedundantEntryOfPrefix]
      have hnot := perm_base_not_mem_of_outlu_none_of_output_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
        (sIn := sIn) hwf hMirror hLookup
      intro hred
      rcases hred with hInv | hFwd
      · exact hnot.2 hInv
      · exact hnot.1 hFwd)


/-- A successful inverse table lookup gives a base representative of the same normalized
permutation pair, in either direction. -/
lemma perm_outlu_pair_mem_baseTrace_of_mirror
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

/-- Appending an inverse permutation answer returned by `tr_∇.p.outlu` leaves the base trace
unchanged. -/
lemma getBaseTrace_append_perm_outlu_eq
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.outlu trΔ.p sOut = some sIn) :
    getBaseTrace (trace ++ [⟨.inr (.inr sOut), sIn⟩]) = getBaseTrace trace := by
  have hBase := perm_outlu_pair_mem_baseTrace_of_mirror
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U) hMirror hLookup
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace
    ⟨.inr (.inr sOut), sIn⟩ (by
    simp only [isRedundantEntryOfPrefix]
    exact hBase.symm)

/-- A successful forward table lookup gives a base representative of the same normalized
permutation pair, in either orientation. -/
lemma perm_inlu_pair_mem_baseTrace_of_mirror
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

/-- Appending a forward answer returned by `tr_∇.p.inlu` leaves the base trace unchanged. -/
lemma getBaseTrace_append_perm_inlu_eq
    {trΔ : TraceNabla T_H T_P StmtIn U}
    {trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {sIn sOut : CanonicalSpongeState U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (hLookup : TraceTableOps.inlu trΔ.p sIn = some sOut) :
    getBaseTrace (trace ++ [⟨.inr (.inl sIn), sOut⟩]) = getBaseTrace trace := by
  have hBase := perm_inlu_pair_mem_baseTrace_of_mirror
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
    hMirror hLookup
  exact DuplexSpongeFS.getBaseTrace_append_singleton_of_redundant_base trace
    ⟨.inr (.inl sIn), sOut⟩ (by
      simp only [isRedundantEntryOfPrefix]
      exact hBase)

/-- The hash branch preserves the hash-table wellformedness fragment on every successful support
point.  This is the local preservation lemma used by global sigma-runner invariants. -/
lemma d2sHandleHashQuery_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
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
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleHashQuery at hi
  cases hLookup : TraceTableOps.inlu st.trΔ.h stmt with
  | none =>
      simp [hLookup] at hi
      have hst' : st' =
          ProverTransform.d2sHashMissState
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt a st := by
        aesop
      rw [hst']
      simpa [ProverTransform.d2sHashMissState] using
        (TraceHashTableWellformed.add_hash
          (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
          (trΔ := st.trΔ) (stmt := stmt) (cap := a) hwf hLookup)
  | some capSeg =>
      simp [hLookup] at hi
      aesop

/-- The inverse-permutation branch preserves the hash-table wellformedness fragment: it only
updates the permutation table and the raw trace. -/
lemma d2sHandleInversePermQuery_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
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
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleInversePermQuery at hi
  cases hLookup : TraceTableOps.outlu st.trΔ.p stateOut with
  | none =>
      simp [hLookup] at hi
      have hh : st'.trΔ.h = st.trΔ.h := by
        aesop
      cases hwf with
      | mk hn hf =>
          constructor
          · simpa [hh]
          · simpa [hh]
  | some recovered =>
      simp [hLookup] at hi
      aesop

/-- The forward `.noResult` branch preserves the hash-table wellformedness fragment. -/
lemma d2sHandleBacktrackNoResult_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleBacktrackNoResult at hi
  have rebuild (hh : st'.trΔ.h = st.trΔ.h) :
      TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
    cases hwf with
    | mk hn hf =>
        constructor
        · simpa [hh]
        · simpa [hh]
  cases hCache : ProverTransform.popRateOnlyTailByInput (U := U) st.rateCacheP stateIn with
  | some cached =>
      simp [hCache] at hi
      exact rebuild (by aesop)
  | none =>
      by_cases hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none
      · simp [hCache, hLookup] at hi
        exact rebuild (by aesop)
      · simp [hCache, hLookup] at hi
        exact rebuild (by aesop)

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

/-- The forward `.some backtrackOut` branch preserves the hash-table wellformedness fragment. -/
lemma d2sHandleBacktrackSome_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
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
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  subst i
  unfold ProverTransform.d2sHandleBacktrackSome at hi
  have rebuild (hh : st'.trΔ.h = st.trΔ.h) :
      TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
    cases hwf with
    | mk hn hf =>
        constructor
        · simpa [hh]
        · simpa [hh]
  exact rebuild (ProverTransform.d2sHandleBacktrackSome_support_hashTable_eq
    (T_H := T_H) (T_P := T_P) (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    gImpl auxImpl stateIn backtrackOut st hi a st' rfl)

/-- One `d2sQueryStep` preserves the hash-table wellformedness fragment on every successful
support point.  Permutation branches leave the hash table unchanged; the hash branch is handled by
`d2sHandleHashQuery_support_hash_wf`. -/
lemma d2sQueryStep_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
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
    TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st'.trΔ := by
  cases q with
  | inl stmt =>
      exact d2sHandleHashQuery_support_hash_wf
        (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
        (U := U) (δ := δ) gImpl auxImpl st hwf hi hiEq
  | inr q' =>
      subst i
      cases q' with
      | inl stateIn =>
          unfold ProverTransform.d2sQueryStep ProverTransform.d2sHandleForwardPermQuery at hi
          cases hbt : Backtrack.backTrack
              (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              st.trace st.trΔ st.h_inv stateIn (st.trace.length + 1) with
          | err =>
              simp [hbt] at hi
              exfalso
              have hEq := Set.mem_singleton_iff.mp hi
              cases hEq
          | noResult =>
              exact d2sHandleBacktrackNoResult_support_hash_wf
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl st hwf (by
                  simpa [hbt] using hi) rfl
          | some backtrackOut =>
              exact d2sHandleBacktrackSome_support_hash_wf
                (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
                (U := U) (δ := δ) gImpl auxImpl backtrackOut st hwf (by
                  simpa [hbt] using hi) rfl
      | inr stateOut =>
          exact d2sHandleInversePermQuery_support_hash_wf
            (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (δ := δ) gImpl auxImpl st hwf hi rfl

/-- The public `d2sQueryImpl` wrapper preserves the hash-table wellformedness fragment on every
successful support point. -/
lemma d2sQueryImpl_support_hash_wf
    [Fintype U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hwf : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (U := U) st.trΔ)
    {r : Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))}
    (hr : r ∈ support ((ProverTransform.d2sQueryImpl
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (m := OptionT ProbComp) gImpl auxImpl q st).run)) :
    ∀ a st', r = some (a, st') →
      TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (U := U) st'.trΔ := by
  intro a₀ st₀ hrEq
  rw [ProverTransform.d2sQueryImpl] at hr
  simp only [Option.elimM, OptionT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨i, hi, hr⟩ := hr
  cases hi_eq : i with
  | none =>
      have hr' : r ∈ support (pure none : ProbComp
          (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
        simpa [hi_eq] using hr
      rw [mem_support_pure_iff] at hr'
      rw [hrEq] at hr'
      simp at hr'
  | some i' =>
      cases i' with
      | none =>
          have hr' : r ∈ support
              ((failure : OptionT ProbComp
                ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                  ProverTransform.D2SQueryState
                    (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run) := by
            simpa [hi_eq] using hr
          rw [hrEq] at hr'
          simp at hr'
      | some pair =>
          rcases pair with ⟨a, st'⟩
          have hi' : some (some (a, st')) ∈ support
              (simulateQ (gImpl + auxImpl)
                (OptionT.run ((ProverTransform.d2sQueryStep
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U) q).run st))).run := by
            simpa [hi_eq] using hi
          have hwf' : TraceHashTableWellformed (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (U := U) st'.trΔ :=
            d2sQueryStep_support_hash_wf
              (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) gImpl auxImpl q st hwf hi' rfl
          have hr' : r = some (a, st') := by
            have hrPure : r ∈ support (pure (some (a, st')) : ProbComp
              (Option ((duplexSpongeChallengeOracle StmtIn U).Range q ×
                ProverTransform.D2SQueryState
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))) := by
              simpa [hi_eq] using hr
            rw [mem_support_pure_iff] at hrPure
            exact hrPure
          have hpair : (a₀, st₀) = (a, st') := by
            rw [hrEq] at hr'
            exact Option.some.inj hr'
          injection hpair with ha hs
          subst ha
          subst hs
          exact hwf'

/-- If the hash handler takes the `tr_∇.h` table-hit branch, every successful simulated result has
the same base trace as the input state.  Operationally the raw trace appends the same hash pair
again, but the mirror invariant proves that pair is already represented in the base trace. -/
lemma d2sHandleHashQuery_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = some cap)
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
    a = cap ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  have hHit :
      a = cap ∧ st'.trace = st.trace ++ [⟨dsHashQuery stmt, cap⟩] := by
    unfold ProverTransform.d2sHandleHashQuery at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_hash_lookup_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- Observable return-value projection for a hash miss: after projecting away the proof-carrying
state component, the handler's returned capacity is exactly the lifted uniform capacity sampler. -/
lemma d2sHandleHashQuery_miss_return_projection
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none) :
    (Option.map Prod.fst <$>
      OptionT.run ((ProverTransform.d2sHandleHashQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st)) =
      (some <$> ProverTransform.d2sSampleCapacity
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
  unfold ProverTransform.d2sHandleHashQuery
  aesop

/-- Sigma-specialized probability bridge for a hash miss.  Once the deterministic lookup says the
handler is in the fresh branch, projecting away the proof-carrying simulator state leaves exactly
one uniform capacity sample. -/
lemma d2sHandleHashQuery_miss_sigma_return_probEvent_eq
    [Fintype U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (P : Option (Option (Vector U SpongeSize.C)) → Prop) :
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleHashQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run]
      =
    Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (Vector U SpongeSize.C)) ] := by
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler :=
    OptionT.run ((ProverTransform.d2sHandleHashQuery
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st)
  have hproj :
      (Option.map Prod.fst <$> handler) =
        (some <$> ProverTransform.d2sSampleCapacity
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
    dsimp [handler]
    exact d2sHandleHashQuery_miss_return_projection
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) st hLookup
  have hdist :
      (Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run) =
        (Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleCapacity
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run) := by
    calc
      Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run
          = (simulateQ impl (Option.map Prod.fst <$> handler)).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
      _ = (simulateQ impl
            (some <$> ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [hproj]
      _ = Option.map some <$>
            (simulateQ impl (ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
  calc
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) | (simulateQ impl handler).run]
        = Pr[ P |
            Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ P |
            Option.map some <$>
              (simulateQ impl (ProverTransform.d2sSampleCapacity
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [hdist]
    _ = Pr[ fun sampled? => P (Option.map some sampled?) |
            (simulateQ impl (ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (Vector U SpongeSize.C)) ] := by
          dsimp [impl]
          exact ProverTransform.d2sSampleCapacity_simulateQ_sigma_probEvent_eq
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g
            (fun sampled? => P (Option.map some sampled?))

/-- Local atom bound for a sigma hash miss.  Conditional on a fixed simulator state whose hash
table misses `stmt`, the handler's fresh capacity hits any fixed old base-trace target with
probability at most `1 / |Σ|^c`; if that old target is not `c`, the atom has probability zero. -/
lemma d2sHandleHashQuery_miss_sigma_atom_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stmt : StmtIn}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.h stmt = none)
    (idx : Fin (2 * (getBaseTrace st.trace).length))
    (c : Vector U SpongeSize.C) :
    Pr[ fun r =>
        Option.map (Option.map Prod.fst) r = some (some c) ∧
          priorCapacityTargetAt (getBaseTrace st.trace) (getBaseTrace st.trace).length idx =
            some c |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleHashQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run]
      ≤ (if priorCapacityTargetAt (getBaseTrace st.trace) (getBaseTrace st.trace).length idx =
            some c then 1 else 0) / capacitySpaceSize (U := U) := by
  classical
  let target :=
    priorCapacityTargetAt (getBaseTrace st.trace) (getBaseTrace st.trace).length idx
  have hdist := d2sHandleHashQuery_miss_sigma_return_probEvent_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hLookup
    (fun o : Option (Option (Vector U SpongeSize.C)) => o = some (some c) ∧ target = some c)
  change
    Pr[ fun r =>
        (Option.map (Option.map Prod.fst) r = some (some c) ∧ target = some c) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleHashQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stmt).run st))).run]
      ≤ (if target = some c then 1 else 0) / capacitySpaceSize (U := U)
  rw [hdist]
  by_cases htarget : target = some c
  · rw [if_pos htarget]
    rw [show (fun sampled : Vector U SpongeSize.C =>
        some (some sampled) = some (some c) ∧ target = some c) =
          (fun sampled : Vector U SpongeSize.C => sampled = c) by
        funext sampled
        apply propext
        constructor
        · intro h
          injection h.1 with hsample
          exact Option.some.inj hsample
        · intro h
          exact ⟨by rw [h], htarget⟩]
    rw [probEvent_eq_eq_probOutput]
    rw [probOutput_uniformSample]
    have hcapacityCard :
        (@Fintype.card (Vector U SpongeSize.C) Vector.instFintype : ℝ≥0∞) =
          capacitySpaceSize (U := U) := by
      have hcardVec :
          @Fintype.card (Vector U SpongeSize.C) Vector.instFintype =
            Fintype.card (Fin SpongeSize.C → U) := by
        exact Fintype.card_congr (Equiv.rootVectorEquivFin (α := U) (n := SpongeSize.C))
      rw [hcardVec, Fintype.card_fun, Fintype.card_fin, capacitySpaceSize, Nat.cast_pow]
    rw [hcapacityCard]
    rw [div_eq_mul_inv]
    simp
  · rw [if_neg htarget]
    rw [show (fun sampled : Vector U SpongeSize.C =>
        some (some sampled) = some (some c) ∧ target = some c) =
          (fun _sampled : Vector U SpongeSize.C => False) by
        funext sampled
        apply propext
        constructor
        · intro h
          exact htarget h.2
        · intro h
          cases h]
    simp

/-- Observable return-value projection for the forward-permutation `.noResult`/fresh branch:
if neither the rate-only `Cache_p` nor `tr_∇.p.inlu` provides an answer, projecting away the
proof-carrying state component leaves exactly the lifted uniform full-state sampler. -/
lemma d2sHandleBacktrackNoResult_miss_return_projection
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCache : ProverTransform.popRateOnlyTailByInput (U := U) st.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none) :
    (Option.map Prod.fst <$>
      OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
        (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st)) =
      (some <$> ProverTransform.d2sSampleState
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
  unfold ProverTransform.d2sHandleBacktrackNoResult
  simp [hCache, hLookup]

/-- Sigma-specialized probability bridge for the forward-permutation `.noResult`/fresh branch.
Once both the rate-only `Cache_p` and `tr_∇.p.inlu` miss, projecting away the proof-carrying
simulator state leaves exactly one uniform sponge-state sample. -/
lemma d2sHandleBacktrackNoResult_miss_sigma_return_probEvent_eq
    [Fintype U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCache : ProverTransform.popRateOnlyTailByInput (U := U) st.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none)
    (P : Option (Option (CanonicalSpongeState U)) → Prop) :
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
          (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run]
      =
    Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (CanonicalSpongeState U)) ] := by
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler :=
    OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st)
  have hproj :
      (Option.map Prod.fst <$> handler) =
        (some <$> ProverTransform.d2sSampleState
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
    dsimp [handler]
    exact d2sHandleBacktrackNoResult_miss_return_projection
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) st hCache hLookup
  have hdist :
      (Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run) =
        (Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleState
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run) := by
    calc
      Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run
          = (simulateQ impl (Option.map Prod.fst <$> handler)).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
      _ = (simulateQ impl
            (some <$> ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [hproj]
      _ = Option.map some <$>
            (simulateQ impl (ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
  calc
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) | (simulateQ impl handler).run]
        = Pr[ P |
            Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ P |
            Option.map some <$>
              (simulateQ impl (ProverTransform.d2sSampleState
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [hdist]
    _ = Pr[ fun sampled? => P (Option.map some sampled?) |
            (simulateQ impl (ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (CanonicalSpongeState U)) ] := by
          dsimp [impl]
          exact ProverTransform.d2sSampleState_simulateQ_sigma_probEvent_eq
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g
            (fun sampled? => P (Option.map some sampled?))

/-- Local finite-target form of the ordinary Item 4(c) miss.  It is the familiar uniform-state
charge; paired with the following cache rule, these are the two `Ordinary` fresh branches. -/
lemma d2sHandleBacktrackNoResult_miss_sigma_capacity_mem_finset_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCache : ProverTransform.popRateOnlyTailByInput st.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  have hdist := d2sHandleBacktrackNoResult_miss_sigma_return_probEvent_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hCache hLookup
    (fun o : Option (Option (CanonicalSpongeState U)) =>
      match o with
      | some (some sampled) => sampled.capacitySegment ∈ S
      | _ => False)
  calc
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run]
        = Pr[ (fun r =>
            match Option.map (Option.map Prod.fst) r with
            | some (some sampled) => sampled.capacitySegment ∈ S
            | _ => False) |
          (simulateQ
            ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
              fun aux => OptionT.lift
                (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
            (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run] := by
              apply probEvent_congr'
              · intro r _
                cases r with
                | none => rfl
                | some inner =>
                    cases inner <;> rfl
              · rfl
    _ = Pr[ fun sampled : CanonicalSpongeState U => sampled.capacitySegment ∈ S |
          ($ᵗ (CanonicalSpongeState U)) ] := by
            simpa using hdist
    _ ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) :=
      probEvent_uniformState_capacitySegment_mem_finset_le (U := U) S

/-- Sigma-specialized capacity projection for Item 4(c)i.  A consumed rate-only tail has no
latent capacity: after projecting the returned state to its capacity component, the handler is
exactly one fresh uniform capacity sample. -/
lemma d2sHandleBacktrackNoResult_cache_sigma_capacity_probEvent_eq
    [Fintype U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {tail : ProverTransform.RateOnlyTail (U := U)}
    {cacheRest : List (ProverTransform.RateOnlyCacheEntry (U := U))}
    (hCache : ProverTransform.popRateOnlyTailByInput st.rateCacheP stateIn =
      some (tail, cacheRest))
    (P : Option (Option (Vector U SpongeSize.C)) → Prop) :
    Pr[ fun r => P (Option.map (Option.map (fun pair => pair.1.capacitySegment)) r) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run]
      =
    Pr[ fun capacity => P (some (some capacity)) | ($ᵗ (Vector U SpongeSize.C)) ] := by
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler :=
    OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st)
  have hproj :
      (Option.map (fun pair => pair.1.capacitySegment) <$> handler) =
        (some <$> ProverTransform.d2sSampleCapacity
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
    dsimp [handler]
    unfold ProverTransform.d2sHandleBacktrackNoResult
    simp [hCache, ProverTransform.materializeRateOnlyCacheEntry,
      ProverTransform.materializeRateOnlyTail]
    congr 1
    funext capacity
    apply congrArg some
    convert ProverTransform.d2sSynthesisState_capacitySegment (U := U) tail.nextRate capacity
    ext i
    simp
  have hdist :
      (Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
        (simulateQ impl handler).run) =
        (Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleCapacity
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run) := by
    calc
      Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
          (simulateQ impl handler).run
          = (simulateQ impl (Option.map (fun pair => pair.1.capacitySegment) <$> handler)).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
      _ = (simulateQ impl
            (some <$> ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [hproj]
      _ = Option.map some <$>
            (simulateQ impl (ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
  calc
    Pr[ fun r => P (Option.map (Option.map (fun pair => pair.1.capacitySegment)) r) |
        (simulateQ impl handler).run]
        = Pr[ P |
            Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
              (simulateQ impl handler).run] := by
            rw [probEvent_map]
            rfl
    _ = Pr[ P |
            Option.map some <$>
              (simulateQ impl (ProverTransform.d2sSampleCapacity
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
            rw [hdist]
    _ = Pr[ fun sampled? => P (Option.map some sampled?) |
            (simulateQ impl (ProverTransform.d2sSampleCapacity
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
            rw [probEvent_map]
            rfl
    _ = Pr[ fun capacity => P (some (some capacity)) | ($ᵗ (Vector U SpongeSize.C)) ] := by
            dsimp [impl]
            exact ProverTransform.d2sSampleCapacity_simulateQ_sigma_probEvent_eq
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g
              (fun sampled? => P (Option.map some sampled?))

/-- Local finite-target form of the rate-only cache rule.  Conditional on the prior state and a
cache hit, the output capacity of this one actual forward occurrence hits `S` with probability at
most `|S| / |Σ|^c`. -/
lemma d2sHandleBacktrackNoResult_cache_sigma_capacity_mem_finset_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {tail : ProverTransform.RateOnlyTail (U := U)}
    {cacheRest : List (ProverTransform.RateOnlyCacheEntry (U := U))}
    (hCache : ProverTransform.popRateOnlyTailByInput st.rateCacheP stateIn =
      some (tail, cacheRest))
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackNoResult
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  have hdist := d2sHandleBacktrackNoResult_cache_sigma_capacity_probEvent_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hCache
    (fun o : Option (Option (Vector U SpongeSize.C)) =>
      match o with
      | some (some capacity) => capacity ∈ S
      | _ => False)
  rw [hdist]
  exact probEvent_uniformCapacity_mem_finset_le (U := U) S

/-- In the ordinary branch, once no rate-only tail is available, a successful forward-table
lookup is only a repeated raw occurrence and leaves the base trace unchanged. -/
lemma d2sHandleBacktrackNoResult_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn recovered : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCache : ProverTransform.popRateOnlyTailByInput st.rateCacheP stateIn = none)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = some recovered)
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
    a = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  have hHit :
      a = recovered ∧ st'.trace = st.trace ++ [⟨dsPermQuery stateIn, recovered⟩] := by
    unfold ProverTransform.d2sHandleBacktrackNoResult at hi
    simp [hCache, hLookup] at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_perm_inlu_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- Observable return projection for the Item 4(d) non-image table miss.  This branch does not
consult `Cache_p`: once `tr_∇.p.inlu` misses it is exactly one fresh full-state sample. -/
lemma d2sHandleBacktrackSome_nonimage_miss_return_projection
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hImage : ProverTransform.d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut = false)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none) :
    (Option.map Prod.fst <$>
      OptionT.run ((ProverTransform.d2sHandleBacktrackSome
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        stateIn backtrackOut).run st)) =
      (some <$> ProverTransform.d2sSampleState
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
  unfold ProverTransform.d2sHandleBacktrackSome
  simp only [hImage, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_lift, OptionT.run_bind, OptionT.run_lift, OptionT.run_pure,
    Option.elimM, pure_bind, Option.elim_some]
  split <;> simp_all

/-- An Item 4(d) non-image table hit is likewise only a repeated base representative. -/
lemma d2sHandleBacktrackSome_nonimage_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn recovered : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hImage : ProverTransform.d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut = false)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = some recovered)
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
    a = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  have hHit :
      a = recovered ∧ st'.trace = st.trace ++ [⟨dsPermQuery stateIn, recovered⟩] := by
    unfold ProverTransform.d2sHandleBacktrackSome at hi
    simp [hImage, hLookup] at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_perm_inlu_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- In the nonempty codec-image branch, the preliminary `gᵢ` query does not change the D2S
table state.  Hence an eventual `tr_∇.p.inlu` hit still returns an already represented pair. -/
lemma d2sHandleBacktrackSome_image_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn recovered : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hImage : ProverTransform.d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut = true)
    (hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = some recovered)
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
    a = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  unfold ProverTransform.d2sHandleBacktrackSome at hi
  simp [hImage, hNonempty] at hi
  obtain ⟨rhoHat, _hrhoHat, hi⟩ := mem_support_option_elimM_some hi
  have hHit :
      a = recovered ∧ st'.trace = st.trace ++ [⟨dsPermQuery stateIn, recovered⟩] := by
    unfold ProverTransform.d2sHandleBacktrackAfterG at hi
    simp [hLookup] at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_perm_inlu_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- Finite-target form of the Item 4(d) non-image miss.  As in an ordinary fresh miss, its
output capacity lies in any fixed target set `S` with probability at most `|S| / |Σ|^c`. -/
lemma d2sHandleBacktrackSome_nonimage_miss_sigma_capacity_mem_finset_le
    [Fintype U] [Nonempty U] [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hImage : ProverTransform.d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut = false)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackSome
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          stateIn backtrackOut).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler := OptionT.run ((ProverTransform.d2sHandleBacktrackSome
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateIn backtrackOut).run st)
  have hproj :
      (Option.map Prod.fst <$> handler) =
        (some <$> ProverTransform.d2sSampleState
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
    dsimp [handler]
    exact d2sHandleBacktrackSome_nonimage_miss_return_projection
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) backtrackOut st hImage hLookup
  have hdist :
      (Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run) =
        (Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleState
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run) := by
    calc
      Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run =
          (simulateQ impl (Option.map Prod.fst <$> handler)).run := by
            rw [simulateQ_map]
            rw [OptionT.run_map]
      _ = (simulateQ impl
            (some <$> ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
            rw [hproj]
      _ = Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleState
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
            rw [simulateQ_map]
            rw [OptionT.run_map]
  calc
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) | (simulateQ impl handler).run]
        = Pr[ (fun result : Option (Option (CanonicalSpongeState U)) =>
            match result with
            | some (some stateOut) => stateOut.capacitySegment ∈ S
            | _ => False) |
            Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run] := by
              rw [probEvent_map]
              apply probEvent_congr'
              · intro r _
                cases r with
                | none => rfl
                | some inner =>
                    cases inner with
                    | none => rfl
                    | some pair =>
                        rcases pair with ⟨stateOut, st'⟩
                        rfl
              · rfl
    _ = Pr[ (fun result : Option (Option (CanonicalSpongeState U)) =>
          match result with
          | some (some stateOut) => stateOut.capacitySegment ∈ S
          | _ => False) |
          Option.map some <$>
            (simulateQ impl (ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
            rw [hdist]
    _ = Pr[ (fun sampled? : Option (CanonicalSpongeState U) =>
          match Option.map some sampled? with
          | some (some stateOut) => stateOut.capacitySegment ∈ S
          | _ => False) |
          (simulateQ impl (ProverTransform.d2sSampleState
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
            rw [probEvent_map]
            rfl
    _ = Pr[ fun sampled : CanonicalSpongeState U => sampled.capacitySegment ∈ S |
          ($ᵗ (CanonicalSpongeState U)) ] := by
            dsimp [impl]
            rw [ProverTransform.d2sSampleState_simulateQ_sigma_probEvent_eq
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g]
            apply probEvent_congr'
            · intro sampled _
              simp
            · rfl
    _ ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) :=
      probEvent_uniformState_capacitySegment_mem_finset_le (U := U) S

/-- Local finite-target charge for `Program` after the codec table miss.  Rate-block parsing and
padding are an arbitrary preceding auxiliary computation; whichever nonempty block list they
produce, exactly one fresh capacity is sampled for its first materialized block. -/
lemma d2sProgramFirstBlock_sigma_capacity_mem_finset_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun result : Option (Option (Vector U SpongeSize.C)) =>
        match result with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (do
          let rateBlocks ← ProverTransform.d2sRateBlocksFromChallenge
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
            (i := backtrackOut.roundIdx) sampledRhoHat
          match rateBlocks.toList with
          | [] => pure none
          | _ :: _ => (some <$> ProverTransform.d2sSampleCapacity
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let rateBlocks := ProverTransform.d2sRateBlocksFromChallenge
    (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
    (i := backtrackOut.roundIdx) sampledRhoHat
  change Pr[ (fun result : Option (Option (Vector U SpongeSize.C)) =>
        match result with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ impl (do
        let blocks ← rateBlocks
        match blocks.toList with
        | [] => pure none
        | _ :: _ => (some <$> ProverTransform.d2sSampleCapacity
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U)
  rw [simulateQ_bind, OptionT.run_bind]
  apply probEvent_bind_le_of_forall_le
  intro blocks? _
  cases blocks? with
  | none =>
      change Pr[ (fun result : Option (Option (Vector U SpongeSize.C)) =>
          match result with
          | some (some capacity) => capacity ∈ S
          | _ => False) | pure none] ≤
        (S.card : ℝ≥0∞) / capacitySpaceSize (U := U)
      rw [probEvent_pure]
      simp
  | some blocks =>
      cases hBlocks : blocks.toList with
      | nil =>
          simp only [hBlocks, Option.elim_some]
          rw [simulateQ_pure, OptionT.run_pure]
          rw [probEvent_pure]
          simp
      | cons firstRate remainingRates =>
          simp only [Option.elim_some, hBlocks]
          rw [simulateQ_map, OptionT.run_map]
          rw [probEvent_map]
          have hpred :
              ((fun result : Option (Option (Vector U SpongeSize.C)) =>
                  match result with
                  | some (some capacity) => capacity ∈ S
                  | _ => False) ∘ Option.map some) =
                (fun capacity? : Option (Vector U SpongeSize.C) =>
                  match capacity? with
                  | some capacity => capacity ∈ S
                  | none => False) := by
                funext capacity?
                cases capacity? <;> rfl
          rw [hpred]
          rw [ProverTransform.d2sSampleCapacity_simulateQ_sigma_probEvent_eq
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g
            (fun capacity? =>
              match capacity? with
              | some capacity => capacity ∈ S
              | none => False)]
          exact probEvent_uniformCapacity_mem_finset_le (U := U) S

/-- Live-handler form of the `Program` first-block charge.  This composes the return projection
with the preceding local lemma, so the forward stopping proof can cite one ordinary handler fact
for all three fresh materialization sites. -/
lemma d2sHandleBacktrackAfterG_miss_sigma_capacity_mem_finset_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackAfterG
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          stateIn backtrackOut sampledRhoHat).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler := OptionT.run ((ProverTransform.d2sHandleBacktrackAfterG
    (δ := δ) (T_H := T_H) (T_P := T_P)
    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    stateIn backtrackOut sampledRhoHat).run st)
  let stateProgram := do
    let rateBlocks ← ProverTransform.d2sRateBlocksFromChallenge
      (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (i := backtrackOut.roundIdx) sampledRhoHat
    match rateBlocks.toList with
    | [] => pure none
    | firstRate :: _ =>
        let capacity ← ProverTransform.d2sSampleCapacity
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        pure (some (ProverTransform.d2sSynthesisState (U := U) firstRate capacity))
  let capacityProgram := do
    let rateBlocks ← ProverTransform.d2sRateBlocksFromChallenge
      (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
      (i := backtrackOut.roundIdx) sampledRhoHat
    match rateBlocks.toList with
    | [] => pure none
    | _ :: _ => (some <$> ProverTransform.d2sSampleCapacity
      (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))
  have hstate : Option.map Prod.fst <$> handler = stateProgram := by
    dsimp [handler, stateProgram]
    exact ProverTransform.d2sHandleBacktrackAfterG_miss_return_projection
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) backtrackOut sampledRhoHat st hLookup
  have hcapacity :
      Option.map (fun pair => pair.1.capacitySegment) <$> handler = capacityProgram := by
    calc
      Option.map (fun pair => pair.1.capacitySegment) <$> handler =
          Option.map (fun state => state.capacitySegment) <$>
            (Option.map Prod.fst <$> handler) := by
              simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
              congr 1
              funext result
              cases result <;> rfl
      _ = Option.map (fun state => state.capacitySegment) <$> stateProgram := by
            rw [hstate]
      _ = capacityProgram := by
            dsimp [stateProgram, capacityProgram]
            simp only [map_eq_bind_pure_comp, bind_assoc]
            congr 1
            funext rateBlocks
            cases hBlocks : rateBlocks.toList with
            | nil => simp [hBlocks]
            | cons firstRate remainingRates =>
                simp only [hBlocks, pure_bind]
                simp only [bind_assoc, pure_bind]
                congr 1
                funext capacity
                simp only [Function.comp_apply]
                change pure (some ((ProverTransform.d2sSynthesisState
                  (U := U) firstRate capacity).capacitySegment)) = pure (some capacity)
                rw [ProverTransform.d2sSynthesisState_capacitySegment]
  have hdist :
      (Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
        (simulateQ impl handler).run) =
        (simulateQ impl capacityProgram).run := by
    calc
      Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
          (simulateQ impl handler).run =
          (simulateQ impl (Option.map (fun pair => pair.1.capacitySegment) <$> handler)).run := by
            rw [simulateQ_map]
            rw [OptionT.run_map]
      _ = (simulateQ impl capacityProgram).run := by rw [hcapacity]
  change Pr[ (fun r =>
      match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
      | some (some capacity) => capacity ∈ S
      | _ => False) | (simulateQ impl handler).run] ≤
        (S.card : ℝ≥0∞) / capacitySpaceSize (U := U)
  calc
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) | (simulateQ impl handler).run] =
        Pr[ (fun result : Option (Option (Vector U SpongeSize.C)) =>
          match result with
          | some (some capacity) => capacity ∈ S
          | _ => False) |
          Option.map (Option.map (fun pair => pair.1.capacitySegment)) <$>
            (simulateQ impl handler).run] := by
              rw [probEvent_map]
              rfl
    _ = Pr[ (fun result : Option (Option (Vector U SpongeSize.C)) =>
          match result with
          | some (some capacity) => capacity ∈ S
          | _ => False) | (simulateQ impl capacityProgram).run] := by
            rw [hdist]
    _ ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
          dsimp [impl, capacityProgram]
          exact d2sProgramFirstBlock_sigma_capacity_mem_finset_le
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            k_g backtrackOut sampledRhoHat S

/-- A `Program` continuation whose forward-table lookup hits merely repeats an already
represented normalized pair; it cannot create a new base position. -/
lemma d2sHandleBacktrackAfterG_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateIn recovered : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (sampledRhoHat : Vector U (challengeSize (pSpec := pSpec) backtrackOut.roundIdx))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = some recovered)
    {i : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))}
    (hi : i ∈ support (simulateQ (gImpl + auxImpl)
      (OptionT.run ((ProverTransform.d2sHandleBacktrackAfterG
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        stateIn backtrackOut sampledRhoHat).run st))).run)
    {a : CanonicalSpongeState U}
    {st' : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)}
    (hiEq : i = some (some (a, st'))) :
    a = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  have hHit :
      a = recovered ∧ st'.trace = st.trace ++ [⟨dsPermQuery stateIn, recovered⟩] := by
    unfold ProverTransform.d2sHandleBacktrackAfterG at hi
    simp [hLookup] at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_perm_inlu_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- Conditioning on Item 4(e)i's `gᵢ` reply does not cost a capacity factor: after a table
miss, every possible reply is followed by the same local `Program` first-block bound. -/
lemma d2sHandleBacktrackSome_image_miss_sigma_capacity_mem_finset_le
    [Fintype U] [Nonempty U] [VCVCompatible U] [SampleableType U]
    [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateIn : CanonicalSpongeState U}
    (backtrackOut : Backtrack.BacktrackOutput
      (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hImage : ProverTransform.d2sInCodecImagePredicate
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) backtrackOut = true)
    (hNonempty : 0 < challengeSize (pSpec := pSpec) backtrackOut.roundIdx)
    (hLookup : TraceTableOps.inlu st.trΔ.p stateIn = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ (fun r =>
        match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
        | some (some capacity) => capacity ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleBacktrackSome
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          stateIn backtrackOut).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  classical
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let P : Option (Option (CanonicalSpongeState U ×
      ProverTransform.D2SQueryState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) → Prop :=
    fun r => match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
    | some (some capacity) => capacity ∈ S
    | _ => False
  letI : DecidablePred P := Classical.decPred P
  change Pr[ P | (simulateQ impl (OptionT.run ((ProverTransform.d2sHandleBacktrackSome
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
    stateIn backtrackOut).run st))).run] ≤ _
  unfold ProverTransform.d2sHandleBacktrackSome
  simp only [hImage, ↓reduceIte, hNonempty, StateT.run_bind,
    StateT.run_get, StateT.run_lift, OptionT.run_bind, OptionT.run_lift,
    Option.elimM, pure_bind, Option.elim_some]
  split
  · simp only [StateT.run_bind, StateT.run_lift, OptionT.run_bind, OptionT.run_lift,
      Option.elim_some, pure_bind]
    rw [Option.elimM, Option.elimM]
    rw [simulateQ_bind, OptionT.run_bind]
    apply probEvent_bind_le_of_forall_le
    intro first hfirst
    cases first with
    | none =>
        simp only [Option.elim_none]
        change Pr[ (fun r : Option (Option (CanonicalSpongeState U ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) =>
          match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
          | some (some capacity) => capacity ∈ S
          | _ => False) | (pure none : ProbComp (Option (Option (CanonicalSpongeState U ×
            ProverTransform.D2SQueryState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))] ≤ _
        rw [probEvent_pure]
        simp
    | some pair =>
        cases pair with
        | none =>
            simp only [Option.elim_some, Option.elim_none]
            rw [simulateQ_pure, OptionT.run_pure]
            change Pr[ (fun r : Option (Option (CanonicalSpongeState U ×
                ProverTransform.D2SQueryState
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U))) =>
              match Option.map (Option.map (fun pair => pair.1.capacitySegment)) r with
              | some (some capacity) => capacity ∈ S
              | _ => False) | (pure (some none) : ProbComp (Option (Option (CanonicalSpongeState U ×
                ProverTransform.D2SQueryState
                  (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)))))] ≤ _
            rw [probEvent_pure]
            simp
        | some rhoAndState =>
            rcases rhoAndState with ⟨rhoHat, stG⟩
            simp only [Option.elim_some] at hfirst
            simp at hfirst
            rcases hfirst with ⟨_, rfl⟩
            simp only [Option.elim_some]
            exact d2sHandleBacktrackAfterG_miss_sigma_capacity_mem_finset_le
              (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
              (U := U) (δ := δ) k_g backtrackOut rhoHat st hLookup S
  · rename_i h
    exact False.elim (h trivial)

/-- If the inverse-permutation handler takes the `tr_∇.p.outlu` table-hit branch, every
successful simulated result has the same base trace as the input state.  The raw trace appends the
same normalized permutation pair again in inverse orientation, and the mirror invariant proves
that pair is already represented in `getBaseTrace`. -/
lemma d2sHandleInversePermQuery_hit_support_baseTrace_eq
    [∀ i, Fintype (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Message i)]
    {stateOut recovered : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = some recovered)
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
    a = recovered ∧ getBaseTrace st'.trace = getBaseTrace st.trace := by
  subst i
  have hHit :
      a = recovered ∧ st'.trace = st.trace ++ [⟨dsPermInvQuery stateOut, recovered⟩] := by
    unfold ProverTransform.d2sHandleInversePermQuery at hi
    aesop
  obtain ⟨ha, hTrace⟩ := hHit
  subst a
  constructor
  · rfl
  · rw [hTrace]
    exact getBaseTrace_append_perm_outlu_eq
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (U := U)
      st.h_mirror hLookup

/-- Observable return-value projection for an inverse-permutation miss: after projecting away the
proof-carrying state component, the returned preimage state is exactly the lifted uniform state
sampler. -/
lemma d2sHandleInversePermQuery_miss_return_projection
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = none) :
    (Option.map Prod.fst <$>
      OptionT.run ((ProverTransform.d2sHandleInversePermQuery
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st)) =
      (some <$> ProverTransform.d2sSampleState
        (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
  unfold ProverTransform.d2sHandleInversePermQuery
  aesop

/-- Sigma-specialized probability bridge for an inverse-permutation miss.  Once the deterministic
lookup says the handler is in the fresh branch, projecting away the proof-carrying simulator state
leaves exactly one uniform sponge-state sample. -/
lemma d2sHandleInversePermQuery_miss_sigma_return_probEvent_eq
    [Fintype U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = none)
    (P : Option (Option (CanonicalSpongeState U)) → Prop) :
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleInversePermQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st))).run]
      =
    Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (CanonicalSpongeState U)) ] := by
  let impl :=
    ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
      fun aux => OptionT.lift
        (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
  let handler :=
    OptionT.run ((ProverTransform.d2sHandleInversePermQuery
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st)
  have hproj :
      (Option.map Prod.fst <$> handler) =
        (some <$> ProverTransform.d2sSampleState
          (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)) := by
    dsimp [handler]
    exact d2sHandleInversePermQuery_miss_return_projection
      (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
      (U := U) (δ := δ) st hLookup
  have hdist :
      (Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run) =
        (Option.map some <$>
          (simulateQ impl (ProverTransform.d2sSampleState
            (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run) := by
    calc
      Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run
          = (simulateQ impl (Option.map Prod.fst <$> handler)).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
      _ = (simulateQ impl
            (some <$> ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [hproj]
      _ = Option.map some <$>
            (simulateQ impl (ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run := by
              rw [simulateQ_map]
              rw [OptionT.run_map]
  calc
    Pr[ fun r => P (Option.map (Option.map Prod.fst) r) | (simulateQ impl handler).run]
        = Pr[ P |
            Option.map (Option.map Prod.fst) <$> (simulateQ impl handler).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ P |
            Option.map some <$>
              (simulateQ impl (ProverTransform.d2sSampleState
                (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [hdist]
    _ = Pr[ fun sampled? => P (Option.map some sampled?) |
            (simulateQ impl (ProverTransform.d2sSampleState
              (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ))).run] := by
          rw [probEvent_map]
          rfl
    _ = Pr[ fun sampled => P (some (some sampled)) | ($ᵗ (CanonicalSpongeState U)) ] := by
          dsimp [impl]
          exact ProverTransform.d2sSampleState_simulateQ_sigma_probEvent_eq
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) k_g
            (fun sampled? => P (Option.map some sampled?))

/-- Local finite-target bound for a sigma inverse-permutation miss.  Conditional on a fixed
simulator state whose inverse table lookup misses `stateOut`, the freshly sampled preimage state's
capacity segment lands in any finite target set `S` with probability at most `|S| / |Σ|^c`. -/
lemma d2sHandleInversePermQuery_miss_sigma_capacity_mem_finset_le
    [Fintype U]
    [Nonempty U]
    [VCVCompatible U]
    [SampleableType U]
    [∀ i, Fintype (pSpec.Challenge i)]
    (k_g : (D_Sigma (U := U) StmtIn pSpec δ).Carrier)
    {stateOut : CanonicalSpongeState U}
    (st : ProverTransform.D2SQueryState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hLookup : TraceTableOps.outlu st.trΔ.p stateOut = none)
    (S : Finset (Vector U SpongeSize.C)) :
    Pr[ fun r =>
        (match Option.map (Option.map Prod.fst) r with
        | some (some sampled) => sampled.capacitySegment ∈ S
        | _ => False) |
      (simulateQ
        ((fun q => OptionT.lift ((D_Sigma (U := U) StmtIn pSpec δ).toImpl k_g q)) +
          fun aux => OptionT.lift
            (((ProverTransform.d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec) aux))
        (OptionT.run ((ProverTransform.d2sHandleInversePermQuery
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stateOut).run st))).run]
      ≤ (S.card : ℝ≥0∞) / capacitySpaceSize (U := U) := by
  have hdist := d2sHandleInversePermQuery_miss_sigma_return_probEvent_eq
    (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec)
    (U := U) (δ := δ) k_g st hLookup
    (fun o : Option (Option (CanonicalSpongeState U)) =>
      match o with
      | some (some sampled) => sampled.capacitySegment ∈ S
      | _ => False)
  rw [hdist]
  exact probEvent_uniformState_capacitySegment_mem_finset_le (U := U) S

end TableHitRepresentatives

end BadEventDS

end DuplexSpongeFS
