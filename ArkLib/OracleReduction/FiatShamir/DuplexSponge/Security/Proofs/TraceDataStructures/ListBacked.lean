/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures.Basic

/-!
# [CO25, Definition 5.2] — Trace data structures: list-backed instance and invariants

The list-backed default instantiation `ListBacked.ListTraceTable` of the trace-table interface
from `TraceDataStructures.Basic`, and the `IsSubsetOfQueryLog` invariant lemmas for `tr_∇`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace DuplexSpongeFS

namespace DSTraceStorage

section TraceDataStructures

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U]

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-! ### List-backed instantiation -/

namespace ListBacked

/-- **[CO25, §5.1]** Default list-backed implementation for trace tables.
`add` is pure cons — `O(1)` insertion. The multiset model is `↑entries`.
`inlu`/`outlu` deduplicate exact pairs, then return `some` iff exactly one distinct mapping
matches. -/
structure ListTraceTable (K V : Type) where
  entries : List (K × V)  -- list of `(k, v)` pairs; multiset model `↑entries`
deriving Inhabited

variable {K V : Type} [DecidableEq K] [DecidableEq V]

@[inline] def empty : ListTraceTable K V := ⟨[]⟩

/-- `O(1)` cons insertion. Duplicates are representable and are resolved by the lookup laws. -/
@[inline] def add (t : ListTraceTable K V) (k : K) (v : V) : ListTraceTable K V :=
  ⟨(k, v) :: t.entries⟩

@[inline] def toMultiSet (t : ListTraceTable K V) : Multiset (K × V) := t.entries

/-- `inlu` succeeds iff `(k, v)` appears and is the unique distinct value for key `k`. -/
@[inline] def fwdProp (t : ListTraceTable K V) (k : K) (v : V) : Prop :=
  (k, v) ∈ toMultiSet t ∧ ∀ v', (k, v') ∈ toMultiSet t → v' = v

/-- `outlu` succeeds iff `(k, v)` appears and is the unique distinct key for value `v`. -/
@[inline] def bwdProp (t : ListTraceTable K V) (k : K) (v : V) : Prop :=
  (k, v) ∈ toMultiSet t ∧ ∀ k', (k', v) ∈ toMultiSet t → k' = k

/-- Computable forward lookup modulo repeated identical pairs. -/
def inlu (t : ListTraceTable K V) (k : K) : Option V :=
  match t.entries.dedup.filterMap (fun p => if p.1 = k then some p.2 else none) with
  | [v] => some v
  | _   => none

/-- Computable backward lookup modulo repeated identical pairs. -/
def outlu (t : ListTraceTable K V) (v : V) : Option K :=
  match t.entries.dedup.filterMap (fun p => if p.2 = v then some p.1 else none) with
  | [k] => some k
  | _   => none

/-! Identical occurrences are harmless; distinct mappings remain conflicts. -/

/-- Shared singleton-lookup law for list-backed trace-table lookups. -/
private def lookupBy {α κ υ : Type} [DecidableEq κ]
    (entries : List α) (keyOf : α → κ) (valueOf : α → υ) (query : κ) : Option υ :=
  match entries.filterMap
    (fun entry => if keyOf entry = query then some (valueOf entry) else none) with
  | [value] => some value
  | _ => none

omit [SpongeSize] in
-- The proof splits a successful singleton `filterMap` and reconstructs multiset uniqueness.
private lemma lookupBy_eq_some_iff {α κ υ : Type} [DecidableEq α] [DecidableEq κ]
    (entries : List α) (keyOf : α → κ) (valueOf : α → υ) (query : κ) (entry : α)
    (hentry_key : keyOf entry = query)
    (hext :
      ∀ found, keyOf found = keyOf entry → valueOf found = valueOf entry → found = entry) :
    lookupBy entries keyOf valueOf query = some (valueOf entry) ↔
      (entries : Multiset α).count entry = 1 ∧
      ∀ entry', entry' ∈ (entries : Multiset α) →
        keyOf entry' = query → entry' = entry := by
  have hfm : entries.filterMap
      (fun entry => if keyOf entry = query then some (valueOf entry) else none) =
      (entries.filter (fun e => keyOf e = query)).map valueOf := by
    induction entries with
    | nil => rfl
    | cons e es ih => by_cases he : keyOf e = query <;> simp [he, ih]
  have hlook : lookupBy entries keyOf valueOf query = some (valueOf entry) ↔
      (entries.filter (fun e => keyOf e = query)).map valueOf = [valueOf entry] := by
    unfold lookupBy
    rw [hfm]
    rcases (entries.filter (fun e => keyOf e = query)).map valueOf with _ | ⟨a, _ | ⟨b, l⟩⟩ <;>
      simp
  rw [hlook, List.map_eq_singleton_iff, Multiset.coe_count]
  simp only [Multiset.mem_coe]
  constructor
  · rintro ⟨a, ha, hav⟩
    have hmem : a ∈ entries.filter (fun e => keyOf e = query) := by simp [ha]
    rw [List.mem_filter, decide_eq_true_eq] at hmem
    obtain rfl := hext a (hmem.2.trans hentry_key.symm) hav
    refine ⟨?_, fun e' he' hk => ?_⟩
    · rw [← List.count_filter (p := fun e => decide (keyOf e = query)) (by simpa using hentry_key),
        ha, List.count_singleton_self]
    · have : e' ∈ entries.filter (fun e => keyOf e = query) := by simp [he', hk]
      simpa [ha] using this
  · rintro ⟨hcount, huniq⟩
    refine ⟨entry, ?_, rfl⟩
    have hc : (entries.filter (fun e => keyOf e = query)).count entry = 1 := by
      rw [List.count_filter (by simpa using hentry_key), hcount]
    have hall : ∀ e ∈ entries.filter (fun e => keyOf e = query), e = entry := by
      intro e he
      rw [List.mem_filter, decide_eq_true_eq] at he
      exact huniq e he.1 he.2
    rw [List.eq_replicate_iff.mpr ⟨rfl, hall⟩] at hc ⊢
    simp only [List.count_replicate_self] at hc
    rw [hc, List.replicate_one]

omit [SpongeSize] in
private lemma count_coe_dedup_eq_one_iff_mem {α : Type} [DecidableEq α]
    (entries : List α) (entry : α) :
    (entries.dedup : Multiset α).count entry = 1 ↔ entry ∈ (entries : Multiset α) := by
  simp [List.count_dedup]

omit [SpongeSize] in
lemma inlu_eq_some_iff (t : ListTraceTable K V) (k : K) (v : V) :
    inlu t k = some v ↔ fwdProp t k v := by
  change lookupBy t.entries.dedup Prod.fst Prod.snd k = some v ↔ fwdProp t k v
  rw [lookupBy_eq_some_iff t.entries.dedup Prod.fst Prod.snd k (k, v) rfl (by
    intro found hkey hvalue
    rcases found with ⟨k', v'⟩
    simp only at hkey hvalue
    subst k'
    subst v'
    rfl)]
  constructor
  · intro h
    exact ⟨(count_coe_dedup_eq_one_iff_mem t.entries (k, v)).mp h.1,
      fun v' hmem => Prod.mk.inj (h.2 (k, v')
        (Multiset.mem_coe.mpr (List.mem_dedup.mpr (Multiset.mem_coe.mp hmem))) rfl) |>.2⟩
  · intro h
    exact ⟨(count_coe_dedup_eq_one_iff_mem t.entries (k, v)).mpr h.1,
      fun entry hmem hkey => by
      rcases entry with ⟨k', v'⟩
      simp only at hkey
      subst k'
      have hmem' : (k, v') ∈ (t.entries : Multiset (K × V)) :=
        Multiset.mem_coe.mpr (List.mem_dedup.mp (Multiset.mem_coe.mp hmem))
      have hv' := h.2 v' hmem'
      subst v'
      rfl⟩

omit [SpongeSize] in
lemma outlu_eq_some_iff (t : ListTraceTable K V) (k : K) (v : V) :
    outlu t v = some k ↔ bwdProp t k v := by
  change lookupBy t.entries.dedup Prod.snd Prod.fst v = some k ↔ bwdProp t k v
  rw [lookupBy_eq_some_iff t.entries.dedup Prod.snd Prod.fst v (k, v) rfl (by
    intro found hkey hvalue
    rcases found with ⟨k', v'⟩
    simp only at hkey hvalue
    subst v'
    subst k'
    rfl)]
  constructor
  · intro h
    exact ⟨(count_coe_dedup_eq_one_iff_mem t.entries (k, v)).mp h.1,
      fun k' hmem => Prod.mk.inj (h.2 (k', v)
        (Multiset.mem_coe.mpr (List.mem_dedup.mpr (Multiset.mem_coe.mp hmem))) rfl) |>.1⟩
  · intro h
    exact ⟨(count_coe_dedup_eq_one_iff_mem t.entries (k, v)).mpr h.1,
      fun entry hmem hkey => by
      rcases entry with ⟨k', v'⟩
      simp only at hkey
      subst v'
      have hmem' : (k', v) ∈ (t.entries : Multiset (K × V)) :=
        Multiset.mem_coe.mpr (List.mem_dedup.mp (Multiset.mem_coe.mp hmem))
      have hk' := h.2 k' hmem'
      subst k'
      rfl⟩

instance instListBasedTraceTableOps {K V : Type} [DecidableEq K] [DecidableEq V] :
  TraceTableOps (ListTraceTable K V) K V where
  empty := empty
  add   := add
  inlu  := inlu
  outlu := outlu
  entries t := t.entries

instance instLawfulListBasedTraceTable {K V : Type} [DecidableEq K] [DecidableEq V] :
    LawfulTraceTable (ListTraceTable K V) K V where
  toTraceTableOps     := instListBasedTraceTableOps
  toMultiSet          := toMultiSet
  toMultiSet_empty    := rfl
  toMultiSet_add      := fun _ _ _ => rfl
  inlu_eq_some        := fun t k v => inlu_eq_some_iff t k v
  outlu_eq_some       := fun t k v => outlu_eq_some_iff t k v
  toMultiSet_ofEntries  := fun _ => rfl

/-! ### Default `tr_∇` type alias and `ofQueryLog` -/

instance instLawfulTraceNablaImplListBased :
    LawfulTraceNablaImpl
      (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
      StmtIn U :=
  ⟨instLawfulListBasedTraceTable, instLawfulListBasedTraceTable⟩

/-- **[CO25, §5.1]** The default (list-backed) `tr_∇`. In fact we want to use a more optimized data
structure for efficient storage and query complexity. -/
abbrev DefaultTraceDelta (StmtIn U : Type) [SpongeUnit U]
    [DecidableEq StmtIn] [DecidableEq U] :=
  TraceNabla
    (DuplexSpongeFS.DSTraceStorage.ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
    (DuplexSpongeFS.DSTraceStorage.ListBacked.ListTraceTable
      (CanonicalSpongeState U) (CanonicalSpongeState U))
    StmtIn U

/-- Specialization of `TraceNabla.ofQueryLog` to the default list-backed implementation. -/
def DefaultTraceDelta.ofQueryLog
    (log : DuplexSpongeTrace StmtIn U) : DefaultTraceDelta StmtIn U :=
    TraceNabla.ofQueryLog log
end ListBacked

lemma TraceNabla.IsSubsetOfQueryLog_empty_nil :
    TraceNabla.IsSubsetOfQueryLog
      (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ : TraceNabla T_H T_P StmtIn U)
      [] := by
  constructor
  · intro _ _ h
    have hms := Multiset.mem_coe.mpr h
    rw [LawfulTraceTable.toMultiSet_ofEntries, LawfulTraceTable.toMultiSet_empty] at hms
    simp at hms
  · intro _ _ h
    have hms := Multiset.mem_coe.mpr h
    rw [LawfulTraceTable.toMultiSet_ofEntries, LawfulTraceTable.toMultiSet_empty] at hms
    simp at hms

/-- The empty table mirrors the empty public trace. -/
lemma TraceNabla.MirrorsQueryLog_empty_nil :
    TraceNabla.MirrorsQueryLog
      (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ : TraceNabla T_H T_P StmtIn U)
      [] := by
  constructor
  · intro stmt cap
    constructor
    · simp
    · intro hMem
      have hms : (stmt, cap) ∈ LawfulTraceTable.toMultiSet (TraceTableOps.empty : T_H) := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact Multiset.mem_coe.mpr hMem
      rw [LawfulTraceTable.toMultiSet_empty] at hms
      simp at hms
  · intro sIn sOut
    constructor
    · simp
    · intro hMem
      have hms : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet (TraceTableOps.empty : T_P) := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact Multiset.mem_coe.mpr hMem
      rw [LawfulTraceTable.toMultiSet_empty] at hms
      simp at hms

lemma TraceNabla.MirrorsQueryLog_append_hash_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    ({trΔ with h := TraceTableOps.add trΔ.h stmt cap} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inl stmt, cap⟩]) := by
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inl.injEq, add_apply_inl,
      heq_eq_eq, List.not_mem_nil, or_false, TraceTableOps.mem_entries_add_iff, Prod.mk.injEq,
      ← hMirror.1]
    tauto
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inr,
      add_apply_inl, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.2]

lemma TraceNabla.MirrorsQueryLog_append_perm_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inl,
      add_apply_inr, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.1]
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inr.injEq, Sum.inl.injEq,
      add_apply_inr, add_apply_inl, heq_eq_eq, List.not_mem_nil, or_false, reduceCtorEq,
      false_and, or_self, TraceTableOps.mem_entries_add_iff, Prod.mk.injEq, ← hMirror.2]
    tauto

lemma TraceNabla.MirrorsQueryLog_append_perm_inv_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inl,
      add_apply_inr, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.1]
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inr.injEq, reduceCtorEq,
      add_apply_inr, add_apply_inl, heq_eq_eq, false_and, List.not_mem_nil, or_self, or_false,
      TraceTableOps.mem_entries_add_iff, Prod.mk.injEq, ← hMirror.2]
    tauto

lemma TraceNabla.MirrorsQueryLog_append_hash_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C)
    (hMem : (stmt, cap) ∈ TraceTableOps.entries trΔ.h) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inl stmt, cap⟩]) := by
  rw [← hMirror.1] at hMem
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inl.injEq, add_apply_inl,
      heq_eq_eq, List.not_mem_nil, or_false, ← hMirror.1, or_iff_left_iff_imp, and_imp]
    aesop
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inr,
      add_apply_inl, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.2]

lemma TraceNabla.MirrorsQueryLog_append_perm_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  rw [← hMirror.2] at hMem
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inl,
      add_apply_inr, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.1]
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inr.injEq, Sum.inl.injEq,
      add_apply_inr, add_apply_inl, heq_eq_eq, List.not_mem_nil, or_false, reduceCtorEq,
      false_and, or_self, ← hMirror.2]
    aesop

lemma TraceNabla.MirrorsQueryLog_append_perm_inv_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  rw [← hMirror.2] at hMem
  constructor
  · intro stmt' cap'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, reduceCtorEq, add_apply_inl,
      add_apply_inr, false_and, List.not_mem_nil, or_self, or_false, ← hMirror.1]
  · intro sIn' sOut'
    simp only [List.mem_append, List.mem_cons, Sigma.mk.injEq, Sum.inr.injEq, reduceCtorEq,
      add_apply_inr, add_apply_inl, heq_eq_eq, false_and, List.not_mem_nil, or_self, or_false,
      ← hMirror.2]
    aesop

lemma TraceNabla.MirrorsQueryLog_append_perm_insert
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.insert trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  unfold TraceTableOps.insert
  split
  · exact TraceNabla.MirrorsQueryLog_append_perm_existing hMirror sIn sOut ‹_›
  · exact TraceNabla.MirrorsQueryLog_append_perm_add hMirror sIn sOut

lemma TraceNabla.MirrorsQueryLog_append_hash_insert
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    ({trΔ with h := TraceTableOps.insert trΔ.h stmt cap} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inl stmt, cap⟩]) := by
  unfold TraceTableOps.insert
  split
  · exact TraceNabla.MirrorsQueryLog_append_hash_existing hMirror stmt cap ‹_›
  · exact TraceNabla.MirrorsQueryLog_append_hash_add hMirror stmt cap

lemma TraceNabla.MirrorsQueryLog_append_perm_inv_insert
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.insert trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  unfold TraceTableOps.insert
  split
  · exact TraceNabla.MirrorsQueryLog_append_perm_inv_existing hMirror sIn sOut ‹_›
  · exact TraceNabla.MirrorsQueryLog_append_perm_inv_add hMirror sIn sOut

lemma TraceNabla.IsSubsetOfQueryLog_append_any
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    trΔ.IsSubsetOfQueryLog (trace ++ [entry]) := by
  constructor
  · intros stmt cap hMem
    exact List.mem_append_left _ (hSub.1 _ _ hMem)
  · intros sIn sOut hMem
    rcases hSub.2 _ _ hMem with hL | hR
    · exact Or.inl (List.mem_append_left _ hL)
    · exact Or.inr (List.mem_append_left _ hR)

lemma TraceNabla.IsSubsetOfQueryLog_append_hash
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    ({trΔ with h := TraceTableOps.insert trΔ.h stmt cap} :
      TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inl stmt, cap⟩]) := by
  constructor
  · intro stmt' cap' hMem
    have h1 := (TraceTableOps.mem_entries_insert_iff trΔ.h stmt cap (stmt', cap')).mp hMem
    rcases h1 with hEq | hRest
    · injection hEq with hS hC; subst hS hC
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · exact List.mem_append_left _ (hSub.1 _ _ hRest)
  · intro sIn sOut hMem
    rcases hSub.2 _ _ hMem with hL | hR
    · exact Or.inl (List.mem_append_left _ hL)
    · exact Or.inr (List.mem_append_left _ hR)

lemma TraceNabla.IsSubsetOfQueryLog_append_perm
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.insert trΔ.p sIn sOut} :
      TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  constructor
  · intro stmt' cap' hMem
    exact List.mem_append_left _ (hSub.1 _ _ hMem)
  · intro sIn' sOut' hMem
    have h1 := (TraceTableOps.mem_entries_insert_iff trΔ.p sIn sOut (sIn', sOut')).mp hMem
    rcases h1 with hEq | hRest
    · injection hEq with hS hO; subst hS hO
      exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · rcases hSub.2 _ _ hRest with hL | hR
      · exact Or.inl (List.mem_append_left _ hL)
      · exact Or.inr (List.mem_append_left _ hR)

lemma TraceNabla.IsSubsetOfQueryLog_append_perm_inv
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.insert trΔ.p sIn sOut} :
      TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  constructor
  · intro stmt' cap' hMem
    exact List.mem_append_left _ (hSub.1 _ _ hMem)
  · intro sIn' sOut' hMem
    have h1 := (TraceTableOps.mem_entries_insert_iff trΔ.p sIn sOut (sIn', sOut')).mp hMem
    rcases h1 with hEq | hRest
    · injection hEq with hS hO; subst hS hO
      exact Or.inr (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · rcases hSub.2 _ _ hRest with hL | hR
      · exact Or.inl (List.mem_append_left _ hL)
      · exact Or.inr (List.mem_append_left _ hR)

end TraceDataStructures

end DSTraceStorage

end DuplexSpongeFS
