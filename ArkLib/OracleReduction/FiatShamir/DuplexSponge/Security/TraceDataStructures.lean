/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# CO25 Definition 5.2 — Trace data structures

Generic trace-table interface for the duplex-sponge simulator's `tr_∇` (CO25 Definition 5.2),
together with a list-backed default instantiation and refinement-model laws via `Multiset`.

## Design: polymorphism via refinement model

We define a **single** operations class `TraceTableOps T K V` covering both the hash-query table
(`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`). Both have the same four-operation
shape: `empty`, `add`, `inlu` (forward lookup), `outlu` (backward lookup).

The lawful class `LawfulTraceTable` uses a `Multiset (K × V)` model:

- `inlu t k = some v` iff `(k, v)` is in the multiset **and** no conflicting value `v'` exists,
  and it's the unique pair with values `(k, v)` in the multiset.
- `outlu t v = some k` iff `(k, v)` is in the multiset **and** no conflicting key `k'` exists,
  and it's the unique pair with values `(k, v)` in the multiset.

This handles the "redundant query" case correctly: if an adversary queries `(k, v)` twice, the
multiset contains `[(k, v), (k, v)]`; the uniqueness condition still holds for `v`, so `inlu`
returns `v` instead of aborting.

By parameterizing algorithms (`BackTrack`, `LookAhead`) over `TraceTableOps`, we can swap in an
`O(log N)` or `O(1)` implementation later without touching algorithms or security proofs.

## Structures

- `DuplexSpongeTrace` — type alias for the paper's `(h, p, p⁻¹)`-trace (CO25 Definition 5.2).
- `TraceTableOps T K V` — generic operations typeclass.
- `LawfulTraceTable T K V` — extends `TraceTableOps` with `Multiset`-based laws.
- `TraceNabla` — paper's `tr_∇ = (h, p)`, parameterized over any `LawfulTraceTable` instances.
- `ListBacked.ListTraceTable K V` — concrete list implementation; `add` is pure `O(1)` cons;
  however lookup takes `O(N)`
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.DSTraceStorage

/-- The canonical duplex-sponge `(h, p, p⁻¹)`-trace in Definition 5.2 -/
abbrev DuplexSpongeTrace (StmtIn U : Type) [SpongeUnit U] [SpongeSize] :=
  QueryLog (duplexSpongeChallengeOracle StmtIn U)

section TraceFilters

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]

/-- `tr^{<j}`: The first `j-1` entries of the trace. -/
def prefix_lt_j (tr : DuplexSpongeTrace StmtIn U) (j : ℕ) : DuplexSpongeTrace StmtIn U :=
  tr.take (j - 1)

/-- `tr_h`: Filter the trace for hash queries (`'h'`).
`(tr.prefix_lt_j j).filterHash` is exactly `tr_h^{<j}` from CO25 Definition 5.2.
This is the log of the oracle spec `(StartType →ₒ Vector U SpongeSize.C)`. -/
def filterHash (tr : DuplexSpongeTrace StmtIn U) : List (StmtIn × Vector U SpongeSize.C) :=
  tr.filterMap fun
    | ⟨.inl stmt, capSeg⟩ => some (stmt, capSeg)
    | _ => none

/-- `tr_p`: Filter the trace for forward permutation queries (`'p'`).
`(tr.prefix_lt_j j).filterFwdPerm` is exactly `tr_p^{<j}` from CO25 Definition 5.2.
This is the log of the oracle spec `(forwardPermutationOracle (CanonicalSpongeState U))`. -/
def filterFwdPerm (tr : DuplexSpongeTrace StmtIn U) :
  List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  tr.filterMap fun
    | ⟨.inr (.inl sIn), sOut⟩ => some (sIn, sOut)
    | _ => none

/-- `tr_{p⁻¹}`: Filter the trace for backward permutation queries (`'p⁻¹'`).
`(tr.prefix_lt_j j).filterBwdPerm` is exactly `tr_{p⁻¹}^{<j}` from CO25 Definition 5.2.
This is the log of the oracle spec `(backwardPermutationOracle (CanonicalSpongeState U))`. -/
def filterBwdPerm (tr : DuplexSpongeTrace StmtIn U) :
  List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  tr.filterMap fun
    | ⟨.inr (.inr sOut), sIn⟩ => some (sOut, sIn)
    | _ => none

end TraceFilters

section TraceDataStructures

/-! ### Generic operations typeclass -/

/-- Operations for a trace table used in CO25 Definition 5.2.
Covers both the one-way hash table (`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`);
both have the same four-operation shape, plus a bulk-enumeration op `entries` used by paper §5.2
partial-key matching for backtracking. -/
class TraceTableOps (T : Type) (K V : outParam Type) where
  empty : T                    -- `∅` — return an empty table
  add   : T → K → V → T       -- `t ∪ {(k,v)}` — insert a `(k, v)` pair
  inlu  : T → K → Option V    -- `inlu(t, k)` — unique forward lookup (CO25 Def. 5.2)
  outlu : T → V → Option K    -- `outlu(t, v)` — unique backward lookup (CO25 Def. 5.2)
  /-- `entries(t)` — enumerate all `(k, v)` pairs (CO25 §5.2 partial-key matching). -/
  entries : T → List (K × V)

/-! ### Refinement-model lawful class -/

/-- Refinement-model lawfulness for a trace table, expressed via a `Multiset (K × V)` model.

`toMultiSet` is the abstract mathematical content of the table.
The `inlu`/`outlu` laws state that a lookup succeeds iff the entry exists **and** is unique
in the multiset — handling duplicate-entry traces correctly. -/
class LawfulTraceTable (T : Type) (K V : outParam Type) [DecidableEq K] [DecidableEq V]
extends TraceTableOps T K V where
  toMultiSet : T → Multiset (K × V)
  toMultiSet_empty : toMultiSet TraceTableOps.empty = (0 : Multiset (K × V)) := by simp [empty]
  toMultiSet_add : ∀ t k v, toMultiSet (add t k v) = (k, v) ::ₘ toMultiSet t
  -- **inlu's query result MUST BE UNIQUE**, i.e. two copies
    -- of `(k, v)` in the multiset do not trigger the "multiple" case
  inlu_eq_some : ∀ t k v,
    inlu t k = some v ↔
      (toMultiSet t).count (k, v) = 1 ∧ -- Uniqueness of the whole (query, answer) pair `(k, v)`
      (∀ v', (k, v') ∈ toMultiSet t → v' = v) -- Uniqueness of answer value `v` according
        -- to the query key `k`
  -- **outlu's query result MUST BE UNIQUE**, i.e. two copies
    -- of `(k, v)` in the multiset do not trigger the "multiple" case
  outlu_eq_some : ∀ t k v,
    outlu t v = some k ↔
      (toMultiSet t).count (k, v) = 1 ∧ -- Uniqueness of the whole (query, answer) pair `(k, v)`
      (∀ k', (k', v) ∈ toMultiSet t → k' = k) -- Uniqueness of query key `k` according
        -- to the query value `v`
  /-- `entries` reflects the abstract multiset content. Order is unspecified; only the multiset
  reading is stable. Used by paper §5.2 partial-key enumeration in `BackTrack`. -/
  toMultiSet_ofEntries : ∀ t, (TraceTableOps.entries t : Multiset (K × V)) = toMultiSet t

/-! ### CO25 `tr_∇` — generic trace payload -/

/-- The simulator's trace table `tr_∇` from CO25 Definition 5.2, generic over any lawful
implementation.

- `h : T_H` — hash-query table (`tr_∇.h`): maps `StmtIn` to capacity segments.
- `p : T_P` — permutation table (`tr_∇.p`): bidirectional map over sponge states.

Both `T_H` and `T_P` must satisfy `LawfulTraceTable`; by parameterizing over them, the
algorithms and security proofs are implementation-agnostic. -/
structure TraceNabla (T_H T_P StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U]
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)] -- lawful trace DS for the hash queries
    -- lawful trace DS for the permutation queries (`p` and `p⁻¹`)
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)] where
  h : T_H -- `tr_∇.h` hash-query table (`StmtIn → Vector U C`)
  p : T_P -- `tr_∇.p` permutation table (`CanonicalSpongeState U ↔ CanonicalSpongeState U`)

/-! ### Generic `TraceNabla` API -/

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U]

/-- Build a `TraceNabla` from a `DuplexSpongeTrace` (CO25 Definition 5.2).

Generic over any `LawfulTraceTable` implementations `T_H` and `T_P`; only uses `empty` and `add`
from `TraceTableOps`, so the construction is independent of the concrete data structure.

Dispatch rules (matching the three tuple forms of Definition 5.2):
- `.inl stmt`         → `('h', stmt, capSeg)` → `T_H.add acc.h stmt capSeg`
- `.inr (.inl sIn)`   → `('p', sIn, sOut)`    → `T_P.add acc.p sIn sOut`
- `.inr (.inr sOut)`  → `('p⁻¹', sOut, sIn)`  → `T_P.add acc.p sIn sOut`

Both permutation directions contribute `(s_in, s_out)` pairs to the **same** bidirectional `p`
table, because `tr_∇.p` is the single bidirectional structure over `(s_in, s_out)` pairs. -/
def TraceNabla.ofQueryLog
    {T_H T_P : Type}
    [LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)]
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (log : DuplexSpongeTrace StmtIn U) :
    TraceNabla T_H T_P StmtIn U :=
  log.foldl (init := ⟨TraceTableOps.empty, TraceTableOps.empty⟩)
    fun acc entry =>
      match entry with
      | ⟨.inl stmt,        capSeg⟩ => { acc with h := TraceTableOps.add acc.h stmt capSeg }
      | ⟨.inr (.inl sIn),  sOut⟩   => { acc with p := TraceTableOps.add acc.p sIn sOut }
      | ⟨.inr (.inr sOut), sIn⟩    => { acc with p := TraceTableOps.add acc.p sIn sOut }

/-! ### List-backed instantiation -/

namespace ListBacked

/-- Default list-backed implementation for trace tables.
`add` is pure cons — `O(1)` insertion. The multiset model is `↑entries`.
`inlu`/`outlu` are computable: filter entries by key/value and return `some` iff exactly one
match exists (zero or multiple → `none`), matching the paper's sorted-list semantics. -/
structure ListTraceTable (K V : Type) where
  entries : List (K × V)  -- list of `(k, v)` pairs; multiset model `↑entries`
deriving Inhabited


variable {K V : Type} [DecidableEq K] [DecidableEq V]

@[inline] def empty : ListTraceTable K V := ⟨[]⟩

/-- `O(1)` cons insertion. Duplicates are representable and are resolved by the lookup laws. -/
@[inline] def add (t : ListTraceTable K V) (k : K) (v : V) : ListTraceTable K V :=
  ⟨(k, v) :: t.entries⟩

@[inline] def toMultiSet (t : ListTraceTable K V) : Multiset (K × V) := t.entries

/-- `inlu` succeeds iff `(k, v)` appears exactly once **and** is the unique value for key `k`.
Two copies of `(k, v)` → `none` (paper: "multiple matches"). -/
@[inline] def fwdProp (t : ListTraceTable K V) (k : K) (v : V) : Prop :=
  (toMultiSet t).count (k, v) = 1 ∧ ∀ v', (k, v') ∈ toMultiSet t → v' = v

/-- `outlu` succeeds iff `(k, v)` appears exactly once **and** is the unique key for value `v`.
Two copies of `(k, v)` → `none` (paper: "multiple matches"). -/
@[inline] def bwdProp (t : ListTraceTable K V) (k : K) (v : V) : Prop :=
  (toMultiSet t).count (k, v) = 1 ∧ ∀ k', (k', v) ∈ toMultiSet t → k' = k

/-- Computable forward lookup: collect all values for key `k`; return `some v` iff exactly one. -/
def inlu (t : ListTraceTable K V) (k : K) : Option V :=
  match t.entries.filterMap (fun p => if p.1 = k then some p.2 else none) with
  | [v] => some v
  | _   => none

/-- Computable backward lookup: collect all keys for value `v`; return `some k` iff exactly one. -/
def outlu (t : ListTraceTable K V) (v : V) : Option K :=
  match t.entries.filterMap (fun p => if p.2 = v then some p.1 else none) with
  | [k] => some k
  | _   => none

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
  constructor
  · intro h
    unfold lookupBy at h
    generalize hvalues :
        entries.filterMap
          (fun entry => if keyOf entry = query then some (valueOf entry) else none) =
          values at h
    have hvalues_single : values = [valueOf entry] := by
      cases values with
      | nil =>
          simp at h
      | cons hd tl =>
          cases tl with
          | nil =>
              simp at h
              subst hd
              rfl
          | cons _ _ =>
              simp at h
    have hfilter :
        entries.filterMap
          (fun entry => if keyOf entry = query then some (valueOf entry) else none) =
          [valueOf entry] := by
      rw [hvalues]
      exact hvalues_single
    rw [List.filterMap_eq_cons_iff] at hfilter
    obtain ⟨before, found, after, hentries, hbefore, hfound, hafter⟩ := hfilter
    by_cases hfound_key : keyOf found = query
    · simp only [hfound_key, ↓reduceIte] at hfound
      injection hfound with hfound_value
      have hfound_eq : found = entry := by
        have hkey : keyOf found = keyOf entry := hfound_key.trans hentry_key.symm
        exact hext found hkey hfound_value
      subst found
      have hafter_none :
          ∀ x ∈ after,
            (fun entry => if keyOf entry = query then some (valueOf entry) else none) x = none := by
        rw [List.filterMap_eq_nil_iff] at hafter
        exact hafter
      have hnot_before : entry ∉ (before : Multiset α) := by
        intro hmem
        have hmem_list : entry ∈ before := Multiset.mem_coe.mp hmem
        have hnone := hbefore entry hmem_list
        simp [hentry_key] at hnone
      have hnot_after : entry ∉ (after : Multiset α) := by
        intro hmem
        have hmem_list : entry ∈ after := Multiset.mem_coe.mp hmem
        have hnone := hafter_none entry hmem_list
        simp [hentry_key] at hnone
      exact
        ⟨by
          rw [hentries]
          rw [← Multiset.coe_add before (entry :: after), ← Multiset.cons_coe]
          rw [Multiset.count_add, Multiset.count_cons_self,
            Multiset.count_eq_zero_of_notMem hnot_before,
            Multiset.count_eq_zero_of_notMem hnot_after],
        by
          intro entry' hmem hkey
          rw [hentries] at hmem
          simp only [Multiset.mem_coe, List.mem_append, List.mem_cons] at hmem
          rcases hmem with hmem_before | hmid | hmem_after
          · have hnone := hbefore entry' hmem_before
            simp [hkey] at hnone
          · exact hmid
          · have hnone := hafter_none entry' hmem_after
            simp [hkey] at hnone⟩
    · simp only [hfound_key, ↓reduceIte] at hfound
      cases hfound
  · intro h
    rcases h with ⟨hcount, huniq⟩
    unfold lookupBy
    have hmem_ms : entry ∈ (entries : Multiset α) := by
      rw [← Multiset.count_pos]
      rw [hcount]
      norm_num
    have hmem_list : entry ∈ entries := Multiset.mem_coe.mp hmem_ms
    rw [List.mem_iff_append] at hmem_list
    obtain ⟨before, after, hentries⟩ := hmem_list
    have hcount_split :
        (entries : Multiset α).count entry =
          (before : Multiset α).count entry + 1 + (after : Multiset α).count entry := by
      rw [hentries]
      simp
      omega
    have hcount_before : (before : Multiset α).count entry = 0 := by
      omega
    have hcount_after : (after : Multiset α).count entry = 0 := by
      omega
    have hnot_before : entry ∉ before := by
      intro hmem
      have hmem_ms_before : entry ∈ (before : Multiset α) := Multiset.mem_coe.mpr hmem
      have hpos := (Multiset.count_pos).2 hmem_ms_before
      omega
    have hnot_after : entry ∉ after := by
      intro hmem
      have hmem_ms_after : entry ∈ (after : Multiset α) := Multiset.mem_coe.mpr hmem
      have hpos := (Multiset.count_pos).2 hmem_ms_after
      omega
    rw [hentries]
    simp only [List.filterMap_append]
    have hbefore_none :
        before.filterMap (fun entry => if keyOf entry = query then some (valueOf entry) else none) =
          [] := by
      rw [List.filterMap_eq_nil_iff]
      intro found hmem
      by_cases hfound_key : keyOf found = query
      · have hfound_eq : found = entry := by
          apply huniq
          · rw [hentries]
            simp only [Multiset.mem_coe, List.mem_append, List.mem_cons]
            exact Or.inl hmem
          · exact hfound_key
        subst found
        exact False.elim (hnot_before hmem)
      · simp only [hfound_key, ↓reduceIte]
    have hafter_none :
        after.filterMap (fun entry => if keyOf entry = query then some (valueOf entry) else none) =
          [] := by
      rw [List.filterMap_eq_nil_iff]
      intro found hmem
      by_cases hfound_key : keyOf found = query
      · have hfound_eq : found = entry := by
          apply huniq
          · rw [hentries]
            simp only [Multiset.mem_coe, List.mem_append, List.mem_cons]
            exact Or.inr (Or.inr hmem)
          · exact hfound_key
        subst found
        exact False.elim (hnot_after hmem)
      · simp only [hfound_key, ↓reduceIte]
    simp [hbefore_none, hafter_none, hentry_key]

omit [SpongeSize] in
lemma inlu_eq_some_iff (t : ListTraceTable K V) (k : K) (v : V) :
    inlu t k = some v ↔ fwdProp t k v := by
  change lookupBy t.entries Prod.fst Prod.snd k = some v ↔ fwdProp t k v
  rw [lookupBy_eq_some_iff t.entries Prod.fst Prod.snd k (k, v) rfl (by
    intro found hkey hvalue
    rcases found with ⟨k', v'⟩
    simp only at hkey hvalue
    subst k'
    subst v'
    rfl)]
  constructor
  · intro h
    exact ⟨h.1, fun v' hmem => Prod.mk.inj (h.2 (k, v') hmem rfl) |>.2⟩
  · intro h
    exact ⟨h.1, fun entry hmem hkey => by
      rcases entry with ⟨k', v'⟩
      simp only at hkey
      subst k'
      have hv' := h.2 v' hmem
      subst v'
      rfl⟩

omit [SpongeSize] in
lemma outlu_eq_some_iff (t : ListTraceTable K V) (k : K) (v : V) :
    outlu t v = some k ↔ bwdProp t k v := by
  change lookupBy t.entries Prod.snd Prod.fst v = some k ↔ bwdProp t k v
  rw [lookupBy_eq_some_iff t.entries Prod.snd Prod.fst v (k, v) rfl (by
    intro found hkey hvalue
    rcases found with ⟨k', v'⟩
    simp only at hkey hvalue
    subst v'
    subst k'
    rfl)]
  constructor
  · intro h
    exact ⟨h.1, fun k' hmem => Prod.mk.inj (h.2 (k', v) hmem rfl) |>.1⟩
  · intro h
    exact ⟨h.1, fun entry hmem hkey => by
      rcases entry with ⟨k', v'⟩
      simp only at hkey
      subst v'
      have hk' := h.2 k' hmem
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

end ListBacked

/-! ### Default `tr_∇` type alias and `ofQueryLog` -/

/-- The default (list-backed) `tr_∇`. In fact we want to use a more optimized data structure
for efficient storage and query complexity. -/
abbrev DefaultTraceDelta (StmtIn U : Type) [SpongeUnit U] [SpongeSize]
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

end TraceDataStructures
end DuplexSpongeFS.DSTraceStorage
