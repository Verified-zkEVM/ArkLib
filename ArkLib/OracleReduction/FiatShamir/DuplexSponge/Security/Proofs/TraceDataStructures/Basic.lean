/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# [CO25, Definition 5.2] — Trace data structures: tables and `tr_∇`

Generic trace-table interface for the duplex-sponge oracle wrapper's `tr_∇`
[CO25, Definition 5.2], together with a list-backed default instantiation and
refinement-model laws via `Multiset`.

## Design: polymorphism via refinement model

We define a **single** operations class `TraceTableOps T K V` covering both the hash-query table
(`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`). Both have the same four-operation
shape: `empty`, `add`, `inlu` (forward lookup), `outlu` (backward lookup).

The lawful class `LawfulTraceTable` uses a `Multiset (K × V)` model:

- `inlu t k = some v` iff `(k, v)` occurs and no distinct value `v'` occurs at `k`.
- `outlu t v = some k` iff `(k, v)` occurs and no distinct key `k'` occurs at `v`.

The external query log retains occurrences, while `tr_∇` has set semantics: repeated identical
`(k, v)` pairs are harmless, but distinct mappings remain conflicts.

By parameterizing algorithms (`BackTrack`, `LookAhead`) over `TraceTableOps`, we can swap in an
`O(log N)` or `O(1)` implementation later without touching algorithms or security proofs.

## Structures

- `DuplexSpongeTrace` — type alias for the paper's `(h, p, p⁻¹)`-trace [CO25, Definition 5.2].
- `TraceTableOps T K V` — generic operations typeclass.
- `LawfulTraceTable T K V` — extends `TraceTableOps` with `Multiset`-based laws.
- `TraceNabla` — paper's `tr_∇ = (h, p)`, parameterized over any `LawfulTraceTable` instances.
- `ListBacked.ListTraceTable K V` — concrete list implementation; `add` is pure `O(1)` cons;
  however lookup takes `O(N)`
-/

@[expose] public section

open OracleComp OracleSpec

universe u

namespace DuplexSpongeFS

namespace DSTraceStorage

/-- **[CO25, Definition 5.2]** The canonical duplex-sponge `(h, p, p⁻¹)`-trace in Definition 5.2 -/
abbrev DuplexSpongeTrace (StmtIn U : Type) [SpongeUnit U] [SpongeSize] :=
  QueryLog (duplexSpongeOracle StmtIn U)

section TraceDataStructures

/-! ### Generic operations typeclass -/

/-- Operations for a trace table used in [CO25, Definition 5.2].
Covers both the one-way hash table (`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`);
both have the same four-operation shape, plus a bulk-enumeration op `entries` used by paper §5.2
partial-key matching for backtracking. -/
class TraceTableOps (T : Type) (K V : outParam Type) where
  empty : T                    -- `∅` — return an empty table
  add   : T → K → V → T       -- `t ∪ {(k,v)}` — insert a `(k, v)` pair
  inlu  : T → K → Option V    -- `inlu(t, k)` — unique forward lookup [CO25, Def. 5.2]
  outlu : T → V → Option K    -- `outlu(t, v)` — unique backward lookup [CO25, Def. 5.2]
  /-- `entries(t)` — enumerate all `(k, v)` pairs ([CO25, §5.2] partial-key matching). -/
  entries : T → List (K × V)

/-- Set-semantic insertion for `tr_∇`. The query log retains every occurrence, whereas the
internal table records an already-present normalized pair only once. -/
def TraceTableOps.insert {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) : T :=
  if (k, v) ∈ TraceTableOps.entries t then t else TraceTableOps.add t k v

/-- On a genuinely new normalized pair, set-semantic insertion is the ordinary table addition. -/
lemma TraceTableOps.insert_eq_add_of_not_mem
    {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) (hmem : (k, v) ∉ TraceTableOps.entries t) :
    TraceTableOps.insert t k v = TraceTableOps.add t k v := by
  simp [TraceTableOps.insert, hmem]

/-! ### Refinement-model lawful class -/

/-- Refinement-model lawfulness for a trace table, expressed via a `Multiset (K × V)` model.

`toMultiSet` is the abstract mathematical content of the table. The lookup laws are insensitive
to multiplicity: success requires the represented pair to exist and forbids only a distinct
value/key match. -/
class LawfulTraceTable (T : Type) (K V : outParam Type) [DecidableEq K] [DecidableEq V]
extends TraceTableOps T K V where
  toMultiSet : T → Multiset (K × V)
  toMultiSet_empty : toMultiSet TraceTableOps.empty = (0 : Multiset (K × V)) := by simp [empty]
  toMultiSet_add : ∀ t k v, toMultiSet (add t k v) = (k, v) ::ₘ toMultiSet t
  inlu_eq_some : ∀ t k v,
    inlu t k = some v ↔
      (k, v) ∈ toMultiSet t ∧
      (∀ v', (k, v') ∈ toMultiSet t → v' = v) -- Uniqueness of answer value `v` according
        -- to the query key `k`
  outlu_eq_some : ∀ t k v,
    outlu t v = some k ↔
      (k, v) ∈ toMultiSet t ∧
      (∀ k', (k', v) ∈ toMultiSet t → k' = k) -- Uniqueness of query key `k` according
        -- to the query value `v`
  /-- `entries` reflects the abstract multiset content. Order is unspecified; only the multiset
  reading is stable. Used by paper §5.2 partial-key enumeration in `BackTrack`. -/
  toMultiSet_ofEntries : ∀ t, (TraceTableOps.entries t : Multiset (K × V)) = toMultiSet t

/-- Membership after `add`, at the public enumeration interface. -/
lemma TraceTableOps.mem_entries_add_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.add t k v) ↔
      pair = (k, v) ∨ pair ∈ TraceTableOps.entries t := by
  rw [← Multiset.mem_coe, LawfulTraceTable.toMultiSet_ofEntries, LawfulTraceTable.toMultiSet_add,
    Multiset.mem_cons, ← LawfulTraceTable.toMultiSet_ofEntries, Multiset.mem_coe]

/-- A successful forward lookup identifies a pair represented in the public table contents. -/
lemma TraceTableOps.mem_entries_of_inlu_eq_some
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V} (h : TraceTableOps.inlu t k = some v) :
    (k, v) ∈ TraceTableOps.entries t := by
  have hLookup := (LawfulTraceTable.inlu_eq_some t k v).mp h
  apply Multiset.mem_coe.mp
  rw [LawfulTraceTable.toMultiSet_ofEntries]
  exact hLookup.1

/-- A successful inverse lookup identifies the corresponding normalized pair in the table. -/
lemma TraceTableOps.mem_entries_of_outlu_eq_some
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V} (h : TraceTableOps.outlu t v = some k) :
    (k, v) ∈ TraceTableOps.entries t := by
  have hLookup := (LawfulTraceTable.outlu_eq_some t k v).mp h
  apply Multiset.mem_coe.mp
  rw [LawfulTraceTable.toMultiSet_ofEntries]
  exact hLookup.1

/-! ### Exact lookup preservation under a fresh table insertion

The raw rate-only D2S oracle wrapper keeps an occurrence log and a set-like lookup table
separately.  For the stopped Lemma-5.8/Claim-5.24 observer, a continuing fresh occurrence must
therefore preserve not merely the table/log mirror but also successful **unique** lookup for
every retained pair.  The four lemmas below isolate that generic refinement fact.  Their
freshness premises are stated through `entries`, so a transition can discharge them from its
concrete no-`E_cap` / no-`E_func` certificate without unfolding the table implementation.
-/

/-- A pair whose input is absent from a lawful table becomes the unique forward lookup at that
input after insertion. -/
lemma TraceTableOps.inlu_add_eq_some_of_no_input
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (hnew : ∀ v', (k, v') ∉ TraceTableOps.entries t) :
    TraceTableOps.inlu (TraceTableOps.add t k v) k = some v := by
  rw [LawfulTraceTable.inlu_eq_some]
  simp only [← LawfulTraceTable.toMultiSet_ofEntries, Multiset.mem_coe,
    TraceTableOps.mem_entries_add_iff, Prod.mk.injEq] at *
  grind

/-- Inserting under a different input leaves an already exact forward lookup exact. -/
lemma TraceTableOps.inlu_add_eq_some_of_exact_of_ne_input
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k k₀ : K) (v v₀ : V) (hExact : TraceTableOps.inlu t k₀ = some v₀)
    (hne : k₀ ≠ k) :
    TraceTableOps.inlu (TraceTableOps.add t k v) k₀ = some v₀ := by
  rw [LawfulTraceTable.inlu_eq_some]
  obtain ⟨hmem, hunique⟩ := (LawfulTraceTable.inlu_eq_some _ _ _).mp hExact
  simp only [← LawfulTraceTable.toMultiSet_ofEntries, Multiset.mem_coe,
    TraceTableOps.mem_entries_add_iff, Prod.mk.injEq] at *
  grind

/-- Set-semantic insertion adds membership for the requested pair and preserves all old pairs. -/
lemma TraceTableOps.mem_toMultiSet_insert_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ LawfulTraceTable.toMultiSet (TraceTableOps.insert t k v) ↔
      pair = (k, v) ∨ pair ∈ LawfulTraceTable.toMultiSet t := by
  by_cases hmem : (k, v) ∈ TraceTableOps.entries t
  · simp only [TraceTableOps.insert, hmem, ite_true]
    rw [← LawfulTraceTable.toMultiSet_ofEntries, Multiset.mem_coe] at *
    grind
  · simp [TraceTableOps.insert, hmem, LawfulTraceTable.toMultiSet_add]

/-- Public-entry membership has the same set-union behavior under `insert`. -/
lemma TraceTableOps.mem_entries_insert_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.insert t k v) ↔
      pair = (k, v) ∨ pair ∈ TraceTableOps.entries t := by
  rw [← Multiset.mem_coe, LawfulTraceTable.toMultiSet_ofEntries,
    TraceTableOps.mem_toMultiSet_insert_iff, ← LawfulTraceTable.toMultiSet_ofEntries,
    Multiset.mem_coe]

/-- Inserting a normalized pair already represented by the table is a no-op. -/
lemma TraceTableOps.insert_eq_self_of_mem
    {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) (h : (k, v) ∈ TraceTableOps.entries t) :
    TraceTableOps.insert t k v = t := by
  simp [TraceTableOps.insert, h]

/-! ### Bulk insertion and the entry/multiset dictionary -/

/-- Insert every pair of `l` into `t`, left to right. -/
def TraceTableOps.addAll {T K V : Type} [TraceTableOps T K V] (t : T) (l : List (K × V)) : T :=
  l.foldl (fun acc pair => TraceTableOps.add acc pair.1 pair.2) t

/-- Public enumeration and the abstract multiset model agree on membership. -/
lemma TraceTableOps.mem_entries_iff_mem_toMultiSet
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (pair : K × V) :
    pair ∈ TraceTableOps.entries t ↔ pair ∈ LawfulTraceTable.toMultiSet t := by
  rw [← LawfulTraceTable.toMultiSet_ofEntries]
  exact Multiset.mem_coe.symm

/-- The empty table has no public entries. -/
lemma TraceTableOps.not_mem_entries_empty
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (pair : K × V) :
    pair ∉ TraceTableOps.entries (TraceTableOps.empty : T) := by
  rw [TraceTableOps.mem_entries_iff_mem_toMultiSet, LawfulTraceTable.toMultiSet_empty]
  simp

/-- Public enumeration and the abstract multiset model agree on duplicate-freeness. -/
lemma TraceTableOps.entries_nodup_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V] (t : T) :
    (TraceTableOps.entries t).Nodup ↔ (LawfulTraceTable.toMultiSet t).Nodup := by
  rw [← LawfulTraceTable.toMultiSet_ofEntries]
  exact Multiset.coe_nodup.symm

/-- Bulk insertion adds exactly the inserted multiset. -/
lemma TraceTableOps.toMultiSet_addAll
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (l : List (K × V)) (t : T) :
    LawfulTraceTable.toMultiSet (TraceTableOps.addAll t l)
      = (l : Multiset (K × V)) + LawfulTraceTable.toMultiSet t := by
  induction l generalizing t with
  | nil => simp [TraceTableOps.addAll]
  | cons a l ih =>
      have hstep : TraceTableOps.addAll t (a :: l)
          = TraceTableOps.addAll (TraceTableOps.add t a.1 a.2) l := rfl
      rw [hstep, ih, LawfulTraceTable.toMultiSet_add, Prod.mk.eta,
        ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons]

/-- Membership after bulk insertion. -/
lemma TraceTableOps.mem_entries_addAll
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (l : List (K × V)) (t : T) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.addAll t l)
      ↔ pair ∈ l ∨ pair ∈ TraceTableOps.entries t := by
  rw [TraceTableOps.mem_entries_iff_mem_toMultiSet, TraceTableOps.toMultiSet_addAll,
    Multiset.mem_add, Multiset.mem_coe, TraceTableOps.mem_entries_iff_mem_toMultiSet]

class LawfulTraceNablaImpl (T_H T_P StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U] where
  /-- lawful trace data structure implementation for the hash queries -/
  lawfulHash : LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)
  /-- lawful trace data structure implementation for the permutation queries (`p` and `p⁻¹`) -/
  lawfulPermutation : LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)

attribute [instance_reducible] LawfulTraceNablaImpl.lawfulHash
  LawfulTraceNablaImpl.lawfulPermutation
attribute [instance] LawfulTraceNablaImpl.lawfulHash LawfulTraceNablaImpl.lawfulPermutation

/-! ### CO25 `tr_∇` — generic trace payload -/

/-- **[CO25, §5.1]** The oracle wrapper's sorted query-answer trace `tr_∇`, generic over any
lawful implementation.

- `h : T_H` — hash-query table (`tr_∇.h`): maps `StmtIn` to capacity segments.
- `p : T_P` — permutation table (`tr_∇.p`): bidirectional map over permutation states.

Both `T_H` and `T_P` must satisfy `LawfulTraceTable`; by parameterizing over them, the
algorithms and security proofs are implementation-agnostic. -/
structure TraceNabla (T_H T_P StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U]
    [instImpl : LawfulTraceNablaImpl T_H T_P StmtIn U]
    -- this holds the implementation & correctness of the `tr_∇` data structure
    where
  h : T_H -- `tr_∇.h` hash-query table (`StmtIn → Vector U C`)
  p : T_P -- `tr_∇.p` permutation table (`CanonicalSpongeState U ↔ CanonicalSpongeState U`)

/-! ### Generic `TraceNabla` API -/

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U]

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- **[CO25, §5.1]** Build a `TraceNabla` from a `DuplexSpongeTrace` (Definition 5.2).

Generic over any `LawfulTraceTable` implementations `T_H` and `T_P`; set-semantic `insert`
coalesces repeated identical pairs while retaining distinct conflicting mappings.

Dispatch rules (matching the three tuple forms of Definition 5.2):
- `.inl stmt`         → `('h', stmt, capSeg)` → `T_H.insert acc.h stmt capSeg`
- `.inr (.inl sIn)`   → `('p', sIn, sOut)`    → `T_P.insert acc.p sIn sOut`
- `.inr (.inr sOut)`  → `('p⁻¹', sOut, sIn)`  → `T_P.insert acc.p sIn sOut`

Both permutation directions contribute `(s_in, s_out)` pairs to the **same** bidirectional `p`
table, because `tr_∇.p` is the single bidirectional structure over `(s_in, s_out)` pairs. -/
def TraceNabla.ofQueryLog
    (log : DuplexSpongeTrace StmtIn U) :
    TraceNabla T_H T_P StmtIn U :=
  log.foldl (init := ⟨TraceTableOps.empty, TraceTableOps.empty⟩)
    fun acc entry =>
      match entry with
      | ⟨.inl stmt,        capSeg⟩ => { acc with h := TraceTableOps.insert acc.h stmt capSeg }
      | ⟨.inr (.inl sIn),  sOut⟩   => { acc with p := TraceTableOps.insert acc.p sIn sOut }
      | ⟨.inr (.inr sOut), sIn⟩    => { acc with p := TraceTableOps.insert acc.p sIn sOut }

/-- **[CO25, §5.5.1]** Build the `tr_∇` used by StdTrace Step 3.

Unlike `TraceNabla.ofQueryLog`, this constructor deliberately ignores inverse-permutation trace
entries, matching Step 3(c) of StdTrace. It coalesces repeated identical forward entries; D2SQuery
still uses the bidirectional constructor above. -/
def TraceNabla.ofQueryLogForwardOnly
    (log : DuplexSpongeTrace StmtIn U) :
    TraceNabla T_H T_P StmtIn U :=
  log.foldl (init := ⟨TraceTableOps.empty, TraceTableOps.empty⟩)
    fun acc entry =>
      match entry with
      | ⟨.inl stmt,        capSeg⟩ => { acc with h := TraceTableOps.insert acc.h stmt capSeg }
      | ⟨.inr (.inl sIn),  sOut⟩   => { acc with p := TraceTableOps.insert acc.p sIn sOut }
      | ⟨.inr (.inr _),    _⟩      => acc

def TraceNabla.IsSubsetOfQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, (stmt, cap) ∈ TraceTableOps.entries trΔ.h → ⟨.inl stmt, cap⟩ ∈ trace) ∧
  (∀ s_in s_out, (s_in, s_out) ∈ TraceTableOps.entries trΔ.p →
    ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace)

/-- `tr_∇` represents exactly the set of hash and normalized permutation pairs occurring in the
external trace.  The log may retain duplicate occurrences; the table deliberately does not. -/
def TraceNabla.MirrorsQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, ⟨.inl stmt, cap⟩ ∈ trace ↔ (stmt, cap) ∈ TraceTableOps.entries trΔ.h) ∧
  (∀ sIn sOut,
    (⟨.inr (.inl sIn), sOut⟩ ∈ trace ∨ ⟨.inr (.inr sOut), sIn⟩ ∈ trace) ↔
      (sIn, sOut) ∈ TraceTableOps.entries trΔ.p)

/-! ### Forward-first permutation pairs (`BackTrack` Step 2(b) restriction)

CO25's backtracking sequences (Def. 5.3) are *hash-anchored*: condition (b) requires the first
input state of a chain to carry the capacity returned by an `h`-query.  The normalized table
`tr_∇.p` deliberately forgets whether a mapping first entered the raw trace through `p` or
through `p⁻¹`, so a chain rooted at an adversarially chosen `p⁻¹` **input** looks, inside
`tr_∇.p`, exactly like a genuine forward chain — even though it can never satisfy Def. 5.3(b).

The executable single-chain scan in `Backtrack.lean` aborts at the first branching, so such a
decoy would make it abort on traces the paper's `BackTrack` handles without complaint.  The
notions below let the scan restrict its Step 2(b) candidate set to the mappings whose **first**
raw occurrence is a forward `p` query, which is exactly the set of mappings that can occur on a
hash-anchored chain built by the oracle wrapper's own forward queries. -/

/-- Normalize one raw trace entry to a permutation pair, if it is a permutation entry at all.
Both query directions normalize to the same `(sIn, sOut)` orientation. -/
def normalizedPermutationPair?
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    Option (CanonicalSpongeState U × CanonicalSpongeState U) :=
  match entry with
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl sIn), sOut⟩ => some (sIn, sOut)
  | ⟨.inr (.inr sOut), sIn⟩ => some (sIn, sOut)

/-- The permutation occurrences of a raw trace, normalized to `(sIn, sOut)` orientation and
listed in occurrence order.  Both query directions contribute the same normalized pair. -/
def normalizedPermutationPairs (trace : DuplexSpongeTrace StmtIn U) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  trace.filterMap normalizedPermutationPair?

/-- Supporting definition for **[CO25, §5.2]**. `PermutationForwardFirst trace sIn sOut` — the
*first* occurrence of the normalized pair `(sIn, sOut)` in the raw trace is the forward one
`⟨p, sIn, sOut⟩`.

Stated in decomposition form: the trace splits as `pre ++ ⟨p, sIn, sOut⟩ :: suffix` with the pair
absent — in **either** direction — from `pre`.  This is the induction-friendly equivalent of
`trace.idxOf ⟨p, sIn, sOut⟩ < trace.idxOf ⟨p⁻¹, sOut, sIn⟩`. -/
def PermutationForwardFirst
    (trace : DuplexSpongeTrace StmtIn U)
    (sIn sOut : CanonicalSpongeState U) : Prop :=
  ∃ pre suffix,
    trace = pre ++
      (⟨.inr (.inl sIn), sOut⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :: suffix ∧
    (sIn, sOut) ∉ normalizedPermutationPairs pre

omit [DecidableEq StmtIn] [DecidableEq U] in
@[simp] lemma normalizedPermutationPairs_cons
    (e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
    (l : DuplexSpongeTrace StmtIn U) :
    normalizedPermutationPairs (e :: l)
      = (normalizedPermutationPair? e).toList ++ normalizedPermutationPairs l := by
  simp only [normalizedPermutationPairs, List.filterMap_cons]
  cases normalizedPermutationPair? e <;> simp

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A forward-first witness is stable when more raw queries are appended. -/
lemma PermutationForwardFirst.append
    {trace : DuplexSpongeTrace StmtIn U} {sIn sOut : CanonicalSpongeState U}
    (h : PermutationForwardFirst trace sIn sOut) (tail : DuplexSpongeTrace StmtIn U) :
    PermutationForwardFirst (trace ++ tail) sIn sOut := by
  rcases h with ⟨pre, suffix, hTrace, hFresh⟩
  refine ⟨pre, suffix ++ tail, ?_, hFresh⟩
  rw [hTrace]
  simp only [List.append_assoc, List.cons_append]

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- The head occurrence of a forward query is forward-first. -/
lemma PermutationForwardFirst.cons_head
    {sIn sOut : CanonicalSpongeState U} (rest : DuplexSpongeTrace StmtIn U) :
    PermutationForwardFirst
      ((⟨.inr (.inl sIn), sOut⟩ :
        duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :: rest) sIn sOut :=
  ⟨[], rest, rfl, by simp [normalizedPermutationPairs]⟩

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- An entry that does not normalize to `(sIn, sOut)` is transparent for forward-firstness. -/
lemma PermutationForwardFirst.cons_of_ne
    {sIn sOut : CanonicalSpongeState U}
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    (he : normalizedPermutationPair? e ≠ some (sIn, sOut))
    (rest : DuplexSpongeTrace StmtIn U) :
    PermutationForwardFirst (e :: rest) sIn sOut ↔ PermutationForwardFirst rest sIn sOut := by
  constructor
  · rintro ⟨pre, suffix, hTrace, hFresh⟩
    cases pre with
    | nil =>
        exact absurd (by
          have : e = (⟨.inr (.inl sIn), sOut⟩ :
              duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
            simpa using (List.cons.inj hTrace).1
          rw [this]; rfl) he
    | cons e' pre' =>
        rw [List.cons_append] at hTrace
        refine ⟨pre', suffix, (List.cons.inj hTrace).2, ?_⟩
        rw [normalizedPermutationPairs_cons] at hFresh
        exact fun hmem => hFresh (List.mem_append_right _ hmem)
  · rintro ⟨pre, suffix, hTrace, hFresh⟩
    refine ⟨e :: pre, suffix, by rw [hTrace]; rfl, ?_⟩
    simpa only [normalizedPermutationPairs_cons, List.mem_append, Option.mem_toList,
      not_or, he, false_or, not_false_eq_true, true_and] using hFresh

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- A leading inverse occurrence blocks forward-firstness for that pair. -/
lemma PermutationForwardFirst.not_cons_inv
    {sIn sOut : CanonicalSpongeState U} (rest : DuplexSpongeTrace StmtIn U) :
    ¬ PermutationForwardFirst
      ((⟨.inr (.inr sOut), sIn⟩ :
        duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :: rest) sIn sOut := by
  rintro ⟨pre, suffix, hTrace, hFresh⟩
  cases pre with
  | nil => exact absurd (List.cons.inj hTrace).1 (by simp)
  | cons e' pre' =>
      rw [List.cons_append] at hTrace
      have he' : e' = (⟨.inr (.inr sOut), sIn⟩ :
          duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := ((List.cons.inj hTrace).1).symm
      subst he'
      exact hFresh (by
        rw [normalizedPermutationPairs_cons]
        exact List.mem_append_left _ (by simp [normalizedPermutationPair?]))

/-- Executable form of `PermutationForwardFirst`: find the first raw occurrence of the normalized
pair `(sIn, sOut)` and check that it is the forward one. -/
def isPermutationForwardFirst
    (trace : DuplexSpongeTrace StmtIn U) (sIn sOut : CanonicalSpongeState U) : Bool :=
  match trace with
  | [] => false
  | e :: rest =>
      if normalizedPermutationPair? e = some (sIn, sOut) then
        decide (e = (⟨.inr (.inl sIn), sOut⟩ :
          duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
      else
        isPermutationForwardFirst rest sIn sOut

/-- The executable check decides the paper-facing predicate. -/
lemma isPermutationForwardFirst_eq_true_iff
    (trace : DuplexSpongeTrace StmtIn U) (sIn sOut : CanonicalSpongeState U) :
    isPermutationForwardFirst trace sIn sOut = true
      ↔ PermutationForwardFirst trace sIn sOut := by
  induction trace with
  | nil =>
      simp only [isPermutationForwardFirst, Bool.false_eq_true, false_iff]
      rintro ⟨pre, suffix, hTrace, -⟩
      exact absurd hTrace.symm (List.append_ne_nil_of_right_ne_nil pre (by simp))
  | cons e rest ih =>
      rw [isPermutationForwardFirst]
      by_cases hnp : normalizedPermutationPair? e = some (sIn, sOut)
      · rw [ite_eq_left hnp]
        rcases e with ⟨q, answer⟩
        rcases q with stmt | a | b
        · simp [normalizedPermutationPair?] at hnp
        · have ha : a = sIn ∧ answer = sOut := by
            simpa [normalizedPermutationPair?, Prod.ext_iff] using hnp
          obtain ⟨ha1, ha2⟩ := ha
          subst ha1; subst ha2
          simpa using PermutationForwardFirst.cons_head (StmtIn := StmtIn) rest
        · have hb : answer = sIn ∧ b = sOut := by
            simpa [normalizedPermutationPair?, Prod.ext_iff] using hnp
          obtain ⟨hb1, hb2⟩ := hb
          subst hb1; subst hb2
          have hne : (⟨.inr (.inr b), answer⟩ :
              duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
              ≠ ⟨.inr (.inl answer), b⟩ := by simp
          rw [decide_eq_false hne]
          simp only [Bool.false_eq_true, false_iff]
          exact PermutationForwardFirst.not_cons_inv (StmtIn := StmtIn) rest
      · rw [ite_eq_right hnp, ih, PermutationForwardFirst.cons_of_ne hnp]

/-! ### The forward-first sub-index of `tr_∇.p` -/

section ForwardPermutationSubindex

variable {T : Type}
  [LawfulTraceTable T (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- Supporting definition for **[CO25, §5.2]**. Rebuild `p` keeping only the mappings whose first
raw occurrence in `trace` is a forward `p` query. When nothing has to be dropped the caller's table
is returned verbatim, which is what makes the wrapper a no-op on inverse-free traces
(`buildForwardPermutationIndex_eq_self`).

This is the executable `BackTrack` candidate source. The bidirectional table also contains
inverse-first pairs, which can introduce competing predecessors into the single-chain scan.
Filtering by occurrence order excludes those candidates; it does not assert that an
inverse-first pair can never belong to a hash-anchored chain. -/
def buildForwardPermutationIndex
    (trace : DuplexSpongeTrace StmtIn U) (p : T) : T :=
  if (TraceTableOps.entries (V := CanonicalSpongeState U) p).all
      (fun pair => isPermutationForwardFirst trace pair.1 pair.2) then
    p
  else
    TraceTableOps.addAll (TraceTableOps.empty : T)
      ((TraceTableOps.entries (V := CanonicalSpongeState U) p).filter
        (fun pair => isPermutationForwardFirst trace pair.1 pair.2))

/-- Characterization of the forward-first sub-index: it keeps exactly the forward-first pairs. -/
lemma mem_entries_buildForwardPermutationIndex
    (trace : DuplexSpongeTrace StmtIn U) (p : T)
    (pair : CanonicalSpongeState U × CanonicalSpongeState U) :
    pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U)
        (buildForwardPermutationIndex (T := T) trace p)
      ↔ pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) p ∧
          PermutationForwardFirst trace pair.1 pair.2 := by
  unfold buildForwardPermutationIndex
  split
  · next hall =>
      rw [List.all_eq_true] at hall
      constructor
      · exact fun h => ⟨h, (isPermutationForwardFirst_eq_true_iff _ _ _).mp (hall _ h)⟩
      · exact fun h => h.1
  · rw [TraceTableOps.mem_entries_addAll, List.mem_filter]
    simp only [TraceTableOps.not_mem_entries_empty, or_false]
    exact and_congr_right fun _ => isPermutationForwardFirst_eq_true_iff _ _ _

/-- On a table all of whose pairs are forward-first, the sub-index is the table itself. -/
lemma buildForwardPermutationIndex_eq_self
    {trace : DuplexSpongeTrace StmtIn U} {p : T}
    (hfwd : ∀ pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) p,
      PermutationForwardFirst trace pair.1 pair.2) :
    buildForwardPermutationIndex (T := T) trace p = p := by
  unfold buildForwardPermutationIndex
  rw [ite_eq_left]
  rw [List.all_eq_true]
  exact fun pair hmem => (isPermutationForwardFirst_eq_true_iff _ _ _).mpr (hfwd pair hmem)

end ForwardPermutationSubindex

/-- Replacing `tr_∇.p` by its forward-first sub-index preserves provenance. -/
lemma TraceNabla.IsSubsetOfQueryLog.forwardIndex
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (h : trΔ.IsSubsetOfQueryLog trace) :
    ({ trΔ with p := buildForwardPermutationIndex trace trΔ.p } :
      TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog trace :=
  ⟨h.1, fun s_in s_out hmem =>
    h.2 s_in s_out
      ((mem_entries_buildForwardPermutationIndex trace trΔ.p (s_in, s_out)).mp hmem).1⟩

/-- The operational trace-index invariant needed by `BackTrack` and `LookAhead`.

Unlike an exact index, this predicate deliberately does not require every raw trace entry to be
represented in `trΔ`: `D2SQuery`'s live table omits cache-pop realizations, while StdTrace's table
omits inverse-only entries.  What the executable searches need is exactly

* provenance: every stored pair really occurs in the source trace; and
* normalization: an identical stored pair occurs at most once, so multiplicity alone cannot turn
  a lookup into a spurious conflict. -/
structure TraceNabla.IsNormalizedSubindex
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop where
  isSubset : trΔ.IsSubsetOfQueryLog trace
  hash_nodup : (TraceTableOps.entries (V := Vector U SpongeSize.C) trΔ.h).Nodup
  permutation_nodup : (TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p).Nodup

/-- The common proof-side fold step of the bidirectional and forward-only indices. -/
private def traceIndexStep (includeInverse : Bool)
    (acc : TraceNabla T_H T_P StmtIn U)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    TraceNabla T_H T_P StmtIn U :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ => { acc with h := TraceTableOps.insert acc.h stmt capSeg }
  | ⟨.inr (.inl sIn), sOut⟩ => { acc with p := TraceTableOps.insert acc.p sIn sOut }
  | ⟨.inr (.inr sOut), sIn⟩ =>
      if includeInverse then { acc with p := TraceTableOps.insert acc.p sIn sOut } else acc

/-- Joint membership certificate for either index: hash entries are unchanged by the choice;
permutation entries include inverse occurrences exactly when requested. Initial entries remain. -/
private lemma index_fold_membership (includeInverse : Bool)
    (trace : DuplexSpongeTrace StmtIn U) (init : TraceNabla T_H T_P StmtIn U) :
    (∀ stmt cap, (stmt, cap) ∈ TraceTableOps.entries
        (trace.foldl (traceIndexStep includeInverse) init).h ↔
      (stmt, cap) ∈ TraceTableOps.entries init.h ∨ ⟨dsHashQuery stmt, cap⟩ ∈ trace) ∧
    (∀ a b, (a, b) ∈ TraceTableOps.entries
        (trace.foldl (traceIndexStep includeInverse) init).p ↔
      (a, b) ∈ TraceTableOps.entries init.p ∨ ⟨dsPermQuery a, b⟩ ∈ trace ∨
        includeInverse = true ∧ ⟨dsPermInvQuery b, a⟩ ∈ trace) := by
  induction trace generalizing init with
  | nil => simp
  | cons entry trace ih =>
      rcases entry with ⟨q, ans⟩
      rcases q with stmt | sIn | sOut
      all_goals
        simp only [List.foldl_cons]
        obtain ⟨hh, hp⟩ := ih (traceIndexStep includeInverse init ⟨_, ans⟩)
        constructor
        · intro x cap
          rw [hh]
          cases includeInverse <;>
            simp [traceIndexStep, TraceTableOps.mem_entries_insert_iff, dsHashQuery] <;> tauto
        · intro a b
          rw [hp]
          cases includeInverse <;>
            simp [traceIndexStep, TraceTableOps.mem_entries_insert_iff,
              dsPermQuery, dsPermInvQuery] <;> tauto

lemma TraceNabla.ofQueryLog_isSubset
    (trace : DuplexSpongeTrace StmtIn U) :
    (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace).IsSubsetOfQueryLog trace := by
  obtain ⟨hh, hp⟩ := index_fold_membership true trace
    (⟨TraceTableOps.empty, TraceTableOps.empty⟩ : TraceNabla T_H T_P StmtIn U)
  simp only [TraceTableOps.not_mem_entries_empty, false_or, true_and] at hh hp
  exact ⟨fun stmt cap hmem => (hh stmt cap).mp hmem, fun a b hmem => (hp a b).mp hmem⟩

/-- The forward-only index records exactly the hash and permutation occurrences of its
raw trace. Inverse occurrences add no permutation pairs; repeated identical occurrences have the
table's usual set semantics. -/
lemma TraceNabla.mem_entries_ofQueryLogForwardOnly
    (trace : DuplexSpongeTrace StmtIn U) :
    (∀ stmt cap, (stmt, cap) ∈ TraceTableOps.entries
        (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace).h ↔
      ⟨dsHashQuery stmt, cap⟩ ∈ trace) ∧
    (∀ a b, (a, b) ∈ TraceTableOps.entries
        (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace).p ↔
      ⟨dsPermQuery a, b⟩ ∈ trace) := by
  have hfold : TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace =
      trace.foldl (traceIndexStep false) ⟨TraceTableOps.empty, TraceTableOps.empty⟩ := by
    unfold TraceNabla.ofQueryLogForwardOnly
    congr 1
  rw [hfold]
  simpa only [TraceTableOps.not_mem_entries_empty, false_or, Bool.false_eq_true,
    false_and, or_false] using index_fold_membership false trace
      (⟨TraceTableOps.empty, TraceTableOps.empty⟩ : TraceNabla T_H T_P StmtIn U)

lemma TraceNabla.ofQueryLogForwardOnly_isSubset
    (trace : DuplexSpongeTrace StmtIn U) :
    (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace).IsSubsetOfQueryLog
      trace := by
  have h := TraceNabla.mem_entries_ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace
  exact ⟨fun stmt cap hmem => (h.1 stmt cap).mp hmem,
    fun a b hmem => Or.inl ((h.2 a b).mp hmem)⟩

end TraceDataStructures

end DSTraceStorage

end DuplexSpongeFS
