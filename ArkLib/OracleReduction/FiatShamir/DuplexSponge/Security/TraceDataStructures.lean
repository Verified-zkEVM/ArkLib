/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# CO25 Definition 5.2 — Trace data structures

Generic trace-table interface for the duplex-sponge simulator's `tr_∇` (CO25 Definition 5.2),
together with a list-backed default instantiation and refinement-model laws via `Multiset`.

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

- `DuplexSpongeTrace` — type alias for the paper's `(h, p, p⁻¹)`-trace (CO25 Definition 5.2).
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

/-- Set-semantic insertion for `tr_∇`. The query log retains every occurrence, whereas the
internal table records an already-present normalized pair only once. -/
def TraceTableOps.insert {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) : T :=
  if (k, v) ∈ TraceTableOps.entries t then t else TraceTableOps.add t k v

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

/-- Set-semantic insertion adds membership for the requested pair and preserves all old pairs. -/
lemma TraceTableOps.mem_toMultiSet_insert_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ LawfulTraceTable.toMultiSet (TraceTableOps.insert t k v) ↔
      pair = (k, v) ∨ pair ∈ LawfulTraceTable.toMultiSet t := by
  by_cases hmem : (k, v) ∈ TraceTableOps.entries t
  · have hmem' : (k, v) ∈ LawfulTraceTable.toMultiSet t := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hmem
    simp only [TraceTableOps.insert, hmem, if_pos]
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact hmem'
      · exact h
  · simp [TraceTableOps.insert, hmem, LawfulTraceTable.toMultiSet_add]

/-- Public-entry membership has the same set-union behavior under `insert`. -/
lemma TraceTableOps.mem_entries_insert_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.insert t k v) ↔
      pair = (k, v) ∨ pair ∈ TraceTableOps.entries t := by
  constructor
  · intro h
    have hms : pair ∈ LawfulTraceTable.toMultiSet (TraceTableOps.insert t k v) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr h
    rw [TraceTableOps.mem_toMultiSet_insert_iff] at hms
    rcases hms with rfl | hOld
    · exact Or.inl rfl
    · exact Or.inr (Multiset.mem_coe.mp
        ((LawfulTraceTable.toMultiSet_ofEntries t).symm ▸ hOld))
  · rintro (rfl | hOld)
    · apply Multiset.mem_coe.mp
      rw [LawfulTraceTable.toMultiSet_ofEntries,
        TraceTableOps.mem_toMultiSet_insert_iff]
      exact Or.inl rfl
    · apply Multiset.mem_coe.mp
      rw [LawfulTraceTable.toMultiSet_ofEntries,
        TraceTableOps.mem_toMultiSet_insert_iff]
      right
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr hOld

/-- Inserting a normalized pair already represented by the table is a no-op. -/
lemma TraceTableOps.insert_eq_self_of_mem
    {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) (h : (k, v) ∈ TraceTableOps.entries t) :
    TraceTableOps.insert t k v = t := by
  simp [TraceTableOps.insert, h]

/-- Inserting the same normalized pair twice is idempotent. -/
lemma TraceTableOps.insert_idem
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) :
    TraceTableOps.insert (TraceTableOps.insert t k v) k v = TraceTableOps.insert t k v := by
  apply TraceTableOps.insert_eq_self_of_mem
  exact (TraceTableOps.mem_entries_insert_iff t k v (k, v)).mpr (Or.inl rfl)

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

/-- The simulator's trace table `tr_∇` from CO25 Definition 5.2, generic over any lawful
implementation.

- `h : T_H` — hash-query table (`tr_∇.h`): maps `StmtIn` to capacity segments.
- `p : T_P` — permutation table (`tr_∇.p`): bidirectional map over sponge states.

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

/-- Build a `TraceNabla` from a `DuplexSpongeTrace` (CO25 Definition 5.2).

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

/-- Build the `tr_∇` used by CO25 StdTrace §5.5.1 Step 3.

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

/-- Regression for occurrence replay: two adjacent identical log entries have the same normalized
bidirectional `tr_∇` as one occurrence. -/
lemma TraceNabla.ofQueryLog_duplicate_head
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
    (trace : DuplexSpongeTrace StmtIn U) :
    TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) (entry :: entry :: trace) =
      TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) (entry :: trace) := by
  rcases entry with ⟨q, answer⟩
  rcases q with stmt | stateIn | stateOut
  · simp only [TraceNabla.ofQueryLog, List.foldl_cons]
    rw [TraceTableOps.insert_idem]
  · simp only [TraceNabla.ofQueryLog, List.foldl_cons]
    rw [TraceTableOps.insert_idem]
  · simp only [TraceNabla.ofQueryLog, List.foldl_cons]
    rw [TraceTableOps.insert_idem]

/-- The forward-only StdTrace constructor likewise coalesces repeated identical occurrences. -/
lemma TraceNabla.ofQueryLogForwardOnly_duplicate_head
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))
    (trace : DuplexSpongeTrace StmtIn U) :
    TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) (entry :: entry :: trace) =
      TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) (entry :: trace) := by
  rcases entry with ⟨q, answer⟩
  rcases q with stmt | stateIn | stateOut
  · simp only [TraceNabla.ofQueryLogForwardOnly, List.foldl_cons]
    rw [TraceTableOps.insert_idem]
  · simp only [TraceNabla.ofQueryLogForwardOnly, List.foldl_cons]
    rw [TraceTableOps.insert_idem]
  · rfl

def TraceNabla.IsSubsetOfQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, (stmt, cap) ∈ TraceTableOps.entries trΔ.h → ⟨.inl stmt, cap⟩ ∈ trace) ∧
  (∀ s_in s_out, (s_in, s_out) ∈ TraceTableOps.entries trΔ.p →
    ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace)

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
hash-anchored chain built by the simulator's own forward queries. -/

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

/-- `PermutationForwardFirst trace sIn sOut` — the *first* occurrence of the normalized pair
`(sIn, sOut)` in the raw trace is the forward one `⟨p, sIn, sOut⟩`.

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
        intro hmem
        exact hFresh (by
          have he' : e' = e := ((List.cons.inj hTrace).1).symm
          subst he'
          rw [normalizedPermutationPairs_cons]
          exact List.mem_append_right _ hmem)
  · rintro ⟨pre, suffix, hTrace, hFresh⟩
    refine ⟨e :: pre, suffix, by rw [hTrace]; rfl, ?_⟩
    rw [normalizedPermutationPairs_cons]
    intro hmem
    rcases List.mem_append.mp hmem with hhead | htail
    · refine absurd ?_ he
      cases hnp : normalizedPermutationPair? e with
      | none => rw [hnp] at hhead; simp at hhead
      | some pr =>
          rw [hnp] at hhead
          simp only [Option.toList_some, List.mem_singleton] at hhead
          exact congrArg some hhead.symm
    · exact hFresh htail

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

/-- Decomposition-form forward-first implies the paper's `idxOf` comparison. -/
lemma PermutationForwardFirst.idxOf_lt
    {trace : DuplexSpongeTrace StmtIn U} {sIn sOut : CanonicalSpongeState U}
    (h : PermutationForwardFirst trace sIn sOut) :
    trace.idxOf
        (⟨.inr (.inl sIn), sOut⟩ :
          duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) <
      trace.idxOf
        (⟨.inr (.inr sOut), sIn⟩ :
          duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  let fwd : duplexSpongeTraceEntry (StartType := StmtIn) (U := U) := ⟨.inr (.inl sIn), sOut⟩
  let inv : duplexSpongeTraceEntry (StartType := StmtIn) (U := U) := ⟨.inr (.inr sOut), sIn⟩
  rcases h with ⟨pre, suffix, hTrace, hFresh⟩
  change trace = pre ++ fwd :: suffix at hTrace
  have hFwdNot : fwd ∉ pre := by
    intro hMem
    exact hFresh (List.mem_filterMap.mpr ⟨fwd, hMem, by simp [fwd, normalizedPermutationPair?]⟩)
  have hInvNot : inv ∉ pre := by
    intro hMem
    exact hFresh (List.mem_filterMap.mpr ⟨inv, hMem, by simp [inv, normalizedPermutationPair?]⟩)
  have hNe : fwd ≠ inv := by simp [fwd, inv]
  change trace.idxOf fwd < trace.idxOf inv
  rw [hTrace, List.idxOf_append_of_notMem hFwdNot, List.idxOf_append_of_notMem hInvNot]
  simp [hNe]

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
      · rw [if_pos hnp]
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
      · rw [if_neg hnp, ih, PermutationForwardFirst.cons_of_ne hnp]

instance PermutationForwardFirst.decidable
    (trace : DuplexSpongeTrace StmtIn U) (sIn sOut : CanonicalSpongeState U) :
    Decidable (PermutationForwardFirst trace sIn sOut) :=
  decidable_of_iff (isPermutationForwardFirst trace sIn sOut = true)
    (isPermutationForwardFirst_eq_true_iff trace sIn sOut)

/-- `trace` records no `p⁻¹` occurrence at all.  This is the typical way a consumer discharges
the forward-first side condition: the honest verifier walk and the rate-only simulator walks
never issue an inverse permutation query. -/
def HasNoInversePermQuery (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  ∀ sOut sIn : CanonicalSpongeState U,
    (⟨.inr (.inr sOut), sIn⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∉ trace

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- The empty trace has no inverse occurrence. -/
lemma HasNoInversePermQuery.nil :
    HasNoInversePermQuery (StmtIn := StmtIn) (U := U) [] := by
  intro _ _ h
  exact absurd h (by simp)

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- Appending a non-inverse occurrence preserves inverse-freeness. -/
lemma HasNoInversePermQuery.append_of_ne
    {trace : DuplexSpongeTrace StmtIn U} (h : HasNoInversePermQuery (StmtIn := StmtIn) trace)
    {e : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)}
    (he : ∀ sOut sIn, e ≠ (⟨.inr (.inr sOut), sIn⟩ :
      duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) :
    HasNoInversePermQuery (StmtIn := StmtIn) (trace ++ [e]) := by
  intro sOut sIn hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact h sOut sIn hold
  · exact he sOut sIn (List.mem_singleton.mp hnew).symm

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- Appending a hash occurrence preserves inverse-freeness. -/
lemma HasNoInversePermQuery.append_hash
    {trace : DuplexSpongeTrace StmtIn U} (h : HasNoInversePermQuery (StmtIn := StmtIn) trace)
    (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    HasNoInversePermQuery (StmtIn := StmtIn)
      (trace ++ [(⟨.inl stmt, cap⟩ : duplexSpongeTraceEntry (StartType := StmtIn) (U := U))]) :=
  h.append_of_ne (by intro _ _ hc; exact absurd hc (by simp))

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- Appending a forward permutation occurrence preserves inverse-freeness. -/
lemma HasNoInversePermQuery.append_perm
    {trace : DuplexSpongeTrace StmtIn U} (h : HasNoInversePermQuery (StmtIn := StmtIn) trace)
    (sIn sOut : CanonicalSpongeState U) :
    HasNoInversePermQuery (StmtIn := StmtIn)
      (trace ++ [(⟨.inr (.inl sIn), sOut⟩ :
        duplexSpongeTraceEntry (StartType := StmtIn) (U := U))]) :=
  h.append_of_ne (by intro _ _ hc; exact absurd hc (by simp))

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- On an inverse-free trace every recorded forward occurrence is forward-first. -/
lemma PermutationForwardFirst.of_hasNoInversePermQuery
    {trace : DuplexSpongeTrace StmtIn U} (hno : HasNoInversePermQuery (StmtIn := StmtIn) trace)
    {sIn sOut : CanonicalSpongeState U}
    (hmem : (⟨.inr (.inl sIn), sOut⟩ :
      duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∈ trace) :
    PermutationForwardFirst trace sIn sOut := by
  induction trace with
  | nil => exact absurd hmem (by simp)
  | cons e rest ih =>
      by_cases hnp : normalizedPermutationPair? e = some (sIn, sOut)
      · rcases e with ⟨q, answer⟩
        rcases q with stmt | a | b
        · simp [normalizedPermutationPair?] at hnp
        · obtain ⟨rfl, rfl⟩ : a = sIn ∧ answer = sOut := by
            simpa [normalizedPermutationPair?, Prod.ext_iff] using hnp
          exact PermutationForwardFirst.cons_head (StmtIn := StmtIn) rest
        · exact absurd (List.mem_cons_self ..) (hno b answer)
      · rw [PermutationForwardFirst.cons_of_ne hnp]
        refine ih (fun a b hb => hno a b (List.mem_cons_of_mem _ hb)) ?_
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (by rw [← h]; rfl) hnp
        · exact h

/-! ### The forward-first sub-index of `tr_∇.p` -/

section ForwardPermutationSubindex

variable {T : Type}
  [LawfulTraceTable T (CanonicalSpongeState U) (CanonicalSpongeState U)]

/-- Rebuild `p` keeping only the mappings whose first raw occurrence in `trace` is a forward
`p` query.  When nothing has to be dropped the caller's table is returned verbatim, which is
what makes the wrapper a no-op on inverse-free traces (`buildForwardPermutationIndex_eq_self`).

This is `BackTrack`'s Step 2(b) candidate source after FIX-BT: the bidirectional `tr_∇.p` also
records the `(s_in, s_out)` pair created by an adversarially chosen `p⁻¹` query, and such a pair
can never sit on a hash-anchored chain (CO25 Def. 5.3(b)), yet it does branch the executable
single-chain scan. -/
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
  rw [if_pos]
  rw [List.all_eq_true]
  exact fun pair hmem => (isPermutationForwardFirst_eq_true_iff _ _ _).mpr (hfwd pair hmem)

/-- The sub-index inherits duplicate-freeness. -/
lemma buildForwardPermutationIndex_nodup
    (trace : DuplexSpongeTrace StmtIn U) {p : T}
    (hnodup : (TraceTableOps.entries (V := CanonicalSpongeState U) p).Nodup) :
    (TraceTableOps.entries (V := CanonicalSpongeState U)
      (buildForwardPermutationIndex (T := T) trace p)).Nodup := by
  unfold buildForwardPermutationIndex
  split
  · exact hnodup
  · rw [TraceTableOps.entries_nodup_iff, TraceTableOps.toMultiSet_addAll,
      LawfulTraceTable.toMultiSet_empty, add_zero, Multiset.coe_nodup]
    exact hnodup.filter _

end ForwardPermutationSubindex

/-- Every pair of a provenance-correct `tr_∇.p` is forward-first when the trace has no `p⁻¹`
occurrence at all. -/
lemma TraceNabla.forwardFirst_entries_of_hasNoInversePermQuery
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hno : HasNoInversePermQuery (StmtIn := StmtIn) trace)
    (hsub : trΔ.IsSubsetOfQueryLog trace) :
    ∀ pair ∈ TraceTableOps.entries (V := CanonicalSpongeState U) trΔ.p,
      PermutationForwardFirst trace pair.1 pair.2 := by
  intro pair hmem
  rcases hsub.2 pair.1 pair.2 (by simpa using hmem) with hfwd | hinv
  · exact PermutationForwardFirst.of_hasNoInversePermQuery hno hfwd
  · exact absurd hinv (hno _ _)

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

/-- The forward-first sub-index preserves the operational trace-index invariant. -/
lemma TraceNabla.IsNormalizedSubindex.forwardIndex
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (h : trΔ.IsNormalizedSubindex trace) :
    ({ trΔ with p := buildForwardPermutationIndex trace trΔ.p } :
      TraceNabla T_H T_P StmtIn U).IsNormalizedSubindex trace :=
  ⟨h.isSubset.forwardIndex, h.hash_nodup,
    buildForwardPermutationIndex_nodup trace h.permutation_nodup⟩


/-- The fold step from `TraceNabla.ofQueryLog`, factored out for reuse in proofs. -/
private def ofQueryLogStep
    (acc : TraceNabla T_H T_P StmtIn U)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    TraceNabla T_H T_P StmtIn U :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      { acc with h := TraceTableOps.insert acc.h stmt capSeg }
  | ⟨.inr (.inl sIn), sOut⟩ =>
      { acc with p := TraceTableOps.insert acc.p sIn sOut }
  | ⟨.inr (.inr sOut), sIn⟩ =>
      { acc with p := TraceTableOps.insert acc.p sIn sOut }

private lemma ofQueryLog_eq_foldl
    (trace : DuplexSpongeTrace StmtIn U) :
    TraceNabla.ofQueryLog trace =
      List.foldl ofQueryLogStep
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace := by
  rfl

/-- After processing a trace list via the fold step, every entry in the hash multiset
either came from the init or from a hash query in the trace. -/
private lemma hash_ms_foldl_inv
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    (p : StmtIn × Vector U SpongeSize.C)
    (hp : p ∈ LawfulTraceTable.toMultiSet
      (List.foldl ofQueryLogStep init trace).h) :
    p ∈ LawfulTraceTable.toMultiSet init.h ∨ ⟨.inl p.1, p.2⟩ ∈ trace := by
  induction trace generalizing init with
  | nil =>
    simp only [List.foldl_nil] at hp
    exact Or.inl hp
  | cons entry trace' ih =>
    simp only [List.foldl_cons] at hp
    rcases entry with ⟨q, a⟩
    rcases q with stmt' | sIn' | sOut'
    -- Hash query: adds (stmt', a) to h
    case inl =>
      simp only [ofQueryLogStep] at hp
      have hIH := ih {init with h := TraceTableOps.insert init.h stmt' a} hp
      have : ({init with h := TraceTableOps.insert init.h stmt' a} :
          TraceNabla T_H T_P StmtIn U).h = TraceTableOps.insert init.h stmt' a := rfl
      rw [this] at hIH
      rcases hIH with hMem | hIn
      · rw [TraceTableOps.mem_toMultiSet_insert_iff] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; right; exact .head ..
        · exact Or.inl hRest
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    -- Forward perm: h unchanged
    case inr.inl =>
      simp only [ofQueryLogStep] at hp
      rcases ih {init with p := TraceTableOps.insert init.p sIn' a} hp with hMem | hIn
      · exact Or.inl hMem
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    -- Inverse perm: h unchanged
    case inr.inr =>
      simp only [ofQueryLogStep] at hp
      rcases ih {init with p := TraceTableOps.insert init.p a sOut'} hp with hMem | hIn
      · exact Or.inl hMem
      · exact Or.inr (List.mem_cons_of_mem _ hIn)

/-- After processing a trace list via the fold step, every entry in the perm multiset
either came from the init or from a permutation query in the trace. -/
private lemma perm_ms_foldl_inv
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    (p : CanonicalSpongeState U × CanonicalSpongeState U)
    (hp : p ∈ LawfulTraceTable.toMultiSet
      (List.foldl ofQueryLogStep init trace).p) :
    p ∈ LawfulTraceTable.toMultiSet init.p ∨
      ⟨.inr (.inl p.1), p.2⟩ ∈ trace ∨
        ⟨.inr (.inr p.2), p.1⟩ ∈ trace := by
  induction trace generalizing init with
  | nil =>
    simp only [List.foldl_nil] at hp
    exact Or.inl hp
  | cons entry trace' ih =>
    simp only [List.foldl_cons] at hp
    rcases entry with ⟨q, a⟩
    rcases q with stmt' | sIn' | sOut'
    -- Hash query: p unchanged
    case inl =>
      simp only [ofQueryLogStep] at hp
      rcases ih {init with h := TraceTableOps.insert init.h stmt' a} hp with hMem | h1 | h2
      · exact Or.inl hMem
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    -- Forward perm: adds (sIn', a) to p
    case inr.inl =>
      simp only [ofQueryLogStep] at hp
      have hIH := ih {init with p := TraceTableOps.insert init.p sIn' a} hp
      have : ({init with p := TraceTableOps.insert init.p sIn' a} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.insert init.p sIn' a := rfl
      rw [this] at hIH
      rcases hIH with hMem | hIn
      · rw [TraceTableOps.mem_toMultiSet_insert_iff] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; exact Or.inr (Or.inl (by exact .head ..))
        · exact Or.inl hRest
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    -- Inverse perm: adds (a, sOut') to p
    case inr.inr =>
      simp only [ofQueryLogStep] at hp
      have hIH := ih {init with p := TraceTableOps.insert init.p a sOut'} hp
      have : ({init with p := TraceTableOps.insert init.p a sOut'} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.insert init.p a sOut' := rfl
      rw [this] at hIH
      rcases hIH with hMem | hIn
      · rw [TraceTableOps.mem_toMultiSet_insert_iff] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; exact Or.inr (Or.inr (by exact .head ..))
        · exact Or.inl hRest
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))

lemma TraceNabla.ofQueryLog_isSubset
    (trace : DuplexSpongeTrace StmtIn U) :
    (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace).IsSubsetOfQueryLog trace := by
  constructor
  · intro stmt cap hMem
    rw [ofQueryLog_eq_foldl] at hMem
    have hMS : (stmt, cap) ∈ LawfulTraceTable.toMultiSet
        (List.foldl ofQueryLogStep
          ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).h := by
      have h := LawfulTraceTable.toMultiSet_ofEntries
          (List.foldl ofQueryLogStep
            ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).h
      rw [← h]; exact Multiset.mem_coe.mpr hMem
    rcases hash_ms_foldl_inv
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace
        (stmt, cap) hMS with hMem' | hIn
    · simp [LawfulTraceTable.toMultiSet_empty] at hMem'
    · exact hIn
  · intro s_in s_out hMem
    rw [ofQueryLog_eq_foldl] at hMem
    have hMS : (s_in, s_out) ∈ LawfulTraceTable.toMultiSet
        (List.foldl ofQueryLogStep
          ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).p := by
      have h := LawfulTraceTable.toMultiSet_ofEntries
          (List.foldl ofQueryLogStep
            ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).p
      rw [← h]; exact Multiset.mem_coe.mpr hMem
    rcases perm_ms_foldl_inv
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace
        (s_in, s_out) hMS with hMem' | h1 | h2
    · simp [LawfulTraceTable.toMultiSet_empty] at hMem'
    · exact Or.inl h1
    · exact Or.inr h2

private def ofQueryLogForwardOnlyStep
    (acc : TraceNabla T_H T_P StmtIn U)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    TraceNabla T_H T_P StmtIn U :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      { acc with h := TraceTableOps.insert acc.h stmt capSeg }
  | ⟨.inr (.inl sIn), sOut⟩ =>
      { acc with p := TraceTableOps.insert acc.p sIn sOut }
  | ⟨.inr (.inr _), _⟩ => acc

private lemma ofQueryLogForwardOnly_eq_foldl
    (trace : DuplexSpongeTrace StmtIn U) :
    TraceNabla.ofQueryLogForwardOnly trace =
      List.foldl ofQueryLogForwardOnlyStep
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace := by
  rfl

private lemma hash_ms_foldl_fwd_inv
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    (p : StmtIn × Vector U SpongeSize.C)
    (hp : p ∈ LawfulTraceTable.toMultiSet
      (List.foldl ofQueryLogForwardOnlyStep init trace).h) :
    p ∈ LawfulTraceTable.toMultiSet init.h ∨ ⟨.inl p.1, p.2⟩ ∈ trace := by
  induction trace generalizing init with
  | nil =>
    simp only [List.foldl_nil] at hp
    exact Or.inl hp
  | cons entry trace' ih =>
    simp only [List.foldl_cons] at hp
    rcases entry with ⟨q, a⟩
    rcases q with stmt' | sIn' | sOut'
    case inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      have hIH := ih {init with h := TraceTableOps.insert init.h stmt' a} hp
      have : ({init with h := TraceTableOps.insert init.h stmt' a} :
          TraceNabla T_H T_P StmtIn U).h = TraceTableOps.insert init.h stmt' a := rfl
      rw [this] at hIH
      rcases hIH with hMem | hIn
      · rw [TraceTableOps.mem_toMultiSet_insert_iff] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; right; exact .head ..
        · exact Or.inl hRest
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    case inr.inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      rcases ih {init with p := TraceTableOps.insert init.p sIn' a} hp with hMem | hIn
      · exact Or.inl hMem
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    case inr.inr =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      rcases ih init hp with hMem | hIn
      · exact Or.inl hMem
      · exact Or.inr (List.mem_cons_of_mem _ hIn)

private lemma perm_ms_foldl_fwd_inv
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    (p : CanonicalSpongeState U × CanonicalSpongeState U)
    (hp : p ∈ LawfulTraceTable.toMultiSet
      (List.foldl ofQueryLogForwardOnlyStep init trace).p) :
    p ∈ LawfulTraceTable.toMultiSet init.p ∨
      ⟨.inr (.inl p.1), p.2⟩ ∈ trace ∨
        ⟨.inr (.inr p.2), p.1⟩ ∈ trace := by
  induction trace generalizing init with
  | nil =>
    simp only [List.foldl_nil] at hp
    exact Or.inl hp
  | cons entry trace' ih =>
    simp only [List.foldl_cons] at hp
    rcases entry with ⟨q, a⟩
    rcases q with stmt' | sIn' | sOut'
    case inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      rcases ih {init with h := TraceTableOps.insert init.h stmt' a} hp with hMem | h1 | h2
      · exact Or.inl hMem
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    case inr.inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      have hIH := ih {init with p := TraceTableOps.insert init.p sIn' a} hp
      have : ({init with p := TraceTableOps.insert init.p sIn' a} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.insert init.p sIn' a := rfl
      rw [this] at hIH
      rcases hIH with hMem | hIn
      · rw [TraceTableOps.mem_toMultiSet_insert_iff] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; exact Or.inr (Or.inl (by exact .head ..))
        · exact Or.inl hRest
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    case inr.inr =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      have hIH := ih init hp
      rcases hIH with hMem | hIn
      · exact Or.inl hMem
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))

lemma TraceNabla.ofQueryLogForwardOnly_isSubset
    (trace : DuplexSpongeTrace StmtIn U) :
    (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace).IsSubsetOfQueryLog
      trace := by
  constructor
  · intro stmt cap hMem
    rw [ofQueryLogForwardOnly_eq_foldl] at hMem
    have hMS : (stmt, cap) ∈ LawfulTraceTable.toMultiSet
        (List.foldl ofQueryLogForwardOnlyStep
          ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).h := by
      have h := LawfulTraceTable.toMultiSet_ofEntries
          (List.foldl ofQueryLogForwardOnlyStep
            ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).h
      rw [← h]; exact Multiset.mem_coe.mpr hMem
    rcases hash_ms_foldl_fwd_inv
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace
        (stmt, cap) hMS with hMem' | hIn
    · simp [LawfulTraceTable.toMultiSet_empty] at hMem'
    · exact hIn
  · intro s_in s_out hMem
    rw [ofQueryLogForwardOnly_eq_foldl] at hMem
    have hMS : (s_in, s_out) ∈ LawfulTraceTable.toMultiSet
        (List.foldl ofQueryLogForwardOnlyStep
          ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).p := by
      have h := LawfulTraceTable.toMultiSet_ofEntries
          (List.foldl ofQueryLogForwardOnlyStep
            ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace).p
      rw [← h]; exact Multiset.mem_coe.mpr hMem
    rcases perm_ms_foldl_fwd_inv
        ⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ trace
        (s_in, s_out) hMS with hMem' | h1 | h2
    · simp [LawfulTraceTable.toMultiSet_empty] at hMem'
    · exact Or.inl h1
    · exact Or.inr h2

/-! ### List-backed instantiation -/

namespace ListBacked

/-- Default list-backed implementation for trace tables.
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

omit [SpongeSize] in
@[simp] lemma inlu_identical_duplicate (k : K) (v : V) :
    inlu (⟨[(k, v), (k, v)]⟩ : ListTraceTable K V) k = some v := by
  simp [inlu]

omit [SpongeSize] in
@[simp] lemma outlu_identical_duplicate (k : K) (v : V) :
    outlu (⟨[(k, v), (k, v)]⟩ : ListTraceTable K V) v = some k := by
  simp [outlu]

omit [SpongeSize] in
lemma inlu_distinct_conflict (k : K) (v₁ v₂ : V) (hne : v₁ ≠ v₂) :
    inlu (⟨[(k, v₁), (k, v₂)]⟩ : ListTraceTable K V) k = none := by
  simp [inlu, hne]

omit [SpongeSize] in
lemma outlu_distinct_conflict (k₁ k₂ : K) (v : V) (hne : k₁ ≠ k₂) :
    outlu (⟨[(k₁, v), (k₂, v)]⟩ : ListTraceTable K V) v = none := by
  simp [outlu, hne]

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

/-- The default (list-backed) `tr_∇`. In fact we want to use a more optimized data structure
for efficient storage and query complexity. -/
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
