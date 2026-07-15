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

- `inlu t k = some v` iff `(k, v)` occurs exactly once in the multiset and no conflicting
  value `v'` exists.
- `outlu t v = some k` iff `(k, v)` occurs exactly once in the multiset and no conflicting
  key `k'` exists.

Duplicate entries, even identical duplicate `(k, v)` entries, are treated as multiple matches and
therefore lookup failure, matching CO25 Definition 5.2's sorted-list lookup semantics.

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

/-- Insert a table pair with set semantics.  The generic `add` operation deliberately retains the
underlying implementation's insertion semantics; D2SQuery uses `insert` where the paper requires
`tr_∇` to mirror the *set* of pairs in the external trace. -/
def TraceTableOps.insert {T K V : Type} [TraceTableOps T K V] [DecidableEq K] [DecidableEq V]
    (t : T) (k : K) (v : V) : T :=
  if (k, v) ∈ TraceTableOps.entries t then t else TraceTableOps.add t k v

/-! ### Refinement-model lawful class -/

/-- Refinement-model lawfulness for a trace table, expressed via a `Multiset (K × V)` model.

`toMultiSet` is the abstract mathematical content of the table.
The `inlu`/`outlu` laws state that a lookup succeeds iff the entry exists exactly once and is the
unique value/key match in the multiset; duplicate-entry traces are treated as multiple matches. -/
class LawfulTraceTable (T : Type) (K V : outParam Type) [DecidableEq K] [DecidableEq V]
extends TraceTableOps T K V where
  toMultiSet : T → Multiset (K × V)
  toMultiSet_empty : toMultiSet TraceTableOps.empty = (0 : Multiset (K × V)) := by simp [empty]
  toMultiSet_add : ∀ t k v, toMultiSet (add t k v) = (k, v) ::ₘ toMultiSet t
  -- **inlu's query result MUST BE UNIQUE**, i.e. two copies
    -- of `(k, v)` in the multiset trigger the "multiple" case
  inlu_eq_some : ∀ t k v,
    inlu t k = some v ↔
      (toMultiSet t).count (k, v) = 1 ∧ -- Uniqueness of the whole (query, answer) pair `(k, v)`
      (∀ v', (k, v') ∈ toMultiSet t → v' = v) -- Uniqueness of answer value `v` according
        -- to the query key `k`
  -- **outlu's query result MUST BE UNIQUE**, i.e. two copies
    -- of `(k, v)` in the multiset trigger the "multiple" case
  outlu_eq_some : ∀ t k v,
    outlu t v = some k ↔
      (toMultiSet t).count (k, v) = 1 ∧ -- Uniqueness of the whole (query, answer) pair `(k, v)`
      (∀ k', (k', v) ∈ toMultiSet t → k' = k) -- Uniqueness of query key `k` according
        -- to the query value `v`
  /-- `entries` reflects the abstract multiset content. Order is unspecified; only the multiset
  reading is stable. Used by paper §5.2 partial-key enumeration in `BackTrack`. -/
  toMultiSet_ofEntries : ∀ t, (TraceTableOps.entries t : Multiset (K × V)) = toMultiSet t

/-- Membership after `add`, expressed at the public `entries` interface. -/
lemma TraceTableOps.mem_entries_add_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.add t k v) ↔
      pair = (k, v) ∨ pair ∈ TraceTableOps.entries t := by
  constructor
  · intro h
    have hms : pair ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add t k v) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]
      exact Multiset.mem_coe.mpr h
    rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at hms
    rcases hms with hEq | hOld
    · exact Or.inl hEq
    · right
      rw [← LawfulTraceTable.toMultiSet_ofEntries] at hOld
      exact Multiset.mem_coe.mp hOld
  · rintro (hEq | hOld)
    · subst pair
      have hms : (k, v) ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add t k v) := by
        rw [LawfulTraceTable.toMultiSet_add]
        exact Multiset.mem_cons_self _ _
      rw [← LawfulTraceTable.toMultiSet_ofEntries] at hms
      exact Multiset.mem_coe.mp hms
    · have hms : pair ∈ LawfulTraceTable.toMultiSet t := by
        rw [← LawfulTraceTable.toMultiSet_ofEntries]
        exact Multiset.mem_coe.mpr hOld
      have hnew : pair ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add t k v) := by
        rw [LawfulTraceTable.toMultiSet_add]
        exact Multiset.mem_cons_of_mem hms
      rw [← LawfulTraceTable.toMultiSet_ofEntries] at hnew
      exact Multiset.mem_coe.mp hnew

/-- Membership after idempotent `insert`. -/
lemma TraceTableOps.mem_entries_insert_iff
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) (k : K) (v : V) (pair : K × V) :
    pair ∈ TraceTableOps.entries (TraceTableOps.insert t k v) ↔
      pair = (k, v) ∨ pair ∈ TraceTableOps.entries t := by
  unfold TraceTableOps.insert
  split
  · constructor
    · intro h
      exact Or.inr h
    · rintro (hEq | hOld)
      · subst pair
        assumption
      · exact hOld
  · exact TraceTableOps.mem_entries_add_iff t k v pair

/-- A successful forward lookup certifies that its pair occurs in the public table contents. -/
lemma TraceTableOps.mem_entries_of_inlu_eq_some
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V} (h : TraceTableOps.inlu t k = some v) :
    (k, v) ∈ TraceTableOps.entries t := by
  have hLookup := (LawfulTraceTable.inlu_eq_some t k v).mp h
  apply Multiset.mem_coe.mp
  rw [LawfulTraceTable.toMultiSet_ofEntries]
  exact Multiset.count_pos.mp (by omega)

/-- A successful backward lookup certifies that its normalized pair occurs in the public table
contents. -/
lemma TraceTableOps.mem_entries_of_outlu_eq_some
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V} (h : TraceTableOps.outlu t v = some k) :
    (k, v) ∈ TraceTableOps.entries t := by
  have hLookup := (LawfulTraceTable.outlu_eq_some t k v).mp h
  apply Multiset.mem_coe.mp
  rw [LawfulTraceTable.toMultiSet_ofEntries]
  exact Multiset.count_pos.mp (by omega)

/-- The permutation-table condition that each output has at most one preimage.  It is phrased over
the lawful multiset model because `outlu` is sensitive to multiplicities, not merely membership. -/
def TraceTableOps.OutputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) : Prop :=
  ∀ k k' v,
    (k, v) ∈ LawfulTraceTable.toMultiSet t →
    (k', v) ∈ LawfulTraceTable.toMultiSet t → k' = k

/-- The dual condition that each input has at most one output. -/
def TraceTableOps.InputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    (t : T) : Prop :=
  ∀ k v v',
    (k, v) ∈ LawfulTraceTable.toMultiSet t →
    (k, v') ∈ LawfulTraceTable.toMultiSet t → v' = v

/-- Adding a genuinely new pair preserves multiset nodupness.  This separates the purely
table-theoretic part of the D2SQuery prefix invariant from the trace-level bad-event argument. -/
lemma TraceTableOps.nodup_add
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hFresh : (k, v) ∉ LawfulTraceTable.toMultiSet t) :
    (LawfulTraceTable.toMultiSet (TraceTableOps.add t k v)).Nodup := by
  rw [LawfulTraceTable.toMultiSet_add]
  exact hNodup.cons hFresh

/-- Set-semantic insertion preserves multiset nodupness.  In particular, the cache-pop update
cannot introduce a duplicate table occurrence. -/
lemma TraceTableOps.nodup_insert
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup) :
    (LawfulTraceTable.toMultiSet (TraceTableOps.insert t k v)).Nodup := by
  unfold TraceTableOps.insert
  by_cases hMem : (k, v) ∈ TraceTableOps.entries t
  · simp [hMem, hNodup]
  · simp only [hMem, ↓reduceIte]
    rw [LawfulTraceTable.toMultiSet_add]
    apply hNodup.cons
    intro hPair
    apply hMem
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hPair

/-- A forward-table addition preserves input functionality when the new input has no prior
association. -/
lemma TraceTableOps.inputFunctional_add
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hFunctional : TraceTableOps.InputFunctional t)
    (hFreshInput : ∀ v', (k, v') ∉ LawfulTraceTable.toMultiSet t) :
    TraceTableOps.InputFunctional (TraceTableOps.add t k v) := by
  intro k' v' v'' hLeft hRight
  rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at hLeft hRight
  rcases hLeft with hLeft | hLeft <;> rcases hRight with hRight | hRight
  · cases hLeft
    cases hRight
    rfl
  · cases hLeft
    exact False.elim (hFreshInput v'' hRight)
  · cases hRight
    exact False.elim (hFreshInput v' hLeft)
  · exact hFunctional _ _ _ hLeft hRight

/-- A permutation-table addition preserves output functionality when the new output has no prior
preimage. -/
lemma TraceTableOps.outputFunctional_add
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hFunctional : TraceTableOps.OutputFunctional t)
    (hFreshOutput : ∀ k', (k', v) ∉ LawfulTraceTable.toMultiSet t) :
    TraceTableOps.OutputFunctional (TraceTableOps.add t k v) := by
  intro k' k'' v' hLeft hRight
  rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at hLeft hRight
  rcases hLeft with hLeft | hLeft <;> rcases hRight with hRight | hRight
  · cases hLeft
    cases hRight
    rfl
  · cases hLeft
    exact False.elim (hFreshOutput k'' hRight)
  · cases hRight
    exact (hFreshOutput k' hLeft).elim
  · exact hFunctional _ _ _ hLeft hRight

/-- Under a nodup, output-functional table prefix, the inverse lookup must return the recorded
preimage.  This is the lookup fact used by the first-witness backward-`E_func` argument. -/
lemma TraceTableOps.outlu_eq_some_of_nodup_of_outputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hFunctional : TraceTableOps.OutputFunctional t)
    (hMem : (k, v) ∈ TraceTableOps.entries t) :
    TraceTableOps.outlu t v = some k := by
  have hMemMs : (k, v) ∈ LawfulTraceTable.toMultiSet t := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact Multiset.mem_coe.mpr hMem
  apply (LawfulTraceTable.outlu_eq_some t k v).mpr
  exact ⟨Multiset.count_eq_one_of_mem hNodup hMemMs,
    fun k' hMem' => hFunctional k k' v hMemMs hMem'⟩

/-- Under a nodup, input-functional table prefix, the forward lookup must return the recorded
output. -/
lemma TraceTableOps.inlu_eq_some_of_nodup_of_inputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K} {v : V}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hFunctional : TraceTableOps.InputFunctional t)
    (hMem : (k, v) ∈ TraceTableOps.entries t) :
    TraceTableOps.inlu t k = some v := by
  have hMemMs : (k, v) ∈ LawfulTraceTable.toMultiSet t := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact Multiset.mem_coe.mpr hMem
  apply (LawfulTraceTable.inlu_eq_some t k v).mpr
  exact ⟨Multiset.count_eq_one_of_mem hNodup hMemMs,
    fun v' hMem' => hFunctional k v v' hMemMs hMem'⟩

/-- If a nodup, input-functional table has no forward lookup result, then that input has no
recorded pair at all.  This turns an Item 4 `inlu = ⊥` branch into the freshness premise needed
by `nodup_add`. -/
lemma TraceTableOps.no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {k : K}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hFunctional : TraceTableOps.InputFunctional t)
    (hNone : TraceTableOps.inlu t k = none) :
    ∀ v, (k, v) ∉ LawfulTraceTable.toMultiSet t := by
  intro v hMem
  have hEntries : (k, v) ∈ TraceTableOps.entries t := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hMem
  have hSome := TraceTableOps.inlu_eq_some_of_nodup_of_inputFunctional
    hNodup hFunctional hEntries
  rw [hNone] at hSome
  contradiction

/-- The inverse dual of
`no_mem_of_inlu_eq_none_of_nodup_of_inputFunctional`: a failed `outlu` means that no pair with
that output is present, provided the prefix is nodup and output-functional. -/
lemma TraceTableOps.no_mem_of_outlu_eq_none_of_nodup_of_outputFunctional
    {T K V : Type} [DecidableEq K] [DecidableEq V] [LawfulTraceTable T K V]
    {t : T} {v : V}
    (hNodup : (LawfulTraceTable.toMultiSet t).Nodup)
    (hFunctional : TraceTableOps.OutputFunctional t)
    (hNone : TraceTableOps.outlu t v = none) :
    ∀ k, (k, v) ∉ LawfulTraceTable.toMultiSet t := by
  intro k hMem
  have hEntries : (k, v) ∈ TraceTableOps.entries t := by
    apply Multiset.mem_coe.mp
    rw [LawfulTraceTable.toMultiSet_ofEntries]
    exact hMem
  have hSome := TraceTableOps.outlu_eq_some_of_nodup_of_outputFunctional
    hNodup hFunctional hEntries
  rw [hNone] at hSome
  contradiction

class LawfulTraceNablaImpl (T_H T_P StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U] where
  /-- lawful trace data structure implementation for the hash queries -/
  lawfulHash : LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)
  /-- lawful trace data structure implementation for the permutation queries (`p` and `p⁻¹`) -/
  lawfulPermutation : LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)

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

Generic over any `LawfulTraceTable` implementations `T_H` and `T_P`; only uses `empty` and `add`
from `TraceTableOps`, so the construction is independent of the concrete data structure.

Dispatch rules (matching the three tuple forms of Definition 5.2):
- `.inl stmt`         → `('h', stmt, capSeg)` → `T_H.add acc.h stmt capSeg`
- `.inr (.inl sIn)`   → `('p', sIn, sOut)`    → `T_P.add acc.p sIn sOut`
- `.inr (.inr sOut)`  → `('p⁻¹', sOut, sIn)`  → `T_P.add acc.p sIn sOut`

Both permutation directions contribute `(s_in, s_out)` pairs to the **same** bidirectional `p`
table, because `tr_∇.p` is the single bidirectional structure over `(s_in, s_out)` pairs. -/
def TraceNabla.ofQueryLog
    (log : DuplexSpongeTrace StmtIn U) :
    TraceNabla T_H T_P StmtIn U :=
  log.foldl (init := ⟨TraceTableOps.empty, TraceTableOps.empty⟩)
    fun acc entry =>
      match entry with
      | ⟨.inl stmt,        capSeg⟩ => { acc with h := TraceTableOps.add acc.h stmt capSeg }
      | ⟨.inr (.inl sIn),  sOut⟩   => { acc with p := TraceTableOps.add acc.p sIn sOut }
      | ⟨.inr (.inr sOut), sIn⟩    => { acc with p := TraceTableOps.add acc.p sIn sOut }

/-- Build the `tr_∇` used by CO25 StdTrace §5.5.1 Step 3.

Unlike `TraceNabla.ofQueryLog`, this constructor deliberately ignores inverse-permutation trace
entries, matching Step 3(c) of StdTrace. D2SQuery still uses the bidirectional constructor above. -/
def TraceNabla.ofQueryLogForwardOnly
    (log : DuplexSpongeTrace StmtIn U) :
    TraceNabla T_H T_P StmtIn U :=
  log.foldl (init := ⟨TraceTableOps.empty, TraceTableOps.empty⟩)
    fun acc entry =>
      match entry with
      | ⟨.inl stmt,        capSeg⟩ => { acc with h := TraceTableOps.add acc.h stmt capSeg }
      | ⟨.inr (.inl sIn),  sOut⟩   => { acc with p := TraceTableOps.add acc.p sIn sOut }
      | ⟨.inr (.inr _),    _⟩      => acc

def TraceNabla.IsSubsetOfQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, (stmt, cap) ∈ TraceTableOps.entries trΔ.h → ⟨.inl stmt, cap⟩ ∈ trace) ∧
  (∀ s_in s_out, (s_in, s_out) ∈ TraceTableOps.entries trΔ.p →
    ⟨.inr (.inl s_in), s_out⟩ ∈ trace ∨ ⟨.inr (.inr s_out), s_in⟩ ∈ trace)

/-- The set-level invariant required by D2SQuery: `tr_∇` contains exactly the hash pairs and
normalized permutation pairs represented in the external trace.  Multiple occurrences of one pair
in the trace still correspond to one table pair. -/
def TraceNabla.MirrorsQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, ⟨.inl stmt, cap⟩ ∈ trace ↔ (stmt, cap) ∈ TraceTableOps.entries trΔ.h) ∧
  (∀ sIn sOut,
    (⟨.inr (.inl sIn), sOut⟩ ∈ trace ∨ ⟨.inr (.inr sOut), sIn⟩ ∈ trace) ↔
      (sIn, sOut) ∈ TraceTableOps.entries trΔ.p)

/-- A mirror is, in particular, a table-to-trace subset invariant. -/
lemma TraceNabla.MirrorsQueryLog.isSubset
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) : trΔ.IsSubsetOfQueryLog trace := by
  constructor
  · intro stmt cap hEntry
    exact (hMirror.1 stmt cap).mpr hEntry
  · intro sIn sOut hEntry
    exact (hMirror.2 sIn sOut).mpr hEntry

/-- The fold step from `TraceNabla.ofQueryLog`, factored out for reuse in proofs. -/
private def ofQueryLogStep
    (acc : TraceNabla T_H T_P StmtIn U)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    TraceNabla T_H T_P StmtIn U :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      { acc with h := TraceTableOps.add acc.h stmt capSeg }
  | ⟨.inr (.inl sIn), sOut⟩ =>
      { acc with p := TraceTableOps.add acc.p sIn sOut }
  | ⟨.inr (.inr sOut), sIn⟩ =>
      { acc with p := TraceTableOps.add acc.p sIn sOut }

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
      have hIH := ih {init with h := TraceTableOps.add init.h stmt' a} hp
      have : ({init with h := TraceTableOps.add init.h stmt' a} :
          TraceNabla T_H T_P StmtIn U).h = TraceTableOps.add init.h stmt' a := rfl
      rw [this] at hIH; erw [LawfulTraceTable.toMultiSet_add] at hIH
      rcases hIH with hMem | hIn
      · rw [Multiset.mem_cons] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; right; exact .head ..
        · exact Or.inl hRest
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    -- Forward perm: h unchanged
    case inr.inl =>
      simp only [ofQueryLogStep] at hp
      rcases ih {init with p := TraceTableOps.add init.p sIn' a} hp with hMem | hIn
      · exact Or.inl hMem
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    -- Inverse perm: h unchanged
    case inr.inr =>
      simp only [ofQueryLogStep] at hp
      rcases ih {init with p := TraceTableOps.add init.p a sOut'} hp with hMem | hIn
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
      rcases ih {init with h := TraceTableOps.add init.h stmt' a} hp with hMem | h1 | h2
      · exact Or.inl hMem
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    -- Forward perm: adds (sIn', a) to p
    case inr.inl =>
      simp only [ofQueryLogStep] at hp
      have hIH := ih {init with p := TraceTableOps.add init.p sIn' a} hp
      have : ({init with p := TraceTableOps.add init.p sIn' a} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.add init.p sIn' a := rfl
      rw [this] at hIH; erw [LawfulTraceTable.toMultiSet_add] at hIH
      rcases hIH with hMem | hIn
      · rw [Multiset.mem_cons] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; exact Or.inr (Or.inl (by exact .head ..))
        · exact Or.inl hRest
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    -- Inverse perm: adds (a, sOut') to p
    case inr.inr =>
      simp only [ofQueryLogStep] at hp
      have hIH := ih {init with p := TraceTableOps.add init.p a sOut'} hp
      have : ({init with p := TraceTableOps.add init.p a sOut'} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.add init.p a sOut' := rfl
      rw [this] at hIH; erw [LawfulTraceTable.toMultiSet_add] at hIH
      rcases hIH with hMem | hIn
      · rw [Multiset.mem_cons] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; exact Or.inr (Or.inr (by exact .head ..))
        · exact Or.inl hRest
      · rcases hIn with h1 | h2
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))

private lemma hash_entries_foldl_mono
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    {pair : StmtIn × Vector U SpongeSize.C}
    (hMem : pair ∈ TraceTableOps.entries init.h) :
    pair ∈ TraceTableOps.entries
      (List.foldl ofQueryLogStep init trace).h := by
  induction trace generalizing init with
  | nil =>
      exact hMem
  | cons entry trace' ih =>
      rcases entry with ⟨q, a⟩
      rcases q with stmt | sIn | sOut
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with h := TraceTableOps.add init.h stmt a }
          ((TraceTableOps.mem_entries_add_iff init.h stmt a pair).mpr (Or.inr hMem))
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with p := TraceTableOps.add init.p sIn a } hMem
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with p := TraceTableOps.add init.p a sOut } hMem

private lemma perm_entries_foldl_mono
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    {pair : CanonicalSpongeState U × CanonicalSpongeState U}
    (hMem : pair ∈ TraceTableOps.entries init.p) :
    pair ∈ TraceTableOps.entries
      (List.foldl ofQueryLogStep init trace).p := by
  induction trace generalizing init with
  | nil =>
      exact hMem
  | cons entry trace' ih =>
      rcases entry with ⟨q, a⟩
      rcases q with stmt | sIn | sOut
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with h := TraceTableOps.add init.h stmt a } hMem
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with p := TraceTableOps.add init.p sIn a }
          ((TraceTableOps.mem_entries_add_iff init.p sIn a pair).mpr (Or.inr hMem))
      · simp only [List.foldl_cons, ofQueryLogStep]
        exact ih { init with p := TraceTableOps.add init.p a sOut }
          ((TraceTableOps.mem_entries_add_iff init.p a sOut pair).mpr (Or.inr hMem))

private lemma hash_mem_entries_foldl_of_mem
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    {stmt : StmtIn} {cap : Vector U SpongeSize.C}
    (hMem : (⟨.inl stmt, cap⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace) :
    (stmt, cap) ∈ TraceTableOps.entries
      (List.foldl ofQueryLogStep init trace).h := by
  induction trace generalizing init with
  | nil =>
      cases hMem
  | cons entry trace' ih =>
      rw [List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · rcases entry with ⟨q, a⟩
        rcases q with stmt' | sIn | sOut
        · injection hHead with hq ha
          cases hq
          cases ha
          simp only [List.foldl_cons, ofQueryLogStep]
          exact hash_entries_foldl_mono
            { init with h := TraceTableOps.add init.h stmt cap } trace'
            ((TraceTableOps.mem_entries_add_iff init.h stmt cap (stmt, cap)).mpr
              (Or.inl rfl))
        · cases hHead
        · cases hHead
      · rcases entry with ⟨q, a⟩
        rcases q with stmt' | sIn | sOut
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with h := TraceTableOps.add init.h stmt' a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p sIn a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p a sOut } hTail

private lemma perm_mem_entries_foldl_of_mem_fwd
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    {sIn sOut : CanonicalSpongeState U}
    (hMem : (⟨.inr (.inl sIn), sOut⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace) :
    (sIn, sOut) ∈ TraceTableOps.entries
      (List.foldl ofQueryLogStep init trace).p := by
  induction trace generalizing init with
  | nil =>
      cases hMem
  | cons entry trace' ih =>
      rw [List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · rcases entry with ⟨q, a⟩
        rcases q with stmt | sIn' | sOut'
        · cases hHead
        · injection hHead with hq ha
          cases hq
          cases ha
          simp only [List.foldl_cons, ofQueryLogStep]
          exact perm_entries_foldl_mono
            { init with p := TraceTableOps.add init.p sIn sOut } trace'
            ((TraceTableOps.mem_entries_add_iff init.p sIn sOut (sIn, sOut)).mpr
              (Or.inl rfl))
        · cases hHead
      · rcases entry with ⟨q, a⟩
        rcases q with stmt | sIn' | sOut'
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with h := TraceTableOps.add init.h stmt a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p sIn' a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p a sOut' } hTail

private lemma perm_mem_entries_foldl_of_mem_bwd
    (init : TraceNabla T_H T_P StmtIn U)
    (trace : DuplexSpongeTrace StmtIn U)
    {sIn sOut : CanonicalSpongeState U}
    (hMem : (⟨.inr (.inr sOut), sIn⟩ :
      Sigma (duplexSpongeChallengeOracle StmtIn U)) ∈ trace) :
    (sIn, sOut) ∈ TraceTableOps.entries
      (List.foldl ofQueryLogStep init trace).p := by
  induction trace generalizing init with
  | nil =>
      cases hMem
  | cons entry trace' ih =>
      rw [List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · rcases entry with ⟨q, a⟩
        rcases q with stmt | sIn' | sOut'
        · cases hHead
        · cases hHead
        · injection hHead with hq ha
          cases hq
          cases ha
          simp only [List.foldl_cons, ofQueryLogStep]
          exact perm_entries_foldl_mono
            { init with p := TraceTableOps.add init.p sIn sOut } trace'
            ((TraceTableOps.mem_entries_add_iff init.p sIn sOut (sIn, sOut)).mpr
              (Or.inl rfl))
      · rcases entry with ⟨q, a⟩
        rcases q with stmt | sIn' | sOut'
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with h := TraceTableOps.add init.h stmt a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p sIn' a } hTail
        · simp only [List.foldl_cons, ofQueryLogStep]
          exact ih { init with p := TraceTableOps.add init.p a sOut' } hTail

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

/-- The canonical `tr_∇` built by folding over a trace mirrors exactly the represented hash and
bidirectional permutation pairs in that trace. -/
lemma TraceNabla.ofQueryLog_mirrors
    (trace : DuplexSpongeTrace StmtIn U) :
    (TraceNabla.ofQueryLog (T_H := T_H) (T_P := T_P) trace).MirrorsQueryLog trace := by
  constructor
  · intro stmt cap
    constructor
    · intro hMem
      rw [ofQueryLog_eq_foldl]
      exact hash_mem_entries_foldl_of_mem
        (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ :
          TraceNabla T_H T_P StmtIn U) trace hMem
    · intro hEntry
      exact (TraceNabla.ofQueryLog_isSubset
        (T_H := T_H) (T_P := T_P) trace).1 stmt cap hEntry
  · intro sIn sOut
    constructor
    · intro hMem
      rw [ofQueryLog_eq_foldl]
      rcases hMem with hFwd | hBwd
      · exact perm_mem_entries_foldl_of_mem_fwd
          (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ :
            TraceNabla T_H T_P StmtIn U) trace hFwd
      · exact perm_mem_entries_foldl_of_mem_bwd
          (⟨(TraceTableOps.empty : T_H), (TraceTableOps.empty : T_P)⟩ :
            TraceNabla T_H T_P StmtIn U) trace hBwd
    · intro hEntry
      exact (TraceNabla.ofQueryLog_isSubset
        (T_H := T_H) (T_P := T_P) trace).2 sIn sOut hEntry

private def ofQueryLogForwardOnlyStep
    (acc : TraceNabla T_H T_P StmtIn U)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    TraceNabla T_H T_P StmtIn U :=
  match entry with
  | ⟨.inl stmt, capSeg⟩ =>
      { acc with h := TraceTableOps.add acc.h stmt capSeg }
  | ⟨.inr (.inl sIn), sOut⟩ =>
      { acc with p := TraceTableOps.add acc.p sIn sOut }
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
      have hIH := ih {init with h := TraceTableOps.add init.h stmt' a} hp
      have : ({init with h := TraceTableOps.add init.h stmt' a} :
          TraceNabla T_H T_P StmtIn U).h = TraceTableOps.add init.h stmt' a := rfl
      rw [this] at hIH; erw [LawfulTraceTable.toMultiSet_add] at hIH
      rcases hIH with hMem | hIn
      · rw [Multiset.mem_cons] at hMem
        rcases hMem with hEq | hRest
        · subst hEq; right; exact .head ..
        · exact Or.inl hRest
      · exact Or.inr (List.mem_cons_of_mem _ hIn)
    case inr.inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      rcases ih {init with p := TraceTableOps.add init.p sIn' a} hp with hMem | hIn
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
      rcases ih {init with h := TraceTableOps.add init.h stmt' a} hp with hMem | h1 | h2
      · exact Or.inl hMem
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h2))
    case inr.inl =>
      simp only [ofQueryLogForwardOnlyStep] at hp
      have hIH := ih {init with p := TraceTableOps.add init.p sIn' a} hp
      have : ({init with p := TraceTableOps.add init.p sIn' a} :
          TraceNabla T_H T_P StmtIn U).p = TraceTableOps.add init.p sIn' a := rfl
      rw [this] at hIH; erw [LawfulTraceTable.toMultiSet_add] at hIH
      rcases hIH with hMem | hIn
      · rw [Multiset.mem_cons] at hMem
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
    (TraceNabla.ofQueryLogForwardOnly (T_H := T_H) (T_P := T_P) trace).IsSubsetOfQueryLog trace := by
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

/-! ### Default `tr_∇` type alias and `ofQueryLog` -/

instance instLawfulTraceNablaImplListBased [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U] :
    LawfulTraceNablaImpl
      (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
      StmtIn U :=
  ⟨instLawfulListBasedTraceTable, instLawfulListBasedTraceTable⟩

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

/-- The empty index mirrors the empty external trace. -/
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

/-- Appending a fresh hash pair and adding it to `tr_∇.h` preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_hash_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C) :
    ({trΔ with h := TraceTableOps.add trΔ.h stmt cap} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inl stmt, cap⟩]) := by
  constructor
  · intro stmt' cap'
    rw [TraceTableOps.mem_entries_add_iff]
    simp only [List.mem_append, List.mem_singleton]
    rw [hMirror.1]
    constructor
    · rintro (hOld | hNew)
      · exact Or.inr hOld
      · exact Or.inl (by simpa using hNew)
    · rintro (hNew | hOld)
      · exact Or.inr (by simpa using hNew)
      · exact Or.inl hOld
  · intro sIn sOut
    constructor
    · intro h
      rcases h with hFwd | hBwd
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inl hOld)
        · simp at hLast
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inr hOld)
        · simp at hLast
    · intro h
      rcases (hMirror.2 _ _).mpr h with hFwd | hBwd
      · exact Or.inl (List.mem_append_left _ hFwd)
      · exact Or.inr (List.mem_append_left _ hBwd)

/-- Appending a fresh forward permutation pair and adding its normalized pair to `tr_∇.p`
preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_perm_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  constructor
  · intro stmt cap
    constructor
    · intro h
      rcases List.mem_append.mp h with hOld | hLast
      · exact (hMirror.1 _ _).mp hOld
      · simp at hLast
    · intro h
      exact List.mem_append_left _ ((hMirror.1 _ _).mpr h)
  · intro sIn' sOut'
    rw [TraceTableOps.mem_entries_add_iff]
    constructor
    · rintro (hFwd | hBwd)
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact Or.inr ((hMirror.2 _ _).mp (Or.inl hOld))
        · exact Or.inl (by simpa [and_comm] using hLast)
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact Or.inr ((hMirror.2 _ _).mp (Or.inr hOld))
        · simp at hLast
    · rintro (hNew | hOld)
      · injection hNew with hIn hOut
        subst sIn'
        subst sOut'
        exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      · rcases (hMirror.2 _ _).mpr hOld with hFwd | hBwd
        · exact Or.inl (List.mem_append_left _ hFwd)
        · exact Or.inr (List.mem_append_left _ hBwd)

/-- Appending a fresh inverse permutation pair and adding its normalized pair to `tr_∇.p`
preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_perm_inv_add
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.MirrorsQueryLog (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  constructor
  · intro stmt cap
    constructor
    · intro h
      rcases List.mem_append.mp h with hOld | hLast
      · exact (hMirror.1 _ _).mp hOld
      · simp at hLast
    · intro h
      exact List.mem_append_left _ ((hMirror.1 _ _).mpr h)
  · intro sIn' sOut'
    rw [TraceTableOps.mem_entries_add_iff]
    constructor
    · rintro (hFwd | hBwd)
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact Or.inr ((hMirror.2 _ _).mp (Or.inl hOld))
        · simp at hLast
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact Or.inr ((hMirror.2 _ _).mp (Or.inr hOld))
        · exact Or.inl (by simpa [and_comm] using hLast)
    · rintro (hNew | hOld)
      · injection hNew with hIn hOut
        subst sIn'
        subst sOut'
        exact Or.inr (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      · rcases (hMirror.2 _ _).mpr hOld with hFwd | hBwd
        · exact Or.inl (List.mem_append_left _ hFwd)
        · exact Or.inr (List.mem_append_left _ hBwd)

/-- Repeating a hash pair already indexed by `tr_∇.h` preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_hash_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace) (stmt : StmtIn) (cap : Vector U SpongeSize.C)
    (hMem : (stmt, cap) ∈ TraceTableOps.entries trΔ.h) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inl stmt, cap⟩]) := by
  constructor
  · intro stmt' cap'
    constructor
    · intro h
      rcases List.mem_append.mp h with hOld | hLast
      · exact (hMirror.1 _ _).mp hOld
      · have hPair : (stmt', cap') = (stmt, cap) := by simpa using hLast
        simpa [hPair] using hMem
    · intro h
      exact List.mem_append_left _ ((hMirror.1 _ _).mpr h)
  · intro sIn sOut
    constructor
    · intro h
      rcases h with hFwd | hBwd
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inl hOld)
        · simp at hLast
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inr hOld)
        · simp at hLast
    · intro h
      rcases (hMirror.2 _ _).mpr h with hFwd | hBwd
      · exact Or.inl (List.mem_append_left _ hFwd)
      · exact Or.inr (List.mem_append_left _ hBwd)

/-- Repeating an indexed forward permutation pair preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_perm_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  constructor
  · intro stmt cap
    constructor
    · intro h
      rcases List.mem_append.mp h with hOld | hLast
      · exact (hMirror.1 _ _).mp hOld
      · simp at hLast
    · intro h
      exact List.mem_append_left _ ((hMirror.1 _ _).mpr h)
  · intro sIn' sOut'
    constructor
    · rintro (hFwd | hBwd)
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inl hOld)
        · have hPair : (sIn', sOut') = (sIn, sOut) := by simpa using hLast
          simpa [hPair] using hMem
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inr hOld)
        · simp at hLast
    · intro h
      rcases (hMirror.2 _ _).mpr h with hFwd | hBwd
      · exact Or.inl (List.mem_append_left _ hFwd)
      · exact Or.inr (List.mem_append_left _ hBwd)

/-- Repeating an indexed inverse permutation pair preserves the exact mirror invariant. -/
lemma TraceNabla.MirrorsQueryLog_append_perm_inv_existing
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hMirror : trΔ.MirrorsQueryLog trace)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries trΔ.p) :
    trΔ.MirrorsQueryLog (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  constructor
  · intro stmt cap
    constructor
    · intro h
      rcases List.mem_append.mp h with hOld | hLast
      · exact (hMirror.1 _ _).mp hOld
      · simp at hLast
    · intro h
      exact List.mem_append_left _ ((hMirror.1 _ _).mpr h)
  · intro sIn' sOut'
    constructor
    · rintro (hFwd | hBwd)
      · rcases List.mem_append.mp hFwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inl hOld)
        · simp at hLast
      · rcases List.mem_append.mp hBwd with hOld | hLast
        · exact (hMirror.2 _ _).mp (Or.inr hOld)
        · have hPair : (sIn', sOut') = (sIn, sOut) := by simpa [and_comm] using hLast
          simpa [hPair] using hMem
    · intro h
      rcases (hMirror.2 _ _).mpr h with hFwd | hBwd
      · exact Or.inl (List.mem_append_left _ hFwd)
      · exact Or.inr (List.mem_append_left _ hBwd)

/-- The cache-pop transition appends a forward pair and inserts it set-semantically, preserving
the exact mirror invariant whether the pair was already indexed or not. -/
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

lemma TraceNabla.IsSubsetOfQueryLog_append_any
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
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
    ({trΔ with h := TraceTableOps.add trΔ.h stmt cap} : TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inl stmt, cap⟩]) := by
  constructor
  · intro stmt' cap' hMem
    have h1 : (stmt', cap') ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add trΔ.h stmt cap) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]; exact hMem
    rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at h1
    rcases h1 with hEq | hRest
    · injection hEq with hS hC; subst hS hC
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · have h2 : (stmt', cap') ∈ TraceTableOps.entries trΔ.h :=
        Multiset.mem_coe.mp ((LawfulTraceTable.toMultiSet_ofEntries trΔ.h).symm ▸ hRest)
      exact List.mem_append_left _ (hSub.1 _ _ h2)
  · intro sIn sOut hMem
    rcases hSub.2 _ _ hMem with hL | hR
    · exact Or.inl (List.mem_append_left _ hL)
    · exact Or.inr (List.mem_append_left _ hR)

lemma TraceNabla.IsSubsetOfQueryLog_append_perm
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  constructor
  · intro stmt' cap' hMem
    exact List.mem_append_left _ (hSub.1 _ _ hMem)
  · intro sIn' sOut' hMem
    have h1 : (sIn', sOut') ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add trΔ.p sIn sOut) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]; exact hMem
    rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at h1
    rcases h1 with hEq | hRest
    · injection hEq with hS hO; subst hS hO
      exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · have h2 : (sIn', sOut') ∈ TraceTableOps.entries trΔ.p :=
        Multiset.mem_coe.mp ((LawfulTraceTable.toMultiSet_ofEntries trΔ.p).symm ▸ hRest)
      rcases hSub.2 _ _ h2 with hL | hR
      · exact Or.inl (List.mem_append_left _ hL)
      · exact Or.inr (List.mem_append_left _ hR)

/-- Set-semantic variant of `IsSubsetOfQueryLog_append_perm`.  Used by the D2SQuery cache-pop
branch: if the pair was already recorded, the table is unchanged; otherwise it is appended once. -/
lemma TraceNabla.IsSubsetOfQueryLog_insert_perm
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.insert trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U)
      |>.IsSubsetOfQueryLog (trace ++ [⟨.inr (.inl sIn), sOut⟩]) := by
  unfold TraceTableOps.insert
  split
  · exact TraceNabla.IsSubsetOfQueryLog_append_any hSub _
  · exact TraceNabla.IsSubsetOfQueryLog_append_perm hSub sIn sOut

lemma TraceNabla.IsSubsetOfQueryLog_append_perm_inv
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (hSub : trΔ.IsSubsetOfQueryLog trace) (sIn sOut : CanonicalSpongeState U) :
    ({trΔ with p := TraceTableOps.add trΔ.p sIn sOut} : TraceNabla T_H T_P StmtIn U).IsSubsetOfQueryLog
      (trace ++ [⟨.inr (.inr sOut), sIn⟩]) := by
  constructor
  · intro stmt' cap' hMem
    exact List.mem_append_left _ (hSub.1 _ _ hMem)
  · intro sIn' sOut' hMem
    have h1 : (sIn', sOut') ∈ LawfulTraceTable.toMultiSet (TraceTableOps.add trΔ.p sIn sOut) := by
      rw [← LawfulTraceTable.toMultiSet_ofEntries]; exact hMem
    rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at h1
    rcases h1 with hEq | hRest
    · injection hEq with hS hO; subst hS hO
      exact Or.inr (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · have h2 : (sIn', sOut') ∈ TraceTableOps.entries trΔ.p :=
        Multiset.mem_coe.mp ((LawfulTraceTable.toMultiSet_ofEntries trΔ.p).symm ▸ hRest)
      rcases hSub.2 _ _ h2 with hL | hR
      · exact Or.inl (List.mem_append_left _ hL)
      · exact Or.inr (List.mem_append_left _ hR)

end TraceDataStructures

end DSTraceStorage

end DuplexSpongeFS
