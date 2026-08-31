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
(`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`). Its generic operations include
insertion, exact-pair membership, forward/backward unique lookup, and proof-facing enumeration.
`LawfulTraceNablaImpl` additionally exposes the two DSFS-specific capacity secondary indices used
by BackTrack; generic tables cannot name those indices because their key/value types have no
generic notion of a sponge-capacity projection.

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

/-- Result of a table lookup that must distinguish no match, a unique match, and ambiguity.

This is the executable form of the paper's “zero, one, or multiple matches” convention. -/
inductive TraceLookupResult (α : Type _) where
  | noMatch
  | unique (value : α)
  | conflict
deriving DecidableEq

/-- Classify a materialized lookup bucket without inspecting entries beyond the second match. -/
@[inline] def TraceLookupResult.ofList {α : Type _} (xs : List α) : TraceLookupResult α :=
  match xs with
  | [] => .noMatch
  | [x] => .unique x
  | _ :: _ :: _ => .conflict

/-- Operations for a trace table used in CO25 Definition 5.2.
Covers both the one-way hash table (`tr_∇.h`) and the bidirectional permutation table (`tr_∇.p`).
`entries` is a refinement/proof view; executable partial-key BackTrack lookup goes through the
capacity secondary-index operations in `LawfulTraceNablaImpl`, never through enumeration. -/
class TraceTableOps (T : Type) (K V : outParam Type) where
  empty : T                    -- `∅` — return an empty table
  add   : T → K → V → T       -- `t ∪ {(k,v)}` — insert a `(k, v)` pair
  /-- Exact-pair membership. An indexed implementation provides this in `O(log |t|)`. -/
  contains : T → K → V → Bool
  inlu  : T → K → Option V    -- `inlu(t, k)` — unique forward lookup (CO25 Def. 5.2)
  outlu : T → V → Option K    -- `outlu(t, v)` — unique backward lookup (CO25 Def. 5.2)
  /-- `entries(t)` — proof/refinement view enumerating all `(k, v)` pairs. -/
  entries : T → List (K × V)

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
  contains_eq_true : ∀ t k v, contains t k v = true ↔ (k, v) ∈ toMultiSet t
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
  reading is stable. Runtime BackTrack does not enumerate this view. -/
  toMultiSet_ofEntries : ∀ t, (TraceTableOps.entries t : Multiset (K × V)) = toMultiSet t

class LawfulTraceNablaImpl (T_H T_P StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U] where
  /-- lawful trace data structure implementation for the hash queries -/
  lawfulHash : LawfulTraceTable T_H StmtIn (Vector U SpongeSize.C)
  /-- lawful trace data structure implementation for the permutation queries (`p` and `p⁻¹`) -/
  lawfulPermutation : LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)
  /-- Capacity-keyed reverse lookup for hash anchors. A production implementation maintains a
  secondary index ordered by answer capacity, as required by CO25 §5.1. -/
  hashCapOutlu : T_H → Vector U SpongeSize.C → TraceLookupResult StmtIn
  /-- Capacity-keyed reverse lookup for permutation predecessors. It is applied to the
  forward-first table constructed once per BackTrack invocation. -/
  permCapOutlu : T_P → Vector U SpongeSize.C →
    TraceLookupResult (CanonicalSpongeState U × CanonicalSpongeState U)
  /-- Extensional law for the hash-capacity secondary index. -/
  hashCapOutlu_eq : ∀ t cap,
    hashCapOutlu t cap = TraceLookupResult.ofList
      ((lawfulHash.toTraceTableOps.entries t).filterMap fun pair =>
        if pair.2 = cap then some pair.1 else none)
  /-- Extensional law for the permutation output-capacity secondary index. -/
  permCapOutlu_eq : ∀ t cap,
    permCapOutlu t cap = TraceLookupResult.ofList
      ((lawfulPermutation.toTraceTableOps.entries t).filterMap fun pair =>
        if pair.2.capacitySegment = cap then some pair else none)

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

/-- Exact set-level correspondence between a raw query log and its normalized two-table index.

Repeated raw occurrences are intentionally collapsed: `trΔ.p` stores a normalized pair
`(sIn, sOut)` regardless of whether it first appeared as a `p` or `p⁻¹` query. -/
def TraceNabla.MirrorsQueryLog
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop :=
  (∀ stmt cap, ⟨.inl stmt, cap⟩ ∈ trace ↔
    (stmt, cap) ∈ TraceTableOps.entries trΔ.h) ∧
  (∀ sIn sOut,
    (⟨.inr (.inl sIn), sOut⟩ ∈ trace ∨ ⟨.inr (.inr sOut), sIn⟩ ∈ trace) ↔
      (sIn, sOut) ∈ TraceTableOps.entries trΔ.p)

/-- The corrected trace-index interface used by Claims 5.19 and 5.20.

The index mirrors the source trace exactly at set level and contains each normalized table pair
at most once.  Thus an arbitrary unrelated `trΔ`, or a duplicate-filled reconstruction of the
raw log, cannot satisfy this predicate. -/
structure TraceNabla.IsNormalizedIndex
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop where
  mirrors : trΔ.MirrorsQueryLog trace
  hash_nodup : (TraceTableOps.entries trΔ.h).Nodup
  permutation_nodup : (TraceTableOps.entries trΔ.p).Nodup

/-- The operational trace-index invariant needed by BackTrack and LookAhead.

Unlike `IsNormalizedIndex`, this predicate deliberately does not require every raw trace entry to
be represented in `trΔ`. D2SQuery's live table omits cache-pop realizations, while StdTrace's
table omits inverse-only entries. What the executable searches need is exactly:

* provenance: every stored pair really occurs in the source trace; and
* normalization: an identical stored pair occurs at most once, so multiplicity alone cannot turn
  a lookup into a spurious conflict.

The absence of the paper bad event then rules out conflicts between *distinct* stored pairs. -/
structure TraceNabla.IsNormalizedSubindex
    (trΔ : TraceNabla T_H T_P StmtIn U) (trace : DuplexSpongeTrace StmtIn U) : Prop where
  isSubset : trΔ.IsSubsetOfQueryLog trace
  hash_nodup : (TraceTableOps.entries trΔ.h).Nodup
  permutation_nodup : (TraceTableOps.entries trΔ.p).Nodup

/-- An exact normalized index is, in particular, provenance-correct for every stored pair. -/
lemma TraceNabla.IsNormalizedIndex.isSubset
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (h : trΔ.IsNormalizedIndex trace) : trΔ.IsSubsetOfQueryLog trace := by
  constructor
  · intro stmt cap hMem
    exact (h.mirrors.1 stmt cap).mpr hMem
  · intro sIn sOut hMem
    exact (h.mirrors.2 sIn sOut).mpr hMem

/-- An exact normalized index is, in particular, a normalized sound subindex. -/
lemma TraceNabla.IsNormalizedIndex.isNormalizedSubindex
    {trΔ : TraceNabla T_H T_P StmtIn U} {trace : DuplexSpongeTrace StmtIn U}
    (h : trΔ.IsNormalizedIndex trace) : trΔ.IsNormalizedSubindex trace :=
  ⟨h.isSubset, h.hash_nodup, h.permutation_nodup⟩

/-! ### Forward-first permutation index for BackTrack

The normalized permutation table intentionally forgets whether a mapping first entered the raw
trace through `p` or `p⁻¹`. BackTrack needs only mappings whose first raw occurrence is forward.
Computing that fact again with `idxOf` at every path step is prohibitively expensive, so this
small auxiliary table is constructed once before the walk. -/

/-- Normalize the permutation occurrences of a raw trace while retaining occurrence order. -/
private def normalizedPermutationPairs
    (trace : DuplexSpongeTrace StmtIn U) :
    List (CanonicalSpongeState U × CanonicalSpongeState U) :=
  trace.filterMap fun entry =>
    match entry with
    | ⟨.inl _, _⟩ => none
    | ⟨.inr (.inl sIn), sOut⟩ => some (sIn, sOut)
    | ⟨.inr (.inr sOut), sIn⟩ => some (sIn, sOut)

/-- A pair has a forward first normalized occurrence in the raw trace.

The prefix excludes the normalized pair in *both* query directions. This decomposition form is
the induction-friendly equivalent of comparing the `idxOf` of the forward and inverse entries. -/
def PermutationForwardFirst
    (trace : DuplexSpongeTrace StmtIn U)
    (sIn sOut : CanonicalSpongeState U) : Prop :=
  ∃ pre suffix,
    trace = pre ++
      (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) :: suffix ∧
    (sIn, sOut) ∉ normalizedPermutationPairs pre

/-- Accumulator for the one-pass forward-first index construction.

`seen` contains every normalized permutation pair encountered in either direction. `forward`
contains exactly those allowed pairs whose first encounter was a forward query. -/
private structure ForwardPermutationIndexState (T_P : Type) where
  seen : T_P
  forward : T_P

/-- Every normalized permutation occurrence in `processed` has reached `seen`. -/
private def ForwardPermutationIndexState.SeenComplete
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (st : ForwardPermutationIndexState T_P)
    (processed : DuplexSpongeTrace StmtIn U) : Prop :=
  ∀ sIn sOut, (sIn, sOut) ∈ normalizedPermutationPairs processed →
    (sIn, sOut) ∈ LawfulTraceTable.toMultiSet st.seen

/-- Every pair already emitted into `forward` has a forward first occurrence in `processed`. -/
private def ForwardPermutationIndexState.ForwardSound
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (st : ForwardPermutationIndexState T_P)
    (processed : DuplexSpongeTrace StmtIn U) : Prop :=
  ∀ sIn sOut, (sIn, sOut) ∈ LawfulTraceTable.toMultiSet st.forward →
    PermutationForwardFirst processed sIn sOut

/-- A forward-first witness is stable when more raw queries are appended. -/
private lemma PermutationForwardFirst.append
    {trace : DuplexSpongeTrace StmtIn U}
    {sIn sOut : CanonicalSpongeState U}
    (h : PermutationForwardFirst trace sIn sOut)
    (tail : DuplexSpongeTrace StmtIn U) :
    PermutationForwardFirst (trace ++ tail) sIn sOut := by
  rcases h with ⟨pre, suffix, hTrace, hFresh⟩
  refine ⟨pre, suffix ++ tail, ?_, hFresh⟩
  rw [hTrace]
  simp only [List.append_assoc, List.cons_append]

/-- Decomposition-form forward-first implies the paper's `idxOf` comparison. -/
lemma PermutationForwardFirst.idxOf_lt
    {trace : DuplexSpongeTrace StmtIn U}
    {sIn sOut : CanonicalSpongeState U}
    (h : PermutationForwardFirst trace sIn sOut) :
    trace.idxOf
        (⟨.inr (.inl sIn), sOut⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) <
      trace.idxOf
        (⟨.inr (.inr sOut), sIn⟩ : Sigma (duplexSpongeChallengeOracle StmtIn U)) := by
  let fwd : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨.inr (.inl sIn), sOut⟩
  let inv : Sigma (duplexSpongeChallengeOracle StmtIn U) := ⟨.inr (.inr sOut), sIn⟩
  rcases h with ⟨pre, suffix, hTrace, hFresh⟩
  change trace = pre ++ fwd :: suffix at hTrace
  have hFwdNot : fwd ∉ pre := by
    intro hMem
    apply hFresh
    unfold normalizedPermutationPairs
    exact List.mem_filterMap.mpr ⟨fwd, hMem, by simp [fwd]⟩
  have hInvNot : inv ∉ pre := by
    intro hMem
    apply hFresh
    unfold normalizedPermutationPairs
    exact List.mem_filterMap.mpr ⟨inv, hMem, by simp [inv]⟩
  have hNe : fwd ≠ inv := by simp [fwd, inv]
  change trace.idxOf fwd < trace.idxOf inv
  rw [hTrace, List.idxOf_append_of_notMem hFwdNot,
    List.idxOf_append_of_notMem hInvNot]
  simp [hNe]

/-- One trace-occurrence update for the forward-first index. Exact-pair membership and insertion
are abstract table operations; a balanced implementation performs both in logarithmic time. -/
private def forwardPermutationIndexStep
    [TraceTableOps T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (allowed : T_P)
    (st : ForwardPermutationIndexState T_P)
    (entry : duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) :
    ForwardPermutationIndexState T_P :=
  match entry with
  | ⟨.inl _, _⟩ => st
  | ⟨.inr (.inl sIn), sOut⟩ =>
      if TraceTableOps.contains st.seen sIn sOut then
        st
      else
        { seen := TraceTableOps.add st.seen sIn sOut
          forward :=
            if TraceTableOps.contains allowed sIn sOut then
              TraceTableOps.add st.forward sIn sOut
            else
              st.forward }
  | ⟨.inr (.inr sOut), sIn⟩ =>
      if TraceTableOps.contains st.seen sIn sOut then
        st
      else
        { st with seen := TraceTableOps.add st.seen sIn sOut }

/-- Build the forward-first subtable used by BackTrack in one left-to-right pass over `trace`.

The `allowed` table is normally `tr_∇.p`; intersecting with it preserves the public BackTrack
semantics even when the caller supplies a provenance-correct sub-index rather than the complete
raw trace index. With `O(log P)` table membership/insertion this preprocessing costs
`O(|trace| log P)` and is performed once, never once per BackTrack hop. -/
def buildForwardPermutationIndex
    [TraceTableOps T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : DuplexSpongeTrace StmtIn U) (allowed : T_P) : T_P :=
  (trace.foldl (forwardPermutationIndexStep allowed)
    { seen := TraceTableOps.empty, forward := TraceTableOps.empty }).forward

omit [DecidableEq StmtIn] in
/-- Every entry placed in the one-pass forward-first index belongs to the caller's allowed
permutation table. This is the provenance bridge used by the executable BackTrack walk. -/
lemma buildForwardPermutationIndex_subset_allowed
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : DuplexSpongeTrace StmtIn U) (allowed : T_P)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries
      (buildForwardPermutationIndex trace allowed)) :
    (sIn, sOut) ∈ TraceTableOps.entries allowed := by
  have fold_subset : ∀ (remaining : DuplexSpongeTrace StmtIn U)
      (st : ForwardPermutationIndexState T_P),
      (∀ a b, (a, b) ∈ LawfulTraceTable.toMultiSet st.forward →
        (a, b) ∈ LawfulTraceTable.toMultiSet allowed) →
      ∀ a b,
        (a, b) ∈ LawfulTraceTable.toMultiSet
          (remaining.foldl (forwardPermutationIndexStep allowed) st).forward →
        (a, b) ∈ LawfulTraceTable.toMultiSet allowed := by
    intro remaining
    induction remaining with
    | nil =>
        intro st hSub a b h
        exact hSub a b h
    | cons entry rest ih =>
        intro st hSub a b h
        apply ih (forwardPermutationIndexStep allowed st entry) ?_ a b h
        intro a' b' h'
        rcases entry with ⟨q, answer⟩
        rcases q with stmt | input | output
        · exact hSub a' b' h'
        · change CanonicalSpongeState U at answer
          simp only [forwardPermutationIndexStep] at h'
          split at h'
          · exact hSub a' b' h'
          · split at h'
            · next hAllowed =>
                change (a', b') ∈ LawfulTraceTable.toMultiSet
                  (TraceTableOps.add st.forward input answer) at h'
                rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at h'
                rcases h' with hEq | hOld
                · injection hEq with hA hB
                  subst hA
                  subst hB
                  exact (LawfulTraceTable.contains_eq_true allowed a' b').mp hAllowed
                · exact hSub a' b' hOld
            · exact hSub a' b' h'
        · change CanonicalSpongeState U at answer
          simp only [forwardPermutationIndexStep] at h'
          split at h' <;> exact hSub a' b' h'
  have hMemMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet
      (buildForwardPermutationIndex trace allowed) := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hMem
  have hAllowedMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet allowed := by
    unfold buildForwardPermutationIndex at hMemMs
    apply fold_subset trace
      { seen := TraceTableOps.empty, forward := TraceTableOps.empty }
    · intro a b h
      rw [LawfulTraceTable.toMultiSet_empty] at h
      simp at h
    · exact hMemMs
  rw [← LawfulTraceTable.toMultiSet_ofEntries] at hAllowedMs
  exact hAllowedMs

omit [DecidableEq StmtIn] in
/-- The one-pass forward-first builder never inserts the same normalized permutation pair twice.

This fact is independent of the caller's `allowed` table: the `seen` table is updated on the first
occurrence in either direction, and every later occurrence of that pair is ignored. -/
lemma buildForwardPermutationIndex_nodup
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : DuplexSpongeTrace StmtIn U) (allowed : T_P) :
    (TraceTableOps.entries (buildForwardPermutationIndex trace allowed)).Nodup := by
  have fold_nodup : ∀ (remaining : DuplexSpongeTrace StmtIn U)
      (st : ForwardPermutationIndexState T_P),
      (LawfulTraceTable.toMultiSet st.forward).Nodup →
      (∀ a b, (a, b) ∈ LawfulTraceTable.toMultiSet st.forward →
        (a, b) ∈ LawfulTraceTable.toMultiSet st.seen) →
      (LawfulTraceTable.toMultiSet
        (remaining.foldl (forwardPermutationIndexStep allowed) st).forward).Nodup := by
    intro remaining
    induction remaining with
    | nil =>
        intro st hNodup _
        exact hNodup
    | cons entry rest ih =>
        intro st hNodup hSubset
        apply ih (forwardPermutationIndexStep allowed st entry)
        · rcases entry with ⟨q, answer⟩
          rcases q with stmt | input | output
          · exact hNodup
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep]
            split
            · exact hNodup
            · next hNotSeen =>
              split
              · change (LawfulTraceTable.toMultiSet
                    (TraceTableOps.add st.forward input answer)).Nodup
                rw [LawfulTraceTable.toMultiSet_add, Multiset.nodup_cons]
                refine ⟨?_, hNodup⟩
                intro hMemForward
                have hMemSeen := hSubset input answer hMemForward
                exact hNotSeen ((LawfulTraceTable.contains_eq_true st.seen input answer).mpr
                  hMemSeen)
              · exact hNodup
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep]
            split <;> exact hNodup
        · intro a b hMem
          rcases entry with ⟨q, answer⟩
          rcases q with stmt | input | output
          · exact hSubset a b hMem
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep] at hMem
            split at hMem
            · next hSeen =>
              simp only [forwardPermutationIndexStep]
              rw [if_pos hSeen]
              exact hSubset a b hMem
            · next hNotSeen =>
              split at hMem
              · next hAllowed =>
                simp only [forwardPermutationIndexStep]
                rw [if_neg hNotSeen, if_pos hAllowed]
                change (a, b) ∈ LawfulTraceTable.toMultiSet
                  (TraceTableOps.add st.seen input answer)
                rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons]
                change (a, b) ∈ LawfulTraceTable.toMultiSet
                  (TraceTableOps.add st.forward input answer) at hMem
                rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at hMem
                rcases hMem with hEq | hOld
                · exact Or.inl hEq
                · exact Or.inr (hSubset a b hOld)
              · next hNotAllowed =>
                simp only [forwardPermutationIndexStep]
                rw [if_neg hNotSeen, if_neg hNotAllowed]
                change (a, b) ∈ LawfulTraceTable.toMultiSet
                  (TraceTableOps.add st.seen input answer)
                rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons]
                exact Or.inr (hSubset a b hMem)
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep] at hMem
            split at hMem
            · next hSeen =>
              simp only [forwardPermutationIndexStep]
              rw [if_pos hSeen]
              exact hSubset a b hMem
            · next hNotSeen =>
              simp only [forwardPermutationIndexStep]
              rw [if_neg hNotSeen]
              change (a, b) ∈ LawfulTraceTable.toMultiSet
                (TraceTableOps.add st.seen answer output)
              rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons]
              exact Or.inr (hSubset a b hMem)
  have hNodupMs : (LawfulTraceTable.toMultiSet
      (buildForwardPermutationIndex trace allowed)).Nodup := by
    unfold buildForwardPermutationIndex
    apply fold_nodup trace
      { seen := TraceTableOps.empty, forward := TraceTableOps.empty }
    · rw [LawfulTraceTable.toMultiSet_empty]
      simp
    · intro a b hMem
      rw [LawfulTraceTable.toMultiSet_empty] at hMem
      simp at hMem
  rw [← LawfulTraceTable.toMultiSet_ofEntries] at hNodupMs
  exact Multiset.coe_nodup.mp hNodupMs

/-- Every pair emitted by the one-pass builder really has a forward first normalized occurrence.

The proof follows the executable fold. `seen` is complete for the processed prefix, so the branch
that inserts a forward pair supplies exactly the absence fact required by
`PermutationForwardFirst`. -/
lemma buildForwardPermutationIndex_forwardFirst
    [LawfulTraceTable T_P (CanonicalSpongeState U) (CanonicalSpongeState U)]
    (trace : DuplexSpongeTrace StmtIn U) (allowed : T_P)
    (sIn sOut : CanonicalSpongeState U)
    (hMem : (sIn, sOut) ∈ TraceTableOps.entries
      (buildForwardPermutationIndex trace allowed)) :
    PermutationForwardFirst trace sIn sOut := by
  have fold_sound : ∀ (remaining processed : DuplexSpongeTrace StmtIn U)
      (st : ForwardPermutationIndexState T_P),
      st.SeenComplete processed → st.ForwardSound processed →
      (remaining.foldl (forwardPermutationIndexStep allowed) st).ForwardSound
        (processed ++ remaining) := by
    intro remaining
    induction remaining with
    | nil =>
        intro processed st _ hSound
        simpa using hSound
    | cons entry rest ih =>
        intro processed st hSeenComplete hForwardSound
        have hSeenStep :
            (forwardPermutationIndexStep allowed st entry).SeenComplete
              (processed ++ [entry]) := by
          intro a b hPair
          rcases entry with ⟨q, answer⟩
          rcases q with stmt | input | output
          · have hOld : (a, b) ∈ normalizedPermutationPairs processed := by
              simpa [normalizedPermutationPairs] using hPair
            exact hSeenComplete a b hOld
          · change CanonicalSpongeState U at answer
            have hOldOrCurrent :
                (a, b) ∈ normalizedPermutationPairs processed ∨
                  (a, b) = (input, answer) := by
              simpa [normalizedPermutationPairs] using hPair
            simp only [forwardPermutationIndexStep]
            split
            · next hSeen =>
              rcases hOldOrCurrent with hOld | hCurrent
              · exact hSeenComplete a b hOld
              · cases hCurrent
                exact (LawfulTraceTable.contains_eq_true st.seen a b).mp hSeen
            · next hNotSeen =>
              change (a, b) ∈ LawfulTraceTable.toMultiSet
                (TraceTableOps.add st.seen input answer)
              rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons]
              rcases hOldOrCurrent with hOld | hCurrent
              · exact Or.inr (hSeenComplete a b hOld)
              · exact Or.inl hCurrent
          · change CanonicalSpongeState U at answer
            have hOldOrCurrent :
                (a, b) ∈ normalizedPermutationPairs processed ∨
                  (a, b) = (answer, output) := by
              simpa [normalizedPermutationPairs] using hPair
            simp only [forwardPermutationIndexStep]
            split
            · next hSeen =>
              rcases hOldOrCurrent with hOld | hCurrent
              · exact hSeenComplete a b hOld
              · cases hCurrent
                exact (LawfulTraceTable.contains_eq_true st.seen a b).mp hSeen
            · next hNotSeen =>
              change (a, b) ∈ LawfulTraceTable.toMultiSet
                (TraceTableOps.add st.seen answer output)
              rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons]
              rcases hOldOrCurrent with hOld | hCurrent
              · exact Or.inr (hSeenComplete a b hOld)
              · exact Or.inl hCurrent
        have hForwardStep :
            (forwardPermutationIndexStep allowed st entry).ForwardSound
              (processed ++ [entry]) := by
          intro a b hForward
          rcases entry with ⟨q, answer⟩
          rcases q with stmt | input | output
          · exact (hForwardSound a b hForward).append [⟨.inl stmt, answer⟩]
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep] at hForward
            split at hForward
            · exact (hForwardSound a b hForward).append
                [⟨.inr (.inl input), answer⟩]
            · next hNotSeen =>
              split at hForward
              · change (a, b) ∈ LawfulTraceTable.toMultiSet
                    (TraceTableOps.add st.forward input answer) at hForward
                rw [LawfulTraceTable.toMultiSet_add, Multiset.mem_cons] at hForward
                rcases hForward with hCurrent | hOld
                · injection hCurrent with hA hB
                  subst hA
                  subst hB
                  refine ⟨processed, [], ?_, ?_⟩
                  · simp
                  · intro hNormalized
                    have hSeenMem := hSeenComplete a b hNormalized
                    exact hNotSeen
                      ((LawfulTraceTable.contains_eq_true st.seen a b).mpr hSeenMem)
                · exact (hForwardSound a b hOld).append
                    [⟨.inr (.inl input), answer⟩]
              · exact (hForwardSound a b hForward).append
                  [⟨.inr (.inl input), answer⟩]
          · change CanonicalSpongeState U at answer
            simp only [forwardPermutationIndexStep] at hForward
            split at hForward <;>
              exact (hForwardSound a b hForward).append
                [⟨.inr (.inr output), answer⟩]
        have hTail := ih (processed ++ [entry])
          (forwardPermutationIndexStep allowed st entry) hSeenStep hForwardStep
        simpa [List.append_assoc] using hTail
  have hInitialSeen :
      (ForwardPermutationIndexState.mk
        (TraceTableOps.empty : T_P) TraceTableOps.empty).SeenComplete
          ([] : DuplexSpongeTrace StmtIn U) := by
    intro a b hPair
    simp [normalizedPermutationPairs] at hPair
  have hInitialForward :
      (ForwardPermutationIndexState.mk
        (TraceTableOps.empty : T_P) TraceTableOps.empty).ForwardSound
          ([] : DuplexSpongeTrace StmtIn U) := by
    intro a b hPair
    rw [LawfulTraceTable.toMultiSet_empty] at hPair
    simp at hPair
  have hFinal := fold_sound trace []
    { seen := TraceTableOps.empty, forward := TraceTableOps.empty }
    hInitialSeen hInitialForward
  have hMemMs : (sIn, sOut) ∈ LawfulTraceTable.toMultiSet
      (buildForwardPermutationIndex trace allowed) := by
    rw [← LawfulTraceTable.toMultiSet_ofEntries]
    exact hMem
  exact hFinal sIn sOut hMemMs

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

/-- Reference exact-pair membership. The production indexed backend may implement this with its
primary ordered map; the list backend remains the executable refinement model. -/
@[inline] def contains (t : ListTraceTable K V) (k : K) (v : V) : Bool :=
  decide ((k, v) ∈ t.entries)

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
  contains := contains
  inlu  := inlu
  outlu := outlu
  entries t := t.entries

instance instLawfulListBasedTraceTable {K V : Type} [DecidableEq K] [DecidableEq V] :
    LawfulTraceTable (ListTraceTable K V) K V where
  toTraceTableOps     := instListBasedTraceTableOps
  toMultiSet          := toMultiSet
  toMultiSet_empty    := rfl
  toMultiSet_add      := fun _ _ _ => rfl
  contains_eq_true    := by
    intro t k v
    change decide ((k, v) ∈ t.entries) = true ↔ (k, v) ∈ t.entries
    simp
  inlu_eq_some        := fun t k v => inlu_eq_some_iff t k v
  outlu_eq_some       := fun t k v => outlu_eq_some_iff t k v
  toMultiSet_ofEntries  := fun _ => rfl

/-! ### Default `tr_∇` type alias and `ofQueryLog` -/

instance instLawfulTraceNablaImplListBased [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq U] :
    LawfulTraceNablaImpl
      (ListBacked.ListTraceTable StmtIn (Vector U SpongeSize.C))
      (ListBacked.ListTraceTable (CanonicalSpongeState U) (CanonicalSpongeState U))
      StmtIn U where
  lawfulHash := instLawfulListBasedTraceTable
  lawfulPermutation := instLawfulListBasedTraceTable
  hashCapOutlu t cap := TraceLookupResult.ofList <|
    t.entries.filterMap fun pair => if pair.2 = cap then some pair.1 else none
  permCapOutlu t cap := TraceLookupResult.ofList <|
    t.entries.filterMap fun pair =>
      if pair.2.capacitySegment = cap then some pair else none
  hashCapOutlu_eq _ _ := rfl
  permCapOutlu_eq _ _ := rfl

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
