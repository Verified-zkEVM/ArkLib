/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SSynthesis

/-!
# Rate-only lazy cache for revised D2SQuery

The corrected Section 5.4 simulator never stores a latent full permutation output in `Cache_p`.
A cache entry stores only the next rate block and the remaining rate blocks of a programmed
verifier squeeze.  When a forward query consumes the entry, the simulator samples exactly one
fresh capacity, installs the resulting full mapping, and moves any residual rate tail to that
new output state.

This deliberately excludes the old full-state cache representation: a rate-only entry has no
output capacity and therefore cannot be observed by an inverse-permutation query.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

variable {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]

/-- The as-yet unmaterialized rate blocks of one verifier-squeeze continuation.
`nextRate` is the rate block consumed by the next forward query at the cache key; `remaining`
contains the blocks after it.  No capacity is stored. -/
structure RateOnlyTail where
  nextRate : Vector U SpongeSize.R
  remaining : List (Vector U SpongeSize.R)

/-- The complete sequence of pending rate blocks in source order. -/
def RateOnlyTail.blocks (tail : RateOnlyTail (U := U)) : List (Vector U SpongeSize.R) :=
  tail.nextRate :: tail.remaining

/-- Turn a nonempty parsed verifier-rate sequence into a pending tail.  This is used for the
first block of the `Program` branch as well as for every later cache continuation. -/
def RateOnlyTail.ofBlocks? : List (Vector U SpongeSize.R) → Option (RateOnlyTail (U := U))
  | [] => none
  | nextRate :: remaining => some ⟨nextRate, remaining⟩

@[simp] lemma RateOnlyTail.ofBlocks?_blocks
    (nextRate : Vector U SpongeSize.R) (remaining : List (Vector U SpongeSize.R)) :
    (RateOnlyTail.ofBlocks? (U := U) (nextRate :: remaining)).map RateOnlyTail.blocks =
      some (nextRate :: remaining) := by
  simp [RateOnlyTail.ofBlocks?, RateOnlyTail.blocks]

/-- Advance a tail after materializing its next block.  `none` means that the consumed block was
the final pending block. -/
def RateOnlyTail.advance? : RateOnlyTail (U := U) → Option (RateOnlyTail (U := U))
  | ⟨_, []⟩ => none
  | ⟨_, next :: remaining⟩ => some ⟨next, remaining⟩

@[simp] lemma RateOnlyTail.blocks_length (tail : RateOnlyTail (U := U)) :
    tail.blocks.length = tail.remaining.length + 1 := by
  simp [RateOnlyTail.blocks, Nat.add_comm]

@[simp] lemma RateOnlyTail.advance?_none_iff (tail : RateOnlyTail (U := U)) :
    tail.advance? = none ↔ tail.remaining = [] := by
  cases tail with
  | mk next remaining =>
      cases remaining <;> simp [RateOnlyTail.advance?]

/-- A rate-only tail is keyed by the already materialized full input state of its next forward
permutation call.  The entry stores no output state and no output capacity. -/
structure RateOnlyCacheEntry where
  stateIn : CanonicalSpongeState U
  tail : RateOnlyTail (U := U)

/-- Pending tails are keyed uniquely by their next full input state.  This is the semantic
invariant behind `popRateOnlyTailByInput`: the executable function removes the first matching
record, while a well-formed D2SQuery run guarantees that no second matching record exists. -/
def RateOnlyCacheKeysNodup (cache : List (RateOnlyCacheEntry (U := U))) : Prop :=
  (cache.map RateOnlyCacheEntry.stateIn).Nodup

/-- Remove the unique first tail record for `stateIn`, returning its pending rate-only tail and
the cache with that record removed.  The D2SQuery invariant establishes uniqueness; this
executable operation remains total even before that invariant is proved. -/
def popRateOnlyTailByInput :
    List (RateOnlyCacheEntry (U := U)) → CanonicalSpongeState U →
      Option (RateOnlyTail (U := U) × List (RateOnlyCacheEntry (U := U)))
  | [], _ => none
  | entry :: rest, stateIn =>
      if entry.stateIn = stateIn then
        some (entry.tail, rest)
      else
        match popRateOnlyTailByInput rest stateIn with
        | none => none
        | some (tail, rest') => some (tail, entry :: rest')

/-- A failed cache pop means precisely that no pending tail is keyed by the queried state.
This is the small dispatcher-order bridge used by the ordinary forward branch: after a failed
cache lookup, a fresh forward installation cannot overwrite the table-miss fact of any retained
tail key merely by adding at the queried input. -/
lemma popRateOnlyTailByInput_eq_none_iff
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U) :
    popRateOnlyTailByInput cache stateIn = none ↔
      ∀ entry ∈ cache, entry.stateIn ≠ stateIn := by
  induction cache with
  | nil => simp [popRateOnlyTailByInput]
  | cons head cache ih =>
      by_cases hEq : head.stateIn = stateIn
      · constructor
        · intro h
          simp [popRateOnlyTailByInput, hEq] at h
        · intro h
          exact False.elim (h head (by simp) hEq)
      · constructor
        · intro h entry hEntry hEntryEq
          rcases List.mem_cons.mp hEntry with hHead | hTail
          · subst entry
            exact hEq hEntryEq
          · apply (ih.mp ?_) entry hTail hEntryEq
            cases hPop : popRateOnlyTailByInput cache stateIn with
            | none => rfl
            | some result =>
                simp [popRateOnlyTailByInput, hEq, hPop] at h
        · intro h
          have hTail : ∀ entry ∈ cache, entry.stateIn ≠ stateIn := by
            intro entry hEntry hEntryEq
            exact h entry (List.mem_cons_of_mem _ hEntry) hEntryEq
          have hPop := ih.mpr hTail
          simp [popRateOnlyTailByInput, hEq, hPop]

/-- A successful pop names an entry that was present at the input cache. -/
lemma popRateOnlyTailByInput_some_mem
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∃ entry ∈ cache, entry.stateIn = stateIn ∧ entry.tail = tail := by
  induction cache generalizing tail rest with
  | nil =>
      simp [popRateOnlyTailByInput] at hpop
  | cons entry cache ih =>
      by_cases hEq : entry.stateIn = stateIn
      · simp [popRateOnlyTailByInput, hEq] at hpop
        rcases hpop with ⟨rfl, rfl⟩
        exact ⟨entry, by simp, hEq, rfl⟩
      · simp only [popRateOnlyTailByInput, if_neg hEq] at hpop
        cases htail : popRateOnlyTailByInput cache stateIn with
        | none => simp [htail] at hpop
        | some result =>
            cases result with
            | mk tail' rest' =>
                simp [htail] at hpop
                rcases hpop with ⟨rfl, rfl⟩
                rcases ih tail' rest' htail with ⟨old, hmem, hstate, htailEq⟩
                exact ⟨old, by simp [hmem], hstate, htailEq⟩

/-- Popping a tail removes at most the selected record: every record retained in the returned
cache was already present before the pop.  This is the list-level transport fact used to preserve
the rate-only-cache execution invariant across a tail materialization. -/
lemma popRateOnlyTailByInput_rest_subset
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∀ entry, entry ∈ rest → entry ∈ cache := by
  induction cache generalizing tail rest with
  | nil =>
      simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
      by_cases hEq : head.stateIn = stateIn
      · simp [popRateOnlyTailByInput, hEq] at hpop
        rcases hpop with ⟨rfl, rfl⟩
        intro entry hEntry
        exact List.mem_cons_of_mem _ hEntry
      · simp only [popRateOnlyTailByInput, if_neg hEq] at hpop
        cases hTail : popRateOnlyTailByInput cache stateIn with
        | none => simp [hTail] at hpop
        | some result =>
            rcases result with ⟨tail', rest'⟩
            simp [hTail] at hpop
            rcases hpop with ⟨rfl, rfl⟩
            intro entry hEntry
            rcases List.mem_cons.mp hEntry with rfl | hEntry
            · simp
            · exact List.mem_cons_of_mem _ (ih tail' rest' hTail entry hEntry)

/-- Removing a selected tail preserves uniqueness of the keys retained in the cache.  This is
the list-level part of the stateful lazy-cache invariant: a tail materialization may re-key one
residual record, but the pop itself cannot introduce a duplicate key. -/
lemma popRateOnlyTailByInput_rest_keys_nodup
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    RateOnlyCacheKeysNodup rest := by
  induction cache generalizing tail rest with
  | nil =>
      simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
      unfold RateOnlyCacheKeysNodup at hNodup ⊢
      simp only [List.map_cons, List.nodup_cons] at hNodup
      rcases hNodup with ⟨hHead, hCache⟩
      by_cases hEq : head.stateIn = stateIn
      · simp [popRateOnlyTailByInput, hEq] at hpop
        rcases hpop with ⟨rfl, rfl⟩
        exact hCache
      · simp only [popRateOnlyTailByInput, if_neg hEq] at hpop
        cases hTail : popRateOnlyTailByInput cache stateIn with
        | none => simp [hTail] at hpop
        | some result =>
            rcases result with ⟨tail', rest'⟩
            simp [hTail] at hpop
            rcases hpop with ⟨rfl, rfl⟩
            refine List.nodup_cons.mpr ⟨?_, ih tail' rest' ?_ hTail⟩
            · intro hMem
              apply hHead
              rcases List.mem_map.mp hMem with ⟨entry, hEntry, hState⟩
              refine List.mem_map.mpr ⟨entry, ?_, hState⟩
              exact popRateOnlyTailByInput_rest_subset cache stateIn tail' rest' hTail entry hEntry
            · exact hCache

/-- Every key retained after a successful pop differs from the selected key.  Together with
`popRateOnlyTailByInput_rest_keys_nodup`, this is the exact list fact needed before re-keying a
tail residual at its newly materialized output. -/
lemma popRateOnlyTailByInput_rest_key_ne
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∀ entry ∈ rest, entry.stateIn ≠ stateIn := by
  induction cache generalizing tail rest with
  | nil =>
      simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
      unfold RateOnlyCacheKeysNodup at hNodup
      simp only [List.map_cons, List.nodup_cons] at hNodup
      rcases hNodup with ⟨hHead, hCache⟩
      by_cases hEq : head.stateIn = stateIn
      · simp [popRateOnlyTailByInput, hEq] at hpop
        rcases hpop with ⟨rfl, rfl⟩
        intro entry hEntry hEntryEq
        apply hHead
        exact List.mem_map.mpr ⟨entry, hEntry, hEntryEq.trans hEq.symm⟩
      · simp only [popRateOnlyTailByInput, if_neg hEq] at hpop
        cases hTail : popRateOnlyTailByInput cache stateIn with
        | none => simp [hTail] at hpop
        | some result =>
            rcases result with ⟨tail', rest'⟩
            simp [hTail] at hpop
            rcases hpop with ⟨rfl, rfl⟩
            intro entry hEntry hEntryEq
            rcases List.mem_cons.mp hEntry with hHeadEntry | hRestEntry
            · subst entry
              exact hEq hEntryEq
            · exact ih tail' rest' hCache hTail entry hRestEntry hEntryEq

/-- Materialize exactly the next pending rate block with one newly sampled capacity block.

This is the only operation that turns a latent `RateOnlyTail` into an observable full sponge
state.  In particular, no capacity is chosen when the tail is created. -/
def materializeRateOnlyTail
    (tail : RateOnlyTail (U := U))
    (capacity : Vector U SpongeSize.C) :
    CanonicalSpongeState U × Option (RateOnlyTail (U := U)) :=
  (d2sSynthesisState (U := U) tail.nextRate capacity, tail.advance?)

/-- Materialize one cache record.  If a rate-only continuation remains, it is re-keyed at the
newly materialized output state; otherwise the record is discharged. -/
def materializeRateOnlyCacheEntry
    (entry : RateOnlyCacheEntry (U := U))
    (capacity : Vector U SpongeSize.C) :
    CanonicalSpongeState U × Option (RateOnlyCacheEntry (U := U)) :=
  let result := materializeRateOnlyTail (U := U) entry.tail capacity
  (result.1, result.2.map fun tail => ⟨result.1, tail⟩)

/-- Consume the unique tail keyed by `stateIn`, using a capacity supplied at that consumption.
The returned cache contains the residual tail, if any, keyed by the newly materialized output.
No output capacity is stored before this operation. -/
def consumeRateOnlyCache
    (cache : List (RateOnlyCacheEntry (U := U)))
    (stateIn : CanonicalSpongeState U)
    (capacity : Vector U SpongeSize.C) :
    Option (CanonicalSpongeState U × List (RateOnlyCacheEntry (U := U))) :=
  match popRateOnlyTailByInput cache stateIn with
  | none => none
  | some (tail, cacheRest) =>
      let materialized := materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity
      let cache' := match materialized.2 with
        | none => cacheRest
        | some successor => successor :: cacheRest
      some (materialized.1, cache')

/-- The output of a materialized cache record has exactly the capacity supplied at that one
materialization.  Re-keying a residual tail changes only its input key, never this fact. -/
lemma materializeRateOnlyCacheEntry_capacitySegment
    (entry : RateOnlyCacheEntry (U := U))
    (capacity : Vector U SpongeSize.C) :
    (materializeRateOnlyCacheEntry (U := U) entry capacity).1.capacitySegment = capacity := by
  change (d2sSynthesisState (U := U) entry.tail.nextRate capacity).capacitySegment = capacity
  exact d2sSynthesisState_capacitySegment _ _

/-- A residual cache entry is keyed at the full state just materialized from the preceding
entry.  This is independent of the sampled capacity and is the provenance link used by the
stateful cache invariant. -/
lemma materializeRateOnlyCacheEntry_some_stateIn
    (entry : RateOnlyCacheEntry (U := U))
    (capacity : Vector U SpongeSize.C)
    (successor : RateOnlyCacheEntry (U := U))
    (hmaterialize : (materializeRateOnlyCacheEntry (U := U) entry capacity).2 = some successor) :
    successor.stateIn = (materializeRateOnlyCacheEntry (U := U) entry capacity).1 := by
  cases hadvance : entry.tail.advance? with
  | none =>
      simp [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] at hmaterialize
  | some tail =>
      have hsuccessor : successor =
          ⟨(materializeRateOnlyCacheEntry (U := U) entry capacity).1, tail⟩ := by
        simpa [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] using
          hmaterialize.symm
      subst successor
      rfl

end DuplexSpongeFS.ProverTransform
