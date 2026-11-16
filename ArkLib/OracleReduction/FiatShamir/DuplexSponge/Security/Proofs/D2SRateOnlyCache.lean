/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.TraceDataStructures

/-!
# Rate-only lazy cache for revised D2SQuery

The Section 5.4 oracle wrapper `D2SQuery` never stores a latent full permutation output in
`Cache_p`; this refines the paper's `Cache_p` by sampling capacities lazily. A cache entry stores
only the next rate block and the remaining rate blocks of a programmed verifier squeeze. When a
forward query consumes the entry, the oracle wrapper samples exactly one fresh capacity, installs
the resulting full mapping, and moves any residual rate tail to that new output state.
-/

@[expose] public section

/-!
## D2S cache and synthesis layout

The small, trace-facing operations used by the `D2SQuery` oracle wrapper's cache and by the
Item 4(e)iiiC state synthesis branch. Keeping them outside `ProverTransform` makes their
capacity provenance reusable in the Lemma 5.8 `E_func` proof without exposing the oracle
wrapper's internal control flow.
-/

namespace DuplexSpongeFS.ProverTransform

variable {U : Type} [SpongeUnit U] [SpongeSize]

/-- **[CO25, §5.4]** Item 4(e)iiiC — the observable permutation state assembled from one
verifier-rate block and its freshly sampled capacity block. -/
def d2sSynthesisState
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState U :=
  (Vector.append rateSeg capSeg).cast (by
    simp [SpongeSize.R_plus_C_eq_N])

/-- The rate of a synthesized state is the programmed rate block itself.  Together with the
capacity identity below, this is the exact state-layout fact used when a lazy `rateCacheP` tail
is consumed by the verifier squeeze. -/
lemma d2sSynthesisState_rateSegment
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState.rateSegment
      (d2sSynthesisState (U := U) rateSeg capSeg) = rateSeg := by
  rw [← Vector.toList_inj]
  change ((d2sSynthesisState (U := U) rateSeg capSeg).take SpongeSize.R).toList
    = rateSeg.toList
  rw [Vector.toList_take, d2sSynthesisState, Vector.toList_cast]
  have happend : (rateSeg.append capSeg).toList = rateSeg.toList ++ capSeg.toList :=
    Vector.toList_append
  rw [happend]
  exact List.take_left' (by simp)

/-- The capacity of a synthesized state is exactly its corresponding sampled capacity block. -/
lemma d2sSynthesisState_capacitySegment
    (rateSeg : Vector U SpongeSize.R)
    (capSeg : Vector U SpongeSize.C) :
    CanonicalSpongeState.capacitySegment
      (d2sSynthesisState (U := U) rateSeg capSeg) = capSeg := by
  change Vector.drop ((Vector.append rateSeg capSeg).cast (by
    rw [SpongeSize.R_plus_C_eq_N])) SpongeSize.R = capSeg
  ext i
  simp only [Vector.drop_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract]
  have hi : SpongeSize.R + i < SpongeSize.R + SpongeSize.C := by
    rw [SpongeSize.R_plus_C_eq_N]
    omega
  change (rateSeg ++ capSeg)[SpongeSize.R + i]'hi = capSeg[i]
  rw [Vector.getElem_append_right]
  · simp only [Nat.add_sub_cancel_left]
    exact Eq.refl _
  · omega

end DuplexSpongeFS.ProverTransform


open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

variable {U : Type} [SpongeUnit U] [SpongeSize] [DecidableEq U]

/-- The as-yet unmaterialized rate blocks of one verifier-squeeze continuation. -/
structure RateOnlyTail where
  nextRate : Vector U SpongeSize.R
  remaining : List (Vector U SpongeSize.R)

/-- The complete sequence of pending rate blocks in source order. -/
def RateOnlyTail.blocks (tail : RateOnlyTail (U := U)) : List (Vector U SpongeSize.R) :=
  tail.nextRate :: tail.remaining

/-- Turn a nonempty parsed verifier-rate sequence into a pending tail. -/
def RateOnlyTail.ofBlocks? : List (Vector U SpongeSize.R) → Option (RateOnlyTail (U := U))
  | [] => none
  | nextRate :: remaining => some ⟨nextRate, remaining⟩

omit [SpongeUnit U] [DecidableEq U] in
/-- Recover the full pending block sequence from a successful tail installation. This bridges
the successful-squeeze head's remainingRates list to the tail induction. -/
lemma RateOnlyTail.blocks_eq_of_ofBlocks?_eq_some
    (blocks : List (Vector U SpongeSize.R))
    (tail : RateOnlyTail (U := U))
    (hblocks : RateOnlyTail.ofBlocks? (U := U) blocks = some tail) :
    tail.blocks = blocks := by
  cases blocks with
  | nil => simp [RateOnlyTail.ofBlocks?] at hblocks
  | cons next remaining =>
      have htail : tail = ⟨next, remaining⟩ :=
        (Option.some.inj hblocks).symm
      subst tail
      rfl

/-- Advance a tail after materializing its next block. -/
def RateOnlyTail.advance? : RateOnlyTail (U := U) → Option (RateOnlyTail (U := U))
  | ⟨_, []⟩ => none
  | ⟨_, next :: remaining⟩ => some ⟨next, remaining⟩

omit [SpongeUnit U] [DecidableEq U] in
@[simp] lemma RateOnlyTail.advance?_none_iff (tail : RateOnlyTail (U := U)) :
    tail.advance? = none ↔ tail.remaining = [] := by
  cases tail with
  | mk next remaining =>
      cases remaining <;> simp [RateOnlyTail.advance?]

omit [SpongeUnit U] [DecidableEq U] in
/-- Advancing a pending tail discards exactly its already-materialized rate block.  This is the
list-level invariant that aligns a rekeyed lazy cache entry with the next permutation boundary
of the verifier's sponge squeeze. -/
lemma RateOnlyTail.blocks_advance?
    (tail successor : RateOnlyTail (U := U))
    (hadvance : tail.advance? = some successor) :
    successor.blocks = tail.blocks.tail := by
  cases tail with
  | mk next remaining =>
      cases remaining with
      | nil => simp [RateOnlyTail.advance?] at hadvance
      | cons next' remaining' =>
          simp only [RateOnlyTail.advance?, Option.some.injEq] at hadvance
          subst successor
          rfl

/-- A rate-only tail is keyed by the already materialized input of its next forward query. -/
structure RateOnlyCacheEntry where
  stateIn : CanonicalSpongeState U
  tail : RateOnlyTail (U := U)

/-- Pending tails are keyed uniquely by their next full input state. -/
def RateOnlyCacheKeysNodup (cache : List (RateOnlyCacheEntry (U := U))) : Prop :=
  (cache.map RateOnlyCacheEntry.stateIn).Nodup

/-- Remove the first tail record keyed by `stateIn`. -/
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

lemma popRateOnlyTailByInput_eq_none_iff
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U) :
    popRateOnlyTailByInput cache stateIn = none ↔
      ∀ entry ∈ cache, entry.stateIn ≠ stateIn := by
  induction cache with
  | nil => simp [popRateOnlyTailByInput]
  | cons head cache ih =>
    by_cases hEq : head.stateIn = stateIn
    · simp [popRateOnlyTailByInput, hEq]
    · simp only [popRateOnlyTailByInput, hEq, ite_false, List.mem_cons, forall_eq_or_imp]
      cases hPop : popRateOnlyTailByInput cache stateIn <;> simp_all

lemma popRateOnlyTailByInput_some_mem
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∃ entry ∈ cache, entry.stateIn = stateIn ∧ entry.tail = tail := by
  induction cache generalizing tail rest with
  | nil => simp [popRateOnlyTailByInput] at hpop
  | cons entry cache ih =>
    simp only [popRateOnlyTailByInput] at hpop
    split at hpop
    · simp_all
    · cases hTail : popRateOnlyTailByInput cache stateIn with
      | none => simp [hTail] at hpop
      | some result => grind

lemma popRateOnlyTailByInput_rest_subset
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∀ entry, entry ∈ rest → entry ∈ cache := by
  induction cache generalizing tail rest with
  | nil => simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
    simp only [popRateOnlyTailByInput] at hpop
    split at hpop
    · simp_all
    · cases hTail : popRateOnlyTailByInput cache stateIn with
      | none => simp [hTail] at hpop
      | some result => grind

lemma popRateOnlyTailByInput_rest_keys_nodup
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    RateOnlyCacheKeysNodup rest := by
  induction cache generalizing tail rest with
  | nil => simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
    simp only [RateOnlyCacheKeysNodup, List.map_cons, List.nodup_cons] at hNodup
    simp only [popRateOnlyTailByInput] at hpop
    split at hpop
    · simp_all [RateOnlyCacheKeysNodup]
    · cases hTail : popRateOnlyTailByInput cache stateIn with
      | none => simp [hTail] at hpop
      | some result =>
        have hSub := popRateOnlyTailByInput_rest_subset cache stateIn result.1 result.2 hTail
        have hRec := ih result.1 result.2 hNodup.2 hTail
        grind [RateOnlyCacheKeysNodup]

lemma popRateOnlyTailByInput_rest_key_ne
    (cache : List (RateOnlyCacheEntry (U := U))) (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U)) (rest : List (RateOnlyCacheEntry (U := U)))
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, rest)) :
    ∀ entry ∈ rest, entry.stateIn ≠ stateIn := by
  induction cache generalizing tail rest with
  | nil => simp [popRateOnlyTailByInput] at hpop
  | cons head cache ih =>
    simp only [RateOnlyCacheKeysNodup, List.map_cons, List.nodup_cons] at hNodup
    have hCache : RateOnlyCacheKeysNodup cache := hNodup.2
    simp only [popRateOnlyTailByInput] at hpop
    split at hpop
    · simp_all
    · cases hTail : popRateOnlyTailByInput cache stateIn with
      | none => simp [hTail] at hpop
      | some result => grind

omit [DecidableEq U] in
/-- Appending one newly-programmed tail preserves unique outstanding keys when its materialized
input is distinct from every old key.  This is the tail-creation counterpart of
`materializePoppedRateOnlyTail_keys_nodup`: a successful `BackTrack` squeeze creates one
continuation, whereas a cache hit removes and possibly rekeys one. -/
lemma RateOnlyCacheKeysNodup_append_singleton
    (cache : List (RateOnlyCacheEntry (U := U)))
    (entry : RateOnlyCacheEntry (U := U))
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hnew : ∀ old ∈ cache, old.stateIn ≠ entry.stateIn) :
    RateOnlyCacheKeysNodup (cache ++ [entry]) := by
  unfold RateOnlyCacheKeysNodup at hNodup ⊢
  rw [List.map_append, List.nodup_append]
  refine ⟨hNodup, List.nodup_singleton _, ?_⟩
  intro a ha b hb
  have hb' : b = entry.stateIn := by simpa using hb
  subst b
  rcases List.mem_map.mp ha with ⟨old, hold, rfl⟩
  exact hnew old hold

/-- Materialize exactly the next pending rate block with one newly sampled capacity block. -/
def materializeRateOnlyTail
    (tail : RateOnlyTail (U := U))
    (capacity : Vector U SpongeSize.C) :
    CanonicalSpongeState U × Option (RateOnlyTail (U := U)) :=
  (d2sSynthesisState (U := U) tail.nextRate capacity, tail.advance?)

/-- Materialize one cache record, rekeying a residual continuation at the output. -/
def materializeRateOnlyCacheEntry
    (entry : RateOnlyCacheEntry (U := U))
    (capacity : Vector U SpongeSize.C) :
    CanonicalSpongeState U × Option (RateOnlyCacheEntry (U := U)) :=
  let result := materializeRateOnlyTail (U := U) entry.tail capacity
  (result.1, result.2.map fun tail => ⟨result.1, tail⟩)

/-- Realize a tail that has already been removed from the cache lookup.  The result is the
fresh full output together with the residual cache, rekeyed at that output when a tail remains.
This is the whole rate-only analogue of Michele's old pure full-pair cache pop. -/
def materializePoppedRateOnlyTail
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) :
    CanonicalSpongeState U × List (RateOnlyCacheEntry (U := U)) :=
  let materialized := materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity
  let cache' := match materialized.2 with
    | none => cacheTail
    | some successor => successor :: cacheTail
  (materialized.1, cache')

/-- Popping a unique pending tail preserves unique cache keys once the newly materialized
output is known not to be an outstanding key.  This is the only list-level fact the stopped
rate-only executor needs after a successful cache consumption; the semantic proof supplies the
fresh-key premise by stopping on the corresponding first bad occurrence. -/
lemma materializePoppedRateOnlyTail_keys_nodup
    (cache : List (RateOnlyCacheEntry (U := U)))
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (hNodup : RateOnlyCacheKeysNodup cache)
    (hpop : popRateOnlyTailByInput cache stateIn = some (tail, cacheTail))
    (hnew : ∀ entry ∈ cacheTail,
      entry.stateIn ≠
        (materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity).1) :
    RateOnlyCacheKeysNodup
      (materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity).2 := by
  have htailNodup : RateOnlyCacheKeysNodup cacheTail :=
    popRateOnlyTailByInput_rest_keys_nodup cache stateIn tail cacheTail hNodup hpop
  unfold materializePoppedRateOnlyTail
  dsimp only
  cases hadvance : tail.advance? with
  | none =>
      simpa [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] using htailNodup
  | some successorTail =>
      have hnew' : ∀ entry ∈ cacheTail,
          entry.stateIn ≠ d2sSynthesisState (U := U) tail.nextRate capacity := by
        intro entry hentry hEq
        apply hnew entry hentry
        simpa [materializePoppedRateOnlyTail, materializeRateOnlyCacheEntry,
          materializeRateOnlyTail, hadvance] using hEq
      have hresult : RateOnlyCacheKeysNodup
          (⟨d2sSynthesisState (U := U) tail.nextRate capacity, successorTail⟩ :: cacheTail) := by
        unfold RateOnlyCacheKeysNodup
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, htailNodup⟩
        intro hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, hstate⟩
        exact hnew' entry hentry hstate
      simpa [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] using hresult

omit [DecidableEq U] in
/-- Every tail remaining after a materialized cache pop is either one of the untouched cache
records or the unique residual tail re-keyed at the materialized output.  This is the structural
case split used by the private stopped observer; it keeps re-key bookkeeping out of the public
`D2SQuery` interface. -/
lemma materializePoppedRateOnlyTail_mem_cases
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C)
    (entry : RateOnlyCacheEntry (U := U))
    (hmem : entry ∈
      (materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity).2) :
    entry ∈ cacheTail ∨
      ∃ successorTail : RateOnlyTail (U := U), tail.advance? = some successorTail ∧
        entry = ⟨(materializePoppedRateOnlyTail (U := U)
          stateIn tail cacheTail capacity).1, successorTail⟩ := by
  unfold materializePoppedRateOnlyTail at hmem
  dsimp only at hmem
  cases hadvance : tail.advance? with
  | none =>
      exact Or.inl (by
        simpa [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] using hmem)
  | some successorTail =>
      rcases (List.mem_cons.mp (by
        simpa [materializeRateOnlyCacheEntry, materializeRateOnlyTail, hadvance] using hmem)) with
        hsuccessor | hcache
      · right
        refine ⟨successorTail, rfl, ?_⟩
        simpa [materializePoppedRateOnlyTail, materializeRateOnlyCacheEntry,
          materializeRateOnlyTail, hadvance] using hsuccessor
      · exact Or.inl hcache

omit [DecidableEq U] in
lemma materializeRateOnlyCacheEntry_capacitySegment
    (entry : RateOnlyCacheEntry (U := U))
    (capacity : Vector U SpongeSize.C) :
    (materializeRateOnlyCacheEntry (U := U) entry capacity).1.capacitySegment = capacity := by
  change (d2sSynthesisState (U := U) entry.tail.nextRate capacity).capacitySegment = capacity
  exact d2sSynthesisState_capacitySegment _ _

omit [DecidableEq U] in
/-- Materializing a pending cache tail makes its next programmed rate block visible to the
sponge.  The capacity is fresh entropy, but the rate is fixed by the decoded verifier message. -/
lemma materializePoppedRateOnlyTail_fst_rateSegment
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) :
    (materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity).1.rateSegment
      = tail.nextRate := by
  change (d2sSynthesisState (U := U) tail.nextRate capacity).rateSegment = tail.nextRate
  exact d2sSynthesisState_rateSegment _ _

omit [DecidableEq U] in
@[simp] lemma materializePoppedRateOnlyTail_fst_capacitySegment
    (stateIn : CanonicalSpongeState U)
    (tail : RateOnlyTail (U := U))
    (cacheTail : List (RateOnlyCacheEntry (U := U)))
    (capacity : Vector U SpongeSize.C) :
    (materializePoppedRateOnlyTail (U := U) stateIn tail cacheTail capacity).1.capacitySegment
      = capacity := by
  change (materializeRateOnlyCacheEntry (U := U) ⟨stateIn, tail⟩ capacity).1.capacitySegment
    = capacity
  exact materializeRateOnlyCacheEntry_capacitySegment _ _

end DuplexSpongeFS.ProverTransform
