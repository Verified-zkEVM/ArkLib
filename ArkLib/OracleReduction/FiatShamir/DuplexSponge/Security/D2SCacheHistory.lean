/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Backtrack
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SSynthesis

/-!
# D2S cache history

The D2S simulator keeps latent permutation pairs in `Cache_p`.  For the `E_func` part of
Lemma 5.8 we also retain their *birth trace position*: it identifies the base-trace prefix
which existed before the capacity used to assemble the cache entry was sampled.  Consuming an
entry moves it into `cacheHistory`, without changing the observable D2S trace.
-/

open OracleComp OracleSpec ProtocolSpec
namespace DuplexSpongeFS.ProverTransform
open Backtrack DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : Nat}

local instance : Inhabited U := ⟨0⟩
noncomputable section

section D2SCacheHistory

variable [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- A latent Item 4(e)iiiC forward-permutation pair together with the exact raw trace prefix
present before its capacity samples were drawn.  `birthRawTraceLength` is the length of that
prefix.  Keeping the prefix, rather than only its length, is
what makes the Eq. (33) causality claim expressible: it pins a cache pair to the random draw
which created it. -/
structure CacheEntry where
  stateIn : CanonicalSpongeState U
  stateOut : CanonicalSpongeState U
  birthRawTraceLength : Nat
  birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)
  /-- Index of the capacity block which assembled `stateIn` in the originating
  Item 4(e)iiiC synthesis call.  This is proof metadata: cache lookup depends only on
  `stateIn` and `stateOut`. -/
  birthCapacityIndex : Nat

/-- Evidence that a latent cache entry was actually consumed by Item 4(c)i.  The consuming
base index is retained separately from the entry's birth index: an arbitrary number of hash
queries and redundant trace entries may occur between them.  This makes the later proof relate a
final `funcConflictAt · j j'` witness to the particular cache-pop transition that created base
position `j`. -/
structure ConsumedCacheEntry where
  entry : CacheEntry (StmtIn := StmtIn) (U := U)
  consumptionRawTraceLength : Nat
  consumptionTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U)

/-- Forget the proof-facing birth position of a cache entry. -/
def CacheEntry.pair (entry : CacheEntry (StmtIn := StmtIn) (U := U)) :
    CanonicalSpongeState U × CanonicalSpongeState U :=
  (entry.stateIn, entry.stateOut)

/-- Attach the common sampling-prefix position to a synthesized cache chain. -/
def cacheEntriesFromPairs
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    List (CacheEntry (StmtIn := StmtIn) (U := U)) :=
  pairs.map fun pair => ⟨pair.1, pair.2, birthRawTraceLength, birthTrace, 0⟩

lemma cacheEntriesFromPairs_length
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (pairs : List (CanonicalSpongeState U × CanonicalSpongeState U)) :
    (cacheEntriesFromPairs (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace pairs).length = pairs.length := by
  unfold cacheEntriesFromPairs
  rw [List.length_map]

/-- Every entry minted by one synthesis branch remembers that branch's pre-sampling trace. -/
lemma cacheEntriesFromPairs_mem_birthTrace
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (pairs : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (entry : CacheEntry (StmtIn := StmtIn) (U := U))
    (hmem : entry ∈ cacheEntriesFromPairs (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace pairs) :
    entry.birthTrace = birthTrace := by
  unfold cacheEntriesFromPairs at hmem
  obtain ⟨pair, _hpair, hEntry⟩ := List.mem_map.mp hmem
  cases pair with
  | mk stateIn stateOut =>
      rw [← hEntry]

/-- Membership in a synthesized cache chain exposes the exact latent input/output pair. -/
lemma cacheEntriesFromPairs_mem_iff
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (pairs : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (entry : CacheEntry (StmtIn := StmtIn) (U := U)) :
    entry ∈ cacheEntriesFromPairs (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace pairs ↔
      (entry.stateIn, entry.stateOut) ∈ pairs ∧
        entry.birthRawTraceLength = birthRawTraceLength ∧ entry.birthTrace = birthTrace ∧
          entry.birthCapacityIndex = 0 := by
  constructor
  · intro hmem
    unfold cacheEntriesFromPairs at hmem
    obtain ⟨pair, hpair, hEntry⟩ := List.mem_map.mp hmem
    cases pair with
    | mk stateIn stateOut =>
        rw [← hEntry]
        exact ⟨hpair, rfl, rfl, rfl⟩
  · rintro ⟨hpair, hLength, hTrace, hIndex⟩
    unfold cacheEntriesFromPairs
    apply List.mem_map.mpr
    refine ⟨(entry.stateIn, entry.stateOut), hpair, ?_⟩
    cases entry with
    | mk stateIn stateOut entryLength entryTrace entryIndex =>
        dsimp at hLength hTrace hIndex ⊢
        rw [hLength, hTrace, hIndex]

/-- Turn a consecutive state chain into latent forward-permutation cache entries.  The
`birthCapacityIndex` is the position of each entry's input state in the chain.  This is the
provenance-preserving version of the old pair-list conversion used by Item 4(e)iiiC. -/
def cacheEntriesFromStateChainAux
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (startIndex : Nat) :
    List (CanonicalSpongeState U) → List (CacheEntry (StmtIn := StmtIn) (U := U))
  | [] => []
  | [_] => []
  | stateIn :: stateOut :: tail =>
      ⟨stateIn, stateOut, birthRawTraceLength, birthTrace, startIndex⟩ ::
        cacheEntriesFromStateChainAux birthRawTraceLength birthTrace
          (startIndex + 1) (stateOut :: tail)

/-- Provenance-preserving Item-4(e)iiiC cache construction.  Entry `i` is precisely the
latent pair from the synthesized state at index `i` to the following state, and retains `i` as
the capacity-sample coordinate of its input. -/
def cacheEntriesFromStateChain
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (states : List (CanonicalSpongeState U)) :
    List (CacheEntry (StmtIn := StmtIn) (U := U)) :=
  cacheEntriesFromStateChainAux (StmtIn := StmtIn) (U := U)
    birthRawTraceLength birthTrace 0 states

/-- Pointwise provenance of the cache-chain constructor. -/
lemma cacheEntriesFromStateChainAux_get?
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (startIndex : Nat)
    (states : List (CanonicalSpongeState U))
    (i : Nat) :
    (cacheEntriesFromStateChainAux (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace startIndex states)[i]? =
      match states[i]?, states[i + 1]? with
      | some stateIn, some stateOut =>
          some ⟨stateIn, stateOut, birthRawTraceLength, birthTrace, startIndex + i⟩
      | _, _ => none := by
  induction states generalizing startIndex i with
  | nil =>
      simp [cacheEntriesFromStateChainAux]
  | cons stateIn states ih =>
      cases states with
      | nil =>
          simp [cacheEntriesFromStateChainAux]
      | cons stateOut tail =>
          cases i with
          | zero =>
              simp [cacheEntriesFromStateChainAux]
          | succ i =>
              rw [cacheEntriesFromStateChainAux]
              simp only [List.getElem?_cons_succ]
              rw [ih]
              simp only [List.getElem?_cons_succ]
              have hIndex : startIndex + 1 + i = startIndex + (i + 1) := by
                omega
              rw [hIndex]

/-- The cache entry at position `i` is the pair of consecutive source states and keeps `i` as
its capacity-sample coordinate. -/
lemma cacheEntriesFromStateChain_get?
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (states : List (CanonicalSpongeState U))
    (i : Nat) (hi : i + 1 < states.length) :
    (cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace states)[i]? =
      some ⟨states[i], states[i + 1], birthRawTraceLength, birthTrace, i⟩ := by
  unfold cacheEntriesFromStateChain
  rw [cacheEntriesFromStateChainAux_get?]
  have hiInput : i < states.length := by
    omega
  rw [List.getElem?_eq_getElem hiInput]
  rw [List.getElem?_eq_getElem hi]
  simp only [Nat.zero_add]

/-- Membership in a newly synthesized cache chain has a unique explicit source position. -/
lemma mem_cacheEntriesFromStateChain_iff
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (states : List (CanonicalSpongeState U))
    (entry : CacheEntry (StmtIn := StmtIn) (U := U)) :
    entry ∈ cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
      birthRawTraceLength birthTrace states ↔
      ∃ (i : Nat) (hi : i + 1 < states.length),
        entry = ⟨states.get ⟨i, by omega⟩, states.get ⟨i + 1, hi⟩,
          birthRawTraceLength, birthTrace, i⟩ := by
  constructor
  · intro hEntry
    obtain ⟨i, hGet⟩ := List.mem_iff_getElem?.mp hEntry
    unfold cacheEntriesFromStateChain at hGet
    rw [cacheEntriesFromStateChainAux_get?] at hGet
    cases hInput : states[i]? with
    | none =>
        simp [hInput] at hGet
    | some stateIn =>
        cases hOutput : states[i + 1]? with
        | none =>
            simp [hInput, hOutput] at hGet
        | some stateOut =>
            rw [hInput, hOutput] at hGet
            have hLength : i + 1 < states.length :=
              (List.getElem?_eq_some_iff.mp hOutput).1
            have hPrevLength : i < states.length := by
              omega
            have hInputSome : states[i]? =
                some (states.get ⟨i, hPrevLength⟩) :=
              List.getElem?_eq_getElem hPrevLength
            rw [hInput] at hInputSome
            have hInputEq : states.get ⟨i, hPrevLength⟩ = stateIn :=
              Option.some.inj hInputSome.symm
            have hOutputSome : states[i + 1]? =
                some (states.get ⟨i + 1, hLength⟩) :=
              List.getElem?_eq_getElem hLength
            rw [hOutput] at hOutputSome
            have hOutputEq : states.get ⟨i + 1, hLength⟩ = stateOut :=
              Option.some.inj hOutputSome.symm
            have hEq : entry =
                ⟨stateIn, stateOut, birthRawTraceLength, birthTrace, 0 + i⟩ :=
              Option.some.inj hGet |>.symm
            simp only [Nat.zero_add] at hEq
            refine ⟨i, hLength, ?_⟩
            rw [← hInputEq, ← hOutputEq] at hEq
            exact hEq
  · rintro ⟨i, hi, hEntry⟩
    subst entry
    rw [List.mem_iff_getElem?]
    refine ⟨i, ?_⟩
    exact cacheEntriesFromStateChain_get?
      (StmtIn := StmtIn) (U := U) birthRawTraceLength birthTrace states i hi

/-- An entry returned from a newly synthesized Item-4(e)iiiC cache chain identifies one exact
coordinate of that invocation's `d2sSampleCapacityList` result. -/
lemma cacheEntriesFromSynthesis_get_input_capacity
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (rateBlocks : List (Vector U SpongeSize.R))
    (caps : List (Vector U SpongeSize.C))
    (hLength : rateBlocks.length = caps.length)
    (i : Nat) (hi : i + 1 < caps.length)
    (entry : CacheEntry (StmtIn := StmtIn) (U := U))
    (hEntry :
      (cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
        birthRawTraceLength birthTrace
        (d2sSynthesisStates (U := U) rateBlocks caps))[i]? = some entry) :
    entry.birthCapacityIndex = i ∧ entry.stateIn.capacitySegment = caps[i] := by
  let states := d2sSynthesisStates (U := U) rateBlocks caps
  have hStatesLength : states.length = caps.length := by
    dsimp [states]
    exact d2sSynthesisStates_length rateBlocks caps hLength
  have hiStates : i + 1 < states.length := by
    rw [hStatesLength]
    exact hi
  have hAt := cacheEntriesFromStateChain_get?
    (StmtIn := StmtIn) (U := U) birthRawTraceLength birthTrace states i hiStates
  dsimp [states] at hAt
  have hEntryEq : entry =
      ⟨(d2sSynthesisStates (U := U) rateBlocks caps)[i],
        (d2sSynthesisStates (U := U) rateBlocks caps)[i + 1],
        birthRawTraceLength, birthTrace, i⟩ :=
    Option.some.inj (hEntry.symm.trans hAt)
  rw [hEntryEq]
  constructor
  · rfl
  · let fi : Fin caps.length := ⟨i, by omega⟩
    have hCap := d2sSynthesisStates_get_capacitySegment
      (U := U) rateBlocks caps hLength fi
    have hiSynthesis : i < (d2sSynthesisStates (U := U) rateBlocks caps).length := by
      rw [d2sSynthesisStates_length rateBlocks caps hLength]
      omega
    change CanonicalSpongeState.capacitySegment
        ((d2sSynthesisStates (U := U) rateBlocks caps).get ⟨i, hiSynthesis⟩) = caps.get fi
    exact hCap

/-- The output of a synthesized cache edge is the *successor* capacity coordinate of the
capacity-list draw that minted the edge.  Thus a later cache pop returning `entry.stateOut` must
be charged to coordinate `entry.birthCapacityIndex + 1`, not to fresh randomness at pop time. -/
lemma cacheEntriesFromSynthesis_get_output_capacity
    (birthRawTraceLength : Nat)
    (birthTrace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (rateBlocks : List (Vector U SpongeSize.R))
    (caps : List (Vector U SpongeSize.C))
    (hLength : rateBlocks.length = caps.length)
    (i : Nat) (hi : i + 1 < caps.length)
    (entry : CacheEntry (StmtIn := StmtIn) (U := U))
    (hEntry :
      (cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
        birthRawTraceLength birthTrace
        (d2sSynthesisStates (U := U) rateBlocks caps))[i]? = some entry) :
    entry.birthCapacityIndex = i ∧ entry.stateOut.capacitySegment = caps[i + 1] := by
  let states := d2sSynthesisStates (U := U) rateBlocks caps
  have hStatesLength : states.length = caps.length := by
    dsimp [states]
    exact d2sSynthesisStates_length rateBlocks caps hLength
  have hiStates : i + 1 < states.length := by
    rw [hStatesLength]
    exact hi
  have hAt := cacheEntriesFromStateChain_get?
    (StmtIn := StmtIn) (U := U) birthRawTraceLength birthTrace states i hiStates
  dsimp [states] at hAt
  have hEntryEq : entry =
      ⟨(d2sSynthesisStates (U := U) rateBlocks caps)[i],
        (d2sSynthesisStates (U := U) rateBlocks caps)[i + 1],
        birthRawTraceLength, birthTrace, i⟩ :=
    Option.some.inj (hEntry.symm.trans hAt)
  rw [hEntryEq]
  constructor
  · rfl
  · let fi : Fin caps.length := ⟨i + 1, hi⟩
    have hCap := d2sSynthesisStates_get_capacitySegment
      (U := U) rateBlocks caps hLength fi
    have hiSynthesis : i + 1 <
        (d2sSynthesisStates (U := U) rateBlocks caps).length := by
      rw [d2sSynthesisStates_length rateBlocks caps hLength]
      exact hi
    change CanonicalSpongeState.capacitySegment
        ((d2sSynthesisStates (U := U) rateBlocks caps).get ⟨i + 1, hiSynthesis⟩) = caps.get fi
    exact hCap

/-- Proof-carrying provenance for one latent cache edge.  It packages exactly the synthesis list
which created the edge; the simulator does not store this witness at runtime, but the
Lemma-5.8 stopping invariant threads it through cache creation and consumption. -/
structure CacheEntryBirthWitness
    (entry : CacheEntry (StmtIn := StmtIn) (U := U)) where
  rateBlocks : List (Vector U SpongeSize.R)
  capacities : List (Vector U SpongeSize.C)
  hLength : rateBlocks.length = capacities.length
  hOutputIndex : entry.birthCapacityIndex + 1 < capacities.length
  hEntry :
    (cacheEntriesFromStateChain (StmtIn := StmtIn) (U := U)
      entry.birthRawTraceLength entry.birthTrace
      (d2sSynthesisStates (U := U) rateBlocks capacities))[entry.birthCapacityIndex]? =
        some entry

/-- The capacity returned by a latent cache edge is the successor coordinate specified by its
birth witness. -/
lemma CacheEntryBirthWitness.output_capacity
    {entry : CacheEntry (StmtIn := StmtIn) (U := U)}
    (w : CacheEntryBirthWitness (StmtIn := StmtIn) (U := U) entry) :
    entry.stateOut.capacitySegment =
      w.capacities[entry.birthCapacityIndex + 1]'w.hOutputIndex := by
  exact (cacheEntriesFromSynthesis_get_output_capacity
    (StmtIn := StmtIn) (U := U)
    entry.birthRawTraceLength entry.birthTrace w.rateBlocks w.capacities w.hLength
    entry.birthCapacityIndex w.hOutputIndex entry w.hEntry).2

/-- The input of a latent cache edge is the capacity coordinate recorded at its birth.  Together
with `output_capacity`, this names both random capacity draws of the cached permutation edge
which is later exposed by Item 4(c)i. -/
lemma CacheEntryBirthWitness.input_capacity
    {entry : CacheEntry (StmtIn := StmtIn) (U := U)}
    (w : CacheEntryBirthWitness (StmtIn := StmtIn) (U := U) entry) :
    entry.stateIn.capacitySegment =
      w.capacities[entry.birthCapacityIndex]'(Nat.lt_trans
        (Nat.lt_succ_self entry.birthCapacityIndex) w.hOutputIndex) := by
  have hInputIndex : entry.birthCapacityIndex < w.capacities.length := by
    exact Nat.lt_trans (Nat.lt_succ_self entry.birthCapacityIndex) w.hOutputIndex
  have hInput := (cacheEntriesFromSynthesis_get_input_capacity
    (StmtIn := StmtIn) (U := U)
    entry.birthRawTraceLength entry.birthTrace w.rateBlocks w.capacities w.hLength
    entry.birthCapacityIndex w.hOutputIndex entry w.hEntry).2
  change entry.stateIn.capacitySegment =
    w.capacities[entry.birthCapacityIndex]'hInputIndex
  exact hInput

/-- Pop the first latent pair whose input is `stateIn`, preserving the entry's origin. -/
def popCacheEntryByInput
    (cache : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (stateIn : CanonicalSpongeState U) :
    Option (CacheEntry (StmtIn := StmtIn) (U := U) ×
      List (CacheEntry (StmtIn := StmtIn) (U := U))) :=
  match cache with
  | [] => none
  | entry :: rest =>
      if entry.stateIn = stateIn then
        some (entry, rest)
      else
        match popCacheEntryByInput rest stateIn with
        | none => none
        | some (entry', rest') => some (entry', entry :: rest')

/-- A successful cache pop returns an entry that was present in the old cache and whose input is
the queried state.  This is the operational half of CO25 Eq. (32). -/
lemma popCacheEntryByInput_eq_some
    (cache : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (stateIn : CanonicalSpongeState U)
    (entry : CacheEntry (StmtIn := StmtIn) (U := U))
    (rest : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (hpop : popCacheEntryByInput (StmtIn := StmtIn) (U := U) cache stateIn =
      some (entry, rest)) :
    entry ∈ cache ∧ entry.stateIn = stateIn := by
  induction cache generalizing entry rest with
  | nil =>
      simp [popCacheEntryByInput] at hpop
  | cons head tail ih =>
      by_cases hHead : head.stateIn = stateIn
      · simp [popCacheEntryByInput, hHead] at hpop
        rcases hpop with ⟨hEntry, _hRest⟩
        subst entry
        exact ⟨List.mem_cons_self, hHead⟩
      · cases hTail : popCacheEntryByInput (StmtIn := StmtIn) (U := U) tail stateIn with
        | none =>
            rw [popCacheEntryByInput, if_neg hHead, hTail] at hpop
            cases hpop
        | some result =>
            cases result with
            | mk tailEntry tailRest =>
                rw [popCacheEntryByInput, if_neg hHead, hTail] at hpop
                have hPair : (tailEntry, head :: tailRest) = (entry, rest) :=
                  Option.some.inj hpop
                have hEntry : tailEntry = entry := congrArg Prod.fst hPair
                subst entry
                have hmem := ih tailEntry tailRest hTail
                exact ⟨List.mem_cons_of_mem _ hmem.1, hmem.2⟩

/-- A cache is observationally inert for a forward query precisely when none of its latent
domains equals that query input.  This is the deterministic boundary used by the Eq. (33)
cache-opacity argument: before the first such equality test, changing an unconsumed cache entry
cannot alter the cache-lookup branch. -/
lemma popCacheEntryByInput_eq_none_iff
    (cache : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (stateIn : CanonicalSpongeState U) :
    popCacheEntryByInput (StmtIn := StmtIn) (U := U) cache stateIn = none ↔
      ∀ entry ∈ cache, entry.stateIn ≠ stateIn := by
  induction cache with
  | nil =>
      simp [popCacheEntryByInput]
  | cons head tail ih =>
      by_cases hHead : head.stateIn = stateIn
      · simp [popCacheEntryByInput, hHead]
      · cases hTail : popCacheEntryByInput (StmtIn := StmtIn) (U := U) tail stateIn with
        | none =>
            constructor
            · intro _ entry hEntry
              rcases List.mem_cons.mp hEntry with hEntry | hEntry
              · rw [hEntry]
                exact hHead
              · exact (ih.mp hTail) entry hEntry
            · intro _
              rw [popCacheEntryByInput, if_neg hHead, hTail]
        | some result =>
            cases result with
            | mk tailEntry tailRest =>
                constructor
                · intro h
                  rw [popCacheEntryByInput, if_neg hHead, hTail] at h
                  cases h
                · intro h
                  have hTailNone : popCacheEntryByInput (StmtIn := StmtIn) (U := U)
                      tail stateIn = none := by
                    apply ih.mpr
                    intro entry hEntry
                    exact h entry (List.mem_cons_of_mem _ hEntry)
                  rw [hTail] at hTailNone
                  cases hTailNone

/-- The executable cache lookup used by D2S.  The history-aware lookup is the primitive; this
projection keeps callers concerned only with the D2S output independent of proof metadata. -/
def popCacheByInput
    (cache : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (stateIn : CanonicalSpongeState U) :
    Option (CanonicalSpongeState U × List (CacheEntry (StmtIn := StmtIn) (U := U))) :=
  match popCacheEntryByInput (StmtIn := StmtIn) (U := U) cache stateIn with
  | none => none
  | some (entry, rest) => some (entry.stateOut, rest)

/-- Forgetting a cache entry's origin preserves exactly whether lookup succeeds. -/
lemma popCacheByInput_eq_none_iff
    (cache : List (CacheEntry (StmtIn := StmtIn) (U := U)))
    (stateIn : CanonicalSpongeState U) :
    popCacheByInput (StmtIn := StmtIn) (U := U) cache stateIn = none ↔
      popCacheEntryByInput (StmtIn := StmtIn) (U := U) cache stateIn = none := by
  unfold popCacheByInput
  cases hEntry : popCacheEntryByInput (StmtIn := StmtIn) (U := U) cache stateIn with
  | none =>
      simp only [reduceCtorEq]
  | some value =>
      cases value with
      | mk entry rest =>
          constructor
          · intro h
            cases h
          · intro h
            cases h

/-- CO25 §5.4 Item 1 — Internal mutable state of the `D2SQuery` oracle wrapper.

- `trace` (`tr`): ordered `h`/`p`/`p⁻¹` query-answer pairs (bullet 1).
- `cacheP` (`Cache_p`): latent `(s_in, s_out)` pairs sorted by input, consumed by Item 4(c)i
  (bullet 2).  `CacheEntry` adds only proof metadata; lookup semantics remain the paper's pair list.
- `cacheHistory`: proof-only metadata recording a cache entry's sampled origin and its exact
  Item-4(c)i consumption prefix, for the CO25 Eq. (33) causality argument.
- `trΔ` (`tr_∇`): dedup index over `trace` for `O(log N)` `inlu`/`outlu` (CO25 Def. 5.2; bullet 3).

`gᵢ`-response consistency (paper Item 4(e)i) is **not** carried in this struct — it is
provided by `D2SAlgo`'s `tr_i` memo at the bridge layer (`D2SAlgoMemo`, threaded through
`d2sCodecBridgeImplMemo`). Keeping `tr_i` out of `D2SQuery` matches the paper's placement of
the memo inside `D2SAlgo` (Item 3, lines 1066-1075), and keeps the §5.8 hybrid `D2SQuery`
analysis (`d2sQueryImpl`) independent of the bridge memo. -/
structure D2SQueryState where
  -- `tr`: ordered `('h', 𝕩, s_C)` / `('p', s_in, s_out)` / `('p⁻¹', …)` pairs (§5.4 Item 1)
  trace : QueryLog (duplexSpongeChallengeOracle StmtIn U) := []
  -- `Cache_p`: `(s_in, s_out) ∈ Σ^{r+c} × Σ^{r+c}` sorted by input (§5.4 Item 1, bullet 2)
  cacheP : List (CacheEntry (StmtIn := StmtIn) (U := U)) := []
  -- Proof-only metadata: records sampled origins and exact consumption prefixes.
  cacheHistory : List (ConsumedCacheEntry (StmtIn := StmtIn) (U := U)) := []
  -- `tr_∇`: deduplicated index for `O(log N)` `inlu`/`outlu` lookups (CO25 Def. 5.2, §5.1)
  trΔ : TraceNabla T_H T_P StmtIn U :=
    ⟨TraceTableOps.empty, TraceTableOps.empty⟩
  -- Invariant: every entry in `trΔ` appears in `trace`. Maintained by construction:
  -- each step that appends to `trace` either leaves `trΔ` unchanged or adds an entry
  -- that matches the new trace element. Required by `backTrack` (CO25 §5.2).
  h_inv : trΔ.IsSubsetOfQueryLog trace
  -- Invariant: `trΔ` contains exactly the distinct hash and normalized permutation pairs in
  -- `trace`.  In particular, a cache-popped forward pair is inserted into `trΔ`, so subsequent
  -- `p⁻¹` lookups see the pair already exposed by Item 4(c)i.
  h_mirror : trΔ.MirrorsQueryLog trace
  -- Phantom: auto-binds `δ` and `pSpec` as implicit struct params (matches the original
  -- shape pre-`gMemo`-deletion, so `set { st with … }` resolves `MonadStateOf` cleanly).
  _phantom : Option (BacktrackOutput
    (δ := δ) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) := none

instance : Inhabited (D2SQueryState
    (δ := δ) (T_H := T_H) (T_P := T_P) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  ⟨{ h_inv := TraceNabla.IsSubsetOfQueryLog_empty_nil
     h_mirror := TraceNabla.MirrorsQueryLog_empty_nil }⟩

end D2SCacheHistory

end

end DuplexSpongeFS.ProverTransform
