/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedCodec
public import VCVio.OracleComp.QueryTracking.RandomOracle.LoggedRun

/-!
# Operational reduction of encoded random-oracle queries

An arbitrary client of an external encoded random oracle is interpreted against the native
key oracle. Decoded image queries use the native oracle, while all off-image queries use private
uniform samples in a separate memoized cache. The reduction returns the original external
query log and off-image cache, including when the client returns an optional failure.
-/

@[expose] public section

open OracleComp OracleSpec

namespace Interaction.Oracle.Security.StateRestoration

universe u

variable {K D C A : Type}

/-- Reconstruct the full encoded-domain cache from the native image cache and the private
off-image cache. A strict decoder makes the two cases disjoint. -/
def StrictCodec.mergeCache (codec : StrictCodec K D)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    (D →ₒ C).QueryCache :=
  QueryCache.ofFn fun d => match codec.decode d with
    | some key => native key
    | none => off d

@[simp] theorem StrictCodec.mergeCache_encode (codec : StrictCodec K D)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) (key : K) :
    codec.mergeCache native off (codec.encode key) = native key := by
  simp [StrictCodec.mergeCache, codec.decode_encode]

theorem StrictCodec.mergeCache_off (codec : StrictCodec K D)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (d : D) (h : codec.decode d = none) :
    codec.mergeCache native off d = off d := by
  simp [StrictCodec.mergeCache, h]

theorem StrictCodec.mergeCache_empty (codec : StrictCodec K D) :
    codec.mergeCache (∅ : (K →ₒ C).QueryCache)
      (∅ : (D →ₒ C).QueryCache) = ∅ := by
  apply QueryCache.ext
  intro d
  cases h : codec.decode d <;> simp [StrictCodec.mergeCache, h]

/-- Updating an image coordinate in the native cache updates precisely its encoded external
coordinate. This uses the strict inverse law, not merely injectivity. -/
theorem StrictCodec.mergeCache_image_update (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D]
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (key : K) (answer : C) :
    codec.mergeCache (native.cacheQuery key answer) off =
      (codec.mergeCache native off).cacheQuery (codec.encode key) answer := by
  apply QueryCache.ext
  intro d
  by_cases hd : d = codec.encode key
  · subst d
    simp [QueryCache.cacheQuery_self]
  · have hkey : ∀ other, codec.decode d = some other → other ≠ key := by
      intro other hdecode heq
      subst other
      exact hd (codec.encode_decode d key hdecode).symm
    cases hdecode : codec.decode d with
    | none =>
        simp [StrictCodec.mergeCache, hdecode,
          QueryCache.cacheQuery_of_ne _ _ hd]
    | some other =>
        have hne := hkey other hdecode
        simp [StrictCodec.mergeCache, hdecode,
          QueryCache.cacheQuery_of_ne _ _ hd,
          QueryCache.cacheQuery_of_ne _ _ hne]

/-- An off-image private-cache update changes only that external coordinate. -/
theorem StrictCodec.mergeCache_off_update (codec : StrictCodec K D)
    [DecidableEq D]
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (d : D) (hdecode : codec.decode d = none) (answer : C) :
    codec.mergeCache native (off.cacheQuery d answer) =
      (codec.mergeCache native off).cacheQuery d answer := by
  apply QueryCache.ext
  intro other
  by_cases h : other = d
  · subst other
    simp [StrictCodec.mergeCache, hdecode, QueryCache.cacheQuery_self]
  · cases hother : codec.decode other with
    | none =>
        simp [StrictCodec.mergeCache, hother,
          QueryCache.cacheQuery_of_ne _ _ h]
    | some key =>
        simp [StrictCodec.mergeCache, hother,
          QueryCache.cacheQuery_of_ne _ _ h]

/-- Route one external query, retaining the exact external hash-log entry. Private uniform
queries do not touch either hash cache or hash log. -/
def StrictCodec.encodedQueryImpl (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C] :
    QueryImpl (unifSpec + (D →ₒ C))
      (WriterT (QueryLog (D →ₒ C))
        (StateT (D →ₒ C).QueryCache (OracleComp (unifSpec + (K →ₒ C))))) :=
  fun query => match query with
    | .inl coin => WriterT.mk <| StateT.mk fun off =>
        (fun answer => ((answer, []), off)) <$>
          (liftM ((unifSpec + (K →ₒ C)).query (.inl coin)))
    | .inr d => match codec.decode d with
      | some key => WriterT.mk <| StateT.mk fun off =>
          (fun answer => ((answer, [⟨d, answer⟩]), off)) <$>
            (liftM ((unifSpec + (K →ₒ C)).query (.inr key)))
      | none => WriterT.mk <| StateT.mk fun off =>
          match off d with
          | some answer => pure ((answer, [⟨d, answer⟩]), off)
          | none =>
              (fun answer => ((answer, [⟨d, answer⟩]), off.cacheQuery d answer)) <$>
                (liftM ($ᵗ C) : OracleComp (unifSpec + (K →ₒ C)) C)

/-- The translated free program. It exposes the off-image cache and full external hash log
as returned data, while its remaining oracle effect is only the native typed-key oracle. -/
def StrictCodec.routeProgram (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (off : (D →ₒ C).QueryCache := ∅) :
    OracleComp (unifSpec + (K →ₒ C))
      ((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) :=
  ((simulateQ codec.encodedQueryImpl program).run).run off

/-- The translated program carries both the off-image cache and the external writer log
through an adaptive continuation. -/
theorem StrictCodec.routeProgram_bind (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    {B : Type} (next : A → OracleComp (unifSpec + (D →ₒ C)) B)
    (off : (D →ₒ C).QueryCache) :
    codec.routeProgram (program >>= next) off =
      codec.routeProgram program off >>= fun first =>
        (fun second => ((second.1.1, first.1.2 ++ second.1.2), second.2)) <$>
          codec.routeProgram (next first.1.1) first.2 := by
  simp [StrictCodec.routeProgram, simulateQ_bind, WriterT.run_bind, StateT.run_bind]

/-- Interpret the translated client through the actual native lazy random oracle, then rebuild
the external cache from its image and off-image parts. The returned external log is not erased. -/
def StrictCodec.routedRawRun (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    ProbComp (((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      (K →ₒ C).QueryCache) :=
  (simulateQ (K →ₒ C).romImpl (codec.routeProgram program off)).run native

def StrictCodec.routedLoggedRun (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    ProbComp ((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) :=
  (fun result => (result.1.1, codec.mergeCache result.2 result.1.2)) <$>
    codec.routedRawRun program native off

/-- Writer and both cache states hand off across adaptive continuations without dropping
either the original external query log or the off-image private cache. -/
theorem StrictCodec.routedRawRun_bind (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    {B : Type} (next : A → OracleComp (unifSpec + (D →ₒ C)) B)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    codec.routedRawRun (program >>= next) native off =
      codec.routedRawRun program native off >>= fun first =>
        (fun second =>
          (((second.1.1.1, first.1.1.2 ++ second.1.1.2), second.1.2), second.2)) <$>
          codec.routedRawRun (next first.1.1.1) first.2 first.1.2 := by
  simp [StrictCodec.routedRawRun, StrictCodec.routeProgram,
    simulateQ_bind, WriterT.run_bind, StateT.run_bind]

/-- A private uniform query is forwarded identically; neither cache nor the hash log changes. -/
theorem StrictCodec.routedLoggedRun_uniformQuery (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (coin : Nat) (native : (K →ₒ C).QueryCache)
    (off : (D →ₒ C).QueryCache) :
    codec.routedLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inl coin))) native off =
    randomOracleLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inl coin)))
      (codec.mergeCache native off) := by
  calc
    _ = (fun answer => ((answer, []), codec.mergeCache native off)) <$>
        (unifSpec.query coin : ProbComp (Fin (coin + 1))) := by
          simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
            StrictCodec.routeProgram, StrictCodec.encodedQueryImpl,
            unifFwdImpl, Functor.map_map]
    _ = _ := by simp [randomOracleLoggedRun_uniformQuery]

/-- A hash query on the image receives the native cached answer and records the original
external key in the log. -/
theorem StrictCodec.routedLoggedRun_imageQuery (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (key : K) (native : (K →ₒ C).QueryCache)
    (off : (D →ₒ C).QueryCache) :
    codec.routedLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inr (codec.encode key)))) native off =
    randomOracleLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inr (codec.encode key))))
      (codec.mergeCache native off) := by
  cases hcache : native key with
  | none =>
      simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        StrictCodec.routeProgram, StrictCodec.encodedQueryImpl,
        codec.decode_encode, randomOracleLoggedRun_hashQuery,
        hcache, StrictCodec.mergeCache_image_update]
  | some answer =>
      simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        StrictCodec.routeProgram, StrictCodec.encodedQueryImpl,
        codec.decode_encode, randomOracleLoggedRun_hashQuery, hcache]

/-- A hash query outside the encoding image uses the memoized private response while retaining
the external key and answer in its log. -/
theorem StrictCodec.routedLoggedRun_offQuery (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (d : D) (h : codec.decode d = none)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    codec.routedLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inr d))) native off =
    randomOracleLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query (.inr d)))
      (codec.mergeCache native off) := by
  cases hcache : off d with
  | none =>
      simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        StrictCodec.routeProgram, StrictCodec.encodedQueryImpl, h,
        randomOracleLoggedRun_hashQuery, hcache,
        StrictCodec.mergeCache_off, StrictCodec.mergeCache_off_update,
        roSim.run_liftM, Functor.map_map]
  | some answer =>
      simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        StrictCodec.routeProgram, StrictCodec.encodedQueryImpl, h,
        randomOracleLoggedRun_hashQuery, hcache, StrictCodec.mergeCache_off]

/-- Every external query, including an off-image query, has an identical full value/log/cache
one-step law after reconstructing the cache from the two reduction states. -/
theorem StrictCodec.routedLoggedRun_query (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (query : (unifSpec + (D →ₒ C)).Domain)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    codec.routedLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query query)) native off =
    randomOracleLoggedRun
      (liftM ((unifSpec + (D →ₒ C)).query query))
      (codec.mergeCache native off) := by
  cases query with
  | inl coin => exact codec.routedLoggedRun_uniformQuery coin native off
  | inr d =>
      cases h : codec.decode d with
      | none => exact codec.routedLoggedRun_offQuery d h native off
      | some key =>
          have hd : d = codec.encode key := (codec.encode_decode d key h).symm
          subst d
          exact codec.routedLoggedRun_imageQuery key native off

/-- The arbitrary adaptive encoded-domain client has exactly the same output, complete
external query log, and final external cache after the native reduction. This includes private
uniform draws, repeated off-image queries, and clients returning failure values. -/
theorem StrictCodec.routedLoggedRun_eq_randomOracleLoggedRun (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    codec.routedLoggedRun program native off =
      randomOracleLoggedRun program (codec.mergeCache native off) := by
  induction program using OracleComp.inductionOn generalizing native off with
  | pure value =>
      simp [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        StrictCodec.routeProgram, randomOracleLoggedRun]
  | query_bind query next ih =>
      rw [randomOracleLoggedRun_bind]
      rw [← codec.routedLoggedRun_query query native off]
      unfold StrictCodec.routedLoggedRun
      rw [StrictCodec.routedRawRun_bind]
      simp only [map_bind, bind_map_left, Functor.map_map]
      apply bind_congr
      intro first
      rw [← ih first.1.1.1 first.2 first.1.2]
      simp [StrictCodec.routedLoggedRun, Functor.map_map]

/-- Keep the native-key queries, in order, from a complete external encoded-domain hash log.
Off-image entries disappear from this projection but remain in the original log and cache. -/
def StrictCodec.decodeImageLog (codec : StrictCodec K D)
    (log : QueryLog (D →ₒ C)) : QueryLog (K →ₒ C) :=
  log.filterMap fun query => (codec.decode query.1).map fun key => ⟨key, query.2⟩

@[simp] theorem StrictCodec.decodeImageLog_nil (codec : StrictCodec K D) :
    codec.decodeImageLog ([] : QueryLog (D →ₒ C)) = [] := rfl

@[simp] theorem StrictCodec.decodeImageLog_append (codec : StrictCodec K D)
    (first second : QueryLog (D →ₒ C)) :
    codec.decodeImageLog (first ++ second) =
      codec.decodeImageLog first ++ codec.decodeImageLog second := by
  simp [StrictCodec.decodeImageLog]

@[simp] theorem StrictCodec.decodeImageLog_image (codec : StrictCodec K D)
    (key : K) (answer : C) :
    codec.decodeImageLog [⟨codec.encode key, answer⟩] = [⟨key, answer⟩] := by
  simp [StrictCodec.decodeImageLog, codec.decode_encode]

@[simp] theorem StrictCodec.decodeImageLog_off (codec : StrictCodec K D)
    (d : D) (h : codec.decode d = none) (answer : C) :
    codec.decodeImageLog [⟨d, answer⟩] = [] := by
  simp [StrictCodec.decodeImageLog, h]

/-- Every distinct native image key logged by the reduction corresponds to a distinct
external encoded key in the original log. -/
theorem StrictCodec.freshImageKeys_card_le (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D]
    (log : QueryLog (D →ₒ C)) :
    (freshKeysOfLog (codec.decodeImageLog log)).card ≤
      (freshKeysOfLog log).card := by
  have hsubset : (freshKeysOfLog (codec.decodeImageLog log)).map
      ⟨codec.encode, codec.encode_injective⟩ ⊆ freshKeysOfLog log := by
    intro d hd
    obtain ⟨key, hkey, rfl⟩ := Finset.mem_map.mp hd
    rw [mem_freshKeysOfLog] at hkey ⊢
    obtain ⟨entry, hentry, heq⟩ := hkey
    simp only [StrictCodec.decodeImageLog, List.mem_filterMap] at hentry
    obtain ⟨source, hsource, hdecode⟩ := hentry
    cases h : codec.decode source.1 with
    | none => simp [h] at hdecode
    | some decoded =>
        simp only [h, Option.map_some, Option.some.injEq] at hdecode
        have hdk : decoded = key := (congrArg Sigma.fst hdecode).trans heq
        subst decoded
        exact ⟨source, hsource, (codec.encode_decode source.1 key h).symm⟩
  calc
    _ = ((freshKeysOfLog (codec.decodeImageLog log)).map
          ⟨codec.encode, codec.encode_injective⟩).card :=
        (Finset.card_map _).symm
    _ ≤ (freshKeysOfLog log).card := Finset.card_le_card hsubset

end Interaction.Oracle.Security.StateRestoration
