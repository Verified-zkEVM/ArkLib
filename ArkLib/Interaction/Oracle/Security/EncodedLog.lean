/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedReduction

/-!
# Native query log of an encoded-oracle reduction

The translated program uses the actual native random oracle. Its native hash log is the
ordered decoding of the external log returned by the routing writer.
-/

@[expose] public section

open OracleComp OracleSpec

namespace Interaction.Oracle.Security.StateRestoration

universe u
variable {K D C A : Type}

private theorem loggedRun_map {B : Type} [DecidableEq K] [SampleableType C]
    (f : A → B) (program : OracleComp (unifSpec + (K →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) :
    randomOracleLoggedRun (f <$> program) native =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun program native := by
  simp [randomOracleLoggedRun, simulateQ_map, WriterT.run_map, StateT.run_map]

private theorem loggedRun_liftM [DecidableEq K] [SampleableType C]
    (sample : ProbComp A) (native : (K →ₒ C).QueryCache) :
    randomOracleLoggedRun
      (liftM sample : OracleComp (unifSpec + (K →ₒ C)) A) native =
        (fun value => ((value, []), native)) <$> sample := by
  induction sample using OracleComp.inductionOn with
  | pure value =>
      simp [randomOracleLoggedRun]
  | query_bind coin next ih =>
      simp only [liftM_bind]
      rw [randomOracleLoggedRun_bind]
      have hfirst : randomOracleLoggedRun
          (liftM (liftM (unifSpec.query coin) : ProbComp (Fin (coin + 1))) :
            OracleComp (unifSpec + (K →ₒ C)) (Fin (coin + 1))) native =
          (fun u => ((u, []), native)) <$>
            (unifSpec.query coin : ProbComp (Fin (coin + 1))) := by
        change randomOracleLoggedRun
          (liftM ((unifSpec + (K →ₒ C)).query (.inl coin))) native = _
        exact randomOracleLoggedRun_uniformQuery coin native
      rw [hfirst]
      simp only [bind_map_left, ih, List.nil_append, Functor.map_map, map_bind]


private theorem StrictCodec.routeProgram_uniformQuery (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (coin : Nat) (off : (D →ₒ C).QueryCache) :
    codec.routeProgram
      (liftM ((unifSpec + (D →ₒ C)).query (.inl coin))) off =
      (fun answer => ((answer, []), off)) <$>
        liftM ((unifSpec + (K →ₒ C)).query (.inl coin)) := by
  simp [StrictCodec.routeProgram, StrictCodec.encodedQueryImpl]

private theorem StrictCodec.routeProgram_imageQuery (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (key : K) (off : (D →ₒ C).QueryCache) :
    codec.routeProgram
      (liftM ((unifSpec + (D →ₒ C)).query (.inr (codec.encode key)))) off =
      (fun answer => ((answer, [⟨codec.encode key, answer⟩]), off)) <$>
        liftM ((unifSpec + (K →ₒ C)).query (.inr key)) := by
  simp [StrictCodec.routeProgram, StrictCodec.encodedQueryImpl,
    codec.decode_encode]

private theorem StrictCodec.routeProgram_offQuery_hit (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (d : D) (hdecode : codec.decode d = none)
    (off : (D →ₒ C).QueryCache) (answer : C) (hit : off d = some answer) :
    codec.routeProgram
      (liftM ((unifSpec + (D →ₒ C)).query (.inr d))) off =
      pure ((answer, [⟨d, answer⟩]), off) := by
  simp [StrictCodec.routeProgram, StrictCodec.encodedQueryImpl, hdecode, hit]

private theorem StrictCodec.routeProgram_offQuery_miss (codec : StrictCodec K D)
    [DecidableEq D] [SampleableType C]
    (d : D) (hdecode : codec.decode d = none)
    (off : (D →ₒ C).QueryCache) (miss : off d = none) :
    codec.routeProgram
      (liftM ((unifSpec + (D →ₒ C)).query (.inr d))) off =
      (fun answer => ((answer, [⟨d, answer⟩]), off.cacheQuery d answer)) <$>
        (liftM ($ᵗ C) : OracleComp (unifSpec + (K →ₒ C)) C) := by
  simp [StrictCodec.routeProgram, StrictCodec.encodedQueryImpl, hdecode, miss]


private theorem StrictCodec.routeProgram_query_log (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (query : (unifSpec + (D →ₒ C)).Domain)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (result : (((((unifSpec + (D →ₒ C)).Range query × QueryLog (D →ₒ C)) ×
      (D →ₒ C).QueryCache) × QueryLog (K →ₒ C)) ×
        (K →ₒ C).QueryCache))
    (supported : result ∈ support (randomOracleLoggedRun
      (codec.routeProgram (liftM ((unifSpec + (D →ₒ C)).query query)) off) native)) :
    result.1.2 = codec.decodeImageLog result.1.1.1.2 := by
  cases query with
  | inl coin =>
      rw [codec.routeProgram_uniformQuery, loggedRun_map,
        randomOracleLoggedRun_uniformQuery] at supported
      rw [support_map] at supported
      rcases supported with ⟨answer, hanswer, rfl⟩
      rw [support_map] at hanswer
      rcases hanswer with ⟨coinAnswer, _, rfl⟩
      rfl
  | inr d =>
      cases hdecode : codec.decode d with
      | some key =>
          have hd : d = codec.encode key := (codec.encode_decode d key hdecode).symm
          subst d
          rw [codec.routeProgram_imageQuery, loggedRun_map,
            randomOracleLoggedRun_hashQuery] at supported
          rw [support_map] at supported
          rcases supported with ⟨answer, hanswer, rfl⟩
          rw [support_map] at hanswer
          rcases hanswer with ⟨nativeAnswer, _, rfl⟩
          simp [StrictCodec.decodeImageLog, codec.decode_encode]
      | none =>
          cases hcache : off d with
          | some answer =>
              rw [codec.routeProgram_offQuery_hit d hdecode off answer hcache] at supported
              simp [randomOracleLoggedRun] at supported
              subst result
              simp [StrictCodec.decodeImageLog, hdecode]
          | none =>
              rw [codec.routeProgram_offQuery_miss d hdecode off hcache,
                loggedRun_map, loggedRun_liftM] at supported
              rw [support_map] at supported
              rcases supported with ⟨answer, hanswer, rfl⟩
              rw [support_map] at hanswer
              rcases hanswer with ⟨privateAnswer, _, rfl⟩
              simp [StrictCodec.decodeImageLog, hdecode]


/-- On every outcome of the actual native logged execution, the native hash log is precisely
the ordered decoding of the external log returned by the translated client. -/
theorem StrictCodec.routeProgram_nativeLog (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (result : (((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      QueryLog (K →ₒ C)) × (K →ₒ C).QueryCache)
    (supported : result ∈ support (randomOracleLoggedRun
      (codec.routeProgram program off) native)) :
    result.1.2 = codec.decodeImageLog result.1.1.1.2 := by
  induction program using OracleComp.inductionOn generalizing result native off with
  | pure value =>
      simp [StrictCodec.routeProgram, randomOracleLoggedRun] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [codec.routeProgram_bind, randomOracleLoggedRun_bind] at supported
      rcases (mem_support_bind_peel _ _ supported) with
        ⟨first, hfirst, hsecond⟩
      rw [loggedRun_map, support_map] at hsecond
      rcases hsecond with ⟨second, hsecond, rfl⟩
      rw [support_map] at hsecond
      rcases hsecond with ⟨third, hthird, rfl⟩
      have hfirstLog := codec.routeProgram_query_log query native off first hfirst
      have hsecondLog := ih first.1.1.1.1 first.2 first.1.1.2 third hthird
      simp only [codec.decodeImageLog_append]
      exact (congrArg₂ (· ++ ·) hfirstLog hsecondLog)


/-- Projecting the actual native logged run to the full external value, log, and reconstructed
cache recovers the external cached random-oracle experiment exactly. -/
theorem StrictCodec.routeProgram_externalProjection (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache) :
    (fun result => (result.1.1.1,
      codec.mergeCache result.2 result.1.1.2)) <$>
      randomOracleLoggedRun (codec.routeProgram program off) native =
      randomOracleLoggedRun program (codec.mergeCache native off) := by
  calc
    _ = codec.routedLoggedRun program native off := by
      rw [StrictCodec.routedLoggedRun, StrictCodec.routedRawRun,
        ← randomOracleLoggedRun_project]
      simp only [Functor.map_map]
    _ = _ := codec.routedLoggedRun_eq_randomOracleLoggedRun program native off

/-- In each actual outcome, the native distinct-key charge is at most the full external
distinct-key charge. The off-image queries remain present on the external side. -/
theorem StrictCodec.routeProgram_nativeCharge_le (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (native : (K →ₒ C).QueryCache) (off : (D →ₒ C).QueryCache)
    (result : (((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      QueryLog (K →ₒ C)) × (K →ₒ C).QueryCache)
    (supported : result ∈ support (randomOracleLoggedRun
      (codec.routeProgram program off) native)) :
    (freshKeysOfLog result.1.2).card ≤
      (freshKeysOfLog result.1.1.1.2).card := by
  rw [codec.routeProgram_nativeLog program native off result supported]
  exact codec.freshImageKeys_card_le result.1.1.1.2


/-- The translated program's actual expected native fresh-query count is bounded by the
external encoded-domain client's actual expected fresh-query count. Both expectations use the
logged cached execution, including failed outputs and repeated queries. -/
theorem StrictCodec.expectedNativeFreshKeys_le_external (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A) :
    expectedFreshQueryCharge (codec.routeProgram program ∅) (fun _ => 1) ≤
      expectedFreshQueryCharge program (fun _ => 1) := by
  let nativeRun := randomOracleLoggedRun (codec.routeProgram program ∅) ∅
  let externalRun := randomOracleLoggedRun program ∅
  let : MeasurableSpace ((((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      QueryLog (K →ₒ C)) × (K →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace ((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) := ⊤
  simp only [expectedFreshQueryCharge, freshQueryCharge, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  change (∫⁻ result, ((freshKeysOfLog result.1.2).card : ENNReal) ∂𝒟[nativeRun]) ≤
    ∫⁻ result, ((freshKeysOfLog result.1.2).card : ENNReal) ∂𝒟[externalRun]
  calc
    _ ≤ ∫⁻ result, ((freshKeysOfLog result.1.1.1.2).card : ENNReal)
        ∂𝒟[nativeRun] := by
          apply MeasureTheory.lintegral_mono_ae
          have hae := evalDist.ae_of_forall_mem_support nativeRun
            (fun result => (freshKeysOfLog result.1.2).card ≤
              (freshKeysOfLog result.1.1.1.2).card)
            MeasurableSet.of_discrete
            (fun result hr => codec.routeProgram_nativeCharge_le
              program ∅ ∅ result hr)
          filter_upwards [hae] with result hresult
          exact_mod_cast hresult
    _ = _ := by
      have hproj := codec.routeProgram_externalProjection program
        (∅ : (K →ₒ C).QueryCache) (∅ : (D →ₒ C).QueryCache)
      rw [codec.mergeCache_empty] at hproj
      dsimp only [externalRun]
      rw [← hproj, lintegral_evalDist_map_of_discrete]

end Interaction.Oracle.Security.StateRestoration
