/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedChallenges

/-!
# Joint random-oracle coupling for common challenge representations

The common-carrier oracle can be interpreted by the native dependent restoration oracle. The
cache/log laws and one-query uniform law establish the local coupling for adaptive programs.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C : Type} {rounds : List Round}

@[simp] theorem CommonChallenge.toCommonCache_apply
    (common : CommonChallenge Input Salt C rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (key : Key Input Salt rounds) :
    common.toCommonCache cache key = (cache key).map (common.challengeEquiv key) := rfl

@[simp] theorem CommonChallenge.toCommonCache_empty
    (common : CommonChallenge Input Salt C rounds) :
    common.toCommonCache (∅ : (oracleSpec Input Salt rounds).QueryCache) = ∅ := by
  apply QueryCache.ext
  intro key
  simp [CommonChallenge.toCommonCache]

/-- Encoding a native cache update updates exactly the corresponding common-carrier cell. -/
theorem CommonChallenge.toCommonCache_update
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt]
    (cache : (oracleSpec Input Salt rounds).QueryCache)
    (key : Key Input Salt rounds) (answer : key.Challenge) :
    common.toCommonCache (cache.cacheQuery key answer) =
      (common.toCommonCache cache).cacheQuery key ((common.challengeEquiv key).toFun answer) := by
  apply QueryCache.ext
  intro other
  by_cases h : other = key
  · subst other
    simp [QueryCache.cacheQuery_self]
  · simp [h]

@[simp] theorem CommonChallenge.toCommonLog_nil
    (common : CommonChallenge Input Salt C rounds) :
    common.toCommonLog ([] : QueryLog (oracleSpec Input Salt rounds)) = [] := rfl

@[simp] theorem CommonChallenge.toCommonLog_append
    (common : CommonChallenge Input Salt C rounds)
    (first second : QueryLog (oracleSpec Input Salt rounds)) :
    common.toCommonLog (first ++ second) =
      common.toCommonLog first ++ common.toCommonLog second := by
  simp [CommonChallenge.toCommonLog]

@[simp] theorem CommonChallenge.toCommonLog_single
    (common : CommonChallenge Input Salt C rounds)
    (key : Key Input Salt rounds) (answer : key.Challenge) :
    common.toCommonLog [⟨key, answer⟩] =
      [⟨key, (common.challengeEquiv key).toFun answer⟩] := rfl

end Interaction.Oracle.Security.StateRestoration

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C : Type} {rounds : List Round}

/-- Encode the entire observed native result, including ordered responses and final cache. -/
def CommonChallenge.encodeJoint
    (common : CommonChallenge Input Salt C rounds) {A : Type}
    (joint : ((A × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache)) :
    (A × QueryLog (Key Input Salt rounds →ₒ C)) ×
      (Key Input Salt rounds →ₒ C).QueryCache :=
  ((joint.1.1, common.toCommonLog joint.1.2), common.toCommonCache joint.2)

/-- A private coin operation is forwarded without touching the encoded challenge oracle. -/
theorem CommonChallenge.simulateNative_uniformQuery
    (common : CommonChallenge Input Salt C rounds) (n : ℕ) :
    common.simulateNative
        (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inl n))) =
      (liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inl n)) :
        OracleComp (unifSpec + oracleSpec Input Salt rounds) (Fin (n + 1))) := by
  simp [CommonChallenge.simulateNative, CommonChallenge.commonQueryImpl]

/-- A common-carrier hash request queries the identical native key and encodes its answer. -/
theorem CommonChallenge.simulateNative_hashQuery
    (common : CommonChallenge Input Salt C rounds) (key : Key Input Salt rounds) :
    common.simulateNative
        (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inr key))) =
      (common.challengeEquiv key) <$>
        (liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inr key)) :
          OracleComp (unifSpec + oracleSpec Input Salt rounds) key.Challenge) := by
  simp [CommonChallenge.simulateNative, CommonChallenge.commonQueryImpl]

/-- Compose a pointwise continuation coupling after an equality of encoded prefix
distributions. This is a measure law, so no equality of arbitrary sampler programs is needed. -/
private theorem evalDist_bind_transport {α β γ : Type}
    (nativePrefix : ProbComp α) (encodedPrefix : ProbComp β) (encode : α → β)
    (nativeContinue : α → ProbComp γ) (commonContinue : β → ProbComp γ)
    (prefixLaw : letI : MeasurableSpace β := ⊤;
      𝒟[encode <$> nativePrefix] = 𝒟[encodedPrefix])
    (continueLaw : ∀ x, letI : MeasurableSpace γ := ⊤;
      𝒟[nativeContinue x] = 𝒟[commonContinue (encode x)]) :
    letI : MeasurableSpace γ := ⊤
    𝒟[nativePrefix >>= nativeContinue] = 𝒟[encodedPrefix >>= commonContinue] := by
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  calc
    𝒟[nativePrefix >>= nativeContinue] =
        𝒟[nativePrefix >>= fun x => commonContinue (encode x)] := by
          apply evalDist_bind_congr
          intro x
          exact continueLaw x
    _ = 𝒟[(encode <$> nativePrefix) >>= commonContinue] := by
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    _ = 𝒟[encodedPrefix >>= commonContinue] := by
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, prefixLaw]

/-- A cached hash request has the same full observed answer and final cache after encoding;
at a fresh cell this follows from the uniform challenge pushforward law. -/
theorem CommonChallenge.evalDist_randomOracle_step
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    (key : Key Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace (C × (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
    𝒟[(fun result => ((common.challengeEquiv key) result.1,
      common.toCommonCache result.2)) <$>
        ((oracleSpec Input Salt rounds).randomOracle key).run cache] =
      𝒟[((Key Input Salt rounds →ₒ C).randomOracle key).run
        (common.toCommonCache cache)] := by
  let : MeasurableSpace (C × (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace C := ⊤
  let : MeasurableSpace key.Challenge := ⊤
  rw [randomOracle.run_eq, randomOracle.run_eq]
  cases h : cache key with
  | none =>
      have hcommon : common.toCommonCache cache key = none := by
        simp [CommonChallenge.toCommonCache, h]
      simp only [hcommon, bind_pure_comp]
      let finish : C → C × (Key Input Salt rounds →ₒ C).QueryCache :=
        fun answer => (answer, (common.toCommonCache cache).cacheQuery key answer)
      have hresult (answer : key.Challenge) :
          ((common.challengeEquiv key) answer, common.toCommonCache (cache.cacheQuery key answer)) =
            finish ((common.challengeEquiv key) answer) := by
        simp [finish, common.toCommonCache_update]
      simp only [Functor.map_map]
      simp_rw [hresult]
      rw [← Functor.map_map]
      rw [evalDist_map_of_discrete]
      rw [common.evalDist_challengeEquiv_uniform key]
      simpa only [finish] using (evalDist_map_of_discrete ($ᵗ C) finish).symm
  | some answer =>
      simp [CommonChallenge.toCommonCache, h]

/-- A single encoded hash query has the same joint returned value, ordered log entry, and
complete final cache distribution as the common-carrier query. -/
theorem CommonChallenge.evalDist_logged_hashQuery
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    (key : Key Input Salt rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace
      ((C × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
    𝒟[common.encodeJoint <$> randomOracleLoggedRun
      (common.simulateNative
        (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inr key)))) cache] =
    𝒟[randomOracleLoggedRun
      (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inr key)))
      (common.toCommonCache cache)] := by
  let : MeasurableSpace
      ((C × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace (C × (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  rw [common.simulateNative_hashQuery, randomOracleLoggedRun_map]
  rw [randomOracleLoggedRun_hashQuery, randomOracleLoggedRun_hashQuery]
  let finish : C × (Key Input Salt rounds →ₒ C).QueryCache →
      (C × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache :=
    fun p => ((p.1, [⟨key, p.1⟩]), p.2)
  have hmap (p : key.Challenge × (oracleSpec Input Salt rounds).QueryCache) :
      common.encodeJoint
        (((common.challengeEquiv key) p.1, [⟨key, p.1⟩]), p.2) =
      finish ((common.challengeEquiv key p.1), common.toCommonCache p.2) := by
    simp [CommonChallenge.encodeJoint, finish]
  simp only [Functor.map_map]
  simp_rw [hmap]
  rw [← Functor.map_map]
  rw [evalDist_map_of_discrete]
  rw [common.evalDist_randomOracle_step key cache]
  simpa only [finish] using
    (evalDist_map_of_discrete
      (((Key Input Salt rounds →ₒ C).randomOracle key).run
        (common.toCommonCache cache)) finish).symm

/-- A private uniform query has identical observations on either side of the encoding. -/
theorem CommonChallenge.evalDist_logged_uniformQuery
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    (n : ℕ) (cache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace
      ((Fin (n + 1) × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
    𝒟[common.encodeJoint <$> randomOracleLoggedRun
      (common.simulateNative
        (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inl n)))) cache] =
    𝒟[randomOracleLoggedRun
      (liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query (.inl n)))
      (common.toCommonCache cache)] := by
  let : MeasurableSpace
      ((Fin (n + 1) × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  rw [common.simulateNative_uniformQuery]
  rw [randomOracleLoggedRun_uniformQuery, randomOracleLoggedRun_uniformQuery]
  simp [CommonChallenge.encodeJoint]

/-- Encoding preserves the ordered log concatenation used by the cached bind interpreter. -/
theorem CommonChallenge.encodeJoint_append
    (common : CommonChallenge Input Salt C rounds) {A B : Type}
    (first : (A × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache)
    (second : (B × QueryLog (oracleSpec Input Salt rounds)) ×
      (oracleSpec Input Salt rounds).QueryCache) :
    common.encodeJoint ((second.1.1, first.1.2 ++ second.1.2), second.2) =
      (((common.encodeJoint second).1.1,
        (common.encodeJoint first).1.2 ++ (common.encodeJoint second).1.2),
        (common.encodeJoint second).2) := by
  simp [CommonChallenge.encodeJoint]

/-- Joint couplings compose through the cached interpreter's exact log and cache handoff. -/
theorem CommonChallenge.evalDist_logged_bind
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    {A B : Type}
    (nativeFirst : OracleComp (unifSpec + oracleSpec Input Salt rounds) A)
    (commonFirst : OracleComp (unifSpec + (Key Input Salt rounds →ₒ C)) A)
    (nativeNext : A → OracleComp (unifSpec + oracleSpec Input Salt rounds) B)
    (commonNext : A → OracleComp (unifSpec + (Key Input Salt rounds →ₒ C)) B)
    (firstLaw : ∀ nativeCache,
      letI : MeasurableSpace
        ((A × QueryLog (Key Input Salt rounds →ₒ C)) ×
          (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
      𝒟[common.encodeJoint <$> randomOracleLoggedRun nativeFirst nativeCache] =
        𝒟[randomOracleLoggedRun commonFirst (common.toCommonCache nativeCache)])
    (nextLaw : ∀ a nativeCache,
      letI : MeasurableSpace
        ((B × QueryLog (Key Input Salt rounds →ₒ C)) ×
          (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
      𝒟[common.encodeJoint <$> randomOracleLoggedRun (nativeNext a) nativeCache] =
        𝒟[randomOracleLoggedRun (commonNext a) (common.toCommonCache nativeCache)])
    (nativeCache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace
      ((B × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
    𝒟[common.encodeJoint <$>
      randomOracleLoggedRun (nativeFirst >>= nativeNext) nativeCache] =
    𝒟[randomOracleLoggedRun (commonFirst >>= commonNext)
      (common.toCommonCache nativeCache)] := by
  let : MeasurableSpace
      ((B × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  rw [randomOracleLoggedRun_bind, randomOracleLoggedRun_bind]
  simp only [map_bind]
  let : MeasurableSpace
      ((A × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  refine evalDist_bind_transport
    (nativePrefix := randomOracleLoggedRun nativeFirst nativeCache)
    (encodedPrefix := randomOracleLoggedRun commonFirst (common.toCommonCache nativeCache))
    (encode := common.encodeJoint)
    (nativeContinue := fun first =>
      common.encodeJoint <$>
        (fun second => ((second.1.1, first.1.2 ++ second.1.2), second.2)) <$>
          randomOracleLoggedRun (nativeNext first.1.1) first.2)
    (commonContinue := fun first =>
      (fun second => ((second.1.1, first.1.2 ++ second.1.2), second.2)) <$>
        randomOracleLoggedRun (commonNext first.1.1) first.2) ?_ ?_
  · exact firstLaw nativeCache
  · intro first
    let : MeasurableSpace
        ((B × QueryLog (oracleSpec Input Salt rounds)) ×
          (oracleSpec Input Salt rounds).QueryCache) := ⊤
    let finish : (B × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache →
        (B × QueryLog (Key Input Salt rounds →ₒ C)) ×
          (Key Input Salt rounds →ₒ C).QueryCache :=
      fun second =>
        ((second.1.1, (common.encodeJoint first).1.2 ++ second.1.2), second.2)
    have hmap (second : (B × QueryLog (oracleSpec Input Salt rounds)) ×
        (oracleSpec Input Salt rounds).QueryCache) :
        common.encodeJoint
          ((second.1.1, first.1.2 ++ second.1.2), second.2) =
        finish (common.encodeJoint second) :=
      common.encodeJoint_append first second
    simp only [Functor.map_map]
    simp_rw [hmap]
    rw [← Functor.map_map]
    rw [evalDist_map_of_discrete, nextLaw first.1.1 first.2]
    exact (evalDist_map_of_discrete
      (randomOracleLoggedRun (commonNext first.1.1) (common.toCommonCache first.2))
      finish).symm

/-- Simulating any adaptive common-carrier program through native challenge types preserves
its return value, ordered query log, and complete final random-oracle cache jointly. -/
theorem CommonChallenge.evalDist_randomOracleLoggedRun_simulateNative
    (common : CommonChallenge Input Salt C rounds)
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    {A : Type}
    (program : OracleComp (unifSpec + (Key Input Salt rounds →ₒ C)) A)
    (nativeCache : (oracleSpec Input Salt rounds).QueryCache) :
    letI : MeasurableSpace
      ((A × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
    𝒟[common.encodeJoint <$>
      randomOracleLoggedRun (common.simulateNative program) nativeCache] =
    𝒟[randomOracleLoggedRun program (common.toCommonCache nativeCache)] := by
  induction program using OracleComp.inductionOn generalizing nativeCache with
  | pure value =>
      simp [CommonChallenge.simulateNative, randomOracleLoggedRun,
        CommonChallenge.encodeJoint]
  | query_bind query next ih =>
      let request : OracleComp (unifSpec + (Key Input Salt rounds →ₒ C))
          ((unifSpec + (Key Input Salt rounds →ₒ C)).Range query) :=
        liftM ((unifSpec + (Key Input Salt rounds →ₒ C)).query query)
      have hfirst (cache : (oracleSpec Input Salt rounds).QueryCache) :
          letI : MeasurableSpace
            (((unifSpec + (Key Input Salt rounds →ₒ C)).Range query ×
                QueryLog (Key Input Salt rounds →ₒ C)) ×
              (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
          𝒟[common.encodeJoint <$>
            randomOracleLoggedRun (common.simulateNative request) cache] =
          𝒟[randomOracleLoggedRun request (common.toCommonCache cache)] := by
        cases query with
        | inl n => exact common.evalDist_logged_uniformQuery n cache
        | inr key => exact common.evalDist_logged_hashQuery key cache
      have hbind := common.evalDist_logged_bind
        (common.simulateNative request) request
        (fun answer => common.simulateNative (next answer)) next
        hfirst ih nativeCache
      simpa only [request, CommonChallenge.simulateNative, simulateQ_bind]
        using hbind

end Interaction.Oracle.Security.StateRestoration
