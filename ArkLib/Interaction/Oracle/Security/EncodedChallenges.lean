/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedWeighted
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# A common uniform challenge carrier for encoded restoration keys

Each restoration key has a challenge type. The supplied equivalences identify those types
with one common external challenge type and transport complete native tables. The
uniform sampler law is proved from the `SampleableType` laws rather than posited as a game equality.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C : Type} {rounds : List Round}

/-- The restricted common-challenge fragment of an otherwise dependent restoration schedule. -/
structure CommonChallenge (Input Salt C : Type) (rounds : List Round) where
  challengeEquiv : (key : Key Input Salt rounds) → key.Challenge ≃ C

/-- Encode all entries of one native dependent challenge table into the common carrier. -/
def CommonChallenge.toCommonTable
    (common : CommonChallenge Input Salt C rounds)
    (table : Table Input Salt rounds) : Key Input Salt rounds → C :=
  fun key => common.challengeEquiv key (table key)

/-- Decode a common-carrier table into the native key-dependent challenge types. -/
def CommonChallenge.fromCommonTable
    (common : CommonChallenge Input Salt C rounds)
    (table : Key Input Salt rounds → C) : Table Input Salt rounds :=
  fun key => (common.challengeEquiv key).symm (table key)

/-- The native and common-carrier complete table presentations are equivalent. -/
def CommonChallenge.tableEquiv
    (common : CommonChallenge Input Salt C rounds) :
    Table Input Salt rounds ≃ (Key Input Salt rounds → C) where
  toFun := common.toCommonTable
  invFun := common.fromCommonTable
  left_inv table := by funext key; exact (common.challengeEquiv key).symm_apply_apply _
  right_inv table := by funext key; exact (common.challengeEquiv key).apply_symm_apply _

/-- Transport an actual native cache cellwise into the common challenge carrier. -/
def CommonChallenge.toCommonCache
    (common : CommonChallenge Input Salt C rounds)
    (cache : (oracleSpec Input Salt rounds).QueryCache) :
    (Key Input Salt rounds →ₒ C).QueryCache :=
  QueryCache.ofFn fun key => (cache key).map (common.challengeEquiv key)

/-- Recover the native dependent cache from a common-carrier cache. -/
def CommonChallenge.fromCommonCache
    (common : CommonChallenge Input Salt C rounds)
    (cache : (Key Input Salt rounds →ₒ C).QueryCache) :
    (oracleSpec Input Salt rounds).QueryCache :=
  QueryCache.ofFn fun key => (cache key).map (common.challengeEquiv key).symm

/-- Complete native cache state and common-carrier cache state are equivalent. -/
def CommonChallenge.cacheEquiv
    (common : CommonChallenge Input Salt C rounds) :
    (oracleSpec Input Salt rounds).QueryCache ≃
      (Key Input Salt rounds →ₒ C).QueryCache where
  toFun := common.toCommonCache
  invFun := common.fromCommonCache
  left_inv cache := by
    apply QueryCache.ext
    intro key
    cases h : cache key with
    | none => simp [CommonChallenge.toCommonCache,
        CommonChallenge.fromCommonCache, h]
    | some value => simp [CommonChallenge.toCommonCache,
        CommonChallenge.fromCommonCache, h]
  right_inv cache := by
    apply QueryCache.ext
    intro key
    cases h : cache key with
    | none => simp [CommonChallenge.toCommonCache,
        CommonChallenge.fromCommonCache, h]
    | some value => simp [CommonChallenge.toCommonCache,
        CommonChallenge.fromCommonCache, h]

/-- Every native hash-log entry becomes an entry at the same key with its common challenge. -/
def CommonChallenge.toCommonLog
    (common : CommonChallenge Input Salt C rounds)
    (log : QueryLog (oracleSpec Input Salt rounds)) :
    QueryLog (Key Input Salt rounds →ₒ C) :=
  log.map fun entry => ⟨entry.1, (common.challengeEquiv entry.1).toFun entry.2⟩

/-- Query interpreter from the common-carrier key oracle into the actual dependent native
restoration oracle. The native challenge answer is converted through its named
challenge equivalence. -/
def CommonChallenge.commonQueryImpl
    (common : CommonChallenge Input Salt C rounds) :
    QueryImpl (unifSpec + (Key Input Salt rounds →ₒ C))
      (OracleComp (unifSpec + oracleSpec Input Salt rounds)) :=
  fun query => match query with
    | .inl coin => liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inl coin))
    | .inr key => (common.challengeEquiv key).toFun <$>
        liftM ((unifSpec + oracleSpec Input Salt rounds).query (.inr key))

/-- Translate a common-carrier oracle computation into a genuine native restoration-oracle
computation. This keeps the caller's private uniform draws and every native hash query. -/
def CommonChallenge.simulateNative
    (common : CommonChallenge Input Salt C rounds)
    {A : Type} (program : OracleComp
      (unifSpec + (Key Input Salt rounds →ₒ C)) A) :
    OracleComp (unifSpec + oracleSpec Input Salt rounds) A :=
  simulateQ common.commonQueryImpl program

/-- Uniform native challenge sampling transports to the common external carrier in measure.
The theorem works for any `SampleableType` implementations satisfying their uniformity laws. -/
theorem CommonChallenge.evalDist_challengeEquiv_uniform
    (common : CommonChallenge Input Salt C rounds) [SampleableType C]
    (key : Key Input Salt rounds) :
    letI : MeasurableSpace C := ⊤
    𝒟[(common.challengeEquiv key) <$> ($ᵗ key.Challenge)] = 𝒟[$ᵗ C] := by
  let : MeasurableSpace C := ⊤
  let : MeasurableSpace key.Challenge := ⊤
  rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample,
    SampleableType.evalDist_uniformSample]
  exact map_uniformOn_univ_of_bijective Measurable.of_discrete
    (common.challengeEquiv key).bijective

end Interaction.Oracle.Security.StateRestoration
