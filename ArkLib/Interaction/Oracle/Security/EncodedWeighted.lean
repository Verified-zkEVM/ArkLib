/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedLog

/-!
# Weighted charge for encoded random-oracle queries

Image keys carry their native local error weight; off-image keys carry zero local error. The
weighted bound is evaluated on the actual native and external cached logs.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory

namespace Interaction.Oracle.Security.StateRestoration

variable {K D C A : Type}

/-- Encoded image keys seen in the external log include every native key decoded from it. -/
theorem StrictCodec.freshImageKeys_map_subset (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D]
    (log : QueryLog (D →ₒ C)) :
    (freshKeysOfLog (codec.decodeImageLog log)).map
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

/-- Weight of an external encoded key: native local weight on-image, zero off-image. -/
def StrictCodec.encodedWeight (codec : StrictCodec K D)
    (weight : K → ENNReal) (d : D) : ENNReal :=
  (codec.decode d).elim 0 weight

@[simp] theorem StrictCodec.encodedWeight_encode (codec : StrictCodec K D)
    (weight : K → ENNReal) (key : K) :
    codec.encodedWeight weight (codec.encode key) = weight key := by
  simp [StrictCodec.encodedWeight, codec.decode_encode]

/-- Native weighted charge on the decoded image log is bounded by external encoded-domain
charge, where an off-image key contributes no local certificate error. -/
theorem StrictCodec.freshImageCharge_le (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D]
    (weight : K → ENNReal) (log : QueryLog (D →ₒ C)) :
    freshQueryCharge weight (codec.decodeImageLog log) ≤
      freshQueryCharge (codec.encodedWeight weight) log := by
  let image := (freshKeysOfLog (codec.decodeImageLog log)).map
    ⟨codec.encode, codec.encode_injective⟩
  have hsum : freshQueryCharge weight (codec.decodeImageLog log) =
      ∑ d ∈ image, codec.encodedWeight weight d := by
    simp [freshQueryCharge, image, Finset.sum_map]
  rw [hsum]
  exact Finset.sum_le_sum_of_subset (codec.freshImageKeys_map_subset log)


/-- The actual expected native weighted charge is at most the encoded-domain expected charge.
The inequality is over the same coupled run and includes all failed/adaptive branches. -/
theorem StrictCodec.expectedNativeCharge_le_external (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (weight : K → ENNReal) :
    expectedFreshQueryCharge (codec.routeProgram program ∅) weight ≤
      expectedFreshQueryCharge program (codec.encodedWeight weight) := by
  let nativeRun := randomOracleLoggedRun (codec.routeProgram program ∅) ∅
  let externalRun := randomOracleLoggedRun program ∅
  let : MeasurableSpace ((((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      QueryLog (K →ₒ C)) × (K →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace ((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) := ⊤
  change (∫⁻ result, freshQueryCharge weight result.1.2 ∂𝒟[nativeRun]) ≤
    ∫⁻ result, freshQueryCharge (codec.encodedWeight weight) result.1.2
      ∂𝒟[externalRun]
  calc
    _ ≤ ∫⁻ result,
        freshQueryCharge (codec.encodedWeight weight) result.1.1.1.2
          ∂𝒟[nativeRun] := by
          apply lintegral_mono_ae
          have hae := evalDist.ae_of_forall_mem_support nativeRun
            (fun result => freshQueryCharge weight result.1.2 ≤
              freshQueryCharge (codec.encodedWeight weight) result.1.1.1.2)
            MeasurableSet.of_discrete
            (fun result hr => by
              rw [codec.routeProgram_nativeLog program ∅ ∅ result hr]
              exact codec.freshImageCharge_le weight result.1.1.1.2)
          filter_upwards [hae] with result hresult
          exact hresult
    _ = _ := by
      have hproj := codec.routeProgram_externalProjection program
        (∅ : (K →ₒ C).QueryCache) (∅ : (D →ₒ C).QueryCache)
      rw [codec.mergeCache_empty] at hproj
      dsimp only [externalRun]
      rw [← hproj, lintegral_evalDist_map_of_discrete]

end Interaction.Oracle.Security.StateRestoration
