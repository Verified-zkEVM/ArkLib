/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedWeighted

/-!
# Exact weighted charge of encoded random-oracle queries

An external query outside the encoding image has zero local certificate weight. Consequently
decoding the actual external log preserves its weighted distinct-key charge exactly.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory

namespace Interaction.Oracle.Security.StateRestoration

variable {K D C A : Type}

/-- The decoded native log and the full external log have the same weighted charge when
off-image keys are assigned zero weight. -/
theorem StrictCodec.freshImageCharge_eq (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D]
    (weight : K → ENNReal) (log : QueryLog (D →ₒ C)) :
    freshQueryCharge weight (codec.decodeImageLog log) =
      freshQueryCharge (codec.encodedWeight weight) log := by
  let image := (freshKeysOfLog (codec.decodeImageLog log)).map
    ⟨codec.encode, codec.encode_injective⟩
  have hsum : freshQueryCharge weight (codec.decodeImageLog log) =
      ∑ d ∈ image, codec.encodedWeight weight d := by
    simp [freshQueryCharge, image, Finset.sum_map]
  rw [hsum]
  apply Finset.sum_subset (codec.freshImageKeys_map_subset log)
  intro d hd hnot
  cases hdecode : codec.decode d with
  | none => simp [StrictCodec.encodedWeight, hdecode]
  | some key =>
      exfalso
      apply hnot
      rw [Finset.mem_map]
      rw [mem_freshKeysOfLog] at hd
      obtain ⟨entry, hentry, heq⟩ := hd
      refine ⟨key, ?_, ?_⟩
      · rw [mem_freshKeysOfLog]
        refine ⟨⟨key, entry.2⟩, ?_, rfl⟩
        simp only [StrictCodec.decodeImageLog, List.mem_filterMap]
        refine ⟨entry, hentry, ?_⟩
        cases entry with
        | mk source answer =>
            cases heq
            simp [hdecode]
      · exact codec.encode_decode d key hdecode

/-- The expected charge of the translated native program equals the external encoded-domain
charge on the same adaptive experiment, including failed branches. -/
theorem StrictCodec.expectedNativeCharge_eq_external (codec : StrictCodec K D)
    [DecidableEq K] [DecidableEq D] [SampleableType C]
    (program : OracleComp (unifSpec + (D →ₒ C)) A)
    (weight : K → ENNReal) :
    expectedFreshQueryCharge (codec.routeProgram program ∅) weight =
      expectedFreshQueryCharge program (codec.encodedWeight weight) := by
  let nativeRun := randomOracleLoggedRun (codec.routeProgram program ∅) ∅
  let externalRun := randomOracleLoggedRun program ∅
  let : MeasurableSpace ((((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) ×
      QueryLog (K →ₒ C)) × (K →ₒ C).QueryCache) := ⊤
  let : MeasurableSpace ((A × QueryLog (D →ₒ C)) × (D →ₒ C).QueryCache) := ⊤
  change (∫⁻ result, freshQueryCharge weight result.1.2 ∂𝒟[nativeRun]) =
    ∫⁻ result, freshQueryCharge (codec.encodedWeight weight) result.1.2
      ∂𝒟[externalRun]
  calc
    _ = ∫⁻ result,
        freshQueryCharge (codec.encodedWeight weight) result.1.1.1.2
          ∂𝒟[nativeRun] := by
          apply lintegral_congr_ae
          have hae := evalDist.ae_of_forall_mem_support nativeRun
            (fun result => freshQueryCharge weight result.1.2 =
              freshQueryCharge (codec.encodedWeight weight) result.1.1.1.2)
            MeasurableSet.of_discrete
            (fun result hr => by
              rw [codec.routeProgram_nativeLog program ∅ ∅ result hr]
              exact codec.freshImageCharge_eq weight result.1.1.1.2)
          filter_upwards [hae] with result hresult
          exact hresult
    _ = _ := by
      have hproj := codec.routeProgram_externalProjection program
        (∅ : (K →ₒ C).QueryCache) (∅ : (D →ₒ C).QueryCache)
      rw [codec.mergeCache_empty] at hproj
      dsimp only [externalRun]
      rw [← hproj, lintegral_evalDist_map_of_discrete]

end Interaction.Oracle.Security.StateRestoration
