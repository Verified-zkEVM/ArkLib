/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import CompPoly.Fields.KoalaBear.Ext6
public import ArkLib.Data.Probability.Uniform
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Computable sampling for the KoalaBear sextic extension

This file gives `KoalaBear.Ext6` a pinned `SampleableType` implementation. It samples a vector of
six independent base-field limbs and transports that vector through the executable coefficient
representation of the extension field. In particular, it does not enumerate the `q ^ 6` extension
elements or use `SampleableType.ofFintype`.
-/

@[expose] public section

open OracleComp

namespace KoalaBear.Ext6

/-- The executable equivalence between six base-field coefficients and the sextic extension. -/
def coeffsEquiv : Vector Field 6 ≃ Ext6 where
  toFun := fun v => CompPoly.Extension.Ext.ofVector (P := ext6Params) v
  invFun := fun x => CompPoly.Extension.Ext.coeffs (P := ext6Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sample `Ext6` by sampling its six base-field coefficients independently. -/
def sample : ProbComp Ext6 :=
  coeffsEquiv <$> ($ᵗ (Vector Field 6))

/-- The pinned six-base-limb sampler for `KoalaBear.Ext6`. -/
@[reducible] def sampleableType : SampleableType Ext6 :=
  SampleableType.ofEquiv coeffsEquiv

instance instSampleableType : SampleableType Ext6 := sampleableType

/-- The canonical `Ext6` uniform sample is definitionally the six-limb sampler above. -/
theorem uniformSample_eq_sample : ($ᵗ Ext6) = sample := rfl

/-- Sampling six independent base limbs induces the uniform executable distribution on `Ext6`. -/
theorem evalDist_sample [MeasurableSpace Ext6] [MeasurableSingletonClass Ext6] :
    𝒟[sample] = ProbabilityTheory.uniformOn Set.univ := by
  rw [← uniformSample_eq_sample]
  exact SampleableType.evalDist_uniformSample

end KoalaBear.Ext6

namespace KoalaBear.Field

open OracleSpec

/-- Every supported log of the selected base-field sample has one primitive uniform query. -/
theorem uniformSample_log_length (result : KoalaBear.Field × QueryLog unifSpec)
    (member : result ∈ support ($ᵗ KoalaBear.Field).withQueryLog) : result.2.length = 1 := by
  change result ∈ support
    (((FinEnum.equiv (α := KoalaBear.Field)).symm <$>
      (liftM (unifSpec.query (KoalaBear.fieldSize - 1)) :
        ProbComp (Fin KoalaBear.fieldSize))).withQueryLog) at member
  rw [OracleComp.withQueryLog_map, support_map] at member
  obtain ⟨original, member, rfl⟩ := member
  rw [withQueryLog_query, mem_support_bind_iff] at member
  obtain ⟨answer, _, member⟩ := member
  rw [mem_support_pure_iff] at member
  subst original
  rfl
end KoalaBear.Field

namespace KoalaBear.Ext6

/-- The selected extension sampler draws six base-field coefficients in traversal order. -/
theorem uniformSample_eq_ofFnM : ($ᵗ Ext6) = coeffsEquiv <$>
    Vector.ofFnM (fun _ : Fin 6 => ($ᵗ KoalaBear.Field)) := by
  rw [uniformSample_eq_sample, sample, SampleableType.uniformSample_vector_eq_ofFnM]

/-- Every supported log of the selected extension sample has six primitive uniform queries. -/
theorem uniformSample_log_length (result : Ext6 × OracleSpec.QueryLog unifSpec)
    (member : result ∈ support ($ᵗ Ext6).withQueryLog) : result.2.length = 6 := by
  rw [uniformSample_eq_ofFnM, OracleComp.withQueryLog_map, support_map] at member
  obtain ⟨original, member, rfl⟩ := member
  exact OracleComp.withQueryLog_ofFnM_const_length ($ᵗ KoalaBear.Field) 1 6
    KoalaBear.Field.uniformSample_log_length original member

end KoalaBear.Ext6
