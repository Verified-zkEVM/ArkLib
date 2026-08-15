/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import CompPoly.Fields.KoalaBear.Ext6
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Computable sampling for the KoalaBear sextic extension

This file gives `KoalaBear.Ext6` a pinned `SampleableType` implementation. It samples a vector of
six independent base-field limbs and transports that vector through the executable coefficient
representation of the extension field. In particular, it does not enumerate the `q ^ 6` extension
elements or use `SampleableType.ofFintype`.
-/

open OracleComp

namespace KoalaBear

/-- The executable equivalence between six base-field coefficients and the sextic extension. -/
def ext6CoeffsEquiv : Vector Field 6 ≃ Ext6 where
  toFun := fun v => CompPoly.Extension.Ext.ofVector (P := ext6Params) v
  invFun := fun x => CompPoly.Extension.Ext.coeffs (P := ext6Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- Boolean equality on `Ext6` agrees with propositional equality coefficientwise. -/
instance instLawfulBEqExt6 : LawfulBEq Ext6 :=
  inferInstanceAs (LawfulBEq (Vector Field 6))

/-- Sample `Ext6` by sampling its six base-field coefficients independently. -/
def sampleExt6 : ProbComp Ext6 :=
  ext6CoeffsEquiv <$> ($ᵗ (Vector Field 6))

/-- The pinned six-base-limb sampler for `KoalaBear.Ext6`. -/
@[reducible] def sampleableTypeExt6 : SampleableType Ext6 :=
  SampleableType.ofEquiv ext6CoeffsEquiv

instance instSampleableTypeExt6 : SampleableType Ext6 := sampleableTypeExt6

/-- The canonical `Ext6` uniform sample is definitionally the six-limb sampler above. -/
theorem uniformSample_ext6_eq_sampleExt6 : ($ᵗ Ext6) = sampleExt6 := rfl

/-- Sampling six independent base limbs induces the uniform distribution on `Ext6`. -/
theorem evalDist_sampleExt6 :
    𝒟[sampleExt6] = liftM (PMF.uniformOfFintype Ext6) := by
  rw [← uniformSample_ext6_eq_sampleExt6]
  exact evalDist_uniformSample Ext6

end KoalaBear
