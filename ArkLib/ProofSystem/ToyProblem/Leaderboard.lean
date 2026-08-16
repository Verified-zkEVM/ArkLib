/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Impl.FRS
import ArkLib.ProofSystem.ToyProblem.Impl.IRS
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Neutral fixed-radius reference interface for the toy problem

This is a small façade over the reusable toy-problem mathematics.  It packages
an encoder, its code and repetition count, and gives stable projections for the
winning-set/spot-check upper bound and the executable extractor's MCA-plus-list
certificate.  It intentionally contains no score format, ranking direction,
submission metadata, or chosen operating radius.
-/

namespace ToyProblem

open Code
open scoped NNReal

variable {ι F A : Type} [Fintype ι] [Field F] [Fintype F]
variable [AddCommGroup A] [Module F A] [Fintype A]

/-- Neutral parameters needed to state a fixed-radius toy-protocol bound. -/
structure FixedRadiusParameters where
  k : ℕ
  t : ℕ
  code : ModuleCode ι F A
  encoder : (Fin k → F) →ₗ[F] (ι → A)
  encoder_injective : Function.Injective encoder
  encoder_range : Set.range encoder = (code : Set (ι → A))

/-- A concrete inhabitant of the neutral fixed-radius façade, built from the
proved Ext6 folded-RS geometric-progression reference point with `s = 32`,
`k = 2^20`, and `t = 128`.

This packages exactly the encoder, range, and injectivity facts required by
`FixedRadiusParameters`; it does not add the smooth base-field provenance or
the numerical security certificate of the separate protected prize profile. -/
noncomputable def koalaFRSFixedRadiusParameters :
    FixedRadiusParameters
      (ι := Fin (2 ^ 16)) (F := KoalaBear.Ext6)
      (A := Fin 32 → KoalaBear.Ext6) where
  k := 2 ^ 20
  t := 128
  code := ReedSolomon.Folded.frsCode Impl.FRS.koalaFRSDomain (2 ^ 20) 32
    Impl.FRS.koalaFoldω
  encoder := Impl.FRS.koalaFRSEnc
  encoder_injective := Impl.FRS.koalaFRSEnc_injective
  encoder_range := Impl.FRS.koalaFRSEnc_range

/-- The certified winning-set/spot-check upper bound for a neutral parameter point. -/
noncomputable def FixedRadiusParameters.winningSetUpperBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  winningSetFixedRadiusUpperBound p.encoder δ p.t

/-- The MCA-plus-list/spot-check certificate used by the executable extractor. -/
noncomputable def FixedRadiusParameters.extractorCertificate
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  extractorCertifiedError p.code δ p.t

omit [Fintype A] in
/-- At every admissible radius, the winning-set/spot-check upper bound is
bounded by the executable extractor certificate. -/
theorem FixedRadiusParameters.winningSetUpperBound_le_extractorCertificate
    [Finite A] [DecidableEq A] [Nonempty ι]
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0)
      ((minRelHammingDistCode (p.code : Set (ι → A)) : ℝ≥0))) :
    p.winningSetUpperBound δ ≤ p.extractorCertificate δ := by
  classical
  letI := Fintype.ofFinite A
  letI : DecidableEq F := Classical.decEq F
  exact winningSetFixedRadiusUpperBound_le_extractorCertifiedError
    p.code δ p.t hδ p.encoder p.encoder_injective p.encoder_range

/-- A neutral carrier for a proved upper bound on the executable extractor's
fixed-radius certificate. -/
structure FixedRadiusCertificateBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) where
  bound : ℝ≥0
  proof : p.extractorCertificate δ ≤ bound

/-- The bound carrier is non-vacuous: the exact certificate always supplies a
canonical inhabitant. -/
noncomputable def FixedRadiusCertificateBound.exact
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : FixedRadiusCertificateBound p δ :=
  ⟨p.extractorCertificate δ, le_rfl⟩

end ToyProblem
