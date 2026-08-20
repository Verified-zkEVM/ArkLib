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

**Verified vs. admitted.**  Both projections below are `sorry`-free and are *symbolic*:
`certifiedExtractorError` unfolds to `ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F| `-shaped data, not to a
numeral.  Instantiating a `FixedRadiusParameters` therefore asserts nothing numeric about a
parameter point; obtaining a numeral additionally requires the external MCA/CA admits of
`Data/CodingTheory/ProximityGap/CapacityBounds.lean`, which is deliberately outside this
file's import cone (see the "Verified vs. admitted" section of `Spec/General.lean` and the
numeric-route notes in `Impl/IRS.lean`).
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
noncomputable def FixedRadiusParameters.koalaFRS :
    FixedRadiusParameters
      (ι := Fin (2 ^ 16)) (F := KoalaBear.Ext6)
      (A := Fin 32 → KoalaBear.Ext6) where
  k := 2 ^ 20
  t := 128
  code := ReedSolomon.Folded.frsCode Impl.FRS.domain (2 ^ 20) 32
    Impl.FRS.foldOmega
  encoder := Impl.FRS.encoder
  encoder_injective := Impl.FRS.encoder_injective
  encoder_range := Impl.FRS.encoder_range

/-! ### Why there is no in-tree interleaved-RS inhabitant

The façade's one in-tree inhabitant is folded-RS over the sextic extension, which leaves an
apparent asymmetry: the executable extractor ArkLib actually ships
(`Impl.IRS.straightlineExtractor`) is *interleaved*-RS.  The asymmetry is deliberate.

[ABF26] §6.4.1's interleaved instantiation fixes `𝔽 = 𝔹^6` over the KoalaBear base field
`𝔹 = 𝔽_q`, a **smooth domain `L ⊆ 𝔹`** with `|L| = 2^18`, `k = 2^20`, `s = 2^3` (so
`s · |L| = 2^21` and rate `ρ = (k/s)/|L| = 1/2`) and `t = 128`.  That exact object is realized
in the downstream prize-challenge repository, built from
`Impl.IRS.encoder`/`encoder_injective`/`encoder_range` and this very structure.  A
second copy here would fork the protected profile.

The two nearby alternatives are both worse than the cross-reference:

* an interleaved point over `𝔹` **alone** would not be §6.4.1's protocol — the challenge `γ`
  is sampled from `𝔽`, and `Λ/|𝔹|` at `|𝔹| = 2^31` is not the paper's regime; and
* a hand-rolled `⟨ω⟩` domain from KoalaBear's two-adic generator table would fork
  `CompPoly.CPolynomial.NTT.KoalaBear.domainOfLogN`, which already supplies the smooth domain
  the downstream profile uses.

So the split is: neutral, provably-inhabited façade plus a folded reference point here; the
concrete interleaved profile, its smooth-domain provenance, and any numeric certificate stay
downstream. -/

/-- The certified winning-set/spot-check upper bound for a neutral parameter point. -/
noncomputable def FixedRadiusParameters.winningSetUpperBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  ToyProblem.winningSetUpperBound p.encoder δ p.t

/-- The MCA-plus-list/spot-check certificate used by the executable extractor. -/
noncomputable def FixedRadiusParameters.certifiedExtractorError
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : ℝ≥0 :=
  ToyProblem.certifiedExtractorError p.code δ p.t

omit [Fintype A] in
/-- At every admissible radius, the winning-set/spot-check upper bound is
bounded by the executable extractor certificate. -/
theorem FixedRadiusParameters.winningSetUpperBound_le_certifiedExtractorError
    [Finite A] [DecidableEq A] [Nonempty ι]
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0)
      ((minRelHammingDistCode (p.code : Set (ι → A)) : ℝ≥0))) :
    p.winningSetUpperBound δ ≤ p.certifiedExtractorError δ := by
  classical
  letI := Fintype.ofFinite A
  letI : DecidableEq F := Classical.decEq F
  exact ToyProblem.winningSetUpperBound_le_certifiedExtractorError
    p.code δ p.t hδ p.encoder p.encoder_injective p.encoder_range

/-- A neutral carrier for a proved upper bound on the executable extractor's
fixed-radius certificate.

**The carrier is directional, and inhabitation alone asserts nothing.**  The field
`proof` is `certifiedExtractorError δ ≤ bound`, so *every* weaker `bound` qualifies and
`FixedRadiusCertificateBound.self` inhabits it unconditionally at the exact certificate.
A **smaller** `bound` is the stronger statement.  Any downstream policy layer must
therefore compare the numerals in `bound` and must not treat "this parameter point has a
`FixedRadiusCertificateBound`" as a security claim. -/
structure FixedRadiusCertificateBound
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) where
  bound : ℝ≥0
  proof : p.certifiedExtractorError δ ≤ bound

/-- The bound carrier is non-vacuous: the exact certificate always supplies a
canonical inhabitant. -/
noncomputable def FixedRadiusCertificateBound.self
    (p : FixedRadiusParameters (ι := ι) (F := F) (A := A))
    (δ : ℝ≥0) : FixedRadiusCertificateBound p δ :=
  ⟨p.certifiedExtractorError δ, le_rfl⟩

end ToyProblem
