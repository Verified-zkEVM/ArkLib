/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-!
## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

/-- Theorem 4.1[BCIKS20] from [ACFY24stir]
  Let `C = RS[F, ι, degree]` be a ReedSolomon code with rate `degree / |ι|`
  and let Bstar(ρ) = √ρ. For all `δ ∈ (0, 1 - Bstar(ρ))`, `f₁,...,fₘ : ι → F`, if
  `Pr_{r ← F} [ δᵣ(rⱼ * fⱼ, C) ≤ δ] > err'(degree, ρ, δ, m)`
  then ∃ S ⊆ ι, |S| ≥ (1 - δ) * |ι| and
  ∀ i : m, ∃ u : C, u(S) = fᵢ(S)

  **ABF26 mapping.** Predicate-style "joint correlated agreement" form of the
  proximity-gap bound. ABF26's numeric counterparts:

  - `ProximityGap.epsCA C δ_fld δ_int` (Def 4.1, in
    `ArkLib/Data/CodingTheory/ProximityGap/Errors.lean`) bounds the same "line δ-close
    but stack not jointly close" probability for **m = 2** (affine lines).
  - For **general m**, the analogue is `epsCA_curves C (m-1) δ_fld δ_int` (the
    polynomial-curve variant).

  **Statement caveat (2026-07-21 audit).** The Lean statement below quantifies over an
  *unconstrained* `GenFun : F → Fin m → F`, whereas BCIKS20 (and STIR) state this for
  power/curve generators `r ↦ (1, r, …, r^{m-1})`; the over-general form is unsourced
  and false-instantiable, a pre-existing defect at the merge-base (Phase-A audit annex).
  Any future bridge (e.g. a `proximity_gap_iff_epsCA_le`) must first restrict `GenFun`
  to the curve form; deferred per Phase 4 of `docs/kb/ABF26_INTEGRATION_PLAN.md`. -/
lemma proximity_gap
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
  (hδPos : 0 < δ)
  (hδLt : δ < 1 - Bstar (LinearCode.rate (code φ degree)))
  (hProb :
    Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ δ] >
      ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
  ∃ S : Finset ι,
    S.card ≥ (1 - δ) * (Fintype.card ι) ∧
    ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x
:= by
  sorry

end STIR
