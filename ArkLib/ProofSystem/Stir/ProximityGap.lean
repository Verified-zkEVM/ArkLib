/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-- Theorem 4.1[BCIKS20] from STIR[ACFY24]
  Let `C = RS[F, ι, degree]` be a ReedSolomon code with rate `degree / |ι|`
  and let Bstar(ρ) = √ρ. For all `δ ∈ (0, 1 - Bstar(ρ))`, `f₁,...,fₘ : ι → F`, if
  `Pr_{r ← F} [ δᵣ(rⱼ * fⱼ, C) ≤ δ] > err'(degree, ρ, δ, m)`
  then ∃ S ⊆ ι, |S| ≥ (1 - δ) * |ι| and
  ∀ i : m, ∃ u : C, u(S) = fᵢ(S) -/
lemma proximity_gap
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
  (h : ∀ (hδLe : δ < 1 - Bstar (LinearCode.rate (code φ degree))) {f : Fin m → ι → F},
        Pr_{
          let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ (δ : ℝ)]
            > ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :

        ∃ S : Finset ι,
          S.card ≥ (1 - δ) * (Fintype.card ι) ∧
        ∃ u : (ι → F),
          u ∈ (code φ degree) ∧ ∀ i : Fin m, ∀ x ∈ S, f i x = u x

:= by sorry

end STIR
