/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
module

public import ArkLib.Data.CodingTheory.Basic.DecodingRadius
public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.Basic.LinearCode
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.CodingTheory.ReedSolomon
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import ArkLib.ProofSystem.Stir.ProximityBound

/-!
# ArkLib.ProofSystem.Stir.ProximityGap

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-!
## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

/-- Theorem 4.1 of [ACFY24stir] (due to [BCIKS20]): taking the powers of a uniform `r ∈ F` as
  coefficients, the random linear combination is a proximity generator for `RS[F, ι, degree]`.

  Let `C = RS[F, ι, degree]`, with `0 < degree`, have rate `ρ = degree / |ι|` and let
  `B⋆(ρ) = √ρ`. For every
  `δ ∈ (0, 1 - B⋆(ρ))` and `f₀, …, f_{m-1} : ι → F`, if
  `Pr_{r ← F}[δᵣ(∑ⱼ rʲ * fⱼ, C) ≤ δ] > err⋆(degree, ρ, δ, m)`,
  then there is `S ⊆ ι` with `|S| ≥ (1 - δ) * |ι|` such that every `fᵢ` agrees on `S` with some
  codeword `u ∈ C`.

  The paper numbers the functions from `1` and weights `fⱼ` by `r^{j-1}`; here they are numbered
  from `0`, so the weight of `fⱼ` is `rʲ`.

  The hypothesis `0 < degree` is implicit in the paper: `err⋆` divides by `ρ`. For `degree = 0`
  the convention `x / 0 = 0` makes `err⋆` zero and the statement false. -/
lemma proximity_gap
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F}
  (hdegPos : 0 < degree) (hδPos : 0 < δ)
  (hδLt : δ < 1 - Bstar (LinearCode.rate (code φ degree)))
  (hProb :
    Pr{let r ← $ᵗ F}[δᵣ((fun x => ∑ j : Fin m, r ^ (j : ℕ) * f j x), code φ degree) ≤ δ] >
      ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
  ∃ S : Finset ι,
    S.card ≥ (1 - δ) * (Fintype.card ι) ∧
    ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x := by
  sorry

end STIR
