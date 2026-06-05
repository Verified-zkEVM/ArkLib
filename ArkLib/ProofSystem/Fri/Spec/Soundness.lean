/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ReedSolomonGap
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.OracleReduction.Security.Basic

/-!
# FRI error accounting definitions

Candidate per-round and total error definitions for the FRI protocol soundness
analysis. These definitions follow the structure of the BCIKS20 proximity gap
bounds and Schwartz-Zippel query consistency bounds, but are not yet tied to a
soundness theorem — they are accounting placeholders pending the sequential
composition infrastructure needed for the full soundness proof.

## References

* [Ben-Sasson, I., Chiesa, A., Goldberg, L., Gur, T., Riabzev, M., Spooner, N.,
  *Proximity Gaps for Reed-Solomon Codes*, FOCS 2020][BCIKS20]
-/

namespace Fri

open Polynomial OracleSpec OracleComp ProtocolSpec Finset NNReal ProximityGap

namespace Spec

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable (k : ℕ) (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
variable (l : ℕ) [NeZero l]
variable {ω : ReedSolomon.SmoothCosetFftDomain n F}

/-- Candidate per-round proximity-gap error for the `i`-th FRI folding round,
    following the BCIKS20 error bound for the round-`i` Reed-Solomon code.
    Pending a soundness proof linking this to actual failure probability. -/
noncomputable def roundError (δ : ℝ≥0) (i : Fin k) : ℝ≥0 :=
  let N := ∑ j' ∈ finRangeTo (k + 1) (Fin.last i.castSucc.val).val, (s j').1
  let dom : ReedSolomon.SmoothCosetFftDomain (n - N) F := ω.subdomainNatReversed N
  let degBound := 2 ^ ((∑ j', (s j').1) - N) * d.1
  errorBound δ degBound (↑dom : Fin (2 ^ (n - N)) ↪ F)

/-- Candidate per-round query consistency error: `(D / N)^l` where `D` is the
    degree bound and `N` the domain size for round `i`. This follows the
    Schwartz-Zippel argument structure but is not yet formally tied to the
    query verifier's failure probability via a proven lemma. -/
noncomputable def queryRoundError (i : Fin (k + 1)) : ℝ≥0 :=
  let N := ∑ j' ∈ finRangeTo (k + 1) i.val, (s j').1
  let _dom : ReedSolomon.SmoothCosetFftDomain (n - N) F := ω.subdomainNatReversed N
  let domSize : ℕ := Fintype.card (Fin (2 ^ (n - N)))
  let degBound := 2 ^ ((∑ j', (s j').1) - N) * d.1
  ((degBound : ℝ≥0) / (domSize : ℝ≥0)) ^ l

/-- Candidate total query consistency error, summing per-round query error
    over all `k + 1` rounds (including the final-polynomial check). -/
noncomputable def queryError : ℝ≥0 :=
  ∑ i : Fin (k + 1), queryRoundError k s d l (ω := ω) i

/-- Candidate total soundness error: sum of per-round proximity-gap errors
    (fold phase) plus query consistency errors (query phase). These are
    accounting definitions; a formal soundness theorem using them is deferred
    pending sequential composition infrastructure. -/
noncomputable def totalError (δ : ℝ≥0) : ℝ≥0 :=
  (∑ i : Fin k, roundError k s d (ω := ω) δ i) + queryError k s d l (ω := ω)

end Spec

end Fri
