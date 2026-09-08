/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.MvPolynomial.Split
import ArkLib.ProofSystem.RingSwitching.Packing.Polynomial

/-!
# Scalar claims and concrete packing layouts

DP24 packs the first Boolean block and retains the second. Flock Appendix B packs the final
Boolean block and retains the first. Both scalar evaluations reconstruct from partial evaluations
at the retained point. The layout records a proved reconstruction identity and the bijective
component decomposition, so a protocol head keeps the original scalar relation as its input.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
-/

noncomputable section

namespace RingSwitching.Packing.ScalarHead

open MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)

/-- A scalar evaluation with an invertible component layout and weighted reconstruction. -/
structure ClaimLayout where
  /-- Source objects whose scalar evaluations are claimed. -/
  Source : Type
  /-- Queries specifying the source evaluation. -/
  Query : Type
  /-- Invertible decomposition into base-ring multilinear components. -/
  components : Source ≃ (data.ιP → B⦃≤ 1⦄[X Fin m])
  /-- Evaluation point for the retained variables. -/
  point : Query → Fin m → data.E
  /-- Reconstruction weight for each packing coordinate. -/
  weight : Query → data.ιP → data.E
  /-- The source scalar evaluation. -/
  eval : Query → Source → data.E
  /-- The weighted component evaluations reconstruct the source evaluation. -/
  reconstruct : ∀ q p, eval q p =
    ∑ i, weight q i * MvPolynomial.aeval (point q) (components p i).val

/--
Pack the prefix coordinates and retain the suffix, with an explicit basis-index
identification.
-/
def packedPrefixLayout (k : ℕ) (index : data.ιP ≃ (Fin k → Fin 2)) : ClaimLayout data m where
  Source := B⦃≤ 1⦄[X Fin (k + m)]
  Query := (Fin k → data.E) × (Fin m → data.E)
  components := (splitFirstEquiv k m).trans (Equiv.arrowCongr index.symm (Equiv.refl _))
  point q := q.2
  weight q i := eqTilde ((index i) : Fin k → data.E) q.1
  eval q p := aeval (Fin.append q.1 q.2) p.val
  reconstruct q p := by
    rw [aeval_append_splitFirst]
    exact (index.sum_comp _).symm

/--
Retain the prefix coordinates and pack the suffix, with an explicit basis-index
identification.
-/
def packedSuffixLayout (k : ℕ) (index : data.ιP ≃ (Fin k → Fin 2)) : ClaimLayout data m where
  Source := B⦃≤ 1⦄[X Fin (m + k)]
  Query := (Fin m → data.E) × (Fin k → data.E)
  components := (splitLastEquiv k m).trans (Equiv.arrowCongr index.symm (Equiv.refl _))
  point q := q.1
  weight q i := eqTilde ((index i) : Fin k → data.E) q.2
  eval q p := aeval (Fin.append q.1 q.2) p.val
  reconstruct q p := by
    rw [aeval_append_splitLast]
    exact (index.sum_comp _).symm

end RingSwitching.Packing.ScalarHead

end
