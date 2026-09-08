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

* [DP24] Diamond, Benjamin E. and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive, Report 2024/504. Construction 3.1.
* [BRW26] Bünz, Benedikt, Ron Rothblum, and William Wang. "Flock: Fast Proving for Batch
  Boolean Computations." Cryptology ePrint Archive, Report 2026/1329. Appendix B.1–B.3.
-/

noncomputable section

namespace RingSwitching.Packing.ScalarHead

open MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)

/-- A scalar evaluation with a lossless component layout and a proved weighted reconstruction. -/
structure ClaimLayout where
  Source : Type
  Query : Type
  components : Source ≃ (data.ιP → B⦃≤ 1⦄[X Fin m])
  point : Query → Fin m → data.E
  weight : Query → data.ιP → data.E
  eval : Query → Source → data.E
  reconstruct : ∀ q p, eval q p =
    ∑ i, weight q i * MvPolynomial.aeval (point q) (components p i).val

/-- DP24's packed prefix and retained suffix, with an explicit basis-index identification. -/
def dp24Layout (k : ℕ) (index : data.ιP ≃ (Fin k → Fin 2)) : ClaimLayout data m where
  Source := B⦃≤ 1⦄[X Fin (k + m)]
  Query := (Fin k → data.E) × (Fin m → data.E)
  components := (splitFirstEquiv k m).trans (Equiv.arrowCongr index.symm (Equiv.refl _))
  point q := q.2
  weight q i := eqTilde ((index i) : Fin k → data.E) q.1
  eval q p := aeval (Fin.append q.1 q.2) p.val
  reconstruct q p := by
    rw [aeval_append_splitFirst]
    exact (index.sum_comp _).symm

/-- Flock's retained prefix and packed suffix, matching Appendix B.1 and Equation (5). -/
def flockLayout (k : ℕ) (index : data.ιP ≃ (Fin k → Fin 2)) : ClaimLayout data m where
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
