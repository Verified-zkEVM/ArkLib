/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.Basic
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.MicciancioYoung
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds.LyubashevskySeiler

/-!
# Norm-Growth Bounds And Short-Element Invertibility For `Rq Φ`

Umbrella re-export of the centered `ZMod q` norms on the cyclotomic ring `Rq Φ` and the
three norm/invertibility facts the Greyhound [NS24] / Hachi [NOZ26] weak-binding argument
relies on:

* `NormBounds.Basic` — the centered `ℓ₁`/`ℓ₂²` norms, the bound expressions
  (`subL2NormSqBound`, `scalarVecMulMulL2NormSqBound`), and the proven subtraction bound
  `sub_l2NormSq_le`.
* `NormBounds.MicciancioYoung` — the proved product bounds `scalarVecMul_mul_l2NormSq_le`
  (`ℓ₂²`) and `Rq.lInftyNorm_mul_le` (`ℓ∞`, [Mic07, ineq. (2.7)]), the latter packaged as
  `powTwoCyclotomic_hasMulLInftyBound : Rq.HasMulLInftyBound (powTwoCyclotomic α)`. `ℓ∞` product
  growth is what bounds Hachi's folded witness `z = Σᵢ cᵢ sᵢ` deterministically, and hence what
  lets its digit count be chosen below `⌈log_b q⌉`; both bounds are pinned to the negacyclic
  modulus, where multiplication by `X` permutes coefficients up to sign.
* `NormBounds.LyubashevskySeiler` — short-element invertibility `isUnit_of_l1Norm_le`
  (proved).

## References

* [Micciancio, D., *Generalized Compact Knapsacks, Cyclic Lattices, and Efficient One-Way
    Functions*][Mic07]
* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
