/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.PowTwo
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# The Inner-Outer Commitment/Hachi Ring `Z_q[X] / (X^{2^α} + 1)`

This file fixes the cyclotomic ring over which the **inner-outer Ajtai commitment** operates.
That commitment — the Greyhound [NS24] / Hachi [NOZ26] construction — works specifically over
the power-of-two cyclotomic ring `R_q := Z_q[X] / (X^{2^α} + 1)`.

The ring itself now lives in `Data/Lattices` as `primePowTwoModulus` / `PrimePowTwoRing` (see
`ArkLib/Data/Lattices/CyclotomicRing/PowTwo.lean`), since it is pure cyclotomic ring theory and
is shared with the extension-field algebra of Hachi [NOZ26, §3]. This file just re-exports it
under the commitment-facing names `hachiModulus` / `HachiRing` and installs the scoped notation,
so the inner-outer correctness/security files are unaffected.

The weak-binding *security* of the scheme genuinely needs this ring: its two deep analytic
inputs — Lyubashevsky–Seiler short-element invertibility (`isUnit_of_l1Norm_le`) and the
Micciancio/Young product norm bound (`scalarVecMul_mul_l2NormSq_le`) — hold only over
`X^{2^α} + 1`. Because `hachiModulus` is *reducibly* equal to `powTwoCyclotomic α`, those
`powTwoCyclotomic`-stated lemmas apply to `HachiRing q α` directly.

## Main definitions

* `hachiModulus q α` — the inner-outer commitment modulus `X^{2^α} + 1` over `ZMod q`
  (a re-export of `primePowTwoModulus`).
* `HachiRing q α` — the inner-outer commitment ring `Z_q[X] / (X^{2^α} + 1)`
  (a re-export of `PrimePowTwoRing`).

## Notation

* `𝓡⟦q, α⟧` (scoped, in `ArkLib.Lattices.Ajtai.InnerOuter`) — the ring `HachiRing q α`.
* `𝓜(q, α)` (scoped, in `ArkLib.Lattices.Ajtai.InnerOuter`) — the modulus `hachiModulus q α`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The **inner-outer commitment modulus** `X^{2^α} + 1` over `ZMod q`. A re-export of
`primePowTwoModulus`; kept `@[reducible]` so the `IsCyclotomic` instance and the
`powTwoCyclotomic`-stated deep lemmas apply to it transparently. -/
@[reducible] def hachiModulus : CyclotomicModulus (ZMod q) := primePowTwoModulus q α

@[inherit_doc] scoped notation:max "𝓜(" q ", " α ")" => hachiModulus q α

/-- The **inner-outer commitment ring** `R_q = Z_q[X] / (X^{2^α} + 1)`. A re-export of
`PrimePowTwoRing`; a computable `CommRing` inherited from `Rq`. -/
@[reducible] def HachiRing : Type := PrimePowTwoRing q α

@[inherit_doc] scoped notation:max "𝓡⟦" q ", " α "⟧" => HachiRing q α

/-- The inner-outer commitment modulus `X^{2^α} + 1` has degree `2^α`. -/
@[simp] theorem hachiModulus_natDegree : (hachiModulus q α).φ.natDegree = 2 ^ α :=
  primePowTwoModulus_natDegree q α

/-- The inner-outer commitment modulus has conductor `2^{α+1}`. -/
@[simp] theorem hachiModulus_conductor : (hachiModulus q α).conductor = 2 ^ (α + 1) := rfl

end ArkLib.Lattices.Ajtai.InnerOuter
