/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# The Inner-Outer Commitment/Hachi Ring `Z_q[X] / (X^{2^α} + 1)`

This file fixes the cyclotomic ring over which the **inner-outer Ajtai commitment** operates.
That commitment — the Greyhound [NS24] / Hachi [NOZ26] construction — works specifically over
the power-of-two cyclotomic ring

`R_q := Z_q[X] / (X^{2^α} + 1)`,

the degree-`d = 2^α` cyclotomic ring over the prime field `ZMod q`. Unlike the generic
inner-outer *definitions* (which are polymorphic over an arbitrary cyclotomic modulus `Φ`), the
weak-binding *security* of the scheme genuinely needs this ring: its two deep analytic inputs —
Lyubashevsky–Seiler short-element invertibility (`isUnit_of_l1Norm_le`) and the Micciancio/Young
product norm bound (`scalarVecMul_mul_l2NormSq_le`) — hold only over `X^{2^α} + 1` (they fail
for general cyclotomics). Keeping the ring in one place avoids re-deriving the modulus inside
`InnerOuter/Correctness.lean` and `InnerOuter/Security.lean`.

This file pins the modulus to `X^{2^α} + 1` (`hachiModulus`), names the resulting ring
(`HachiRing`), and records its basic arithmetic: it is a computable `CommRing` (inherited from
`Rq`), its modulus is monic and genuinely cyclotomic (the `IsCyclotomic` instance, inherited
from `powTwoCyclotomic`), it has conductor `2^{α+1}`, and its degree is `2^α`
(`hachiModulus_natDegree`). Because `hachiModulus` is *reducibly* equal to `powTwoCyclotomic α`,
the `powTwoCyclotomic`-stated deep lemmas apply to `HachiRing q α` directly.

## Main definitions

* `hachiModulus q α` — the inner-outer commitment modulus `X^{2^α} + 1` over `ZMod q`.
* `HachiRing q α` — the inner-outer commitment ring `Z_q[X] / (X^{2^α} + 1)`.

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

open ArkLib.Lattices.CyclotomicModulus CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The **inner-outer commitment modulus** `X^{2^α} + 1` over `ZMod q` (the `2^{α+1}`-th
cyclotomic polynomial), as used by the Greyhound [NS24] / Hachi [NOZ26] / LaBRADOR-style
schemes. This is `powTwoCyclotomic α`; kept `@[reducible]` so the `IsCyclotomic` instance and
the `powTwoCyclotomic`-stated deep lemmas (`isUnit_of_l1Norm_le`,
`scalarVecMul_mul_l2NormSq_le`) apply to it transparently. -/
@[reducible] def hachiModulus : CyclotomicModulus (ZMod q) := powTwoCyclotomic α

@[inherit_doc] scoped notation:max "𝓜(" q ", " α ")" => hachiModulus q α

/-- The **inner-outer commitment ring** `R_q = Z_q[X] / (X^{2^α} + 1)`, the degree-`2^α`
power-of-two cyclotomic ring over `ZMod q` underlying the Greyhound [NS24] / Hachi [NOZ26]
(LaBRADOR-style) commitment. It is a computable `CommRing`, inherited from `Rq`. -/
@[reducible] def HachiRing : Type := Rq (hachiModulus q α)

@[inherit_doc] scoped notation:max "𝓡⟦" q ", " α "⟧" => HachiRing q α

/-- The inner-outer commitment modulus `X^{2^α} + 1` has degree `2^α`. -/
@[simp] theorem hachiModulus_natDegree : (hachiModulus q α).φ.natDegree = 2 ^ α := by
  have h : (hachiModulus q α).φ.toPoly = Polynomial.X ^ (2 ^ α) + 1 := by
    change (CPolynomial.X ^ (2 ^ α) + 1 : CPolynomial (ZMod q)).toPoly = _
    rw [toPoly_add, toPoly_pow, toPoly_X, toPoly_one]
  rw [CompPoly.CPolynomial.natDegree_toPoly, h]
  compute_degree!

/-- The inner-outer commitment modulus has conductor `2^{α+1}`. -/
@[simp] theorem hachiModulus_conductor : (hachiModulus q α).conductor = 2 ^ (α + 1) := rfl

end ArkLib.Lattices.Ajtai.InnerOuter
