/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import Mathlib.Algebra.Field.ZMod

/-!
# The Prime Power-of-Two Cyclotomic Ring `Z_q[X] / (X^{2^α} + 1)`

This file pins the cyclotomic modulus to the power-of-two cyclotomic polynomial
`X^{2^α} + 1` over the prime field `ZMod q`, and names the resulting ring.

This is the ring that underlies the Greyhound [NS24] / Hachi [NOZ26] / LaBRADOR-style
lattice constructions, and — more importantly for the algebraic development — it is the ring
in which Hachi [NOZ26, §3] identifies the finite field extensions `F_{q^k}` (via Galois
automorphisms, the trace map, and the packing map `ψ`). Those two consumers care about
*different* structure:

* the commitment-scheme security needs `q ≡ 5 (mod 8)` (Lyubashevsky–Seiler invertibility)
  and the power-of-two degree;
* the extension-field algebra (`CyclotomicRing/Galois/`, `CyclotomicRing/Subfield/`) needs the
  power-of-two degree `d = 2^α` so that the conductor `2d = 2^{α+1}` is a power of two, and
  `q` prime so that the fixed subring is a field.

The object lives here, in `Data/Lattices`, rather than next to any one consumer: it is pure
power-of-two cyclotomic ring theory over a prime field. The inner-outer commitment re-exports
it under the names `hachiModulus` / `HachiRing` (see
`ArkLib/CommitmentScheme/Ajtai/InnerOuter/Arithmetic.lean`).

Because `primePowTwoModulus` is *reducibly* equal to `powTwoCyclotomic α`, the
`powTwoCyclotomic`-stated lemmas and the `IsCyclotomic` instance apply transparently.

## Main definitions

* `primePowTwoModulus q α` — the modulus `X^{2^α} + 1` over `ZMod q`.
* `PrimePowTwoRing q α` — the ring `Z_q[X] / (X^{2^α} + 1)`, a computable `CommRing`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open Polynomial CompPoly CompPoly.CPolynomial ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices

variable (q : ℕ) [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] (α : ℕ)

/-- The **prime power-of-two cyclotomic modulus** `X^{2^α} + 1` over `ZMod q` (the `2^{α+1}`-th
cyclotomic polynomial). Kept `@[reducible]` so the `IsCyclotomic` instance and the
`powTwoCyclotomic`-stated deep lemmas apply transparently. -/
@[reducible] def primePowTwoModulus : CyclotomicModulus (ZMod q) := powTwoCyclotomic α

/-- The **prime power-of-two cyclotomic ring** `R_q = Z_q[X] / (X^{2^α} + 1)`, the degree-`2^α`
power-of-two cyclotomic ring over `ZMod q`. It is a computable `CommRing`, inherited from `Rq`.
This is the ring in which Hachi [NOZ26, §3] embeds the extension fields `F_{q^k}`. -/
@[reducible] def PrimePowTwoRing : Type := Rq (primePowTwoModulus q α)

/-- The prime power-of-two modulus `X^{2^α} + 1` has degree `2^α`
(a `ZMod q` specialization of `powTwoCyclotomic_natDegree`). -/
@[simp] theorem primePowTwoModulus_natDegree : (primePowTwoModulus q α).φ.natDegree = 2 ^ α :=
  powTwoCyclotomic_natDegree α

/-- The prime power-of-two modulus has conductor `2^{α+1}`. -/
@[simp] theorem primePowTwoModulus_conductor : (primePowTwoModulus q α).conductor = 2 ^ (α + 1) :=
  rfl

end ArkLib.Lattices
