/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Core.Modulus
import ArkLib.Data.Lattices.CyclotomicRing.Core.Basic

/-!
# Foundational Construction of the Cyclotomic Ring `R_q = Z_q[X] / (φ)`

Aggregator for the *low-level construction* layer of the cyclotomic ring — the modulus data and
the semantic quotient it is built from:

* `Core/Modulus.lean` — the `CyclotomicModulus` data (`φ`, conductor) and `powTwoCyclotomic α`.
* `Core/Basic.lean` — the semantic quotient `R[X]/(φ)`, the computable `reduce`/`mul`, and the
  soundness bridge `quotientHom`.

The canonical reduced-representative ring `Rq` and its power-of-two prime specialization are built
on top of this layer and live one level up, at
`ArkLib.Data.Lattices.CyclotomicRing.Rq` and `ArkLib.Data.Lattices.CyclotomicRing.PowTwo`.

## References

* [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs*][LNP22]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
