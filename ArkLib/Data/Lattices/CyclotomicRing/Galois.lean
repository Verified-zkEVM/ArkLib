/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Automorphism
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Order
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Group
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Trace
import ArkLib.Data.Lattices.CyclotomicRing.Galois.FixedSubring

/-!
# Galois Theory of the Power-of-Two Cyclotomic Ring

Aggregator for the Galois-automorphism layer of `R_q = Z_q[X] / (X^{2^α} + 1)`, the algebraic
foundation for the extension-field embedding of Hachi [NOZ26, §3]:

* `Galois/Automorphism.lean` — the automorphisms `σ_i : X ↦ X^i` (computable + semantic).
* `Galois/Group.lean` — the group law, the generators `σ_{-1}`, `σ_{4k+1}`, and `H`.
* `Galois/Trace.lean` — the trace map `Tr_H`.
* `Galois/FixedSubring.lean` — the fixed subring `R_q^H`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
