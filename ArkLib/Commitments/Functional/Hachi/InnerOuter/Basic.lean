/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Correctness
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security

/-!
# Inner-Outer Ajtai Commitment

Umbrella module for `Hachi/InnerOuter/`: the Greyhound [NS24] / Hachi [NOZ26] two-layer Ajtai
commitment over the cyclotomic ring `Rq Φ` (Hachi [NOZ26, §4.1]). Each message block is
gadget-decomposed and inner-committed under the matrix `A`; the inner commitments are
gadget-decomposed again, flattened, and outer-committed under `B`. The scheme's opening notion
is Hachi's *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`, whose per-block challenges `cᵢ` only ever arise
during knowledge extraction (the honest committer uses `cᵢ = 1`).

## Folder structure

* `InnerOuter/Scheme.lean` — the scheme itself: public parameters, the committer data
  `Decomp` and its challenge extension `Opening`, honest commitment (`generateDecomps` /
  `commitWithDecomps`), the weak verifier `verify_weak`, and the bundled `commitmentScheme`.
* `InnerOuter/Correctness.lean` — perfect correctness for lawful gadget decompositions,
  unconditional for the genuine base-`b` digit decomposition (`perfectlyCorrect`).
* `InnerOuter/Security.lean` — weak binding: two differing verified weak openings yield a
  Module-SIS solution for the inner matrix `A` or the outer matrix `B`
  (`outputToModuleSIS_valid`, `advantage_le_moduleSIS`).
* `InnerOuter/Arithmetic.lean` — pins the ring to the power-of-two cyclotomic
  `Z_q[X] / (X^{2^α} + 1)` (`hachiModulus` / `HachiRing`, scoped notation `𝓜(q, α)` /
  `𝓡⟦q, α⟧`), which the security statements genuinely require.

This umbrella re-exports the scheme, its perfect correctness, and its weak-binding reduction to
Module-SIS (`Correctness` + `Security`, which transitively import `Scheme` and `Arithmetic`).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
