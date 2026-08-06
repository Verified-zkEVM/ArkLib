/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Profile
import ArkLib.ProofSystem.RingSwitching.Packing.General

/-!
# `Packing`: packing small-ring coordinates into large-ring elements

Umbrella for `RingSwitching/Packing/`: the ring switches that move an evaluation claim
from a small ring to a large one **by packing**. When the large ring `L` is free of rank
`2^κ` over the small ring `B`, a `B`-basis identifies each block of `2^κ` coefficients of a
`B`-multilinear `t` with a single `L`-element: an `ℓ`-variate multilinear over `B` *is* an
`(ℓ − κ)`-variate multilinear `t' = packMLE t` over `L`. A claim `t(r) = s` therefore has an
equivalent formulation in terms of `t'` — and a commitment made cheaply over `B` can be
opened by a protocol that runs entirely over `L`.

The family is called **Packing** because one basis-sized block of `2^κ` small-ring
coefficients is encoded as one large-ring coefficient. Thus `κ` Boolean variables worth of
coefficient positions are packed into the coordinates of a single element of `L`; “tensor”
describes one useful realization of the carrier algebra, but is not the essential operation.

The equivalence is not free: the original claim constrains `t'` through the basis
coordinates, so the reduction must *relocate* the claim onto `t'` at some point the
large-ring opening can handle. Two ingredients separate cleanly:

* the **packing data** — the basis, a carrier ring `A` where the relocation checks run, a
  pair of embeddings into it, and faithful coordinate maps back out — is one abstraction,
  `RingSwitchingProfile` (`Profile.lean`), shared by every instance;
* the **relocation** is per-instance and depends on where the evaluation point lives. If the
  point is arbitrary in `L`, the claim is relocated *interactively*: the prover sends the
  folded carrier element `ŝ`, the verifier reconstructs the original claim from `ŝ`'s
  coordinates, collapses the `2^κ` coordinate claims with one random batching vector, and a
  dedicated degree-2 sumcheck moves the batched claim to a fresh random point that the
  downstream opening consumes (the protocol files of this folder; round-by-round knowledge
  soundness, `[IsDomain L]`). If the point is engineered to lie in a subring, the relocation
  degenerates to a *deterministic* one-message identity check — a planned second `Profile`
  instance with none of the interaction.

The *opposite-direction* `Lift` construction—from a large quotient ring down into a field—is
**not** a packing; it lives in the sibling folder `RingSwitching/Lift/`.

## Folder structure

* `Profile.lean` — `RingSwitchingProfile`, the shared packing data layer (basis, carrier,
  embeddings, coordinate maps, reconstruction laws).
* `Prelude.lean` — the packing algebra and protocol vocabulary: `packMLE`/`unpackMLE`, the
  carrier operations, the verifier's coordinate subroutine `eqWeightedCoordSum`, statement/
  witness types, the `MLIOPCS` downstream-opening interface, and the binary-tower instance
  `binaryTowerProfile`. Its component-wise carrier embedding is the `d = 1` case of the
  family-shared coefficient transport (`../Transport/Coeffs.lean`).
* `Spec.lean` — the transcript shape: the batching round (message then scalar challenge),
  the sumcheck loop, and the final one-message round (the family-shared wire
  `pSpecMessage`), with their `OracleInterface`/`SampleableType` instances.
* `BatchingPhase.lean` — the relocation's first phase: send `ŝ`, check the original claim
  against its column decomposition, batch the coordinate claims into one sumcheck target.
  The verifier is an instance of the family-shared `scalarRoundOracleVerifier`
  (`../RoundVerifiers.lean`).
* `SumcheckPhase.lean` — the relocation sumcheck (`ℓ'` rounds) and the final consistency
  step handing the residual evaluation claim to the downstream opening; its verifier is an
  instance of the family-shared `messageRoundOracleVerifier` (`../RoundVerifiers.lean`).
* `General.lean` — the composed reduction (batching ++ sumcheck ++ downstream opening),
  perfect completeness, and the round-by-round knowledge-soundness statement
  (`[IsDomain L]`; leaf proofs still open).

## Instantiations

* **Binius** ([DP24] Construction 3.1) — `B`/`L` binary-tower fields, carrier
  `A = L ⊗[B] L`; instantiated by `ProofSystem/Binius/FRIBinius/`.
* **Hachi §3 head** ([NOZ26] Theorem 2, planned) — subfield-valued evaluation point,
  `A = L = R_q`, `φ₁` an automorphism; deterministic one-message trace check.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based
  Multilinear Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026).
-/
