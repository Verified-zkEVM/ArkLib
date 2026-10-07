/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Batching
public import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation
public import ArkLib.ProofSystem.RingSwitching.Packing.Multiplier
public import ArkLib.ProofSystem.RingSwitching.Packing.Relations
public import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky
public import ArkLib.ProofSystem.RingSwitching.Packing.Profile
public import ArkLib.ProofSystem.RingSwitching.Packing.General

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
  `RingSwitchingProfile` (`Profile.lean`), shared by every interactive relocation;
* the **relocation** is per-instance and depends on where the evaluation point lives. If the
  point is arbitrary in `L`, the claim is relocated *interactively*: the prover sends the
  folded carrier element `ŝ`, the verifier reconstructs the original claim from `ŝ`'s
  coordinates, collapses the `2^κ` coordinate claims with one random batching vector, and a
  dedicated degree-2 sumcheck moves the batched claim to a fresh random point that the
  downstream opening consumes (the protocol files of this folder; round-by-round knowledge
  soundness, `[IsDomain L]`). If the point is engineered to lie in a subring, the relocation
  degenerates to a *deterministic* one-message identity check. That trace head computes in
  `L` itself, so it needs its own algebraic interface rather than a `Profile` instance.

The *opposite-direction* `Lift` construction—from a large quotient ring down into a field—is
**not** a packing; it lives in the sibling folder `RingSwitching/Lift/`.

## Folder structure

The shared coordinate algebra imports no reduction framework. It holds over commutative rings,
except the Schwartz–Zippel batching strategies (finite domains) and the quirky layout (a field):

* `Coordinates.lean` — `PackingData`: independent finite bases of a packing algebra and an
  opening algebra over a common ring, the coordinate transpose, and the batching map `bridge`.
* `FiniteObservation.lean`, `CheckedObservation.lean` — weighted observations, their coordinate
  slices, and read-back of a scalar claim from an accepted honest message.
* `Polynomial.lean`, `Relations.lean` — packed multilinear polynomials with both round trips, and
  the opening, slice and batched-sumcheck relations.
* `Multiplier.lean` — the public multiplier evaluated by a read-once matrix program.
* `Batching.lean` — `BatchingStrategy`: uniform challenges with a proved collision bound.
* `ScalarHead/Layout.lean`, `ScalarHead/Quirky.lean` — prefix, suffix and quirky source
  layouts, each with a proved reconstruction identity.

The DP24 construction:

* `Profile.lean` — `RingSwitchingProfile`, the shared packing data layer (basis, carrier,
  embeddings, coordinate maps, reconstruction and inverse laws) and their consequences.
* `Algebra.lean` — the framework-independent packing algebra: `packMLE`/`unpackMLE`, the
  carrier operations, the verifier subroutines (`eqWeightedCoordSum`, the multiplier
  `compute_A_MLE`, the targets `compute_s0`/`compute_final_eq_value`) and the tensor-product
  constructor `tensorProductProfile`. Its component-wise carrier embedding is the `d = 1` case
  of the family-shared coefficient transport (`../Transport/Coeffs.lean`).
* `ProfileCoordinates.lean`, `ProfileLayout.lean`, `BatchingAlgebra.lean`,
  `FinalAlgebra.lean` — the profile's coordinate equivalences, the prefix layout of
  `packMLE`, and the batching/final verifier identities. The first three are stated through the
  finite-coordinate modules (`Coordinates`, `FiniteObservation`, `CheckedObservation`,
  `Relations`, `Polynomial`, `ScalarHead/Layout`, `Batching`). None of these imports the
  reduction framework.
* `Prelude.lean` — the protocol vocabulary: statement/witness types, the `MLIOPCS`
  downstream-opening interface, the relaxed and strict (honest) oracle compatibility of
  `AbstractOStmtIn`, and the sumcheck relations; re-exports `Algebra.lean`.
* `Compatibility.lean` — `AbstractOStmtIn.Functional`: an oracle statement is compatible with at
  most one packed polynomial. This is the binding hypothesis of the knowledge-soundness theorems.
* `Spec.lean` — the transcript shape: the batching round (message then scalar challenge),
  the sumcheck loop, and the final one-message round (the family-shared wire
  `pSpecMessage`), with their `OracleInterface`/`SampleableType` instances.
* `BatchingPhase.lean` — the relocation's first phase: send `ŝ`, check the original claim
  against its column decomposition (aborting on failure), batch the coordinate claims into one
  sumcheck target. The verifier is an instance of the family-shared `scalarRoundOracleVerifier`
  (`../RoundVerifiers.lean`). Perfect completeness and worst-case round-by-round knowledge
  soundness at error `κ/|L|` are proved; soundness assumes `AbstractOStmtIn.Functional`.
* `SumcheckPhase.lean` — the relocation sumcheck (`ℓ'` rounds, each aborting on a failed round
  check) and the final consistency step handing the residual evaluation claim `t'(r') = s'` to
  the downstream opening; the final verifier is an instance of the family-shared
  `messageRoundOracleVerifier` (`../RoundVerifiers.lean`). Per-round and final-step completeness
  and worst-case round-by-round knowledge soundness (`2/|L|` per round) are proved, and so are
  the composed completeness and the composed worst-case round-by-round knowledge soundness
  (`coreInteraction_rbrKnowledgeSoundnessWorstCase`, sorry-free and axiom-clean under its stated
  hypotheses), through the guarded worst-case composition theorems.
* `General.lean` — the composed reduction (batching ++ sumcheck ++ downstream opening). Perfect
  completeness at the strict relations is proved from the phases and the downstream opening's
  completeness. Worst-case round-by-round knowledge soundness of batching ++ sumcheck
  (`batchingCore_rbrKnowledgeSoundnessWorstCase`) is sorry-free and axiom-clean under its stated
  hypotheses (`[NoZeroDivisors L]`, `AbstractOStmtIn.Functional`). The full composite's
  round-by-round knowledge soundness depends on the admitted
  `OracleVerifier.append_rbrKnowledgeSoundness`, because the downstream opening's
  `MLIOPCS.rbrKnowledgeSoundness` contract is averaged; it loses that dependency once a worst-case
  extension of `MLIOPCS` supplies a worst-case contract.

## Instantiations

* **Binius** ([DP24] Construction 3.1) — `B`/`L` binary-tower fields, carrier
  `A = L ⊗[B] L`; instantiated by `ProofSystem/Binius/FRIBinius/`.

Hachi's §3 head ([NOZ26] Theorem 2) has carrier `A = L = R_q` and an automorphism `φ₁`. For
`κ > 0` and finite `R_q` it is not a profile instance (`RingSwitchingProfile.card_A`); its
deterministic trace check is planned against its own interface.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based
  Multilinear Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026).
-/

@[expose] public section
