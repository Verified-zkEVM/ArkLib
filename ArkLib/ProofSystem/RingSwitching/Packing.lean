/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Batching.CoordinateSample
public import ArkLib.ProofSystem.RingSwitching.Packing.CheckedObservation
public import ArkLib.ProofSystem.RingSwitching.Packing.ClaimLayout.Quirky
public import ArkLib.ProofSystem.RingSwitching.Packing.Conformance
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.RingSwitching.Packing.Profile
public import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch

/-!
# Packing-based ring switching

Let `P` and `E` be finite free algebras over a common commutative ring `B`. A packing basis
identifies a component family `(pᵢ)` with one polynomial `p = ∑ᵢ βᵢ pᵢ` over `P`. An independent
basis of `E` transports a scalar evaluation query into coordinates. Neither rank must be a power
of two, and the ranks need not agree.

A scalar layout reconstructs its source evaluation as `∑ᵢ λᵢ(q) pᵢ(x(q))`. The shared head sends
these component values through a specified carrier encoding, checks reconstruction, then samples
batching weights. A public coordinate transpose derives the product-sumcheck target. Product
sumcheck and a matrix-evaluated terminal check reduce it to an evaluation of the same polynomial
against the same commitment oracle collection. The original query remains in the public context.

## Interfaces

* `PackingData` (`Coordinates.lean`) supplies independent packing and opening bases. The pure
  coordinate, polynomial and observation layers require no reduction framework.
* `ClaimLayout` (`ClaimLayout.lean`) supplies an invertible component decomposition and scalar
  reconstruction. Prefix, suffix and quirky layouts are provided; the quirky layout requires a
  field for its interpolation nodes.
* `BatchingRule` (`Batching.lean`) supplies sampled challenges and weights. `BatchingStrategy` adds
  a collision bound. Power and equality-fold certificates require no zero divisors; coordinate
  sampling works over arbitrary commutative rings. Fixed-list bounds charge only wrong families.
* `PackedCommitment` supplies oracle compatibility. `PackedCommitment.Honest` separately supplies
  honest coverage; `Functional` is an explicit binding hypothesis.
* `Head.lean` gives the scalar guard, derived target, source extractor and head security. Its
  endpoint is directly the initial `ProductSumcheck.rel`, without a formatting phase.
* `ProductSumcheck/` gives degree-two scalar rounds and the terminal same-commitment evaluation
  relation. A certified `Multiplier` separates its polynomial from its executable point evaluator.
* `RingSwitch.lean` composes the shared head and product sumcheck. Completeness holds over
  commutative rings. Round-by-round knowledge soundness additionally requires a finite
  challenge ring with no zero divisors, functional compatibility and injective transport `P → C`.
  Its exact challenge-error sum is `bat.error + m * (2 / card C)`.

## Consumers

`TensorPrefix.lean` defines prefix ring switching through the shared protocol, retaining the
original carrier `P.A` and equality-fold challenges. `Binius/FRIBinius/RingSwitch.lean` composes
it with the Binary Basefold opening. Exact first encodings give completeness;
compatibility within the unique decoding radius gives round-by-round security.

The maintained `ArkLibTest/.../Packing/RingSwitch/` examples instantiate independent F₁₆/F₈
algebras with suffix and quirky layouts. Their transparent polynomial oracle is specification
data rather than a succinct commitment scheme. A native consumer must provide its
  commitment/opening interface and prove the transport of any additional source invariant.
Fixed candidate lists certify the head-only bound; they do not supply list-valued tail security.

Hachi's deterministic trace head uses the coordinate and claim-layout layers through its own trace
check. It does not need this interactive head or product sumcheck. The opposite-direction `Lift`
construction lives separately in `RingSwitching/Lift/`.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section
