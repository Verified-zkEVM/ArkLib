/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction

/-!
# Hachi Ring-Switching Lift (Figure 4 / Lemma 9)

Umbrella module for `Hachi/RingSwitch/`: the entry of Hachi's [NOZ26, §4.3] sumcheck-based
opening — the
Huang–Mao–Zhang [HMZ25] ring-switching lift. Following [HMZ25], `M z = y` over the cyclotomic
ring `Rq` holds **iff** there is a quotient `r` with `M z = y + (Xᵈ + 1)·r` over `Zq[X]`; the
prover commits to the lifted witness `(z, r)` and both sides evaluate the lifted rows at a random
`X := α ∈ F` (an extension field `F ⊇ Zq`). This "switches" the R_q-statement into the extension
field where the sumcheck runs. (This is the §4.3 lift; the *separate* §3 F_{q^k}↔R_q packing
reduction — also a ring-switching idea — lives under `ArkLib/ProofSystem/RingSwitching/`.)

## Folder structure

* `RingSwitch/Rlin.lean` — the zero-round **entry adapter**: reinterprets `QuadEval`'s Eq. (20)
  output (`relOut`) as the unstructured linear relation `R^lin` (`relRlin`), the input the lift
  addresses. The package carries the parallel escape set unchanged. Statement reshaping only
  (`ReduceClaim`), so it is CWSS for any structure; the sorried pieces are the block-matrix
  assembly/unstacking and the block-row equivalence pull-back.
* `RingSwitch/Reduction.lean` — **Hachi Figure 4 / Lemma 9**: the two-round lift (commit
  `t := Com(w̃)`; sample `α ← F`; evaluate the lifted rows at `α`), the abstract weak-binding
  commitment `LiftCom`, the output relation `relLift`, and the plain-special-sound CWSS theorem
  `lift_coordinateWiseSpecialSound` at `k = 2d` (**sorried**: Lemma 9's interpolation extraction).

This umbrella re-exports the folder (`Reduction` transitively imports `Rlin`). The plain
`relLift` is the input of the batching bridge in `ZeroCheck/`; the chain is composed in
`Composition.lean`.

## References

* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
