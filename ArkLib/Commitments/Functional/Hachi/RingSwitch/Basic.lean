/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Completeness

/-!
# Hachi's `Lift` instance (Figure 4 / Lemma 9)

Umbrella module for `Hachi/RingSwitch/`: the entry of Hachi's [NOZ26, §4.3] sumcheck-based
opening — the
Huang–Mao–Zhang [HMZ25] ring-switching lift. Following [HMZ25], `M z = y` over the cyclotomic
ring `Rq` holds **iff** there is a quotient `r` with `M z = y + (Xᵈ + 1)·r` over `Zq[X]`; the
prover commits to the lifted witness `(z, r)` and both sides evaluate the lifted rows at a random
`X := α ∈ F` (an extension field `F ⊇ Zq`). This "switches" the R_q-statement into the extension
field where the sumcheck runs. (This is the §4.3 lift, the cyclotomic instance of
`ProofSystem/RingSwitching/Lift/`; the *separate* §3 F_{q^k}↔R_q packing reduction —
also a ring-switching idea — is planned as a `RingSwitchingProfile` instance under
`ProofSystem/RingSwitching/Packing/`; see `ProofSystem/RingSwitching/Basic.lean` for the
family taxonomy.)

The name **Lift** is algebraic: the quotient-ring equation is lifted from equality modulo
`Xᵈ + 1` to an exact polynomial equation by supplying `r`; only then is it evaluated in `F`.
By contrast, **Packing** groups a basis-sized block of small-field coefficients into one
`R_q` element. The two names expose the distinct operations hidden by the broader phrase
“ring switching.”

## Folder structure

* `RingSwitch/Rlin.lean` — the zero-round **entry adapter**: reinterprets `QuadEval`'s Eq. (20)
  output (`relOut`) as the unstructured linear relation `R^lin` (`relRlin`), the input the lift
  addresses. Statement reshaping only
  (`ReduceClaim`), so it is CWSS for any structure; the block-matrix assembly/unstacking and
  the block-row equivalence are proven — **sorry-free**.
* `RingSwitch/Reduction.lean` — **Hachi Figure 4 / Lemma 9**: the two-round lift (commit
  `t := Com(w̃)`; sample `α ← F`; evaluate the lifted rows at `α`), the abstract weak-binding
  commitment `LiftCom` with its short-collision set `LiftCom.Collision`, the output relation
  `relLift`, the weak-binding escape event (`CommittedScalar.escEvent`), and the composable
  escape-aware CWSS package
  `liftPackage` at `k = 2d` (certificate `liftPackage.isCWSS`) — **proven, sorry-free and
  axiom-clean**. It is the **cyclotomic instance** of generic `Lift`
  (`ProofSystem/RingSwitching/Lift/` — presentation data + laws, `checkAt`, the
  interpolation/descent engine, and the CWSS protocol shell): `liftPackage` is assembled
  wholesale from generic `Lift.package`. The
  `IsPresentation` law-discharge lemmas live in
  `Data/Lattices/CyclotomicRing/QuotientLift.lean`. Hachi keeps only its norms, its
  statement's bound convention, the commitment interface, and the norm implication
  `vecLInftyNorm_le_of_liftShort`.

* `RingSwitch/Completeness.lean` — the **honest direction of both links**: the protocol objects
  `rlinReduction` / `liftReduction` (each sharing its package's verifier, by `rfl`) and
  `rlinReduction_perfectCompleteness` / `liftReduction_perfectCompleteness`, both at error `0` and
  both `sorry`-free and axiom-clean. Like the soundness side they are instantiations: the honest
  quotient witness, the check-at-every-challenge step and the two-round execution are generic
  (`RingSwitching.Lift.honestWitness` / `…checkAt_honestWitness` /
  `…reduction_perfectCompleteness`, over
  `CoordinateWise.CommittedScalar.reduction_perfectCompleteness`).
  The lift's completeness carries two explicit honest-side hypotheses — the statement bound
  convention and admissibility (`liftShort`) of the honest lifted witness, i.e. Figure 4's range
  checks; see that file's docstring.

This umbrella re-exports the folder (`Completeness` transitively imports `Reduction`, which imports
`Rlin`). The plain `relLift` is the input of the batching bridge in `ZeroCheck/`; the chain is
composed in `Composition.lean`.

## References

* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
