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

* `RingSwitch/ComputableWitness.lean` — the computable twin `honestLiftWitnessC` of the honest
  lifted witness, at the same signature and equal to it (`honestLiftWitnessC_eq_honestWitness`).
  It replaces Mathlib's `/ₘ` by CompPoly's synthetic division `CPolynomial.divByMonic` on the
  canonical coefficient arrays, which is what makes the whole honest path executable
  (`Hachi/Concrete.lean`, `scripts/HachiRuntime.lean`); `Completeness.lean` re-points
  `liftReduction` at it and transfers completeness through the agreement lemma.
* `RingSwitch/QuotientNorms.lean` — centered coefficient bounds for the honest lift quotient. For
  `φ = X^d + 1` division by the modulus *selects* coefficients
  (`Polynomial.coeff_divByMonic_X_pow_add_one`), so the quotient bound is a row-sum coefficient
  bound: `μ · 2d · βM · βz` from explicit matrix/witness bounds, with **no wraparound hypothesis**
  (centered representatives are minimal among integer representatives). Also the unconditional
  fallback `rhoShort_half` (`RhoShort (q/2)` always), which is what the Hachi chain uses — see its
  docstring for why nothing sharper is available when the `R^lin` matrix carries the Ajtai key.
* `RingSwitch/Completeness.lean` — the **honest direction of both links**, proven and axiom-clean:
  `rlinReduction_perfectCompleteness_image` (into the honest seam `relRlinImage`, unconditional)
  with `rlinReduction_perfectCompleteness` as its coarsening to `relRlin`, and
  `liftReduction_perfectCompleteness_image` — **unconditional** perfect completeness of the lift at
  `bound = γ`, `ρBound = q/2`, error `0`: both halves of `liftShort` are discharged (the `z` half
  from seam membership, the quotient half from `QuotientNorms`), so no `hshort` and no `hbound`
  remain. `…_of_zShort` / `…_of_matrixShort` are the parameterized forms, the latter at the sharp
  quotient bound. Both protocol objects share their package's verifier by `rfl`. The lift consumes
  `relRlinImage`, not `relRlin`: the honest side needs the Eq. (20) provenance that the soundness
  relation deliberately discards (see `relRlinImage`). The execution and algebra are generic
  (`RingSwitching.Lift.honestWitness` / `checkAt_honestWitness` /
  `reduction_perfectCompleteness_of_relIn`, over
  `CoordinateWise.CommittedScalar.reduction_perfectCompleteness`).

This umbrella re-exports the folder (`Completeness` imports `ComputableWitness` and
`QuotientNorms`, both of which import `Reduction`, which imports `Rlin`). The plain `relLift` is
the input of the batching bridge in `ZeroCheck/`; the chain is composed in `Composition.lean`, and
the honest side's parameter bookkeeping in `HonestChain.lean`.

## References

* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
