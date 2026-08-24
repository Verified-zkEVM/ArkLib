/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Lift.Presentation
import ArkLib.ProofSystem.RingSwitching.Lift.Reduction

/-!
# `Lift`: lifting quotient-ring claims to field evaluations

Umbrella for `RingSwitching/Lift/`: the ring switch that moves a linear claim from a
large quotient ring **down into a field**, by lifting and evaluating. When a ring `S` is
*presented* as `R[X]/(φ)` for a monic modulus `φ`, every row of a linear claim `M z = y`
over `S` is equivalent to an `R[X]` identity carrying one explicit quotient polynomial:

  `(M *ᵥ z) i = y i  in S    ↔    ∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) = rep(yᵢ) + φ·ρᵢ  in R[X]`

The family is called **Lift** because the right-hand identity lifts an equality in the
quotient `S`—where equality only holds modulo `φ`—to an exact equality in `R[X]`. The extra
quotient witness `ρ` records the multiple of `φ` that disappears in `S`. Evaluation then
transports that lifted polynomial identity into the field; evaluation is the check performed
after the lift, not the defining operation named by the module.

The switch has the prover commit to the **lifted witness** `(z, ρ)`, the verifier send one
scalar challenge `α` from a field `F ⊇ R`, and the output relation check the lifted
identities *evaluated at `α`*. Everything downstream then works with field elements: the
residual claims are field-native and can be handed to a sumcheck. This is the *opposite
direction* of the `Packing` switch (`RingSwitching/Packing/`).

Why evaluating at one point suffices: each lifted row is a polynomial identity of degree
`< 2·deg φ`, so `2·deg φ` accepted challenges pin it down exactly (the interpolation kernel
of `../Transport/Eval.lean`), and the recovered `R[X]` identity descends back to `S` along
the presentation's coset laws. Security is therefore **coordinate-wise special soundness**
at plain `k = 2·deg φ` (not round-by-round): the extractor is the committed-scalar assembler
`CommittedScalar.treeExtractor`
(`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`),
and the recovery obligation is proven **once**, from the presentation laws — instances
inherit it for free.

Because the commitment binds only on short openings, the certificate is the escape-threaded one:
its escape event is `CommittedScalar.escEvent` ("the tree's branch openings exhibit a short
collision of the committed value"), and relations and extractor stay ordinary.

## Folder structure

* `Presentation.lean` — the data layer, mirroring the `CyclotomicModulus`/`IsCyclotomic`
  split: proof-free `Presentation R S` (monic modulus + canonical representatives) and the
  `IsPresentation` law class, plus the entire lift algebra proven over the laws — the
  exactness layer (`rep` is additive on the nose), `rowSum` with degree bounds, both
  directions of the quotient-witness correspondence, and the packaged per-row recovery
  engine `mulVec_eq_of_evalAt_rowSum`. The `evalAt` evaluation leg and the interpolation
  kernel `eq_of_evalAt_eq` it consumes live one level up, in the family-shared
  `../Transport/Eval.lean`.
* `Reduction.lean` — the protocol layer over the committed-scalar shell: the lifted witness
  `LiftedWitness`, the input relation `relLin`, the challenge-local predicate `checkAt`, the
  generic recovery theorem `recover`, and the escape-threaded CWSS theorem +
  `EscapeCWSSPackage` assembly.

## Instances

* **Cyclotomic rings** (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`) —
  `S := Rq Φ`, representatives `(·.1.toPoly)`, modulus `Φ.φ.toPoly`
  (`cyclotomicPresentation`); the `IsPresentation` laws are discharged from the `Rq`
  quotient bridge (`Data/Lattices/CyclotomicRing/QuotientLift.lean`). This is [NOZ26]
  Figure 4 / Lemma 9 (the [HMZ25] lift as used by Hachi), proven and sorry-free.

## Instantiation note

Instances whose statement types are formulated against this layer from the start can take
`Lift.package` wholesale. Instances with pre-existing concrete relations (Hachi)
define their `checkAt` through `Lift.checkAt`, prove their recovery from the
presentation engine, and assemble the package through the committed-scalar shell — passing
the instantiated predicates as *single opaque terms*. Avoid re-elaborating large
instantiated `checkAt`/relation terms on both sides of a unification seam: over carriers
with computable representations (e.g. `Rq`), the definitional-equality fallback can unfold
into the computable layer and blow up.

## References

* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
