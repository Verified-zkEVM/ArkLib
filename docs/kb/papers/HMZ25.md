---
kind: paper
bibkey: HMZ25
title: "Sublinear Proofs over Polynomial Rings"
year: "2025"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2025/199
source_metadata: ../sources/HMZ25/metadata.yml
status: seeded
related_concepts:
  - ring-switching
related_modules:
  - ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean
  - ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean
  - ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean
  - ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean
---

# HMZ25

## At A Glance

`HMZ25` (Huang–Mao–Zhang, ePrint 2025/199) builds sublinear-size proof systems for rank-one
constraint satisfaction over polynomial rings `Z_Q[X]/(X^N + 1)`. ArkLib uses one specific idea
from it: the **ring-switching lift**. A linear relation `M z = y` over a quotient ring
`R_q = Z_q[X]/(f)` holds iff the canonical representatives satisfy
`M(X)·z(X) = y(X) + f(X)·r(X)` over `Z_q[X]` for a quotient vector `r` of degree `< deg f`;
evaluating the lifted identity at a random point `α` of an extension field `F ⊇ Z_q` turns the ring
statement into field arithmetic, where sumcheck-style protocols run efficiently. Hachi
([`NOZ26`](NOZ26.md)) adopts this lift as the entry of its §4.3 sumcheck chain
(Figure 4 / Lemma 9).

## What ArkLib Uses From This Paper

- The quotient-witness correspondence and its interpolation soundness kernel:
  `ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean` (generic, monic cyclotomic modulus,
  abstract extension embedding `φF : R →+* F`) — proven and axiom-clean.
- The lift as a two-round subprotocol (commit to the lifted witness, evaluate at a random `α`)
  with `k = 2d` plain special soundness, **formalized generically** in
  `ArkLib/ProofSystem/RingSwitching/Lift/` over any monic-modulus presentation `S ≅ R[X]/(φ)`
  (`Presentation`/`IsPresentation`), on the committed-scalar shell
  `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`;
  Hachi's presentation instance, norms, local predicate, interpolation recovery, and `liftPackage`
  (whose CWSS certificate is its `isCWSS` field) are in
  `ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean`.

## Main ArkLib Touchpoints

- [`ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean)
  and [`Reduction.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean)
  — the generic quotient-evaluation switch: presentation data + laws, lift algebra,
  interpolation engine, and the escape-threaded CWSS reduction over the committed-scalar shell.
- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean)
  — the generic commitment-anchored scalar phase: its extractor projects the shared opening, and
  its escape event `escEvent` targets the commitment's short-collision set.
- [`ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/QuotientLift.lean)
  — the quotient-witness correspondence and interpolation kernel.
- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Basic.lean)
  — umbrella module; overview of the lift and the folder structure.
- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean)
  — the Hachi instance and Lemma 9 certificate (row 4 of the opening chain).
- [`ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean`](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean)
  — the zero-round entry adapter reshaping Hachi's Eq. (20) output into the unstructured linear
  relation `R^lin` the lift addresses.
- Concept page: [`../concepts/ring-switching.md`](../concepts/ring-switching.md)

## Known Divergences From ArkLib

- ArkLib formalizes only the lift step as used inside Hachi's opening argument, not the paper's
  full Ring-R1CS proof system.
- ArkLib never sends the lifted witness `(z, r)` in the clear: it is the output-relation witness of
  the composed chain, and the verifier is a pure statement-extending pass-through; the paper's
  final-message checks live in the output relation `relLift`.
- The commitment is abstract (`LiftCom`, an alias of `CoordinateWise.BindingCommitment`) and only
  *weakly* binding — binding on short openings ([NOZ26] Remark 2 / Lemma 7), not the paper's plain
  binding. That weakness is carried by an **escape event** on the transcript tree
  (`CommittedScalar.escEvent`, targeting `LiftCom.Collision`), not by a widened relation or a
  sum-typed extractor: the certificate concludes "either the tree exhibits a short collision of the
  commitment, or extraction succeeds".
- The paper's full protocol digit-decomposes the quotient before commitment. ArkLib currently
  exposes that encoding boundary through `RhoShort`; the concrete digit encoding and completeness
  bound belong to the downstream Hachi constraint layer.
- The modulus is an arbitrary monic cyclotomic `Φ.φ` (paper: `X^d + 1`), and the extension field is
  abstract with an embedding (paper: `F_{q^k}`).

## Version Notes

Cited via the ePrint version (2025/199); Hachi ([`NOZ26`](NOZ26.md)) cites the same report. ArkLib
follows Hachi's presentation of the lift rather than the original Ring-R1CS setting. Track the
version if proof obligations start depending on exact statements.

## Source Access

- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
- Source metadata: [`../sources/HMZ25/metadata.yml`](../sources/HMZ25/metadata.yml)
- https://eprint.iacr.org/2025/199
