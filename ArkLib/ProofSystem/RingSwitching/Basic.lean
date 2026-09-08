/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Transport
import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
import ArkLib.ProofSystem.RingSwitching.Packing
import ArkLib.ProofSystem.RingSwitching.Lift

/-!
# Ring Switching — a family of constructions, not one protocol

Umbrella for `ProofSystem/RingSwitching/`. "Ring switching" names several reductions that
move an evaluation or linear claim between a small ring and a large ring — so that each part
of a proof system can run where it is cheap or sound: commit over the small ring, evaluate
and open over a large extension; or state a relation over a structured quotient ring, check
it inside a field. The constructions share *algebra*, not *protocol*; no single *protocol* in
this library unifies Lift and Packing. The coordinate core of Packing permits independent
packing and evaluation algebras; it does not subsume the [HMZ25] quotient-evaluation lift.
The two construction families, one folder each:

1. **Packing** (`Packing/`) — a finite basis of a commutative `B`-algebra `P` packs
   a family of `B`-multilinears into one `P`-multilinear. Evaluations may take values
   in an independent finite-free `B`-algebra `E`, with a different basis rank. The coordinate
   transpose and polynomial inverses need no embedding between `P` and `E`. The binary-table
   specialization groups `2^κ` coefficients and reduces the number of variables. The legacy
   DP24 data boundary (`RingSwitchingProfile`, `Packing/Profile.lean`) requires faithful
   tensor coordinates, including two-sided inverse laws and agreement of the embeddings on `B`.
   Distinct relocation constructions require their own laws:
   * **interactive relocation** — `ScalarHead/` proves the original DP24/Flock scalar
     reconstruction; `FullFamily/` proves checked coordinate batching to a sumcheck claim.
     `Tail/` composes the actual scalar or full-family head with product sumcheck and terminal
     read-back to the same packed opening relation, with explicit commitment functionality
     at its randomized security bounds. The native tensor batching head consumes those shared
     reconstruction and separation proofs, with completeness and exact worst-case knowledge
     security. FRI-Binius instantiates it with its actual commitment binding, then interleaves
     FRI with sumcheck. Legacy loop and unrestricted composition admissions remain separate.
   * **deterministic relocation** — `Commitments/Functional/Hachi/TraceHead/` implements
     the one-message, zero-challenge trace head at fixed-subring points ([NOZ26] §3.1).
     Actual monomial packing, the unit trace factor, honest committer coverage, completeness
     and CWSS preserve the existing norm-conditioned ring-opening relation.

2. **Lift** (`Lift/`) — the *opposite* direction, a quotient ring
   `S ≅ R[X]/(φ)` → a field `F ⊇ R`. Each row of a linear claim `M z = y` over `S` lifts to
   an `R[X]` identity with an explicit quotient polynomial; the prover commits to the lifted
   witness and the identities are checked *evaluated at* one random field challenge. The name
   says exactly what happens algebraically: an equality modulo `φ` is **lifted** to an exact
   polynomial equality before being transported to the field. Generic
   over any monic-modulus presentation of `S` (`Lift/Presentation.lean` — *not*
   specific to cyclotomic rings), with coordinate-wise special soundness at `k = 2·deg φ`
   and a commitment-collision escape via the committed-scalar seam. The cyclotomic instance
   (`Commitments/Functional/Hachi/RingSwitch/`) realizes [HMZ25]'s lift as used by Hachi.

## Shared support

* Within **Packing**, `FiniteObservation.lean` proves weighted coordinate reconstruction for
  arbitrary finite tables. Actual Boolean, native tensor and Hachi monomial proofs consume it.
  `CheckedObservation.lean` shares deterministic checking and exact inverse witness transport
  while retaining each protocol's concrete guard and commitment predicate. Hachi's CWSS and
  randomized packing's RBR knowledge certificates retain their separate security contracts.
* The **round-shape verifiers** (this folder's top level): every verifier round of the family
  is "one prover message, a deterministic local check, an accept/reject statement update" —
  message-only (`pSpecMessage` + `guardedMessageRoundOracleVerifier`: scalar claim heads
  and DP24's final step) or with a trailing scalar challenge
  (`pSpecScalar` + `guardedScalarRoundOracleVerifier`: DP24's batching round; the check-free limit
  of this shape is the committed-scalar verifier `Lift` builds on). See
  `RoundVerifiers.lean`.
* The **claim-transport algebra** (`Transport/`): both constructions move a polynomial claim
  by pushing its base-ring coefficients through a ring embedding and evaluating in the
  switch's target carrier. `Transport/Eval.lean` is the univariate leg — `evalAt` and the
  interpolation kernel `eq_of_evalAt_eq`, consumed by `Lift/`;
  `Transport/Coeffs.lean` is the multivariate leg — the degree-generic coefficient transport
  `embedCoeffs`, whose `d = 1` case is `Packing/`'s component-wise carrier embedding.
  Each leg currently has call sites in one construction; the *pattern* is what they share.
* The **committed-scalar seam**
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`) — the
  commit-then-scalar-challenge shell with its CWSS extractor and its binding-break escape event,
  which `Lift` builds on. It mentions no rings and is not ring-switching-specific,
  which is why it lives under `OracleReduction/`, not here.
* The wire format `CoordinateWise.ScalarRound.pSpecScalar` — the two-round
  message-then-scalar-challenge shape both DP24's batching round and the `Lift`
  round run on (and which `guardedScalarRoundOracleVerifier` above is the verifier skeleton of); it
  stays under `OracleReduction/` with the CWSS machinery built on it.

Anything else — the tensor-algebra batching check, the relocation sumcheck, the
quotient-witness correspondence, the trace identity — belongs to exactly one construction and
lives with it. The faithful tensor-coordinate laws and the monic-quotient representative laws
are distinct.
Coordinate additivity follows from the Profile inverse laws; a quotient representative need not
preserve multiplication as a polynomial. The shared verifier shapes do not identify these laws
or supply a shared security theorem.

## Folder structure

* `Basic.lean` — this family-taxonomy umbrella.
* `RoundVerifiers.lean` — the family's shared verifier skeletons: the one-message wire
  `pSpecMessage` and guarded message/scalar verifiers with absorbing failure. Total fallback
  variants are also available; their rejection statements need a separate relation contract.
* `Transport/` — the shared claim-transport algebra (see `Transport.lean`): evaluation
  through a ring embedding with the interpolation kernel (`Eval.lean`, univariate) and
  degree-bounded coefficient transport (`Coeffs.lean`, multivariate).
* `Packing/` — finite-free coordinate algebra, checked scalar and full-family phases,
  the generic sumcheck pipelines to a packed opening, and the legacy DP24 construction.
  See `Packing.lean`.
* `Lift/` — the generic quotient-ring lift to field evaluations (see `Lift.lean`).

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
* [HMZ25] Huang, M.-Y. M., Mao, X., and Zhang, J. "Sublinear Proofs over Polynomial Rings."
  Cryptology ePrint Archive (2025).
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based
  Multilinear Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026).

See also the KB concept page `docs/kb/concepts/ring-switching.md`.
-/
