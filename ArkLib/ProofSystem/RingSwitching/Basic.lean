/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.ProofSystem.RingSwitching.Transport
public import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
public import ArkLib.ProofSystem.RingSwitching.Packing
public import ArkLib.ProofSystem.RingSwitching.Lift

/-!
# Ring Switching — a family of constructions, not one protocol

Umbrella for `ProofSystem/RingSwitching/`. "Ring switching" names several reductions that
move an evaluation or linear claim between a small ring and a large ring — so that each part
of a proof system can run where it is cheap or sound: commit over the small ring, evaluate
and open over a large extension; or state a relation over a structured quotient ring, check
it inside a field. `Packing/RingSwitch` certifies a reusable scalar-to-product-sumcheck
protocol over independent commutative algebras. `Lift` retains its own quotient-evaluation
protocol and security interpretation. The two construction families have separate folders:

1. **Packing** (`Packing/`) — `PackingData` gives independent finite bases of a packing
   algebra and an opening algebra over a common commutative ring. A `ClaimLayout` identifies the
   original scalar claim and its component decomposition. `Head` sends the encoded component
   values, checks reconstruction and derives a product-sumcheck claim using a `BatchingRule`.
   `RingSwitch` directly appends `ProductSumcheck`, retaining the original query, batching
   challenge, commitment oracle and packed witness through the terminal evaluation claim.
   Completeness requires a commutative challenge ring. Round-by-round knowledge
   soundness additionally uses a certified `BatchingStrategy`, functional compatibility,
   injective coefficient transport and a finite challenge ring with no zero divisors. The
   challenge-error sum is `bat.error + 2m/|C|`. The head separately supports a fixed list
   covering all compatible packed candidates, without asserting list security for the tail.
   Honest commitment coverage is a separate constructor contract, unused by security.
   * **tensor-prefix relocation** — equal packing/opening algebras, power-of-two ranks, prefix
     layout and equality-fold batching. `Packing/TensorPrefix` defines the protocol through
     `RingSwitch` with the original tensor carrier `P.A`, decoded by its column equivalence.
     Its operational equation is the original scalar check and row-coordinate batching target.
     `Binius/FRIBinius/RingSwitch` appends the Binary Basefold opening. Exact first-codeword
     encodings give completeness; unique-radius compatibility gives round-by-round security.
   * **deterministic relocation** — for a subring-valued evaluation point the interaction
     collapses to one message and one identity check, with zero soundness error ([NOZ26] §3.1).
     Its carrier is `L` itself, so it is not a `Profile` instance: the Hachi trace head
     (`Commitments/Functional/Hachi/TraceHead/`) uses the coordinate layer of `Packing/`
     directly, with one opening coordinate: its `ψ` packing is `packedMLE` of a
     monomial-coefficient `ClaimLayout`, its conformance theorem states its accepting condition
     through the shared `sliceRel`, and its read-back is a `CheckedObservation`. It exercises
     only the packing, evaluation and opening part of that layer (no batching, multiplier or
     sumcheck), as in [NOZ26] §3.1.

2. **Lift** (`Lift/`) — the *opposite* direction, a quotient ring
   `S ≅ R[X]/(φ)` → a field `F ⊇ R`. Each row of a linear claim `M z = y` over `S` lifts to
   an `R[X]` identity with an explicit quotient polynomial; the prover commits to the lifted
   witness and the identities are checked *evaluated at* one random field challenge. The name
   says exactly what happens algebraically: an equality modulo `φ` is **lifted** to an exact
   polynomial equality before being transported to the field. Generic
   over any monic-modulus presentation of `S` (`Lift/Presentation.lean` — *not*
   specific to cyclotomic rings), with coordinate-wise special soundness at `k = 2·deg φ`
   via the committed-scalar seam. The cyclotomic instance
   (`Commitments/Functional/Hachi/RingSwitch/`) realizes [HMZ25]'s lift as used by Hachi.

## Shared support for the two families

* The **round-shape verifiers** (this folder's top level) implement a prover message,
  a deterministic local check and an accepted update or an abort —
  message-only (`pSpecMessage` + `messageRoundOracleVerifier`: DP24's final step; Hachi's
  §3.1 trace head has the same one-message shape as a plain aborting `Verifier`) or with a
  trailing scalar challenge
  (`pSpecScalar` + `scalarRoundOracleVerifier`: DP24's batching round; the check-free limit
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
  round run on (and which `scalarRoundOracleVerifier` above is the verifier skeleton of); it
  stays under `OracleReduction/` with the CWSS machinery built on it.

Anything else — the tensor-algebra batching check, the relocation sumcheck, the
quotient-witness correspondence, the trace identity — belongs to exactly one construction and
lives with it. In particular the two *data layers* do not unify: their laws govern different
maps (a profile's coordinate bijections onto `2^κ` coordinates over `L`, a presentation's
representative map `rep`, which is not multiplicative on the nose), so no common parent
structure would carry a lemma either side's proofs consume.

## Folder structure

* `Basic.lean` — this family-taxonomy umbrella.
* `RoundVerifiers.lean` — the family's shared verifier skeletons: the one-message wire
  `pSpecMessage` and the check-then-update verifiers `messageRoundOracleVerifier` /
  `scalarRoundOracleVerifier`.
* `Transport/` — the shared claim-transport algebra (see `Transport.lean`): evaluation
  through a ring embedding with the interpolation kernel (`Eval.lean`, univariate) and
  degree-bounded coefficient transport (`Coeffs.lean`, multivariate).
* `Packing/` — independent coordinate algebra, the generic scalar head and the DP24 construction
  (see `Packing.lean`).
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

@[expose] public section
