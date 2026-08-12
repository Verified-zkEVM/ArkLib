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
this library unifies Lift and Packing. Generic work on the Packing side is in progress and is
intended to subsume the shared packing abstraction, but it does not subsume `Lift`, which is the
[HMZ25] quotient-evaluation lift rather than a packing. The two construction families, one folder
each:

1. **Packing** (`Packing/`) — small ring `B` → large ring `L`, `L` free of rank
   `2^κ` over `B`. A basis identifies each `2^κ`-block of a `B`-multilinear's coefficients
   with one `L`-element, so the polynomial *packs* into an `L`-multilinear in fewer
   variables, and the claim about the original must be relocated onto the packed one. The
   packing data is one shared abstraction (`RingSwitchingProfile`,
   `Packing/Profile.lean`); the relocation is per-instance:
   * **interactive relocation** (the protocol files of `Packing/`) — for an arbitrary
     large-ring evaluation point: carrier message, batching challenge, dedicated packing
     sumcheck; RBR knowledge soundness (`[IsDomain L]`). Consumed by
     `ProofSystem/Binius/FRIBinius/` (this is [DP24]'s construction).
   * **deterministic relocation** (planned) — for a subring-valued evaluation point the
     interaction collapses to one message and one identity check, with zero soundness error;
     a second `Profile` instance ([NOZ26] §3).

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

## What is genuinely shared between the two families

* The **round-shape verifiers** (this folder's top level): every verifier round of the family
  is "one prover message, a deterministic local check, an accept/reject statement update" —
  message-only (`pSpecMessage` + `messageRoundOracleVerifier`: DP24's final step today,
  Hachi §3's trace-check head tomorrow) or with a trailing scalar challenge
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
lives with it. In particular the two *data layers* do not unify: above a spanning-and-faithful
core their law sets are incomparable (coordinate additivity is not derivable from
`decomposeRows_spec` alone, and `rep` is not multiplicative on the nose), so no common parent
structure would carry a lemma either side's proofs consume.

## Folder structure

* `Basic.lean` — this family-taxonomy umbrella.
* `RoundVerifiers.lean` — the family's shared verifier skeletons: the one-message wire
  `pSpecMessage` and the check-then-update verifiers `messageRoundOracleVerifier` /
  `scalarRoundOracleVerifier`.
* `Transport/` — the shared claim-transport algebra (see `Transport.lean`): evaluation
  through a ring embedding with the interpolation kernel (`Eval.lean`, univariate) and
  degree-bounded coefficient transport (`Coeffs.lean`, multivariate).
* `Packing/` — packing data layer + the DP24 construction (see `Packing.lean`).
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
