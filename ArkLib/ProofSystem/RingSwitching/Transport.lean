/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.ProofSystem.RingSwitching.Transport.Eval
import ArkLib.ProofSystem.RingSwitching.Transport.Coeffs

/-!
# Claim transport through ring embeddings

Umbrella for `RingSwitching/Transport/`. A ring switch moves a claim between rings: the
claim's data — polynomial coefficients, witnesses, evaluation points — lives over one ring,
but the check that discharges the claim runs in another. The transport layer is the algebra
that makes this move meaningful in both directions: push the data through a ring homomorphism
`φ : R →+* T` into the target carrier, evaluate there, and — because the transported objects
are polynomials of bounded degree — recover the original identity from agreement at enough
points.

## Folder structure

* `Eval.lean` — the univariate leg. `evalAt φ a : R[X] →+* T` evaluates a base-ring
  polynomial at a carrier point through the embedding (so transported identities hold at
  every point), and the interpolation kernel `eq_of_evalAt_eq` gives the converse: agreement
  at `N` pairwise-distinct points of a domain pins down a degree-`< N` polynomial exactly.
  This is the soundness core of any switch that checks transported identities at
  (e.g. randomly chosen) carrier points.
* `Coeffs.lean` — the multivariate leg. `embedCoeffs φ : R⦃≤ d⦄[X σ] → T⦃≤ d⦄[X σ]`
  transports a degree-bounded polynomial coefficient-wise, preserving the degree bound, and
  `embedCoeffs_eval` commutes transport with evaluation. This is how a base-ring polynomial
  is interpreted inside the carrier where the verifier's checks run.

The two legs are deliberately separate compile units: `Eval.lean` is Mathlib-only and stays
import-light for the data layers that consume it; `Coeffs.lean` pulls in the multivariate
degree machinery.

## Instantiations in this folder

* `Lift` (`../Lift/`) states its challenge-local checks via
  `evalAt` and extracts via `eq_of_evalAt_eq`.
* `Packing` (`../Packing/`) embeds its packed multilinear into the
  pack/trace carrier via `embedCoeffs` at `d = 1`.
-/
