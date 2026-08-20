/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Completeness

/-!
# Hachi Sumcheck Loop

Umbrella module for `Hachi/Sumcheck/`: the sumcheck loop that finishes Hachi's opening
(§4.3 of [NOZ26]). It reduces the zero-check's point-evaluation claims
`H₀(τ₀) = 0 ∧ H_α(τ_α) = 0` to hypercube-sum claims, runs `m₀` sumcheck rounds down to a
single evaluation of the committed table `w̃`, and closes with the final-evaluation step that
hands the resulting evaluation claim to the recursion (`Recursion/`). It operates on the
batched-constraint encoding of `ZeroCheck/Constraints.lean` (the sumcheck polynomials
`F_{0,τ₀}`/`F_{α,τ₁}` and `nestedRoundRel`).

## Relation to `ArkLib/ProofSystem/Sumcheck`

This folder is a self-contained round layer, deliberately not built on either generic
sumcheck in `ProofSystem/Sumcheck/`:

* the structured (witness-mode) round rejects by returning a dummy statement
  (`Structured/SingleRound.lean`'s `roundOracleVerifier`), a convention the extraction
  argument here cannot use — all `k` siblings of a tree node share the message pair, so a
  dummy output collapses every branch onto the same statement and destroys extractability.
  Hence the `failure`-guarded `roundVerifier` (see `Sumcheck/Rounds.lean`);
* the wire object differs (`CPolynomial.degreeLE` here, the Mathlib subtype `L⦃≤ d⦄[X]`
  there), as does the shape: Hachi sends the *pair* `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under one shared
  challenge, and its verifier is a plain `Verifier` (the round polynomials go in the clear),
  not an `OracleVerifier`;
* neither generic mode carries a soundness proof to inherit.

If this material is ever generalized, the natural direction is to promote the guarded round
and the round-polynomial layer (`Sumcheck/RoundPoly.lean`) into the generic sumcheck layer as
a guarded/paired variant.

## Folder structure

* `Sumcheck/Bridge.lean` — the zero-round entry bridge: from the zero-check's
  point-evaluation claims to the initial sumcheck hypercube-sum claims (`∑ F_{0,τ₀} = 0`,
  `∑ F_{α,τ_α} = a` with the linear target `a` computed by the verifier). Pure reshaping
  through the batching identities.
* `Sumcheck/RoundPoly.lean` — the round-polynomial layer the round soundness runs on: the
  cube split `hypercubeSum_succ`, the partial sum as a univariate `roundPoly` with its
  evaluation and degree lemmas, and the two degree instances at Hachi's summands (`≤ 2b` and
  `≤ 2`). Proof-side only: `roundPoly` is `noncomputable`, the wire object stays computable.
* `Sumcheck/Rounds.lean` — the `m₀`-round paired sumcheck loop: each round sends the
  univariate pair `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under a shared challenge `aᵢ`, checked by guarded round
  verifiers (`gᵢ(0)+gᵢ(1) = targetᵢ₋₁`) and composed by recursion over the binary guarded
  append. Soundness is `round_coordinateWiseSpecialSoundWithEscape`, with extractor
  `roundExtractor` and the two load-bearing side conditions `i < m₀` and `0 < b`.
* `Sumcheck/FinalEval.lean` — the closing step: the prover sends the claimed evaluation
  `y′ = w̃(a)`, the guarded verifier checks the two final sumcheck targets, and the output is
  the evaluation claim `mle[w̃](a) = y′` consumed by the `Recursion/` adapters. Soundness is
  `finalEval_coordinateWiseSpecialSoundWith`, with extractor `finalEvalExtractor`.

This umbrella re-exports the folder (`Completeness` transitively imports `FinalEval`,
`Rounds`, `RoundPoly` and `Bridge`). The output relation `relWEvalClaim` is the input of the
recursion; the full chain is composed in `Composition.lean`.

## Status

The soundness side is complete and `sorry`-free. So is the honest side, per link:

* `Bridge` — done. `mem_nestedRoundRel_of_relNestedZeroCheck` (the point-to-sum push-forward,
  converse of the pull-back) and `nestedSumcheckBridgeReduction_perfectCompleteness`
  (zero-round `ReduceClaim`, error `0`, unconditional beyond the two arity conditions the sum
  identities need). Verifier shared with the package by `rfl`.
* `FinalEval` — done. `honestComputeY := wTableMleEval`, the protocol object
  `finalEvalReduction`, the guard-passage lemma `finalCheck_honestComputeY`, relation
  preservation `mem_relWEvalClaim_of_nestedRoundRel`, the run characterization
  `finalEvalProver_run_support` and `finalEvalReduction_perfectCompleteness` (error `0`,
  unconditional). This is the **first** Hachi link whose verifier can actually reject, so
  "the honest run cannot fail" had to be *proved* (from the guard lemma) rather than holding
  by construction.
* `Rounds` / `Completeness` — done, with one framework caveat. The computable round message is
  `computableRoundPoly` (`RoundPoly`): the summand evaluated in the ring `CPolynomial F` itself
  (`CMvPolynomial.eval₂`, which *is* computable), with `X` in the free coordinate and constants
  elsewhere, summed over the remaining cube. `computableRoundPoly_toPoly` identifies it with the
  proof-side `roundPoly`, which is where its values (`computableRoundPoly_eval`) and its two
  `degreeLE` memberships come from. `honestComputeG` packages the pair,
  `roundReduction_perfectCompleteness` is one round's completeness (error `0`, hypotheses `0 < b`
  and `i < m₀` — the same two the round's soundness carries), and `roundsReduction` folds `m₀` of
  them, sharing its verifier with `roundsChain` (`roundsReduction_verifier`).

  ⚠ **The caveat is the fold, not the round.** `roundsReduction_perfectCompleteness` and
  `sumcheckReduction_perfectCompleteness` (bridge ▷ rounds ▷ final evaluation) go through
  `Reduction.append_perfectCompleteness`, hence through the still-`sorry`
  `Reduction.append_completeness`, and so depend on `sorryAx`. Everything per-link is
  axiom-clean. `Commitment.lean`'s `opening` waits on that same framework lemma.

Extraction here is tree-based: it yields a witness (or an escape) from a structured accepting
tree, and says nothing about a *probability* of extraction. Turning that into a
knowledge-soundness error — the per-round Schwartz–Zippel `2b/|F|`, and the `(2b+1)^{m₀}`
leaf count the composed structure demands — needs a Lemma-4-style bridge in the sense of
FMN24, which the repo does not have for any protocol yet.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
