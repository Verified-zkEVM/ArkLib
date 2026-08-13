/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval

/-!
# Hachi Sumcheck Loop (Figure 6 / Lemma 11 + Figure 7 tail)

Umbrella module for `Hachi/Sumcheck/`: the sumcheck loop that finishes Hachi's [NOZ26, §4.3]
opening. It
reduces the zero-check's point-evaluation claims `H₀(τ₀) = 0 ∧ H_α(τ_α) = 0` to hypercube-sum
claims, runs `m₀` sumcheck rounds down to a single evaluation of the committed table `w̃`, and
closes with the final-evaluation tail that hands the resulting evaluation claim to the §4.5
recursion (`Recursion/`). It operates on the shared batched-constraint encoding of
`ZeroCheck/Constraints.lean` (the sumcheck polynomials `F_{0,τ₀}`/`F_{α,τ₁}` and
`nestedRoundRel`).

## Relation to `ArkLib/ProofSystem/Sumcheck`

This folder is a **self-contained round layer**, deliberately not built on either generic sumcheck
in `ProofSystem/Sumcheck/`. The two are not interchangeable at the seam this subprotocol needs:

* the structured (witness-mode) round rejects by returning a **dummy statement**
  (`Structured/SingleRound.lean`'s `roundOracleVerifier`), which is precisely the convention
  Lemma 11 cannot use — all `k` siblings of a tree node share the message pair, so a dummy output
  collapses every branch onto the same statement and destroys extractability. Hence the
  `failure`-guarded `roundVerifier` here (see `Sumcheck/Rounds.lean`);
* the wire object differs (`CPolynomial.degreeLE` here, the Mathlib subtype `L⦃≤ d⦄[X]` there), as
  does the shape: Hachi sends the **pair** `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under one shared challenge, and its
  verifier is a plain `Verifier` (the round polynomials go in the clear), not an `OracleVerifier`;
* neither generic mode carries a soundness certificate to inherit: `Sumcheck/Spec/*` states
  completeness and RBR knowledge soundness but leaves them `sorry`, and `Sumcheck/Structured/*` is
  definitions and degree bookkeeping only.

So the useful direction of travel is the **reverse** of a rebase: if this material is ever
generalized, promote the guarded round and the round-polynomial layer (`Sumcheck/RoundPoly.lean`)
into the generic sumcheck layer as a guarded/paired variant, and keep this certificate as its
first instance. The round polynomials themselves *are* structured-mode shaped —
`F_α` is the identity combinator and `F₀` the range combinator `P_b` of degree `2b − 1` (giving the
`2b` per-variable pin, `ZeroCheck/Constraints.lean`) — so `SumcheckMultiplierParam` remains the
natural home for them on that path.

## Folder structure

* `Sumcheck/Bridge.lean` — the zero-round **entry bridge**: from the zero-check's point-evaluation
  claims to the *initial* sumcheck hypercube-sum claims (`∑ F_{0,τ₀} = 0`, `∑ F_{α,τ_α} = a` with
  the linear target `a` computed by the verifier); the paper's "finish the proof using sumcheck
  protocols" step. Pure reshaping through the batching identities.
* `Sumcheck/RoundPoly.lean` — the **round-polynomial layer** the round soundness runs on: the cube
  split `hypercubeSum_succ`, the partial sum as a univariate `roundPoly` with its evaluation and
  degree lemmas, and the two degree instances at Hachi's summands (`≤ 2b` and `≤ 2`). Proof-side
  only: `roundPoly` is `noncomputable`, the wire object stays computable.
* `Sumcheck/Rounds.lean` — **Hachi Figure 6 / Lemma 11**: the `m₀`-round paired sumcheck loop
  (each round sends the univariate pair `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under a shared challenge `aᵢ`), with
  **guarded** round verifiers (`gᵢ(0)+gᵢ(1) = targetᵢ₋₁`), composed by recursion over the binary
  guarded append. CWSS theorem `round_coordinateWiseSpecialSoundWithEscape` (**proven**, and
  axiom-clean), with its named extractor `roundExtractor`; it carries the two load-bearing side
  conditions `i < m₀` and `0 < b`.
* `Sumcheck/FinalEval.lean` — **Hachi Figure 7 tail**: the closing step — the prover sends the
  claimed evaluation `y′ = w̃(a)`, the guarded verifier checks the two final sumcheck targets, and
  the output is the evaluation claim `mle[w̃](a) = y′` consumed by the `Recursion/` adapters. CWSS
  theorem `finalEval_coordinateWiseSpecialSoundWith` (**proven**, and axiom-clean) with its named
  extractor `finalEvalExtractor`; no challenge round, hence no escape event.

This umbrella re-exports the folder (`FinalEval` transitively imports `Rounds`, `RoundPoly` and
`Bridge`). The plain output relation `relWEvalClaim` is the input of the §4.5 recursion; the full
chain, including its guarded tail, is composed in `Composition.lean`.

## Status

All three links (rows 7–9 of the chain in `Composition.lean`) are **sorry-free and axiom-clean**:
`mem_relNestedZeroCheck_of_nestedRoundRel`, `round_coordinateWiseSpecialSoundWithEscape` (with the
whole `roundsChain`) and `finalEval_coordinateWiseSpecialSoundWith` depend only on
`propext`/`Classical.choice`/`Quot.sound`.

What is *not* here is the **honest-prover / completeness layer**: `roundProver` and
`finalEvalProver` are skeletons parameterized by `computeG`/`computeY`, nothing instantiates them
honestly, there is no chained prover for the loop, and there is no completeness theorem. The
missing ingredient is a *computable* round message — a `CPolynomial`-valued partial sum in the free
coordinate, together with its agreement lemma against the noncomputable `roundPoly` (see the
Computability section of `Sumcheck/RoundPoly.lean`). That layer is also what
`Commitment.lean`'s `opening` waits on.

Extraction here is tree-based CWSS: it yields a witness (or an escape) from a structured accepting
tree, and says nothing about a *probability* of extraction. Turning that into a knowledge-soundness
error — the per-round Schwartz–Zippel `2b/|F|`, and the `(2b+1)^{m₀}` leaf count the composed
structure demands — needs the FMN24 Lemma-4-style bridge, which the repo does not have for any
protocol yet.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
