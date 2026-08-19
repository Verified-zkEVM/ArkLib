/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
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

This folder keeps Hachi's paired, guarded round layer local: its two sumchecks share a challenge,
each output statement replaces its targets, and the verifier can reject on the prior-target check.
The reusable round-polynomial facts live in `Sumcheck/RoundPoly.lean`; a future generic
guarded/paired sumcheck layer could promote that file and the guarded scalar-round assembly.

## Folder structure

* `Sumcheck/Bridge.lean` — the zero-round **entry bridge**: from the zero-check's point-evaluation
  claims to the *initial* sumcheck hypercube-sum claims (`∑ F_{0,τ₀} = 0`, `∑ F_{α,τ_α} = a` with
  the linear target `a` computed by the verifier); the paper's "finish the proof using sumcheck
  protocols" step. Pure reshaping through the batching identities.
* `Sumcheck/Rounds.lean` — **Hachi Figure 6 / Lemma 11**: the `m₀`-round paired sumcheck loop
  (each round sends the univariate pair `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under a shared challenge `aᵢ`), with
  **guarded** round verifiers (`gᵢ(0)+gᵢ(1) = targetᵢ₋₁`), composed by recursion over the binary
  guarded append. Lemma 11 is proved at a computable extractor that reads the supplied branch
  openings directly.
* `Sumcheck/RoundPoly.lean` — the partial-hypercube round-polynomial construction and its
  degree/evaluation facts used by Lemma 11.
* `Sumcheck/FinalEval.lean` — **Hachi Figure 7 tail**: the closing step — the prover sends the
  claimed evaluation `y′ = w̃(a)`, the guarded verifier checks the two final sumcheck targets, and
  the output is the evaluation claim `mle[w̃](a) = y′` consumed by the `Recursion/` adapters. Its
  computable extractor reads the unique leaf opening directly.

This umbrella re-exports the folder (`FinalEval` transitively imports `Rounds` and `Bridge`).
The plain output relation `relWEvalClaim` is the input of the §4.5 recursion; the full chain,
including its guarded tail, is composed in `Composition.lean`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
