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
closes with the final-evaluation tail producing the multilinear-evaluation claim `relWEvalClaim`
— the seam where one `iteration` ends and `Composition.lean`'s `endPiece` takes over. (The §4.5
`Recursion/` adapters target the same seam but are not currently composed.) It operates on the
shared batched-constraint encoding of
`ZeroCheck/Constraints.lean` (the sumcheck polynomials `F_{0,τ₀}`/`F_{α,τ₁}` and
`nestedRoundRel`).

## TODO — reuse the existing structured sum-check

This subprotocol should be **rebased onto `ArkLib/ProofSystem/Sumcheck/Structured`** rather than
carrying bespoke round machinery. Concretely: the round polynomials `F_{0,τ₀}`/`F_{α,τ₁}` are
instances of `Sumcheck.Structured.computeRoundPoly` via `SumcheckMultiplierParam` (identity
combinator for the degree-2 linear check `F_α`; the range combinator `∏ⱼ (X − j)` of degree `2b`
for `F₀` — the multiplier docstring in `Structured.lean` already anticipates exactly this Hachi
case); the round consistency is `Sumcheck.Structured.sumcheckConsistencyProp` over
`SumcheckDomain.boolDomain`; the per-round data is `Structured.Statement`/`SumcheckWitness`. The
**exact CWSS round verifier is left `sorry` for now** (`Sumcheck/Rounds.lean`): wiring the
structured round into the CWSS chain first needs the wire format (`!v[...]`) and the
record-then-bridge convention reconciled with the structured round's `![...]` RBR verifier
(`Structured/SingleRound.lean`'s `roundOracleVerifier`), which is deferred.

## Folder structure

* `Sumcheck/Bridge.lean` — the zero-round **entry bridge**: from the zero-check's point-evaluation
  claims to the *initial* sumcheck hypercube-sum claims (`∑ F_{0,τ₀} = 0`, `∑ F_{α,τ_α} = a` with
  the linear target `a` computed by the verifier); the paper's "finish the proof using sumcheck
  protocols" step. Pure reshaping through the batching identities.
* `Sumcheck/Rounds.lean` — **Hachi Figure 6 / Lemma 11**: the `m₀`-round paired sumcheck loop
  (each round sends the univariate pair `(gᵢ⁽⁰⁾, gᵢ⁽ᵅ⁾)` under a shared challenge `aᵢ`), with
  **guarded** round verifiers (`gᵢ(0)+gᵢ(1) = targetᵢ₋₁`), composed by recursion over the binary
  guarded append. CWSS theorem `round_coordinateWiseSpecialSoundWithEscape` (**sorried**).
* `Sumcheck/FinalEval.lean` — **Hachi Figure 7 tail**: the closing step — the prover sends the
  claimed evaluation `y′ = w̃(a)`, the guarded verifier checks the two final sumcheck targets, and
  the output is the evaluation claim `mle[w̃](a) = y′` consumed by `Composition.lean`'s `endPiece`.

This umbrella re-exports the folder (`FinalEval` transitively imports `Rounds` and `Bridge`).
The plain output relation `relWEvalClaim` is the seam where one `iteration` ends; the full chain —
its guarded tail plus the closing `endPiece` — is composed in `Composition.lean`. The §4.5
`Recursion/` adapters re-enter at this same seam and are future work.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
