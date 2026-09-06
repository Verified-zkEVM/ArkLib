/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Completeness
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction

/-!
# Hachi Zero-Check (Figure 5 / Lemma 10)

Umbrella module for `Hachi/ZeroCheck/`: the batched-constraint encoding (Hachi [NOZ26]
Eqs. (21)–(23))
and the zero-check subprotocol that reduces the two polynomial identities `H₀ ≡ 0 ∧ H_α ≡ 0` — the
`eq̃`-batched range constraints and `α`-evaluated linear constraints — to evaluations at direct
points assembled from scalar challenges, together with both of its security directions:
coordinate-wise special soundness (`ZeroCheck/Reduction.lean`) and perfect completeness
(`ZeroCheck/Completeness.lean`).

## Deviation from the paper's Lemma 10

Figure 5 is sound as printed; Lemma 10's *deterministic* route to `H₀ ≡ 0` is what fails, since a
coordinate-wise star only certifies vanishing on an axis cross
(`MvPolynomial.exists_nonzero_vanishing_on_axis_cross`). Because this chain composes through
coordinate-wise special soundness rather than a probabilistic bound,
`ZeroCheck/Reduction.lean` draws each coordinate in its own scalar round, turning the accepting
family into a path-dependent complete binary evaluation tree on which vanishing does determine a
multilinear polynomial. No prover message separates those rounds, so the interactive protocol is
unchanged.

That file's header states the deviation, the witness-fed extractor interface, and the genuine costs
of the scalar-round route: `ChallengeTree.LeafWitnesses` supplies candidate output witnesses at the
leaves, `nestedZeroCheckExtractor` reads the all-left entry without a relation search, and the full
tree has `2 ^ (m₀ + m₁)` leaves. The full analysis is
`docs/kb/audits/noz26-zero-check-lemma10.md`.

## Folder structure

* `ZeroCheck/Constraints.lean` — the constraint encoding (Eqs. (21)–(23)): the table `w̃`, the
  batched polynomials `H₀`/`H_α` as computable `CMlPolynomialEval` Boolean-value vectors (with
  derived Mathlib multilinear views used only in algebraic proofs), Eq. (22)'s public
  `M̃_α`/`α̃` contraction and its proved equality with `H_α`'s row-defect table
  (`alphaDefect_wTable`, `hAlpha_eq_zero_iff_alphaDefect`), the sumcheck summands
  `F_{0,τ₀}`/`F_{α,τ₁}` with their per-variable degrees, `hypercubeSum`, and the direct-point
  relation `nestedRoundRel`. Shared between this zero-check and the sumcheck
  rounds (`Sumcheck/`).
* `ZeroCheck/Batch.lean` — the zero-round batching bridge: reinterprets the lift's per-row claims
  as the two identities `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatched`, Eqs. (22)–(23)). The
  pull-back `mem_relLift_of_relBatched` (`relBatched → relLift`) recovers the per-row equation
  from `H_α ≡ 0` (via `hAlpha_eq_zero_iff` and `hAlphaEvals_rowPoint`, arity `n ≤ 2 ^ m₁`; the
  identification of `H_α` with paper Eq. (22) is `hAlpha_eq_zero_iff_alphaDefect`) and
  **derives shortness `liftShort` from `H₀ ≡ 0`** (via `hZero_eq_zero_imp_liftShort`, arity
  `(μ + n·δ)·deg φ ≤ 2 ^ m₀`, range-base fit `b − 1 ≤ γ`, digit-base admissibility) — so
  shortness is proved, not assumed (`relBatched` carries no `liftShort` conjunct). The point
  relations below it
  *do* carry one, but as the commitment's **shortness index**, not as a range assumption:
  `LiftCom.Collision` is defined on pairs of distinct *short* openings, so the conjunct is what
  makes the weak-binding branch a Module-SIS break. Since `relBatched` — the relation whose
  `H₀ ≡ 0` proves shortness — is itself norm-free, the derivation is not circular. See the
  "Where the norm sits" section of `ZeroCheck/Reduction.lean`. The **honest direction**
  `mem_relBatched_of_relLift` lives here too (`hZero_eq_zero_of_liftShort` +
  `hAlpha_eq_zero_of_rows`), so the bridge is settled both ways; it needs neither arity hypothesis,
  but the range-base fits in the opposite orientation, which pins the paper's
  `bound = b − 1`.
* `ZeroCheck/Reduction.lean` — Hachi Figure 5 / Lemma 10: `m₀ + m₁` scalar challenge rounds
  assemble the direct points `τ₀` and `τα`. The coordinate-wise special soundness theorem
  `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` reduces `relBatched` to
  `relNestedZeroCheck`; its extraction handles escapes, weak-binding collisions, and the common
  opening by the evaluation-tree zero test — `H₀` through the first `m₀` levels of a single tree,
  `H_α` through its last `m₁`. Tree size is machine-checked by
  `nestedZeroCheck_numLeaves`/`_lt`.
* `ZeroCheck/Completeness.lean` — the honest direction:
  `nestedZeroCheckReduction_perfectCompleteness`, perfect completeness of Figure 5 relative to
  `relBatched`. Its algebraic half `mem_relNestedZeroCheck_of_relBatched` holds at *every* pair of
  evaluation points — `relBatched` asserts the identities, so no property of the challenge
  distribution is used and the error is exactly `0` — and its execution half
  `nestedZeroCheckReduction_run_support` shows an honest run cannot fail and gives prover and
  verifier the same output statement. They are joined by the generic
  `Reduction.perfectCompleteness_of_run_support` (`OracleReduction/Security/Basic.lean`). The
  file also closes the **batching bridge** on the honest side:
  `batchReduction_perfectCompleteness` (protocol object `batchReduction`, verifier shared with
  `batchPackage` by `rfl`), from `Batch.lean`'s honest direction `mem_relBatched_of_relLift`
  through `ReduceClaim.reduction_completeness_of_imp`. Both links of this folder are therefore
  certified in both directions; the appended statements live in `HonestChain.lean`.

The generic zero test lives in `ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean` (Mathlib-level,
`k`-ary trees and individual degree `< k`) with the computable view in
`ArkLib/ToCompPoly/Multilinear/NestedEvaluationTree.lean`.

This umbrella re-exports the folder (`Completeness` imports `Reduction`, which
transitively imports `Batch` and `Constraints`).
Its output relation `relNestedZeroCheck` is the input of the sumcheck bridge in `Sumcheck/`, and
the chain is composed in `Composition.lean`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
