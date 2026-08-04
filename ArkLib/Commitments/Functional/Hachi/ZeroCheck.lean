/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction

/-!
# Hachi Zero-Check (Figure 5 / Lemma 10)

Umbrella for `Hachi/ZeroCheck/`: the batched-constraint encoding (Hachi [NOZ26] Eqs. (21)–(23))
and the zero-check subprotocol that reduces the two polynomial identities `H₀ ≡ 0 ∧ H_α ≡ 0` — the
`eq̃`-batched range constraints and `α`-evaluated linear constraints — to evaluations at direct
points assembled from scalar challenges.

## Deviation from the paper's Lemma 10

The paper's Lemma 10 argues extraction from uniform vector challenges, but a coordinate-wise
family of accepting transcripts only certifies that `H` vanishes on an axis cross, which for
`m ≥ 2` does not imply `H ≡ 0`. `ZeroCheck/Reduction.lean` instead draws each coordinate in its
own scalar round. Two distinct accepting children at every round form a complete, path-dependent
binary evaluation tree, on which vanishing determines a multilinear polynomial. The
counterexample to the uniform-challenge argument is
`LinearMvExtension.exists_nonzero_vanishing_on_axis_cross`, and the deviation is recorded in
`docs/kb/audits/noz26-zero-check-lemma10.md`.

## Folder structure

* `ZeroCheck/Constraints.lean` — the constraint encoding (Eqs. (21)–(23)): the table `w̃`, the
  batched polynomials `H₀`/`H_α` as computable `CMlPolynomialEval` Boolean-value vectors (with
  derived Mathlib multilinear views used only in algebraic proofs), Eq. (22)'s public
  `M̃_α`/`α̃` contraction and its proved equality with `H_α`'s row-defect table
  (`alphaDefect_wTable`, `hAlpha_eq_zero_iff_alphaDefect`), the sumcheck summands
  `F_{0,τ₀}`/`F_{α,τ₁}` with their per-variable degrees, `hypercubeSum`, and the direct-point
  relation `nestedRoundRel`/`nestedRoundRelE`. Shared between this zero-check and the sumcheck
  rounds (`Sumcheck/`).
* `ZeroCheck/Batch.lean` — the zero-round batching bridge: reinterprets the lift's per-row claims
  as the two identities `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatched`/`relBatchedE`, Eqs. (22)–(23)). The
  pull-back `mem_relLiftE_of_relBatchedE` (`relBatchedE → relLiftE`) recovers the per-row equation
  from `H_α ≡ 0` (via `hAlpha_eq_zero_iff` and `hAlphaEvals_rowPoint`, arity `n ≤ 2 ^ m₁`; the
  identification of `H_α` with paper Eq. (22) is `hAlpha_eq_zero_iff_alphaDefect`) and
  **derives shortness `liftShort` from `H₀ ≡ 0`** (via `hZero_eq_zero_imp_liftShort`, arity
  `(μ + n)·deg φ ≤ 2 ^ m₀` and range-base fits `b − 1 ≤ γ, ρBound`) — so shortness is proved,
  not assumed (`relBatched` carries no `liftShort` conjunct). **No relation in this folder
  does**: the admissibility that conditions `K.collision_mem` is [NOZ26] Lemma 7's
  slack-relative weak-opening data, a different notion from the range claim `liftShort`, and it
  is carried by the commitment's own opening type `LiftCom.Opening` rather than by the
  reductions above it. Figure 5's point relation is therefore as norm-free as the paper's.
* `ZeroCheck/Reduction.lean` — Hachi Figure 5 / Lemma 10: `m₀ + m₁` scalar challenge rounds
  assemble the direct points `τ₀` and `τα`. The coordinate-wise special soundness theorem
  `nestedZeroCheck_coordinateWiseSpecialSound` reduces `relBatchedE` to
  `relNestedZeroCheckE`; its extraction handles escapes, weak-binding collisions, and the common
  opening by the CompPoly binary-evaluation-tree zero test.

This umbrella re-exports the folder (`Reduction` transitively imports `Batch` and `Constraints`).
Its output relation `relNestedZeroCheckE` is the input of the sumcheck bridge in `Sumcheck/`, and
the chain is composed in `Composition.lean`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
