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
`eq̃`-batched range constraints and `α`-evaluated linear constraints — to evaluations at derived
points.

## Deviation from the paper's Lemma 10

The paper's Lemma 10 argues extraction from uniform vector challenges, but a coordinate-wise
family of accepting transcripts only certifies that `H` vanishes on an axis cross, which for
`m ≥ 2` does not imply `H ≡ 0`. `ZeroCheck/Reduction.lean` instead draws two scalar seeds
`(ρ₀, ρ_α)` and derives the evaluation points along the Kronecker curves
`κ_m(ρ) = (ρ, ρ², ρ⁴, …)`, where root counting determines a multilinear polynomial. The
counterexample to the uniform-challenge argument is
`LinearMvExtension.exists_nonzero_vanishing_on_axis_cross`, and the deviation is recorded in
`docs/kb/audits/noz26-zero-check-lemma10.md`.

## Folder structure

* `ZeroCheck/Constraints.lean` — the constraint encoding (Eqs. (21)–(23)): the table `w̃`, the
  batched polynomials `H₀`/`H_α` as computable `CMlPolynomialEval` Boolean-value vectors (with
  derived Mathlib multilinear views for Kronecker root counting), the sumcheck summands
  `F_{0,τ₀}`/`F_{α,τ₁}` with their per-variable degrees, `kroneckerPoint`, `hypercubeSum`, and the
  per-round relation `roundRel`/`roundRelE`. Shared between this zero-check and the sumcheck rounds
  (`Sumcheck/`).
* `ZeroCheck/Batch.lean` — the zero-round batching bridge: reinterprets the lift's per-row claims
  as the two identities `H₀ ≡ 0 ∧ H_α ≡ 0` (`relBatched`/`relBatchedE`, Eqs. (22)–(23)). The
  pull-back `mem_relLiftE_of_relBatchedE` (`relBatchedE → relLiftE`) recovers the per-row equation
  from `H_α ≡ 0` (via `hAlpha_eq_zero_iff` and `hAlphaEvals_rowPoint`, arity `n ≤ 2 ^ m₁`) and
  **derives shortness `liftShort` from `H₀ ≡ 0`** (via `hZero_eq_zero_imp_liftShort`, arity
  `(μ + n)·deg φ ≤ 2 ^ m₀` and range-base fits `b − 1 ≤ γ, ρBound`) — so shortness is proved,
  not assumed (`relBatched` no longer carries a `liftShort` conjunct). At the point-check and
  sumcheck seams, however, `relZeroCheck`/`roundRel` temporarily carry `liftShort` as a semantic
  admissibility condition: their point and partial-sum claims do not suffice to derive the norm
  precondition required by `K.collision_mem`.
* `ZeroCheck/Reduction.lean` — Hachi Figure 5 / Lemma 10: one challenge round carrying the seed
  pair `(ρ₀, ρ_α) ∈ F²`, reducing the identities to point evaluations at the derived Kronecker
  points. The coordinate-wise special soundness theorem
  `zeroCheck_coordinateWiseSpecialSound` reduces `relBatchedE` to `relZeroCheckE` with
  `k = D = zeroCheckD m₀ m₁`, its extraction handling escapes, weak-binding collisions, and
  Kronecker root counting (`arm_eq_zero_of_family`).

This umbrella re-exports the folder (`Reduction` transitively imports `Batch` and `Constraints`).
Its output relation `relZeroCheckE` is the input of the sumcheck bridge in `Sumcheck/`, and the
chain is composed in `Composition.lean`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
