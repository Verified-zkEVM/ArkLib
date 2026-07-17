/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction

/-!
# Hachi Zero-Check (Figure 5 / corrected Lemma 10)

Umbrella for `Hachi/ZeroCheck/`: the batched-constraint encoding (Hachi [NOZ26] Eqs. (21)–(23))
and the zero-check subprotocol that reduces the two polynomial identities `H₀ ≡ 0 ∧ H_α ≡ 0` — the
range constraints and the `α`-evaluated linear constraints, both `eq̃`-batched — to their
evaluations at random points.

## ⚠ The paper's Lemma 10 is repaired here

Hachi's Lemma 10 (uniform-vector-challenge extraction) is **not provable as stated**: a
coordinate-wise star certifies only axis-cross vanishing, and for `m ≥ 2` that does not imply
`H ≡ 0`. `ZeroCheck/Reduction.lean` implements the adopted repair — two scalar **Kronecker seeds**
`(ρ₀, ρ_α)`, with the evaluation points derived on the curves `κ_m(ρ) = (ρ, ρ², ρ⁴, …)`, where
univariate root counting is information-complete. The formal counterexample to the paper's
argument is `LinearMvExtension.exists_nonzero_vanishing_on_axis_cross`; the specification boundary
is recorded in `docs/kb/audits/noz26-zero-check-lemma10.md`.

## Folder structure

* `ZeroCheck/Constraints.lean` — the **shared constraint encoding** (Eqs. (21)–(23)): the table
  `w̃`, the batched polynomials `H₀`/`H_α` (genuine `MvPolynomial.MLE`s, so their multilinearity
  is `sorry`-free), the sumcheck polynomials `F_{0,τ₀}`/`F_{α,τ₁}` with their degree pins, the
  Kronecker point `kroneckerPoint`, `hypercubeSum`, and `roundRel`/`roundRelE`. Consumed by both
  this zero-check *and* the sumcheck round loop (`Sumcheck/`), so it sits at the shared base of the
  batched-sumcheck machinery. The table entry function `wTable` and the `M̃_α` contraction
  `hAlphaEvals` (the genuine F5 index bookkeeping) and the sumcheck-polynomial stubs remain
  `sorry`.
* `ZeroCheck/Batch.lean` — the zero-round **batching bridge** (entry head): reinterprets the lift's
  per-row/per-entry residual claims as the two `MvPolynomial` identities `H₀ ≡ 0 ∧ H_α ≡ 0`
  (`relBatched`/`relBatchedE`, Eqs. (22)–(23)); the un-batching pull-back
  `mem_relLiftE_of_relBatchedE` is the sorried F6 content.
* `ZeroCheck/Reduction.lean` — **Hachi Figure 5 / corrected Lemma 10**: one challenge round
  carrying the seed pair `(ρ₀, ρ_α) ∈ F²`, reducing the identities to point evaluations at the
  derived Kronecker points. The CWSS theorem `zeroCheck_coordinateWiseSpecialSound` (`relBatchedE
  → relZeroCheckE`, `k = D = zeroCheckD m₀ m₁`) is **proof-`sorry`-free** — its escape/collision/
  root-counting extraction is complete; it is not *axiom-clean* only because `hZero`/`hAlpha` are
  built on the still-`sorry` F5 encodings. The Kronecker kernel `arm_eq_zero_of_family` is
  axiom-clean.

This umbrella re-exports the folder (`Reduction` transitively imports `Batch` and `Constraints`).
Its output relation `relZeroCheckE` is the input of the sumcheck bridge in `Sumcheck/`; the chain
is composed in `Composition.lean` (`openCore`, row 6).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
