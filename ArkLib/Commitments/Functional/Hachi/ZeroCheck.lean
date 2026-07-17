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
  batched-sumcheck machinery. The `M̃_α` contraction `hAlphaEvals` is now **concrete** — the
  `α`-evaluated per-row lift defect (row-encoded into the `m₁`-cube), so `H_α` is a genuine
  batched polynomial with meaningful coefficients (`hAlphaEvals_rowPoint`, axiom-clean). The table
  entry function `wTable` is now **concrete** too (it reads the committed `z`/`ρ` coefficients
  directly, so `H₀` non-vacuously tests shortness of the committed data). Only the range-side
  soundness (`H₀ ≡ 0 ⇒ liftShort`) and the sumcheck-polynomial stubs remain F5.
* `ZeroCheck/Batch.lean` — the zero-round **batching bridge** (entry head): reinterprets the lift's
  per-row residual claims as the two `MvPolynomial` identities `H₀ ≡ 0 ∧ H_α ≡ 0`
  (`relBatched`/`relBatchedE`, Eqs. (22)–(23)); the un-batching pull-back
  `mem_relLiftE_of_relBatchedE` (`relBatchedE → relLiftE`, arity pin `n ≤ 2 ^ m₁`) is
  **proof-`sorry`-free** (via `MLE_eq_zero_iff` + `hAlphaEvals_rowPoint`; the residual `sorryAx` is
  only the `wTable`/`H₀` conjunct in its statement type).
* `ZeroCheck/Reduction.lean` — **Hachi Figure 5 / corrected Lemma 10**: one challenge round
  carrying the seed pair `(ρ₀, ρ_α) ∈ F²`, reducing the identities to point evaluations at the
  derived Kronecker points. The CWSS theorem `zeroCheck_coordinateWiseSpecialSound` (`relBatchedE
  → relZeroCheckE`, `k = D = zeroCheckD m₀ m₁`) is **`sorry`-free and now axiom-clean** — its
  escape/collision/root-counting extraction is complete, and with the encodings `hAlphaEvals`/
  `wTable` now concrete, `#print axioms` reports no `sorryAx` (only the ambient
  `propext`/`Classical.choice`/`Quot.sound`; the `Classical.choice` is from the classical-choice
  branch selection in `buildWitnessE`, the documented constructivity caveat). The Kronecker kernel
  `arm_eq_zero_of_family` is likewise axiom-clean.

This umbrella re-exports the folder (`Reduction` transitively imports `Batch` and `Constraints`).
Its output relation `relZeroCheckE` is the input of the sumcheck bridge in `Sumcheck/`; the chain
is composed in `Composition.lean` (`openCore`, row 6).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
