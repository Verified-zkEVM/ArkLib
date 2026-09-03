/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Soundness
import ArkLib.Commitments.Functional.Hachi.QuadEval.Completeness
import ArkLib.Commitments.Functional.Hachi.QuadEval.Bridge

/-!
# Hachi Polynomial-Evaluation Reduction `QuadEval`

Umbrella module for `Hachi/QuadEval/`: Hachi's [NOZ26, §4.2] polynomial-evaluation reduction
(Figure 3, "Polynomial Evaluation as Quadratic Equation" — hence the name `QuadEval`). The
reduction proves an evaluation claim `f(x) = y` on an inner-outer-committed multilinear
polynomial by rewriting the evaluation as the quadratic form `bᵀ M a` (Eq. (12)) and folding the
`2ʳ` carrier blocks under the verifier's challenge vector; it is Hachi's multilinear /
inner-outer lift of Greyhound's [NS24, §3.1] folding protocol.

## Folder structure

* `QuadEval/Gadgets.lean` — the gadget algebra under the reduction: `PublicParamsD` (the
  inner-outer parameters extended with the short-commitment matrix `D`), the honest-prover
  carrier `w`/`ŵ` with its short commitment `v = D ŵ`, the `J`-decomposition of the response
  `z`, and the `tensorG` / `tensorG1` challenge combinations with the coordinate-isolation
  lemmas at the heart of the Lemma 8 extraction.
* `QuadEval/Reduction.lean` — the two-round protocol data: the statement/response/witness types,
  the challenge space `ShortChallenge`, the ordinary relations `relIn` (an eval-consistent weak
  opening) and `relOut` (Eq. (20) + the range checks) over the fixed commitment key `pp`, the
  `QuadEvalSISBreak`/`quadEvalSISSet` break vocabulary for the Module-SIS(B/D) extraction outcomes
  (validated against the same fixed `pp` — the key is a parameter, never statement data),
  the pure pass-through `verifier`, the honest `prover` parameterized by its two computations, and
  their concrete instantiation from the gadget algebra (`honestComputeV` / `honestZ` /
  `honestComputeResp`) bundled with the verifier as the computable protocol object
  `quadEvalReduction`. The `ẑ = J⁻¹(z)` step takes a **`BoundedDigitDecomposition`**: the
  folded witness is deterministically short, so its digit count `τ` is set by that bound and not
  by `q`. The correctness-only strengthening `relInMsgShort` (`relIn` plus `‖sᵢ‖∞ ≤ msgBound`)
  carries the one
  extra invariant that bound needs, with `relInMsgShort_subset_relIn` keeping the soundness-side
  relation untouched.
* `QuadEval/Soundness.lean` — **Hachi Lemma 8**: the subtract-and-divide extraction
  (`buildWitness`, split into the plain assembler `quadEvalMkWitness` and the escape event
  `quadEvalEscLocal`) and the escape-threaded coordinate-wise special soundness
  `quadEval_coordinateWiseSpecialSoundWithEscape` at the **plain** relations, bundled as the
  composable `quadEvalPackage`; also the reduction's derived norm constants `B_z` / `βSq`. Its
  one deep input is Lyubashevsky–Seiler short-element invertibility, `isUnit_of_l1Norm_le`.
* `QuadEval/Completeness.lean` — the honest direction, in **two readings** that must not be
  conflated (both at error `0`; the file's docstring is the reference):
  - *ball-relaxed*, into ArkLib's `relOut`: `quadEvalReduction_perfectCompleteness`, concretely
    `…_boundedBalancedDigits` at `τ` chosen from the honest bound;
  - *paper-exact*, into `paperRelOut` (Eq. (20) verbatim, box `S_b`):
    `quadEvalReduction_perfectCompleteness_paperRelOut`, concretely
    `…_boundedBalancedDigits_paperRelOut` at the bounded balanced digits, from the box-carrying
    input relation `relInBox`.

  The shared linear content is `honestRows_of_relIn` (Eq.-(20) rows c1–c5 at *every* challenge
  vector — hence error `0`); the deterministic shortness of `z` is `vecLInftyNorm_honestZ_le`
  (`‖z‖∞ ≤ 2ʳ·ω·msgBound`, from `ShortChallenge`'s `ℓ₁` bound and the committer's message bound);
  the range steps and the run characterization `quadEvalReduction_run_support` complete each
  reading.
  `quadEvalPackage_verifier_eq_quadEvalReduction_verifier`
  (in `Soundness.lean`) checks that the two security directions speak about the same verifier.
* `QuadEval/Bridge.lean` — the zero-round polynomial-level head: reinterprets a `CMlPolynomial`
  evaluation statement (`PolyEvalStatement`) as a `QuadEvalStatement` via the monomial tensor
  bases, with the pulled-back relation `relPolyEval` and the composable `bridgePackage`.

This umbrella re-exports the whole folder (`Soundness`, `Completeness` and `Bridge` transitively
import `Reduction` and `Gadgets`). The chain `bridgePackage ▷ quadEvalPackage` is composed in the
sibling `Composition.lean`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
