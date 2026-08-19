/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Commitment
import ArkLib.Commitments.Functional.Hachi.Composition
import ArkLib.Commitments.Functional.Hachi.HonestChain
import ArkLib.Commitments.Functional.Hachi.Gadget.Basic
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Basic
import ArkLib.Commitments.Functional.Hachi.QuadEval.Basic
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Basic
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Basic
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Basic
import ArkLib.Commitments.Functional.Hachi.Recursion.Basic

/-!
# Hachi: a Lattice-Based Multilinear Polynomial Commitment

Formalization of the Hachi [NOZ26] functional commitment — a lattice-based commitment to
multilinear polynomials with evaluation-opening proofs, built on the Greyhound [NS24]
inner-outer Ajtai commitment over the power-of-two cyclotomic ring `Z_q[X] / (X^{2^α} + 1)`.

**This development is in progress.** Finished and `sorry`-free — axiom-clean down to the
Lyubashevsky–Seiler short-element invertibility (`isUnit_of_l1Norm_le`) the soundness rests on,
which is itself proven, not deferred: the inner-outer commitment (§4.1) with perfect correctness
and the weak-binding reduction to Module-SIS, the polynomial-evaluation reduction
(§4.2, Lemma 8) with its polynomial-level bridge, and **the whole §4.3 opening chain** — the
`R^lin` adapter, the HMZ25 lift (Lemma 9), the batching bridge, the corrected zero-check
(Lemma 10), the sumcheck bridge, the paired sumcheck rounds (Lemma 11) and the final evaluation —
together with their composite, the one-iteration certificate
`hachi_iteration_coordinateWiseSpecialSoundWithEscape`, and the closing `endPiece` (`EndPiece/`)
that consumes that iteration's evaluation claim — `sorry`-free and axiom-clean, as is the
composite `evaluation`. What is still open: the
completeness layer — the honest-prover `opening` (`hachi.opening` in `Commitment.lean`), whose
first two links are in place: the zero-check (Figure 5) in `ZeroCheck/Completeness.lean` and the
polynomial-evaluation reduction (Figure 3) in `QuadEval/Completeness.lean` are both proved
perfectly complete — and the §4.5 `Recursion/` adapters, separate future work with
their own sorries and a documented soundness gap described in `Recursion/Basic.lean`. See the
`TODO` blocks in `Composition.lean` and `Commitment.lean`.

## Folder structure

The folder `Hachi/` is organized by paper section. Each subfolder carries a `Basic.lean`
umbrella re-export inside the folder, and this file is that umbrella for the whole Hachi
development:

* `Gadget/` (§2.1) — the base-`b` Ajtai gadget matrix `G` and its digit-decomposition inverse
  `G⁻¹` (`Core`), with centered `ℓ∞` / `ℓ₂²` norm bounds for both directions (`Norms`).
* `EvalSplit.lean` (§4, Eq. (12)) — multilinear evaluation as the vector–matrix–vector product
  `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))`; kept top-level because the future §3 packing head reuses
  it over the subfield.
* `InnerOuter/` (§4.1) — the inner-outer Ajtai commitment: the scheme with its weak openings
  (`Scheme`), perfect correctness (`Correctness`), the weak-binding reduction to Module-SIS
  (`Security`), and the pinned power-of-two ring (`Arithmetic`).
* `QuadEval/` (§4.2, Figure 3) — the quadratic polynomial-evaluation reduction: gadget algebra
  (`Gadgets`), protocol data, relations and the honest protocol object (`Reduction`), Hachi Lemma 8
  coordinate-wise special soundness (`Soundness`), completeness (`Completeness` — both the
  ball-relaxed reading at `relOut` and the paper-exact one at `paperRelOut`; see that file), and the
  zero-round polynomial-level bridge (`Bridge`, itself proved in both directions:
  `bridge_coordinateWiseSpecialSoundWith` and `bridgeReduction_perfectCompleteness`).
* `RingSwitch/`, `ZeroCheck/`, and `Sumcheck/` (§4.3) — the lift, corrected zero-check, and
  guarded sumcheck stages of the opening chain. `RingSwitch/` and `ZeroCheck/` are proved in both
  directions (`…/Completeness.lean` each; the lift's honest direction is conditional on the range
  check of its honest lifted witness); `Sumcheck/`'s completeness is still open.
* `EndPiece/` (§4.3, closing) — the terminal link: the prover reveals the reduced witness and the
  guarded verifier checks the evaluation claim against it directly. Escape-free, `sorry`-free and
  axiom-clean (`Reduction`, re-exported by `Basic`).
* `Recursion/` (§4.5) — the partial-evaluation, packing, and trace-handoff adapters that would
  close one iteration at the next ring's plain `QuadEval.relIn` relation (future recursion work;
  not yet composed in `Composition.lean`).
* `Composition.lean` — the CWSS composition home: the `iteration` (the chained subprotocols,
  rows 1–9), the imported `endPiece`, and the complete
  `evaluation` = iteration ⧺ end-piece. Every package exposes the ordinary
  `relIn` / `relOut` flow; the cryptographic failure modes of extraction (`QuadEval`'s Module-SIS
  break, the weak-binding collisions of Figures 4–6) are **escape events** on the transcript tree,
  entering each certificate as a disjunct of its conclusion.
* `Commitment.lean` — Hachi as a `Commitment.Scheme`: the multilinear eval-oracle interface and
  the honest `keygen` / `commit` (the opening `Proof` is a documented `sorry` pending the
  remaining subprotocols), plus the honest-committer facts the honest chain consumes: the honest
  opening as a `WeakBinding.VerifiedOpening`, its balanced-box membership, and
  `mem_relInBox_of_honestBalanced` — paper-exact `QuadEval`'s input relation established for the
  balanced-digit committer.
* `HonestChain.lean` — the honest side's parameter bookkeeping: `HonestRangeParams` (digit base,
  Eq. (20) ball radius, zero-check range base, with the relations the seams need, and a proof that
  they are satisfiable) and the per-seam corollaries restating each link's completeness at those
  parameters. Its docstring records the one genuine limitation: at a single shared range base the
  seams pin `γ = q/2`, because the honest lift quotient is not short.

This file is the folder's **re-export hub**: it imports every per-folder umbrella
(`Gadget/`, `InnerOuter/`, `QuadEval/`, `RingSwitch/`, `ZeroCheck/`, `Sumcheck/`, `Recursion/`
`Basic.lean`), each of which re-exports its own leaves — soundness *and* completeness. So
`import ArkLib.Commitments.Functional.Hachi` brings in the whole development, and no Hachi file
depends on the generated root `ArkLib.lean` to be reachable. Adding a file to this tree means adding
it to its folder umbrella; the umbrella chain then carries it here.

Generic infrastructure the development builds on: the coordinate-wise-special-soundness notion
and its composition live in `OracleReduction/Security/CoordinateWiseSpecialSoundness/`, the
cyclotomic-ring norm theory in `Data/Lattices/CyclotomicRing/`, and the simple Ajtai commitment
in `Commitments/Ordinary/Ajtai/Simple/`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
