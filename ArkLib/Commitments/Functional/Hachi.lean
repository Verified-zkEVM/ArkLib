/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Commitment
import ArkLib.Commitments.Functional.Hachi.Composition

/-!
# Hachi: a Lattice-Based Multilinear Polynomial Commitment

Formalization of the Hachi [NOZ26] functional commitment — a lattice-based commitment to
multilinear polynomials with evaluation-opening proofs, built on the Greyhound [NS24]
inner-outer Ajtai commitment over the power-of-two cyclotomic ring `Z_q[X] / (X^{2^α} + 1)`.

**This development is in progress.** Finished and `sorry`-free — axiom-clean down to the
Lyubashevsky–Seiler short-element invertibility (`isUnit_of_l1Norm_le`) the soundness rests on,
which is itself proven, not deferred: the inner-outer commitment (§4.1) with perfect correctness
and the weak-binding reduction to Module-SIS, and the polynomial-evaluation reduction
(§4.2, Lemma 8) with its polynomial-level bridge. The §4.3/§4.5 opening subprotocols are in the
tree as sorried skeletons, inventoried link by link in `Composition.lean`; still to come are their
proofs and the completeness layer — the honest-prover `opening` (`hachi.opening` in
`Commitment.lean`). See the `TODO` blocks in `Composition.lean` and `Commitment.lean`.

## Folder structure

The folder `Hachi/` is organized by paper section. Each subfolder carries a `Basic.lean`
umbrella re-export inside the folder (as this file does for the whole Hachi development):

* `Gadget/` (§2.1) — the base-`b` Ajtai gadget matrix `G` and its digit-decomposition inverse
  `G⁻¹` (`Core`), with centered `ℓ∞` / `ℓ₂²` norm bounds for both directions (`Norms`).
* `EvalSplit.lean` (§4, Eq. (12)) — multilinear evaluation as the vector–matrix–vector product
  `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))`; kept top-level because the future §3 packing head reuses
  it over the subfield.
* `InnerOuter/` (§4.1) — the inner-outer Ajtai commitment: the scheme with its weak openings
  (`Scheme`), perfect correctness (`Correctness`), the weak-binding reduction to Module-SIS
  (`Security`), and the pinned power-of-two ring (`Arithmetic`).
* `QuadEval/` (§4.2, Figure 3) — the quadratic polynomial-evaluation reduction: gadget algebra
  (`Gadgets`), protocol data and relations (`Reduction`), Hachi Lemma 8 coordinate-wise special
  soundness (`Soundness`), and the zero-round polynomial-level bridge (`Bridge`).
* `RingSwitch/`, `ZeroCheck/`, and `Sumcheck/` (§4.3) — the lift, corrected zero-check, and
  guarded sumcheck stages of the opening chain.
* `Recursion/` (§4.5) — the partial-evaluation, packing, and trace-handoff adapters that close
  one iteration at the next ring's plain `QuadEval.relIn` relation.
* `Composition.lean` — the CWSS composition home: `evalChain = bridgePackage ▷
  quadEvalPackage`, followed by the opening subprotocols. Every package exposes the ordinary
  `relIn` / `relOut` flow; the cryptographic failure modes of extraction (`QuadEval`'s Module-SIS
  break, the weak-binding collisions of Figures 4–6) are **escape events** on the transcript tree,
  entering each certificate as a disjunct of its conclusion.
* `Commitment.lean` — Hachi as a `Commitment.Scheme`: the multilinear eval-oracle interface and
  the honest `keygen` / `commit` (the opening `Proof` is a documented `sorry` pending the
  remaining subprotocols).

Generic infrastructure the development builds on: the coordinate-wise-special-soundness notion
and its composition live in `OracleReduction/Security/CoordinateWiseSpecialSoundness/`, the
cyclotomic-ring norm theory in `Data/Lattices/CyclotomicRing/`, and the simple Ajtai commitment
in `Commitments/Ordinary/Ajtai/Simple/`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
