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

**This development is in progress.** Finished and `sorry`-free: the inner-outer commitment
(§4.1) with perfect correctness and the weak-binding reduction to Module-SIS, and the
polynomial-evaluation reduction (§4.2, Lemma 8) with its polynomial-level bridge. Still to come:
the remaining §4.3+/§4.5 subprotocols and the completeness layer (see the `TODO` blocks in
`Composition.lean` and `Commitment.lean`).

## Folder structure

The folder `Hachi/` is organized by paper section, each subfolder carrying an umbrella `.lean`
re-export next to it (as this file does for the whole folder):

* `Gadget/` (§2.1) — the base-`b` Ajtai gadget matrix `G` and its digit-decomposition inverse
  `G⁻¹` (`Basic`), with centered `ℓ∞` / `ℓ₂²` norm bounds for both directions (`Norms`).
* `EvalSplit.lean` (§4, Eq. (12)) — multilinear evaluation as the vector–matrix–vector product
  `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))`; kept top-level because the future §3 packing head reuses
  it over the subfield.
* `InnerOuter/` (§4.1) — the inner-outer Ajtai commitment: the scheme with its weak openings
  (`Scheme`), perfect correctness (`Correctness`), the weak-binding reduction to Module-SIS
  (`Security`), and the pinned power-of-two ring (`Arithmetic`).
* `QuadEval/` (§4.2, Figure 3) — the quadratic polynomial-evaluation reduction: gadget algebra
  (`Gadgets`), protocol data and relations (`Reduction`), Hachi Lemma 8 coordinate-wise special
  soundness (`Soundness`), and the zero-round polynomial-level bridge (`Bridge`).
* `Composition.lean` — the CWSS composition home: the finished core
  `evalChain = bridgePackage ▷ quadEvalPackage` with its certificate
  `eval_coordinateWiseSpecialSound`; every further subprotocol lands as one more `CWSSPackage`
  `▷`-appended there.
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
