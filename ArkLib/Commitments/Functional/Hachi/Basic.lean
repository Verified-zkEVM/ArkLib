/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Commitment
import ArkLib.Commitments.Functional.Hachi.Composition
import ArkLib.Commitments.Functional.Hachi.HonestChain
import ArkLib.Commitments.Functional.Hachi.Correctness
import ArkLib.Commitments.Functional.Hachi.Concrete
import ArkLib.Commitments.Functional.Hachi.Params
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

An opening is a chain of nine reductions carrying a polynomial-evaluation claim `f(x) = y` down
to a single evaluation claim on the committed table, closed by an end-piece that reveals that
table. Each link is certified in both security directions: coordinate-wise special soundness
(CWSS) — a witness is extracted from a structured tree of accepting transcripts, with the
cryptographic failure modes of extraction appearing as *escape events* rather than as witnesses —
and perfect completeness. `Composition.lean` chains the soundness certificates,
`HonestChain.lean` the honest provers, and `Correctness.lean` packages the result as a
`Commitment.Scheme` with perfect correctness.

Two scope facts a reader should have up front. The recursive opening of [NOZ26] §4.5 —
`Recursion/` and the `opening` field of `Commitment.lean`'s `hachi` — is outside this
development; the complete scheme is the nonrecursive `hachiNonrecursive`. And every *composed*
completeness statement rests on the generic `Reduction.append_completeness`, which this
repository admits; each link's own completeness does not.

## Folder structure

The folder is organized by paper section; each subfolder carries a `Basic.lean` umbrella
re-export, and this file is the umbrella for the whole development.

* `Gadget/` (§2.1) — the base-`b` Ajtai gadget matrix `G` and its digit-decomposition inverse
  `G⁻¹` (`Core`), with centered `ℓ∞` / `ℓ₂²` norm bounds for both directions (`Norms`). `Core`
  carries **two** decompositions, deliberately: the full-width `DigitDecomposition` for arbitrary
  residues (message and inner digits, `δ = ⌈log_b q⌉`) and the short-input
  `BoundedDigitDecomposition` for the folded witness `z`, whose digit count `τ` is set by the
  deterministic bound `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋` rather than by `q` (`τ = 5` at ArkLib's conservative
  reading of the `ℓ = 30` parameters — see `Params.lean`).
* `EvalSplit.lean` (§4, Eq. (12)) — multilinear evaluation as the vector–matrix–vector product
  `mb(xl) ⬝ᵥ (toMatrix p *ᵥ mb(xh))`.
* `InnerOuter/` (§4.1) — the inner-outer Ajtai commitment: the scheme with its weak openings
  (`Scheme`), perfect correctness (`Correctness`), the weak-binding reduction to Module-SIS
  (`Security`), and the pinned power-of-two ring (`Arithmetic`).
* `QuadEval/` (§4.2, Figure 3) — the quadratic polynomial-evaluation reduction: gadget algebra
  (`Gadgets`), protocol data and relations (`Reduction`), Lemma 8 special soundness
  (`Soundness`), completeness (`Completeness`), and the zero-round polynomial-level bridge
  (`Bridge`).
* `RingSwitch/`, `ZeroCheck/`, `Sumcheck/` (§4.3) — the HMZ25 lift, the zero-check, and the
  sumcheck loop, each with its own `Completeness.lean`.
* `EndPiece/` (§4.3, closing) — the terminal link: the prover reveals the reduced witness and the
  guarded verifier checks the evaluation claim against it directly.
* `Recursion/` (§4.5) — the partial-evaluation, packing, and trace-handoff adapters of the
  recursive opening. Outside the completed development; see `Recursion/Basic.lean`.
* `Composition.lean` — the composed soundness certificate: the `iteration` (the nine chained
  subprotocols) and `evaluation` = iteration ⧺ end-piece.
* `Commitment.lean` — the `Commitment.Scheme` interface: the multilinear eval oracle, honest
  `keygen` / `commit`, and the honest-committer facts feeding `QuadEval`'s input relation.
* `HonestChain.lean` — the honest side's parameter bookkeeping (`HonestRangeParams`) and the
  composed honest chain from the polynomial-evaluation claim through the sumcheck.
* `Correctness.lean` — the complete nonrecursive opening: the terminal reveal-and-check, the
  commitment-input adapter, the scheme `hachiNonrecursive`, and its perfect correctness.
* `Concrete.lean` — the same scheme at the concrete Ajtai lift commitment `D · (z ‖ ρ)`, where
  the whole honest run is computable; `scripts/HachiRuntime.lean` runs it.
* `Params.lean` — the [NOZ26] Figure 9 `ℓ = 30` parameters (`q = 4294967197`, `b = 16`,
  `δ = 8`, `r = m = 10`, `ω = 16`, `α = 10`) **with ArkLib's conservative `τ = 5`** in place of
  Figure 9's `τ = 4`, plus the arithmetic facts the chain consumes at them: `16⁵ < q` — the reason
  `τ` needs the bounded decomposition — and `honestZBound ≤ balancedDigitCapacity 16 5`. The `τ`
  divergence is deliberate: this development proves only the naive `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072`,
  for which `5` digits are minimal (`tau_minimal`), whereas Figure 9's `τ = 4` rests on its own
  sharper bound `30583` (not formalized here).

Importing this file brings in the whole development. A new file joins its folder umbrella; the
umbrella chain carries it here.

Generic infrastructure this builds on: the CWSS notion and its composition in
`OracleReduction/Security/CoordinateWiseSpecialSoundness/`, the cyclotomic-ring norm theory in
`Data/Lattices/CyclotomicRing/`, and the simple Ajtai commitment in
`Commitments/Ordinary/Ajtai/Simple/`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
