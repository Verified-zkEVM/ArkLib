/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Gadget.Core
import ArkLib.Commitments.Functional.Hachi.Gadget.Norms

/-!
# Ajtai Gadget Matrices

Umbrella for `Hachi/Gadget/`: the base-`b` Ajtai gadget matrix
`G = I_rows ⊗ [1, b, b², …, b^(digits-1)]` over the cyclotomic ring `Rq Φ` and its norm-reducing
inverse `G⁻¹`, the base-`b` digit decomposition of Hachi [NOZ26, §2.1]. The gadget trades one
ring element for `digits` elements with small coefficients: `G⁻¹` shortens, `G` recombines. It is
the shortness workhorse of the Greyhound [NS24] / Hachi [NOZ26] inner-outer commitment — honest
commitments consist of gadget digits (hence are short), and the verifier's checks recombine them
through `G`.

## Folder structure

* `Gadget/Core.lean` — the algebra: the gadget matrix `G` (`gadgetMatrix` / `gadgetMul`), lawful
  decompositions (`IsLawfulGadgetDecomposition`, i.e. `G · G⁻¹(x) = x`), the abstract
  per-coefficient digit map (`DigitDecomposition`) with its concrete `ZMod q` instance — the
  paper's **balanced** digits `balancedZmodDigitDecomposition`, shifted from the naive unsigned
  `zmodDigitDecomposition` — and the induced gadget inverse `gadgetDecompose` with its lawfulness
  proof.
* `Gadget/Norms.lean` — the analysis: centered `ℓ∞` / `ℓ₂²` shortness of the honest
  decomposition `G⁻¹(x)` (feeding perfect correctness in `InnerOuter/Correctness.lean`), and
  controlled norm growth of the recomposition `G·ẑ` for any range-checked `ẑ` (feeding Lemma 8
  in `QuadEval/Soundness.lean`).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
