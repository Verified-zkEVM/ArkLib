/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Commitments.Functional.Hachi.TraceHead.Commitment

/-!
# Scalar trace head

`Coordinates` instantiates finite-free packing over the fixed subring with the `psi` basis.
`Coefficients` packs the final variables' monomial coefficients. `Protocol` sends one ring
value, checks the scaled trace equality, and forwards the weak opening to `relPolyEval`.
`Completeness` and `Commitment` supply honest execution and balanced-gadget commitment
coverage, including the additional message bound for the nonrecursive opening chain.

The construction uses the fixed subring as a ring; the field identification in
`Subfield/Field.lean` is a separate, unfinished result. The finite-sum `traceH` and fixed-subring
operations are noncomputable, so these semantic protocols do not supply an executable scalar
opening scheme. The recursive trace handoff of [NOZ26] §4.5 has separate proof obligations.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/
