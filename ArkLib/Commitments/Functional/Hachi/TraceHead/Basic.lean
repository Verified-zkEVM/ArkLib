/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Commitments.Functional.Hachi.TraceHead.Commitment

/-!
# Scalar trace head

`Coefficients` packs the final variables' monomial coefficients over the fixed subring, as the
shared `RingSwitching.Packing` `packedMLE` of a monomial-coefficient `ScalarHead.ClaimLayout`
with one opening coordinate. `Coordinates` indexes `psi` by the monomials and turns the scaled
trace equality into a coefficient inner product. `Protocol` sends one ring value, checks the
scaled trace equality, and forwards the weak opening to `relPolyEval`; its read-back is a
`CheckedObservation`.
`Completeness` and `Commitment` supply honest execution and balanced-gadget commitment
coverage, including the additional message bound for the nonrecursive opening chain.

The construction uses the fixed subring as a ring and does not use its field identification
(`Subfield/Field.lean`). The verifier is stated with the noncomputable `traceH`; the computable
`traceHComp` agrees with it (`traceHComp_eq`), but the protocol is not wired to it. The recursive
trace handoff of [NOZ26] §4.5 has separate proof obligations.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section
