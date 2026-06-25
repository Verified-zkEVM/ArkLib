/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Correctness
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security

/-!
# Inner-Outer Ajtai Commitment

Re-exports the Greyhound [NS24] / Hachi [NOZ26] inner-outer Ajtai commitment scheme, its
perfect correctness, and its weak-binding reduction to Module-SIS, over the cyclotomic ring
`Rq Φ`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
