/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!

# The Plonk Protocol

We aim to formalize the Plonk protocol (as a polynomial IOP) as stated in the original
Plonk paper [GWZC19].

As we do so, we will break down Plonk into modular components, such as . We also plan to formalize
various extensions of Plonk, such as Maller's optimization trick (which can be seen as a change on
the PIOP level), integration with lookup arguments (i.e. logup), high-degree constraints, and more.

## References

* [Gabizon, A., Williamson, Z.J., and Ciobotaru, O., *Plonk: Permutations over lagrange-bases
    for oecumenical noninteractive arguments of knowledge*][GWZC19]

-/

@[expose] public section

namespace Plonk

section AuxiliaryPolynomials

/-! ## Auxiliary polynomials in Plonk-/



end AuxiliaryPolynomials

/-! ## Protocol Structure

The Plonk protocol
-/

end Plonk
