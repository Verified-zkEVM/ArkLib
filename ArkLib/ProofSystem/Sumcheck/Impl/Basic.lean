/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.Data.MlPoly.Equiv

/-!
  # Executable Spec of the Sum-check Protocol

This file contains the basic implementation of the sum-check protocol. Instead of viewing the
protocol purely as a non-computable specification in terms of `MvPolynomial`, we give the standard
algorithms (linear time & streaming) for the setting of:
- A number of computable multilinear polynomials `p : ι → MlPoly R`
- A combination function `f` that is itself a (very simple) computable multivariate polynomial
  `f : CMvPoly ι R`. (pending merge from Plonky3's development by Nethermind)

Future extensions will include optimized variants for various protocols (well, to the extent that
they change the verifier, since we don't care too much about prover's efficiency):
- Not sending evaluation at 0/1
- Sending evaluation at infinity instead
-/

namespace Sumcheck

namespace Impl

end Impl

end Sumcheck
