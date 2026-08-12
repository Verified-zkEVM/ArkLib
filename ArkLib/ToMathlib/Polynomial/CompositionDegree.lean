/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Additional polynomial composition-degree lemmas

## Main statements

* `Polynomial.natDegree_comp_C_mul_X_le` — composing with a scaling `X ↦ a * X` does not
  increase the degree.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

namespace Polynomial

variable {F : Type*} [Semiring F]

/-- Composing with the scaling `X ↦ a * X` does not increase the natural degree. -/
lemma natDegree_comp_C_mul_X_le (p : F[X]) (a : F) :
    (p.comp (C a * X)).natDegree ≤ p.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hm => by
    simp [comp_C_mul_X_coeff, coeff_eq_zero_of_natDegree_lt hm]

end Polynomial
