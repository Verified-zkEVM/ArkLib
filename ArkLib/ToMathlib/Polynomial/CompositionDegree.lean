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

/-- Composing with the scaling `X ↦ a * X` does not increase the natural degree.

This is the specialization of Mathlib's `Polynomial.natDegree_comp_le` to a composand of
degree at most one, and is proved as such. -/
lemma natDegree_comp_C_mul_X_le (p : F[X]) (a : F) :
    (p.comp (C a * X)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans <| by
    calc p.natDegree * (C a * X).natDegree
        ≤ p.natDegree * 1 := by
          gcongr
          exact (natDegree_C_mul_le a X).trans natDegree_X_le
      _ = p.natDegree := mul_one _

end Polynomial
