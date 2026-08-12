/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Degree of a polynomial composed with a scaling

Substituting `a * X` for `X` cannot raise the degree, since the substituted polynomial has
degree at most one. This is the corresponding specialization of `natDegree_comp_le`.

## Main statements

* `Polynomial.natDegree_comp_C_mul_X_le`: `(p.comp (C a * X)).natDegree ≤ p.natDegree`.

## Tags

polynomial, degree, composition
-/

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- Composing with the scaling `X ↦ a * X` does not increase the natural degree.

This is `natDegree_comp_le` for a composand of degree at most one. -/
lemma natDegree_comp_C_mul_X_le (p : R[X]) (a : R) :
    (p.comp (C a * X)).natDegree ≤ p.natDegree :=
  natDegree_comp_le.trans <| by
    calc p.natDegree * (C a * X).natDegree
        ≤ p.natDegree * 1 := by
          gcongr
          exact (natDegree_C_mul_le a X).trans natDegree_X_le
      _ = p.natDegree := mul_one _

end Polynomial
