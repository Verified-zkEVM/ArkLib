/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Univariate.Raw.Size
public import CompPoly.Univariate.Basic

import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Coefficient-array bounds for canonical polynomials
-/

@[expose] public section

namespace CompPoly.CPolynomial

/-- A canonical constant stores at most one coefficient. -/
theorem size_C_le {R : Type} [Zero R] [BEq R] [LawfulBEq R] (x : R) :
    (C x).val.size ≤ 1 := by
  change (Raw.C x).trim.size ≤ 1
  simpa only [Raw.C, Array.size_singleton] using Raw.Trim.size_le_size (Raw.C x)

/-- Canonical subtraction stores at most the larger input size. -/
theorem size_sub_le {R : Type} [Ring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : (p - q).val.size ≤ max p.val.size q.val.size := by
  change (Raw.addRaw p.val (Raw.neg q.val)).trim.size ≤ _
  refine (Raw.Trim.size_le_size _).trans ?_
  rw [Raw.add_size]
  simp only [Raw.neg, Array.size_map, le_refl]

/-- The variable polynomial stores its zero constant and unit linear coefficient. -/
@[simp]
theorem size_X {R : Type} [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).val.size = 2 := by rfl

/-- A linear monic factor stores at most two coefficients. -/
theorem size_X_sub_C_le {R : Type} [Ring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (x : R) : (X - C x).val.size ≤ 2 := by
  refine (size_sub_le X (C x)).trans ?_
  apply max_le _ (le_trans (size_C_le x) (by decide))
  rfl

/-- A canonical coefficient array has at most one more entry than its natural degree. -/
theorem size_le_natDegree_add_one {R : Type} [Zero R] (p : CPolynomial R) :
    p.val.size ≤ p.natDegree + 1 := by
  cases hs : p.val.size <;> simp [natDegree, hs]

/-- A strict natural-degree bound bounds the stored coefficient count. -/
theorem size_le_of_natDegree_lt {R : Type} [Zero R] (p : CPolynomial R) {d : ℕ}
    (h : p.natDegree < d) : p.val.size ≤ d :=
  (size_le_natDegree_add_one p).trans (Nat.succ_le_of_lt h)

/-- Canonical multiplication stores no more coefficients than its padded convolution. -/
theorem size_mul_le {R : Type} [Semiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) : (p * q).val.size ≤ p.val.size + q.val.size - 1 := by
  exact (Raw.Trim.size_le_size _).trans (Raw.size_mulRaw_le _ _)

end CompPoly.CPolynomial
