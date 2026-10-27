/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import CompPoly.Univariate.Raw.Proofs

import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops

/-!
# Sizes of raw polynomial products
-/

@[expose] public section

namespace CompPoly.CPolynomial.Raw
/-- A raw scalar stores one coefficient even when that coefficient is zero. -/
@[simp]
theorem size_C {R : Type*} (x : R) : (C x).size = 1 := by rfl

/-- Scalar multiplication preserves the coefficient count. -/
@[simp]
theorem size_smul {R : Type*} [Mul R] (x : R) (p : Raw R) :
    (smul x p).size = p.size := by simp [smul]

/-- Multiplication by a power of `X` retains every prepended zero. -/
@[simp]
theorem size_mulPowX {R : Type*} [Zero R] (i : ℕ) (p : Raw R) :
    (mulPowX i p).size = i + p.size := by simp [mulPowX]

/-- Padded addition stores the larger input size. -/
theorem size_addRaw {R : Type*} [Zero R] [Add R] (p q : Raw R) :
    (addRaw p q).size = max p.size q.size := by
  simp [addRaw, Array.size_rightpad, max_comm]

variable {R : Type*} [Semiring R]

/-- Raw convolution retains every shifted row, including padding from an empty right array. -/
theorem size_mulRaw (p q : Raw R) :
    (mulRaw p q).size = if p.size = 0 then 0 else q.size + p.size - 1 := by
  unfold mulRaw
  have h := Array.foldl_induction (as := p.zipIdx)
    (motive := fun i (acc : Raw R) ↦ acc.size = if i = 0 then 0 else q.size + i - 1)
    (init := mk #[]) (by rfl)
    (f := fun acc ai ↦ acc.addRaw ((smul ai.1 q).mulPowX ai.2)) ?_
  · simpa only [Array.size_zipIdx] using h
  · intro i acc ih
    have hz : (p.zipIdx)[i].2 = i.val := by
      change ((p.zipIdx)[i.val]'i.isLt).2 = i.val
      rw [Array.getElem_zipIdx]
      exact Nat.zero_add _
    simp only [add_size, mulPowX, smul, Array.size_append, Array.size_replicate, Array.size_map]
    rw [hz, ih]
    by_cases hi : i.val = 0
    · simp [hi]
    · simp [hi]
      omega

/-- The padded convolution has at most the sum of the input sizes minus one coefficients. -/
theorem size_mulRaw_le (p q : Raw R) :
    (mulRaw p q).size ≤ p.size + q.size - 1 := by
  rw [size_mulRaw]
  split_ifs <;> omega

end CompPoly.CPolynomial.Raw
