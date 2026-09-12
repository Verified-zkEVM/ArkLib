/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Multivariate.Restrict

/-!
# Executable coordinatewise box truncation

Sparse polynomials represent the canonical coefficient vectors for the parameter box
`0 ≤ eᵢ < N`. Multiplication is ordinary stored polynomial multiplication followed by
coordinatewise filtering. In particular mixed terms are retained even when their total
degree is at least `N`. This module supplies coefficient refinement and canonical bounds;
it does not equip the truncated space with field structure or implement Taylor decoding.
-/

@[expose] public section

namespace CPoly.BoxTruncation

variable {r : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Every coordinate of the stored exponent vector is strictly below the precision. -/
def InBox (N : ℕ) (m : CMvMonomial r) : Prop := ∀ i : Fin r, m.degreeOf i < N

instance (N : ℕ) (m : CMvMonomial r) : Decidable (InBox N m) :=
  inferInstanceAs (Decidable (∀ i : Fin r, m.degreeOf i < N))

/-- Executable sparse filtering; this also handles precision zero without subtraction. -/
def truncate (N : ℕ) (p : CMvPolynomial r R) : CMvPolynomial r R :=
  p.restrictBy (InBox N)

/-- Addition followed by canonical box reduction. -/
def add (N : ℕ) (p q : CMvPolynomial r R) : CMvPolynomial r R :=
  truncate N (p + q)

/-- Multiplication in the parameter box, with overflow in any coordinate discarded. -/
def mul (N : ℕ) (p q : CMvPolynomial r R) : CMvPolynomial r R :=
  truncate N (p * q)

/-- Exact coefficient specification for the executable filter. -/
@[simp] theorem coeff_truncate (N : ℕ) (p : CMvPolynomial r R) (m : CMvMonomial r) :
    (truncate N p).coeff m = if InBox N m then p.coeff m else 0 :=
  coeff_restrictBy (InBox N) m p

/-- Semantic refinement in Mathlib's polynomial representation. -/
theorem coeff_semantics (N : ℕ) (p : CMvPolynomial r R) (m : Fin r →₀ ℕ) :
    MvPolynomial.coeff m (fromCMvPolynomial (truncate N p)) =
      if ∀ i, m i < N then MvPolynomial.coeff m (fromCMvPolynomial p) else 0 := by
  simp only [coeff_eq, coeff_truncate]
  simp [InBox, CMvMonomial.degreeOf, CMvMonomial.ofFinsupp]

/-- A nonzero output coefficient has every exponent below the box precision. -/
theorem canonical_bound (N : ℕ) (p : CMvPolynomial r R) (m : CMvMonomial r)
    (h : (truncate N p).coeff m ≠ 0) : InBox N m := by
  by_contra hn
  simp [hn] at h

/-- The semantic support lies in the coordinatewise box. -/
theorem support_bound (N : ℕ) (p : CMvPolynomial r R) (m : Fin r →₀ ℕ)
    (h : m ∈ (fromCMvPolynomial (truncate N p)).support) : ∀ i, m i < N := by
  have hn := MvPolynomial.mem_support_iff.mp h
  by_contra hb
  exact hn (by simp [coeff_semantics, hb])

/-- Canonical box reduction is idempotent. -/
@[simp] theorem truncate_idempotent (N : ℕ) (p : CMvPolynomial r R) :
    truncate N (truncate N p) = truncate N p := by
  apply CMvPolynomial.ext
  intro m
  simp only [coeff_truncate]
  split_ifs <;> rfl

/-- Filtering commutes with addition. -/
theorem truncate_add (N : ℕ) (p q : CMvPolynomial r R) :
    truncate N (p + q) = truncate N p + truncate N q := by
  apply CMvPolynomial.ext
  intro m
  simp only [coeff_truncate, CMvPolynomial.coeff_add]
  split_ifs <;> simp

/-- Addition depends only on the canonical input representatives. -/
theorem add_truncate (N : ℕ) (p q : CMvPolynomial r R) :
    add N (truncate N p) (truncate N q) = add N p q := by
  simp [add, ← truncate_add]

/-- Truncated multiplication refines ordinary semantic multiplication inside the box. -/
theorem coeff_mul_semantics (N : ℕ) (p q : CMvPolynomial r R) (m : Fin r →₀ ℕ) :
    MvPolynomial.coeff m (fromCMvPolynomial (mul N p q)) =
      if ∀ i, m i < N then
        MvPolynomial.coeff m (fromCMvPolynomial p * fromCMvPolynomial q) else 0 := by
  simp only [mul, coeff_semantics, CPoly.map_mul]

/-- Discarding overflow terms before multiplication does not alter box coefficients. -/
theorem mul_truncate_left (N : ℕ) (p q : CMvPolynomial r R) :
    mul N (truncate N p) q = mul N p q := by
  apply eq_iff_fromCMvPolynomial.mpr
  apply MvPolynomial.ext
  intro m
  simp only [coeff_mul_semantics]
  by_cases hm : ∀ i, m i < N
  · simp only [if_pos hm, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' : ab.1 + ab.2 = m := Finset.mem_antidiagonal.mp hab
    have ha : ∀ i, ab.1 i < N := by
      intro i
      have hi := congrArg (fun e : Fin r →₀ ℕ => e i) hab'
      simp only [Finsupp.add_apply] at hi
      have := hm i
      omega
    rw [coeff_semantics, if_pos ha]
  · simp [hm]

/-- Truncated multiplication is commutative over a commutative coefficient semiring. -/
theorem mul_comm (N : ℕ) (p q : CMvPolynomial r R) : mul N p q = mul N q p := by
  simp only [mul, _root_.mul_comm]

/-- Input reduction on the right likewise preserves the result. -/
theorem mul_truncate_right (N : ℕ) (p q : CMvPolynomial r R) :
    mul N p (truncate N q) = mul N p q := by
  rw [mul_comm, mul_truncate_left, mul_comm]

/-- Overflow reduction is compatible with associativity of multiplication. -/
theorem mul_assoc (N : ℕ) (p q s : CMvPolynomial r R) :
    mul N (mul N p q) s = mul N p (mul N q s) := by
  change mul N (truncate N (p * q)) s = mul N p (truncate N (q * s))
  rw [mul_truncate_left, mul_truncate_right]
  simp only [mul, _root_.mul_assoc]

end CPoly.BoxTruncation
