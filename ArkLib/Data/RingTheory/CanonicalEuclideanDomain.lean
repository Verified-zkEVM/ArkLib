/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Init.Data.Int.Order

universe u
local infixl:50 " ≺ " => EuclideanDomain.r -- the valuation function

/--
# Canonical Euclidean Domains

A `CanonicalEuclideanDomain` is a restriction of `EuclideanDomain`. It introduces a selection
rule for canonical remainders and guarantees there exists exactly one
`canonical` quotient (`q`) and remainder (`r`) for any pair of dividend (`a`) and divisor (`b`)
(assuming `b ≠ 0`), no matter how the division is implemented (i.e. the division result is
unique and consistent across different implementations).

## Motivation: The unpredictable behaviors of `/` and `%` in `EuclideanDomain`

In a standard `EuclideanDomain`, the operators `/` and `%` are viewed as black-boxes and are
only required to return *some* valid pair satisfying `a = b * q + r` and `r ≺ b`. This loose
specification allows implementations to be **unpredictable** and **inconsistent**:
1. **Unprovable Algebraic Identities:**
  An implementation is permitted to switch strategies arbitrarily (e.g., rounding up for input `x`
  but down for input `y`; or following truncation-towards-zero as in C/Rust/Java, ...).
  This makes natural identities like `(a + b * k) / b = a / b + k` **false** in the general
  case, as the term `b * k` might trigger a strategy switch.
2. **Non-Determinism Accumulation (Unit Drift):**
  Algorithms that chain multiple operations (like GCD) accumulate arbitrary unit factors
  at every step. For example, `gcd(a, b)` is only unique up to a unit.
    * `gcd(a, gcd(b, c))` might return `g`.
    * `gcd(gcd(a, b), c)` might return `-g` (or `u * g`).
    While mathematically equivalent (associates), they are **not equal** as data structures.
    This breaks any system relying on bit-exact equality (hashing, caching, serialization).

**The Solution:** `CanonicalEuclideanDomain` solves this by enforcing a strict
`is_canonical_remainder` predicate. This restricts the implementation space to **exactly one**
valid function, ensuring the `bit-exact` uniqueness of the outputs, no matter what
implementations are used.

## Advantages

* **Algebraic Stability:** Restores critical algebraic properties,
    enabling a suite of powerful rewrite rules (e.g., `add_mod_eq`, `add_mul_div_right`,
    `mul_mod_eq`, `mod_eq_of_eq_add_mul`) that are unprovable in the normal `EuclideanDomain`
    setting. This brings **canonical regularity** to domains with **non-unique remainders**
    (e.g., `ℤ`, `Polynomial F`).

* **Generic Algorithms over Rings:** Guarantees strictly normalized outputs (positive GCDs,
    monic generators) for high-level algorithms (Smith Normal Form, Hermite Normal Form).
    It prevents the `unit drift` described above, allowing generic algorithms to run
    deterministically on complex domains like `Polynomial F`.

* **Protocol Determinism:** Essential for cryptographic protocols (ZK transcripts, Fiat-Shamir)
    where objects must have bit-exact representations. It ensures that every implementation
    (Lean, Rust, ZK circuits) converges to the *same* remainder given the same canonical
    remainder rule, guaranteeing correctness and hash consistency.

## Supported Instances

This abstraction unifies commonly used mathematical objects under one interface:
1.  **Integers (`ℤ`):** The canonical rule enforces **non-negative remainders** (`0 ≤ r < |b|`).
    This matches the behavior of Python's `%` or Rust's `rem_euclid`.
2.  **Polynomials (`Polynomial F`):** Uniqueness is naturally enforced by the degree structure.
    Any remainder with `degree(r) < degree(b)` is automatically unique due to the ultrametric
    property of polynomial degrees (i.e., `degree(a - b) ≤ max(degree a, degree b)`).
3.  **Fields (`ℚ`, `ℝ`, `ZMod p` where p is prime, ...):** Division is exact; the canonical
  remainder is always `0`.
4.  **Other Euclidean Rings:** Gaussian Integers (`ℤ[i]`), Eisenstein Integers (`ℤ[ω]`), and
    Discrete Valuation Rings (DVRs) can potentially be adapted to this interface by defining
    strict geometric or valuation-based selection rules.

## Definition
It extends `EuclideanDomain` with:
1.  `is_canonical_remainder b r`: A predicate deciding if a remainder `r` is the "chosen one".
2.  `remainder_is_canonical`: A proof that the built-in `%` operator satisfies this predicate.
3.  `unique_division`: The `Uniqueness Axiom` stating that if `(q1, r1)` and `(q2, r2)`
    both satisfy the division equation and the canonical rule, they must be equal.
-/
class CanonicalEuclideanDomain (R : Type u) extends EuclideanDomain R where
  is_canonical_remainder : (b : R) → (r : R) → Prop
  -- The built-in operator `remainder (%)` must obey the rule
  remainder_is_canonical : ∀ (a b : R), (hb : b ≠ 0) → is_canonical_remainder b (remainder a b)

  unique_division : ∀ {a b q₁ q₂ r₁ r₂: R}, (hb : b ≠ 0) → (h_eq_div_mul_add₁ : a = b * q₁ + r₁)
    → (h_eq_div_mul_add₂ : a = b * q₂ + r₂)
    → (is_canonical_remainder₁ : is_canonical_remainder b r₁)
    → (is_canonical_remainder₂ : is_canonical_remainder b r₂)
    → q₁ = q₂ ∧ r₁ = r₂

section Instances

instance Int.instCanonicalEuclideanDomainInt : CanonicalEuclideanDomain ℤ where
  toEuclideanDomain := Int.euclideanDomain
  -- "A canonical integer remainder is non-negative AND strictly smaller than divisor"
  is_canonical_remainder b r := 0 ≤ r ∧ r.natAbs < b.natAbs

  -- Proof that Int.emod fits this description
  remainder_is_canonical a b hb := by
    constructor
    · exact Int.emod_nonneg a hb  -- Proof it is >= 0
    · exact Nat.lt_of_sub_pos (by
        simp only [tsub_pos_iff_lt];
        exact EuclideanDomain.remainder_lt (a := a) (b := b) (hb);
      )      -- Proof it is < |b|

  -- Uniqueness proof is now easy because we have both bounds
  unique_division := by
    intro a b q₁ q₂ r₁ r₂ hb h_eq1 h_eq2 h_can1 h_can2
    -- 2. Unpack the "Canonical" definition
    rcases h_can1 with ⟨h_r1_ge_zero, h_r1_lt_b⟩
    rcases h_can2 with ⟨h_r2_ge_zero, h_r2_lt_b⟩
    -- 3. Algebraic Rearrangement: b * (q₁ - q₂) = r₂ - r₁
    have h_diff : b * (q₁ - q₂) = r₂ - r₁ := by
      calc b * (q₁ - q₂)
        _ = b * q₁ - b * q₂ := mul_sub b q₁ q₂
        _ = (a - r₁) - (a - r₂) := by rw [eq_sub_of_add_eq h_eq1.symm, eq_sub_of_add_eq h_eq2.symm]
        _ = r₂ - r₁ := by exact sub_sub_sub_cancel_left r₁ r₂ a
    -- 4. Convert natAbs bounds: Since r ≥ 0, we have r = r.natAbs, so r < b.natAbs
    have h_r1_lt_abs : r₁ < |b| := by
      rw [Int.abs_eq_natAbs]
      convert h_r1_lt_b using 1
      omega
    have h_r2_lt_abs : r₂ < |b| := by
      rw [Int.abs_eq_natAbs]
      convert h_r2_lt_b using 1
      omega
    -- 5. Prove that the difference between remainders is "small"
    -- We want to show: |r₂ - r₁| < |b|
    have h_bound : |r₂ - r₁| < |b| := by
      rw [abs_sub_lt_iff]
      constructor
      · -- Show: -|b| < r₂ - r₁
        have h_neg_lt : -|b| < -r₁ := by
          rw [neg_lt_neg_iff]
          exact h_r1_lt_abs
        have h_neg_le : -r₁ ≤ r₂ - r₁ := by
          linarith [h_r2_ge_zero]
        omega
      · omega -- Show: r₂ - r₁ < |b|

    -- 6. The "Killer Move": Divisibility + Smallness = Zero
    -- We established b * (q₁ - q₂) = r₂ - r₁, so b divides (r₂ - r₁)
    have h_dvd : b ∣ (r₂ - r₁) := by
      rw [← h_diff]
      exact dvd_mul_right b (q₁ - q₂)
    have h_rem_diff_zero : r₂ - r₁ = 0 := by
      -- If b ≠ 0 divides x and |x| < |b|, then x = 0
      by_contra h_ne_zero
      -- Since b ∣ (r₂ - r₁), we have r₂ - r₁ = k * b for some k
      obtain ⟨k, h_eq⟩ := h_dvd
      -- If k = 0, then r₂ - r₁ = 0, contradicting h_ne_zero
      by_cases h_k_zero : k = 0
      · rw [h_k_zero, mul_zero] at h_eq
        exact h_ne_zero h_eq
      · -- k ≠ 0, so |k| ≥ 1, hence |r₂ - r₁| = |k| * |b| ≥ |b|
        have h_abs_k_ge_one : |k| ≥ 1 := by
          -- For integers, if k ≠ 0, then |k| ≥ 1
          exact Int.one_le_abs h_k_zero
        have h_abs_ge : |r₂ - r₁| ≥ |b| := by
          rw [h_eq, abs_mul]
          -- ⊢ |b| * |k| ≥ |b|
          calc
            |b| * |k| ≥ 1 * |b| := by
              rw [mul_comm];
              simp only [ge_iff_le]
              rw [Int.mul_le_mul_right (b := 1) (c := |k|) (a := |b|)]; exact h_abs_k_ge_one
              exact abs_pos.mpr hb
            _ = |b| := one_mul |b|
        -- This contradicts h_bound: |r₂ - r₁| < |b|
        linarith [h_bound, h_abs_ge]
    have h_r_eq : r₁ = r₂ := by omega
    constructor
    · -- Prove q₁ = q₂
      -- If b * (q₁ - q₂) = 0 and b ≠ 0, then (q₁ - q₂) must be 0.
      rw [h_rem_diff_zero] at h_diff
      have h_q_diff_zero : q₁ - q₂ = 0 :=
        (mul_eq_zero.mp h_diff).resolve_left hb
      exact sub_eq_zero.mp h_q_diff_zero
    · -- Prove r₁ = r₂
      exact h_r_eq

-- For Polynomials over a Field F
noncomputable instance Polynomial.instCanonicalEuclideanDomainPoly {F : Type u} [Field F] :
    CanonicalEuclideanDomain (Polynomial F) where
  -- 1. The Rule: Any valid Euclidean remainder (degree < degree b) is canonical.
  --    The geometry of polynomials prevents ambiguity automatically.
  is_canonical_remainder b r := EuclideanDomain.r r b
  -- 2. Compliance: Standard % satisfies the degree bound
  remainder_is_canonical a b hb := EuclideanDomain.mod_lt a hb
  -- 3. Uniqueness Proof
  unique_division := by
    intro a b q₁ q₂ r₁ r₂ hb h_eq1 h_eq2 h_can1 h_can2
    -- Step A: Algebraic Setup: b * (q₁ - q₂) = r₂ - r₁
    have h_diff : b * (q₁ - q₂) = r₂ - r₁ := by
      calc b * (q₁ - q₂)
        _ = b * q₁ - b * q₂ := mul_sub b q₁ q₂
        _ = (a - r₁) - (a - r₂) := by
          apply eq_sub_of_add_eq
          conv_rhs => rw [h_eq1]
          conv_lhs => rw [h_eq2]
          ring_nf
        _ = r₂ - r₁ := by ring_nf
    -- Step B: Contradiction by Degree
    -- If q₁ ≠ q₂, then LHS has degree ≥ degree(b).
    -- But RHS has degree < degree(b) (because r₁, r₂ are small).
    by_cases h_q : q₁ = q₂
    · -- Easy case: If q₁ = q₂, then r₁ = r₂ follows immediately
      constructor
      · exact h_q
      · rw [h_q] at h_diff
        simp only [sub_self, mul_zero, eq_comm, sub_eq_zero] at h_diff
        exact h_diff
    · -- Hard case: If q₁ ≠ q₂, we find a contradiction.
      have h_lhs_deg : (b * (q₁ - q₂)).degree ≥ b.degree := by
        -- degree(f * g) = degree(f) + degree(g)
        rw [Polynomial.degree_mul]
        apply le_add_of_nonneg_right
        have h_sub_ne_zero : q₁ - q₂ ≠ 0 := by exact sub_ne_zero_of_ne h_q
        exact Polynomial.zero_le_degree_iff.mpr h_sub_ne_zero
      have h_rhs_deg : (r₂ - r₁).degree < b.degree := by
        -- degree(f - g) ≤ max(degree f, degree g)
        apply (Polynomial.degree_sub_le r₂ r₁).trans_lt
        -- max(deg r₂, deg r₁) < deg b
        rw [max_lt_iff]
        constructor
        · exact h_can2 -- degree r₂ < degree b
        · exact h_can1 -- degree r₁ < degree b
      rw [h_diff] at h_lhs_deg
      -- Contradiction: deg(r2-r1) cannot be both < deg(b) AND ≥ deg(b)
      have h_impossible := lt_of_le_of_lt h_lhs_deg h_rhs_deg
      exact (lt_irrefl _ h_impossible).elim

lemma Field.mod_eq_zero {K : Type u} [Field K] (a b : K) (hb : b ≠ 0) :
    a % b = 0 := by
  rw [Field.mod_eq, mul_div_cancel_right₀ a hb, sub_self]

-- For any Field K (like Rat, Real, ZMod p)
instance Field.instCanonicalEuclideanDomainField {K : Type u} [Field K] :
    CanonicalEuclideanDomain K where
  toEuclideanDomain := Field.toEuclideanDomain
  -- 1. The Rule: Remainder must be exactly 0
  is_canonical_remainder b r := r = 0
  -- 2. Compliance: a % b is 0 in a field
  remainder_is_canonical a b hb := by
    change a % b = 0 -- by definition of EuclideanDomain.remainder of Field.toEuclideanDomain
    rw [Field.mod_eq_zero (a := a) (b := b) (hb := hb)]
  -- 3. Uniqueness: Trivial
  unique_division := by
    intro a b q₁ q₂ r₁ r₂ hb h_eq1 h_eq2 h_can1 h_can2
    have h_r : r₁ = r₂ := by
      rw [h_can1, h_can2]
    constructor
    · -- Prove q₁ = q₂
      -- a = b * q₁ + 0  vs  a = b * q₂ + 0
      rw [h_can1, add_zero] at h_eq1
      rw [h_can2, add_zero] at h_eq2
      -- Therefore b * q₁ = b * q₂
      rw [h_eq1] at h_eq2
      -- Cancel b (since b ≠ 0)
      exact mul_left_cancel₀ hb h_eq2
    · -- Prove r₁ = r₂
      exact h_r
end Instances

namespace CanonicalEuclideanDomain
variable {R : Type u} [CanonicalEuclideanDomain R]

section DivisionUniqueness

/-- The Fundamental Theorem of Canonical Euclidean Domains.
    If you find ANY pair (q, r) that satisfies the division equation
    AND the canonical condition, then q MUST be the result of the division operation. -/
theorem div_eq_of_canonical_eq_mul_add {a b q r : R} (hb : b ≠ 0)
    (h_eq : a = b * q + r)
    (h_can : is_canonical_remainder b r) :
    a / b = q := by
  -- 1. Get the "Standard" division from the instance
  --    In Lean, `a / b` is hardcoded to the instance's implementation.
  let q_std := a / b
  let r_std := a % b
  -- 2. We know standard division satisfies the equation:
  have h_std_eq : a = b * q_std + r_std := by
    -- EuclideanDomain.div_add_mod a b
    dsimp only [q_std, r_std]
    rw [EuclideanDomain.div_add_mod]
  -- 3. We know standard division is canonical.
  --    This is guaranteed by the `remainder_is_canonical` axiom of our class.
  have h_std_can : is_canonical_remainder b r_std :=
    remainder_is_canonical a b hb
  -- 4. Apply the "Highlander" Axiom (Unique Division)
  --    We compare our candidate (q, r) against the standard (q_std, r_std).
  have h_unique := unique_division hb h_eq h_std_eq h_can h_std_can
  -- 5. The axiom proves q = q_std
  --    h_unique is (q = q_std ∧ r = r_std)
  rw [h_unique.1]

/-- The Fundamental Theorem of CEDs:
Satisfying the division equation + size constraint is EQUIVALENT
to being the output of the division function. -/
theorem div_eq_and_mod_eq_iff {a b q r : R} (hn : b ≠ 0) :
    (a / b = q ∧ a % b = r) ↔ (a = b * q + r ∧ is_canonical_remainder b r) := by
  constructor
  -- Direction 1: If it's the result of division, it holds (Standard ED property)
  · rintro ⟨rfl, rfl⟩
    constructor
    · exact Eq.symm (EuclideanDomain.div_add_mod a b)
    · exact remainder_is_canonical a b hn
  -- Direction 2: Uniqueness (Specific to CED)
  · rintro ⟨h_eq, h_can⟩
    have h_q_eq_a_div_b : q = a / b := by
      exact Eq.symm (CanonicalEuclideanDomain.div_eq_of_canonical_eq_mul_add hn h_eq h_can)
    constructor
    · exact h_q_eq_a_div_b.symm
    · -- ⊢ a % b = r
      rw [h_q_eq_a_div_b] at h_eq
      -- h_eq : a = b * (a / b) + r
      have h_std := EuclideanDomain.div_add_mod a b
      conv_rhs at h_std => rw [h_eq]
      -- h_std becomes: b * (a / b) + a % b = b * (a / b) + r
      simp only [add_right_inj] at h_std
      exact h_std

end DivisionUniqueness

section DivisionCommonAlgebra

/-! # Division Properties -/

/-- Generalized `add_mul_div_right`: `(a + b * r) / b = a / b + r`
In a standard ED, this isn't always true (the quotient is not unique).
In a CED, it is always true. -/
theorem add_mul_div_right (a b r : R) (hb : b ≠ 0) :
    (a + b * r) / b = a / b + r := by
  -- We prove that (a/b + r) is THE quotient for (a + b*r).
  -- By our IFF theorem, we just need to check the equation and the size.
  apply CanonicalEuclideanDomain.div_eq_of_canonical_eq_mul_add (hb := hb) (q := a / b + r)
    (r := a % b)
  · -- 1. Check algebraic equation:
    -- Does ⊢ a + b * r = b * (a / b + r) + a % b
    rw [mul_add, mul_comm b r, add_assoc]
    conv_rhs => rw [add_comm (r * b) (a % b), ←add_assoc]
    -- ⊢ a + r * b = b * (a / b) + a % b + r * b
    let mul_div_add_mod_form_of_a: b * (a / b) + a % b = a :=
      EuclideanDomain.quotient_mul_add_remainder_eq a b
    conv_rhs => rw [mul_div_add_mod_form_of_a]
  · -- 2. Check size: ⊢ a % b ≺ b
    exact remainder_is_canonical a b hb

/--
Generalized `add_mul_mod_right`: (a + b * r) % b = a % b
The remainder ignores multiples of the divisor.
-/
theorem add_mul_mod_right (a b r : R) (hb : b ≠ 0) :
    (a + b * r) % b = a % b := by
  -- We use the same logic as above. Since (a/b + r) is the quotient,
  -- then (a % b) MUST be the remainder.
  have h_unique := (div_eq_and_mod_eq_iff (a := a + b * r) (b := b)
    (q := a / b + r) (r := a % b) hb).mpr
    (And.intro
      (by
        rw [mul_add, mul_comm b r, add_assoc];
        conv_rhs => rw [add_comm (r * b) (a % b), ←add_assoc]
        rw [add_left_inj]
        exact Eq.symm (EuclideanDomain.div_add_mod a b)
      )
      (remainder_is_canonical a b hb))
  rw [←h_unique.2]

/-- Generalized `add_mul_mod_left`: (a * r + b) % a = b % a`
The remainder ignores multiples of the divisor. -/
theorem add_mul_mod_left (a b r : R) (hb : a ≠ 0) :
    (a * r + b) % a = b % a := by
  rw [add_comm]
  rw [add_mul_mod_right (hb := hb)]

/-- `If a = b + n * r, then a % n = b % n.` -/
theorem mod_eq_of_eq_add_mul {a b n q : R} (h_eq_add_mul : a = b + n * q) (hn : n ≠ 0) :
    a % n = b % n := by
  rw [h_eq_add_mul]
  rw [add_mul_mod_right (hb := hn)]

/-! # Arithmetic Modulo Properties -/

/-- `(a * b) % n = ((a % n) * b) % n` -/
theorem mul_mod_eq_mul_mod_left (a b n : R) (hn : n ≠ 0) :
    (a * b) % n = ((a % n) * b) % n := by
  -- Let a = qn + r. Then ab = (qn + r)b = qnb + rb = n(qb) + rb.
  -- The remainder of (a*b) is the remainder of (rb).
  nth_rw 1 [← EuclideanDomain.div_add_mod a n]
  rw [add_mul, mul_assoc, add_comm]
  rw [add_mul_mod_right (hb := hn)]


/-- `(a * b) % n = 0` if `a % n = 0` -/
theorem mul_mod_eq_zero_of_mod_dvd (a b n : R) (hn : n ≠ 0)
    (h_mod_eq_zero : a % n = 0) : (a * b) % n = 0 := by
  -- If a % n = 0, then (a * b) % n = ((a % n) * b) % n = (0 * b) % n = 0 % n = 0
  rw [mul_mod_eq_mul_mod_left a b n hn]
  rw [h_mod_eq_zero]
  rw [zero_mul]
  rw [EuclideanDomain.zero_mod]

/-- `(a + b) % n = ((a % n) + b) % n` -/
theorem add_mod_eq_add_mod_left (a b n : R) (hn : n ≠ 0) :
    (a + b) % n = ((a % n) + b) % n := by
  nth_rw 1 [← EuclideanDomain.div_add_mod a n]
  rw [add_assoc, add_comm (a%n), add_comm]
  rw [add_mul_mod_right (hb := hn)]

/-- `(a + b) % n = (a % n + b % n) % n` -/
theorem add_mod_eq (a b n : R) (hn : n ≠ 0) :
    (a + b) % n = (a % n + b % n) % n := by
  rw [add_mod_eq_add_mod_left a b n hn]
  rw [add_comm, add_mod_eq_add_mod_left b (a%n) n hn, add_comm]

/-- `(a * b) % n = ((a % n) * (b % n)) % n` -/
theorem mul_mod_eq (a b n : R) (hn : n ≠ 0) :
    (a * b) % n = ((a % n) * (b % n)) % n := by
  rw [mul_mod_eq_mul_mod_left a b n hn]
  rw [mul_comm (a%n) b]
  rw [mul_mod_eq_mul_mod_left b (a%n) n hn]
  rw [mul_comm]

/-- `(a % n) % n = a % n` -/
theorem mod_mod_eq_mod (a n : R) (hn : n ≠ 0) :
    (a % n) % n = a % n := by
  apply Eq.symm
  apply CanonicalEuclideanDomain.mod_eq_of_eq_add_mul (a := a) (b := a % n)
    (q := a / n) (hn := hn) (h_eq_add_mul := by exact Eq.symm (EuclideanDomain.mod_add_div a n))

/-- `b | a - (a % b)` -/
theorem dvd_sub_mod (a b : R) :
    b ∣ a - (a % b) := by
-- We start with the fundamental division identity: a = b * (a / b) + (a % b)
  have h := EuclideanDomain.div_add_mod a b
  refine dvd_sub_comm.mp ?_
  rw (occs := .pos [2]) [←h]
  simp only [sub_add_cancel_right, dvd_neg, dvd_mul_right]

end DivisionCommonAlgebra

end CanonicalEuclideanDomain
