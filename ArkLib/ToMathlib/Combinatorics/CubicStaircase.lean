/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A cubic lower bound for a real-cutoff staircase count

Fix a weight `D : ℕ` and a real cutoff `L`. Count the triples `(x, b₀, b₁)` of natural numbers
with `x + D * (b₀ + b₁) < D * L`. Grouping by `s = b₀ + b₁`, there are `s + 1` pairs `(b₀, b₁)`
with that sum, and for each of them `x` ranges over the naturals below `D * (L - s)`, of which there
are `⌈D * (L - s)⌉₊`. This gives

  `CubicStaircase.count D L = ∑ s < ⌈L⌉₊, (s + 1) * ⌈D * (L - s)⌉₊`.

The type `CubicStaircase.Slot D L` realizes this sum as a dependent triple, and
`Slot.exponents` sends a slot injectively to an exponent triple below the cutoff. The main result
is the exact, non-asymptotic lower bound `D * (max L 0) ^ 3 / 6 ≤ count D L`, valid for every real
`L`, including nonintegral and nonpositive cutoffs.

## Main statements

* `CubicStaircase.card_slot` — `Fintype.card (Slot D L) = count D L`.
* `CubicStaircase.Slot.exponents_injective` and `CubicStaircase.Slot.weighted_degree_lt` — slots
  decode injectively to triples below the weighted cutoff.
* `CubicStaircase.six_mul_sum` — the closed form of the unrounded sum.
* `CubicStaircase.cube_div_six_le_sum` — `L ^ 3 / 6` is below the unrounded sum for every `L`.
* `CubicStaircase.count_ge_cubic` — `D * (max L 0) ^ 3 / 6 ≤ count D L`.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean`: `CubicStaircase.count`,
`CubicStaircase.Slot`, `CubicStaircase.card_slot`, `CubicStaircase.Slot.exponents`,
`CubicStaircase.Slot.exponents_injective`, `CubicStaircase.Slot.weighted_degree_lt`,
`CubicStaircase.six_mul_sum` and `CubicStaircase.count_ge_cubic` are ported with the same
statements. `CubicStaircase.cube_div_six_le_sum` drops the source hypothesis `0 < L`. The
source's consumer is the weighted-support dimension bound (`WeightedSupport/Dimension.lean`),
which is not yet ported. The converse `CubicStaircase.Slot.exists_of_weighted_degree_lt` (every
triple below the cutoff comes from a slot) has no consumer in the source and is not ported. This
file is unrelated to the natural-number staircase `Finset.staircase` of
`ArkLib.Data.Finset.Staircase`, which counts pairs below a natural cutoff.
-/

@[expose] public section

namespace CubicStaircase

noncomputable section

/-- The number of natural triples `(x, b₀, b₁)` with `x + D * (b₀ + b₁) < D * L`, written as a
sum over `s = b₀ + b₁`: there are `s + 1` pairs with sum `s`, and `⌈D * (L - s)⌉₊` admissible
values of `x` for each. For `L ≤ 0` the sum is empty. -/
def count (D : ℕ) (L : ℝ) : ℕ :=
  ∑ s ∈ Finset.range ⌈L⌉₊, (s + 1) * ⌈(D : ℝ) * (L - s)⌉₊

/-- A slot is a total degree `s < ⌈L⌉₊`, a first exponent `b₀ ≤ s`, and a weighted exponent
`x < ⌈D * (L - s)⌉₊`. The second exponent is `s - b₀`. -/
def Slot (D : ℕ) (L : ℝ) :=
  Σ s : Fin ⌈L⌉₊, Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊

instance (D : ℕ) (L : ℝ) : Fintype (Slot D L) :=
  inferInstanceAs (Fintype (Σ s : Fin ⌈L⌉₊,
    Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊))

/-- The number of slots is `count D L`. -/
theorem card_slot (D : ℕ) (L : ℝ) : Fintype.card (Slot D L) = count D L := by
  change Fintype.card (Σ s : Fin ⌈L⌉₊,
    Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ (s + 1) * ⌈(D : ℝ) * (L - s)⌉₊) ⌈L⌉₊

/-- The exponent triple `(x, b₀, s - b₀)` of a slot. -/
def Slot.exponents {D : ℕ} {L : ℝ} (a : Slot D L) : ℕ × ℕ × ℕ :=
  (a.2.2.val, a.2.1.val, a.1.val - a.2.1.val)

/-- Distinct slots have distinct exponent triples: `s` is recovered as `b₀ + b₁`. -/
theorem Slot.exponents_injective (D : ℕ) (L : ℝ) :
    Function.Injective (Slot.exponents (D := D) (L := L)) := by
  intro ⟨s, b, x⟩ ⟨t, c, y⟩ h
  have hx : x.val = y.val := congrArg Prod.fst h
  have hb : b.val = c.val := congrArg (fun z ↦ z.2.1) h
  have hr : s.val - b.val = t.val - c.val := congrArg (fun z ↦ z.2.2) h
  have hs : s = t := Fin.ext (by have := b.isLt; have := c.isLt; omega)
  subst t
  congr 2
  · exact Fin.ext hb
  · exact Fin.ext hx

/-- The exponent triple `(x, b₀, b₁)` of a slot satisfies `x + D * (b₀ + b₁) < D * L`. -/
theorem Slot.weighted_degree_lt {D : ℕ} {L : ℝ} (a : Slot D L) :
    (a.exponents.1 : ℝ) + D * (a.exponents.2.1 + a.exponents.2.2 : ℕ) < D * L := by
  have hb : a.2.1.val ≤ a.1.val := by have := a.2.1.isLt; omega
  have hx : (a.2.2.val : ℝ) < (D : ℝ) * (L - a.1.val) :=
    Nat.lt_ceil.mp a.2.2.isLt
  simp only [Slot.exponents, Nat.add_sub_of_le hb]
  nlinarith only [hx]

/-- The unrounded sum has the closed form
`6 * ∑ s < n, (s + 1) * (L - s) = n * (n + 1) * (3 * L - 2 * n + 2)` for every `n` and `L`. -/
theorem six_mul_sum (n : ℕ) (L : ℝ) :
    6 * (∑ s ∈ Finset.range n, ((s : ℝ) + 1) * (L - s)) =
      (n : ℝ) * (n + 1) * (3 * L - 2 * n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith only [ih]

/-- `L ^ 3 / 6 ≤ ∑ s < ⌈L⌉₊, (s + 1) * (L - s)` for every real `L`. For `L ≤ 0` the sum is
empty and `L ^ 3 ≤ 0`. For `L > 0` the proof uses the closed form `six_mul_sum` and
`L ≤ ⌈L⌉₊ ≤ L + 1`. The source version assumes `0 < L`; that hypothesis is dropped here. -/
theorem cube_div_six_le_sum (L : ℝ) :
    L ^ 3 / 6 ≤ ∑ s ∈ Finset.range ⌈L⌉₊, ((s : ℝ) + 1) * (L - s) := by
  rcases le_or_gt L 0 with hL | hL
  · rw [Nat.ceil_eq_zero.mpr hL, Finset.sum_range_zero]
    have : L ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) hL
    linarith
  let n := ⌈L⌉₊
  have hn : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n from Nat.lt_ceil.mpr (by simpa using hL))
  have hLn : L ≤ n := Nat.le_ceil L
  have hnL : (n : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one hL.le).le
  have hcube : L ^ 3 ≤ L * (n : ℝ) ^ 2 := by
    calc
      L ^ 3 = L * L ^ 2 := by ring
      _ ≤ L * (n : ℝ) ^ 2 := by gcongr
  have hfactor : 0 ≤ (2 * (n : ℝ) + 3) * L - 2 * (n : ℝ) ^ 2 + 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * (n : ℝ) + 3)
      (by linarith : 0 ≤ L + 1 - n)]
  have hnonneg := mul_nonneg (by positivity : (0 : ℝ) ≤ n) hfactor
  have heq := six_mul_sum n L
  change L ^ 3 / 6 ≤ ∑ s ∈ Finset.range n, ((s : ℝ) + 1) * (L - s)
  nlinarith only [hcube, hnonneg, heq]

/-- `D * (max L 0) ^ 3 / 6 ≤ count D L` for every weight `D` and every real cutoff `L`. There
is no hypothesis: for `L ≤ 0` both sides are `0`. For `L > 0` the count dominates
`D * ∑ s < ⌈L⌉₊, (s + 1) * (L - s)` by rounding each term up, and `cube_div_six_le_sum` bounds that
sum below. -/
theorem count_ge_cubic (D : ℕ) (L : ℝ) :
    (D : ℝ) * (max L 0) ^ 3 / 6 ≤ count D L := by
  by_cases hL : 0 < L
  · rw [max_eq_left hL.le]
    have hround : (D : ℝ) *
        (∑ s ∈ Finset.range ⌈L⌉₊, ((s : ℝ) + 1) * (L - s)) ≤ count D L := by
      rw [count, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      calc
        (D : ℝ) * (((s : ℝ) + 1) * (L - s)) =
            ((s : ℝ) + 1) * ((D : ℝ) * (L - s)) := by ring
        _ ≤ ((s : ℝ) + 1) * ⌈(D : ℝ) * (L - s)⌉₊ :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
    have h := (mul_le_mul_of_nonneg_left (cube_div_six_le_sum L)
      (Nat.cast_nonneg D)).trans hround
    simpa only [mul_div_assoc] using h
  · rw [max_eq_right (le_of_not_gt hL)]
    simp

end

end CubicStaircase
