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
# A cubic lower bound for staircase coefficient counts

At total degree `s` in two variables there are `s+1` exponent pairs. Each pair leaves
`D * (L-s)` available values for a third exponent. Rounding that number upward and summing
therefore gives a cubic staircase count. The exact finite sum proves the cubic lower bound
without an asymptotic error term, including nonintegral and nonpositive cutoffs.
-/

@[expose] public section

open scoped BigOperators

namespace CubicStaircase

noncomputable section

/-- Number of coefficient slots after grouping the two unweighted exponents by their sum. -/
def count (D : ℕ) (L : ℝ) : ℕ :=
  ∑ s ∈ Finset.range ⌈L⌉₊, (s + 1) * ⌈(D : ℝ) * (L - s)⌉₊

/-- A slot records total degree in two variables, the first exponent, and the remaining
weighted exponent. The second exponent is the total minus the first. -/
def Slot (D : ℕ) (L : ℝ) :=
  Σ s : Fin ⌈L⌉₊, Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊

instance (D : ℕ) (L : ℝ) : Fintype (Slot D L) :=
  inferInstanceAs (Fintype (Σ s : Fin ⌈L⌉₊,
    Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊))

/-- The staircase sum is the exact cardinality of the coefficient slots. -/
theorem card_slot (D : ℕ) (L : ℝ) : Fintype.card (Slot D L) = count D L := by
  change Fintype.card (Σ s : Fin ⌈L⌉₊,
    Fin (s.val + 1) × Fin ⌈(D : ℝ) * (L - s.val)⌉₊) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ (s + 1) * ⌈(D : ℝ) * (L - s)⌉₊) ⌈L⌉₊

/-- Decode a slot as the three exponents `(x,b₀,b₁)`. -/
def Slot.exponents {D : ℕ} {L : ℝ} (a : Slot D L) : ℕ × ℕ × ℕ :=
  (a.2.2.val, a.2.1.val, a.1.val - a.2.1.val)

/-- Distinct slots yield distinct exponent triples. -/
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

/-- Every decoded slot satisfies the strict weighted-degree cutoff. -/
theorem Slot.weighted_degree_lt {D : ℕ} {L : ℝ} (a : Slot D L) :
    (a.exponents.1 : ℝ) + D * (a.exponents.2.1 + a.exponents.2.2 : ℕ) < D * L := by
  have hb : a.2.1.val ≤ a.1.val := by have := a.2.1.isLt; omega
  have hx : (a.2.2.val : ℝ) < (D : ℝ) * (L - a.1.val) :=
    Nat.lt_ceil.mp a.2.2.isLt
  simp only [Slot.exponents, Nat.add_sub_of_le hb]
  nlinarith only [hx]

/-- Every exponent triple below the strict cutoff is represented by a slot. Together with
injectivity, this identifies the finite staircase count with the actual coefficient count. -/
theorem Slot.exists_of_weighted_degree_lt {D : ℕ} {L : ℝ} (hD : 0 < D)
    (x b₀ b₁ : ℕ) (h : (x : ℝ) + D * (b₀ + b₁ : ℕ) < D * L) :
    ∃ a : Slot D L, a.exponents = (x, b₀, b₁) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : ((b₀ + b₁ : ℕ) : ℝ) < L := by
    nlinarith [show (0 : ℝ) ≤ x by positivity]
  have hx : (x : ℝ) < (D : ℝ) * (L - (b₀ + b₁ : ℕ)) := by nlinarith only [h]
  refine ⟨⟨⟨b₀ + b₁, Nat.lt_ceil.mpr hs⟩,
    ⟨b₀, by change b₀ < b₀ + b₁ + 1; omega⟩, ⟨x, Nat.lt_ceil.mpr hx⟩⟩, ?_⟩
  simp [Slot.exponents]

/-- The unrounded staircase sum is an exact cubic polynomial in its endpoint. -/
theorem six_mul_sum (n : ℕ) (L : ℝ) :
    6 * (∑ s ∈ Finset.range n, ((s : ℝ) + 1) * (L - s)) =
      (n : ℝ) * (n + 1) * (3 * L - 2 * n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith only [ih]

/-- Summing the residual degree above integer pairs dominates the corresponding cubic volume. -/
theorem cube_div_six_le_sum {L : ℝ} (hL : 0 < L) :
    L ^ 3 / 6 ≤ ∑ s ∈ Finset.range ⌈L⌉₊, ((s : ℝ) + 1) * (L - s) := by
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

/-- The rounded coefficient-slot count is at least `D/6` times the positive cutoff cubed. -/
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
    have h := (mul_le_mul_of_nonneg_left (cube_div_six_le_sum hL)
      (Nat.cast_nonneg D)).trans hround
    simpa only [mul_div_assoc] using h
  · rw [max_eq_right (le_of_not_gt hL)]
    simp

end
end CubicStaircase
