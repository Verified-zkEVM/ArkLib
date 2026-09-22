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
# A quadratic lower bound for a real-cutoff staircase count

Fix a weight `D : ℕ` and a real cutoff `L`. Count the pairs `(x, u)` of natural numbers with
`x + D * u < D * L`. For each `u < ⌈L⌉₊` the admissible values of `x` are the naturals below
`D * (L - u)`, of which there are `⌈D * (L - u)⌉₊`. This gives

  `QuadraticStaircase.count D L = ∑ u < ⌈L⌉₊, ⌈D * (L - u)⌉₊`.

The type `QuadraticStaircase.Slot D L` realizes this sum as a dependent pair, and
`Slot.exponents` sends a slot injectively to a pair below the cutoff. The main result is the exact,
non-asymptotic lower bound `D * (max L 0) ^ 2 / 2 ≤ count D L`, valid for every real `L`.

## Main statements

* `QuadraticStaircase.card_slot` — `Fintype.card (Slot D L) = count D L`.
* `QuadraticStaircase.Slot.exponents_injective` and `QuadraticStaircase.Slot.weighted_degree_lt` —
  slots decode injectively to pairs below the weighted cutoff.
* `QuadraticStaircase.two_mul_sum` — the closed form of the unrounded sum.
* `QuadraticStaircase.square_div_two_le_sum` — `L ^ 2 / 2` is below the unrounded sum for
  `L ≥ 0`.
* `QuadraticStaircase.count_ge_quadratic` — `D * (max L 0) ^ 2 / 2 ≤ count D L`.
* `QuadraticStaircase.count_div_sub_eq_sum` — at the cutoff `L / D - c` with natural `L`, `c`,
  the count is the natural sum `∑ u < L, (L - D * (u + c))`.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean`: `QuadraticStaircase.count`,
`QuadraticStaircase.Slot`, `QuadraticStaircase.card_slot`, `QuadraticStaircase.Slot.exponents`,
`QuadraticStaircase.Slot.exponents_injective`, `QuadraticStaircase.Slot.weighted_degree_lt`,
`QuadraticStaircase.two_mul_sum` and `QuadraticStaircase.count_ge_quadratic` are ported with the
same statements. `QuadraticStaircase.square_div_two_le_sum` weakens the source hypothesis `0 < L`
to `0 ≤ L`. The source file imported `CubicStaircase` without using it; that import is dropped.
From `HiddenDerivative/Interpolation/PartitionSupport/Dimension.lean` at the same revision:
`partition_residual_ceil` is `QuadraticStaircase.ceil_mul_div_sub_sub`, and
`quadraticStaircase_le_partition_slice` is strengthened from an inequality to the equality
`QuadraticStaircase.count_div_sub_eq_sum`. The source consumer `RatePartition/Area.lean` is not yet
ported.
-/

@[expose] public section

noncomputable section

namespace QuadraticStaircase

/-- The number of natural pairs `(x, u)` with `x + D * u < D * L`, written as a sum over `u`:
there are `⌈D * (L - u)⌉₊` admissible values of `x` for each `u < ⌈L⌉₊`. For `L ≤ 0` the sum is
empty. -/
def count (D : ℕ) (L : ℝ) : ℕ :=
  ∑ u ∈ Finset.range ⌈L⌉₊, ⌈(D : ℝ) * (L - u)⌉₊

/-- A slot is an unweighted exponent `u < ⌈L⌉₊` and a weighted exponent `x < ⌈D * (L - u)⌉₊`. -/
def Slot (D : ℕ) (L : ℝ) :=
  Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊

instance (D : ℕ) (L : ℝ) : Fintype (Slot D L) :=
  inferInstanceAs (Fintype (Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊))

/-- The number of slots is `count D L`. -/
theorem card_slot (D : ℕ) (L : ℝ) : Fintype.card (Slot D L) = count D L := by
  change Fintype.card (Σ s : Fin ⌈L⌉₊, Fin ⌈(D : ℝ) * (L - s.val)⌉₊) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ ⌈(D : ℝ) * (L - s)⌉₊) ⌈L⌉₊

/-- The exponent pair `(x, u)` of a slot, weighted exponent first. -/
def Slot.exponents {D : ℕ} {L : ℝ} (a : Slot D L) : ℕ × ℕ :=
  (a.2.val, a.1.val)

/-- Distinct slots have distinct exponent pairs. -/
theorem Slot.exponents_injective (D : ℕ) (L : ℝ) :
    Function.Injective (Slot.exponents (D := D) (L := L)) := by
  rintro ⟨s, x⟩ ⟨t, y⟩ h
  have hs : s = t := Fin.ext (congrArg Prod.snd h)
  subst t
  exact congrArg (Sigma.mk s) (Fin.ext (congrArg Prod.fst h))

/-- The exponent pair `(x, u)` of a slot satisfies `x + D * u < D * L`. -/
theorem Slot.weighted_degree_lt {D : ℕ} {L : ℝ} (a : Slot D L) :
    (a.exponents.1 : ℝ) + D * a.exponents.2 < D * L := by
  have hx : (a.2.val : ℝ) < (D : ℝ) * (L - a.1.val) := Nat.lt_ceil.mp a.2.isLt
  dsimp [Slot.exponents]
  linarith

/-- The unrounded sum has the closed form `2 * ∑ u < n, (L - u) = n * (2 * L - n + 1)` for every
`n` and `L`. -/
theorem two_mul_sum (n : ℕ) (L : ℝ) :
    2 * (∑ u ∈ Finset.range n, (L - (u : ℝ))) = (n : ℝ) * (2 * L - n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith only [ih]

/-- For `L ≥ 0`, `L ^ 2 / 2 ≤ ∑ u < ⌈L⌉₊, (L - u)`. The proof uses the closed form
`two_mul_sum` and `L ≤ ⌈L⌉₊ ≤ L + 1`. The hypothesis `0 ≤ L` is needed: at `L = -1` the sum is
empty and the left side is `1/2`. -/
theorem square_div_two_le_sum {L : ℝ} (hL : 0 ≤ L) :
    L ^ 2 / 2 ≤ ∑ u ∈ Finset.range ⌈L⌉₊, (L - (u : ℝ)) := by
  have hlower := Nat.le_ceil L
  have hupper := (Nat.ceil_lt_add_one hL).le
  have hproduct : 0 ≤ ((⌈L⌉₊ : ℝ) - L) * (L + 1 - (⌈L⌉₊ : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hsum := two_mul_sum ⌈L⌉₊ L
  nlinarith

/-- `D * (max L 0) ^ 2 / 2 ≤ count D L` for every weight `D` and every real cutoff `L`. There is
no hypothesis: for `L ≤ 0` both sides are `0`. For `L > 0` the count dominates
`D * ∑ u < ⌈L⌉₊, (L - u)` by rounding each term up, and `square_div_two_le_sum` bounds that sum
below. -/
theorem count_ge_quadratic (D : ℕ) (L : ℝ) :
    (D : ℝ) * (max L 0) ^ 2 / 2 ≤ count D L := by
  rcases le_or_gt L 0 with hL | hL
  · rw [max_eq_right hL]
    simp
  rw [max_eq_left hL.le]
  have harea := mul_le_mul_of_nonneg_left (square_div_two_le_sum hL.le)
    (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  calc
    (D : ℝ) * L ^ 2 / 2 ≤ D * ∑ u ∈ Finset.range ⌈L⌉₊, (L - (u : ℝ)) := by
      simpa [mul_div_assoc] using harea
    _ = ∑ u ∈ Finset.range ⌈L⌉₊, (D : ℝ) * (L - u) := Finset.mul_sum ..
    _ ≤ ∑ u ∈ Finset.range ⌈L⌉₊, (⌈(D : ℝ) * (L - u)⌉₊ : ℝ) :=
      Finset.sum_le_sum fun _ _ ↦ Nat.le_ceil _
    _ = count D L := by simp [count]

/-- At a rational cutoff `L / D - c` with natural `L` and `c`, each rounded term is the natural
difference `L - D * (u + c)`: `⌈D * (L / D - c - u)⌉₊ = L - D * (u + c)`. The hypothesis `0 < D`
is needed to cancel `D` against `L / D`; for `D = 0` the left side is `0` and the right side is
`L`. -/
theorem ceil_mul_div_sub_sub {D : ℕ} (hD : 0 < D) (L c u : ℕ) :
    ⌈(D : ℝ) * ((L : ℝ) / D - c - u)⌉₊ = L - D * (u + c) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have h : (D : ℝ) * ((L : ℝ) / D - c - u) = (L : ℝ) - ((D * (u + c) : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [h, Nat.ceil_sub_natCast, Nat.ceil_natCast]

/-- The staircase at the cutoff `L / D - c`, for natural `L` and `c` and `0 < D`, counts the pairs
`(x, u)` with `x + D * (u + c) < L`: `count D (L / D - c) = ∑ u < L, (L - D * (u + c))`, with
natural subtraction. The terms with `u ≥ ⌈L / D - c⌉₊` are zero, which is why the sum may run over
the larger range `u < L`. The hypothesis `0 < D` is needed: for `D = 0` the left side is `0`,
since the cutoff is `L / 0 - c = -c ≤ 0`, while the right side is `L ^ 2`. -/
theorem count_div_sub_eq_sum {D : ℕ} (hD : 0 < D) (L c : ℕ) :
    count D ((L : ℝ) / D - c) = ∑ u ∈ Finset.range L, (L - D * (u + c)) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hceil : ⌈(L : ℝ) / D - c⌉₊ ≤ L := by
    refine Nat.ceil_le.mpr ((sub_le_self _ (Nat.cast_nonneg c)).trans ?_)
    rw [div_le_iff₀ hDR]
    have : (1 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
  unfold count
  simp_rw [ceil_mul_div_sub_sub hD]
  refine Finset.sum_subset (Finset.range_mono hceil) fun u _ hu ↦ ?_
  have hle : (L : ℝ) / D - c ≤ u := Nat.ceil_le.mp (by simpa using hu)
  have hLe : (L : ℝ) ≤ ((D * (u + c) : ℕ) : ℝ) := by
    have hdiv : (L : ℝ) / D ≤ u + c := by linarith
    push_cast
    rwa [div_le_iff₀ hDR, mul_comm] at hdiv
  exact Nat.sub_eq_zero_of_le (by exact_mod_cast hLe)

end QuadraticStaircase
