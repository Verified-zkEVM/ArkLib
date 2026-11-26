/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.Polynomial.SymbolicInterpolationSurplus
public import Mathlib.Analysis.Real.Sqrt

/-!
# Parameters of the multiplier interpolation

The interpolation fixes a degree `d`, a length `n`, a multiplier degree `e`,
the degree fraction `ρ = d / n`, and a slack parameter `η`.
From them it builds a multiplicity, two degree budgets and two agreement thresholds.
Under the standing hypotheses, there are more unknowns than linear constraints.
The parameter definitions use real square roots and ceilings and are noncomputable.

Reed–Solomon codes use `e = 1`.
On the grid `𝔽_{q₀}^k` of `n = q₀^k` points, Reed–Muller codes use `e = n / q₀ = q₀^(k-1)`.
There `d = ρ n` is the degree after the reduction to univariate polynomials.
The standing condition `e · 4 / ρ ≤ n η²` is then `q₀ η² ≥ 4 / ρ`.

The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedSolomon.AffineParams`: the standing hypotheses on `d`, `n`, `e` and `η`.
* `ReedSolomon.affineMultiplicity`: the multiplicity `m = ⌈2 / η⌉`.
* `ReedSolomon.affineYZBudget`: the `(Y, Z)`-degree budget `D = ⌈(m + 1/2)² / (3ρ)⌉ - 1`,
  with natural-number subtraction.
* `ReedSolomon.affineThreshold`: the agreement threshold `A = ⌈(√ρ + η) n⌉`.
* `ReedSolomon.affinePersistenceThreshold`: the threshold `B = ⌈(√ρ + η / 2) n⌉ - e`,
  with natural-number subtraction.
* `ReedSolomon.affineRootBudget`: the `Z`-degree budget `M = min D ⌊(m A - e D - 1) / d⌋`,
  with natural-number subtraction.

## Main statements

* `ReedSolomon.sub_le_affinePersistenceThreshold`: `(√ρ + η / 2) n - e ≤ B`.
* `ReedSolomon.AffineParams.surplus`: more unknowns than constraints.
* `ReedSolomon.AffineParams.ceil_add_mul_yzBudget_le`: the budgets fit, `U + e D ≤ m A`.
* `ReedSolomon.AffineParams.mul_yzBudget_le`: `e D ≤ m A`.
* `ReedSolomon.AffineParams.four_mul_le`: `4 e ≤ d η²`.
* `ReedSolomon.AffineParams.persistenceThreshold_add_lt`: `B + e < A`.
* `ReedSolomon.AffineParams.bounds`: the order relations, such as `d + e < B < A ≤ n`.
* `ReedSolomon.AffineParams.yzBudget_le_nine_div`: `D ≤ 9 / (2 ρ η²)`.
* `ReedSolomon.AffineParams.mul_rootBudget_le`: `d M ≤ 3 n / η`.
* `ReedSolomon.AffineParams.card_div_sub_le`: `n / (A - B - e + 1) ≤ 2 / η`.
* `ReedSolomon.AffineParams.card_mul_sub_div_sq_sub_le`:
  `n (B - d - e) / (B² - n (d + e)) ≤ 4 / η`.
* `ReedSolomon.AffineParams.add_lt_persistenceThreshold` and
  `ReedSolomon.AffineParams.card_mul_add_lt_sq`: `d + e < B` and `n (d + e) < B²`.
* `ReedSolomon.AffineParams.sixty_four_mul_lt`: `64 e < n`.
* `ReedSolomon.affineCount_numerics_le`: the final numerical estimate for `k ≥ 1`.
* `ReedSolomon.affineThreshold_johnson`: the Johnson condition `n d < (A - 1)²` at the
  threshold `A`.

## References

The parameters are those of Lemma 4.2 and Section 4.1 of [CWYZ26].
Appendix A of [CWYZ26] uses them with `e = n / q₀` and the univariate degree `ρ n`.
The sufficient surplus sums constraints over all `s < m`.
The count (4.5) stops at `min(m - 1, M)`.
The surplus theorem proves the full-constraint inequality for these parameters.
Its key step is the paper's condition `e D ≤ m A - U` with `U = ⌈(m + 1/2) √ρ n⌉`.

The estimates are those of "The bound" in Appendix A of [CWYZ26].
For a Reed–Muller code of degree `d₀`, the univariate degree is `d = d₀ e`.
The side conditions `d + e < B` and `n (d + e) < B²` then read `(d₀ + 1) e < B`
and `n (d₀ + 1) e < B²`.
The paper derives both from `a − √b ≥ η/4`, which is not formalized.
The Lean proves `d + e < B`, `n (d + e) < B²` and `ℓ ≤ 4 / η` directly.
The paper's `q₀ > 64` is `64 e < n`.

The positive multiplier degree is a standing hypothesis, which the paper leaves implicit.
It gives `B + e < A`.
At `e = 0` the standing condition is void.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial.SymbolicInterpolation

/-- The multiplicity `⌈2 / η⌉`. -/
noncomputable def affineMultiplicity (η : ℝ) : ℕ := ⌈2 / η⌉₊

/-- The `(Y, Z)`-degree budget `⌈(m + 1/2)² / (3 d / n)⌉ - 1`, with natural-number subtraction.
-/
noncomputable def affineYZBudget (d n : ℕ) (η : ℝ) : ℕ :=
  ⌈((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))⌉₊ - 1

/-- The agreement threshold `⌈(√(d / n) + η) n⌉`. -/
noncomputable def affineThreshold (d n : ℕ) (η : ℝ) : ℕ := ⌈(√((d : ℝ) / n) + η) * n⌉₊

/-- The persistence threshold `⌈(√(d / n) + η / 2) n⌉ - e`, with natural-number subtraction. -/
noncomputable def affinePersistenceThreshold (d n e : ℕ) (η : ℝ) : ℕ :=
  ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ - e

/-- The `Z`-degree budget `min D ⌊(m A - e D - 1) / d⌋`, with natural-number subtraction. -/
noncomputable def affineRootBudget (d n e : ℕ) (η : ℝ) : ℕ :=
  min (affineYZBudget d n η)
    ((affineMultiplicity η * affineThreshold d n η - e * affineYZBudget d n η - 1) / d)

/-- The persistence threshold is at least `(√(d / n) + η / 2) n - e`. -/
theorem sub_le_affinePersistenceThreshold (d n e : ℕ) (η : ℝ) :
    (√((d : ℝ) / n) + η / 2) * n - e ≤ affinePersistenceThreshold d n e η := by
  have hle : ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ ≤ affinePersistenceThreshold d n e η + e := by
    unfold affinePersistenceThreshold
    omega
  have hcast : (⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ : ℝ) ≤
      (affinePersistenceThreshold d n e η : ℝ) + e := by
    exact_mod_cast hle
  linarith [Nat.le_ceil ((√((d : ℝ) / n) + η / 2) * n)]

/-- The standing hypotheses on the degree `d`, the length `n`, the multiplier degree `e` and the
slack parameter `η`. -/
structure AffineParams (d n e : ℕ) (η : ℝ) : Prop where
  /-- The degree is positive, so the degree fraction is positive. -/
  one_le : 1 ≤ d
  /-- The degree fraction is below one. -/
  degree_lt_length : d < n
  /-- The multiplier degree is positive. -/
  one_le_multiplierDegree : 1 ≤ e
  /-- The slack parameter is positive. -/
  pos : 0 < η
  /-- The threshold `√ρ + η` is below one. -/
  lt_one_sub : η < 1 - √((d : ℝ) / n)
  /-- The condition `e · 4 / (d / n) ≤ n η²` on the slack parameter.
  For positive `d` and `n`, it is equivalent to `4 e ≤ d η²`.
  The separate positivity hypotheses matter because real division by zero is zero. -/
  four_div_le : e * (4 / ((d : ℝ) / n)) ≤ n * η ^ 2

namespace AffineParams

variable {d n e : ℕ} {η : ℝ}

/-- The length is positive. -/
theorem card_pos (h : AffineParams d n e η) : (0 : ℝ) < n :=
  Nat.cast_pos.mpr (Nat.zero_lt_of_lt h.degree_lt_length)

/-- The degree fraction `d / n` is positive. -/
theorem degreeFraction_pos (h : AffineParams d n e η) : (0 : ℝ) < (d : ℝ) / n :=
  div_pos (by exact_mod_cast h.one_le) h.card_pos

/-- The degree fraction `d / n` is below one. -/
theorem degreeFraction_lt_one (h : AffineParams d n e η) : (d : ℝ) / n < 1 :=
  (div_lt_one h.card_pos).mpr (by exact_mod_cast h.degree_lt_length)

/-- The square root of the degree fraction is positive. -/
theorem sqrt_degreeFraction_pos (h : AffineParams d n e η) : 0 < √((d : ℝ) / n) :=
  Real.sqrt_pos.mpr h.degreeFraction_pos

/-- The square root of the degree fraction is below one. -/
theorem sqrt_degreeFraction_lt_one (h : AffineParams d n e η) : √((d : ℝ) / n) < 1 :=
  (Real.sqrt_lt' one_pos).mpr (by simpa using h.degreeFraction_lt_one)

/-- The slack parameter is below one. -/
theorem lt_one (h : AffineParams d n e η) : η < 1 := by
  linarith [h.lt_one_sub, h.sqrt_degreeFraction_pos]

/-- The degree is `√ρ² n`. -/
private theorem degree_eq (h : AffineParams d n e η) :
    (d : ℝ) = √((d : ℝ) / n) ^ 2 * n := by
  rw [Real.sq_sqrt h.degreeFraction_pos.le]
  field_simp [h.card_pos.ne']

/-- The multiplier degree is small: `4 e ≤ d η²`. -/
theorem four_mul_le (h : AffineParams d n e η) : 4 * (e : ℝ) ≤ d * η ^ 2 := by
  have := h.four_div_le
  rw [← mul_div_assoc, div_le_iff₀ h.degreeFraction_pos] at this
  have hd : (d : ℝ) = (d : ℝ) / n * n := by field_simp [h.card_pos.ne']
  rw [hd]
  linarith

/-- The multiplier degree is small: `4 e ≤ n η² √ρ²`. -/
private theorem four_mul_le_sqrt (h : AffineParams d n e η) :
    4 * (e : ℝ) ≤ n * η ^ 2 * √((d : ℝ) / n) ^ 2 := by
  have := h.four_mul_le
  rw [h.degree_eq] at this
  linarith

/-- The length exceeds `64` times the multiplier degree: `64 e < n`. -/
theorem sixty_four_mul_lt (h : AffineParams d n e η) : 64 * e < n := by
  have h4 := h.four_mul_le_sqrt
  have hn := h.card_pos
  have hr0 := h.sqrt_degreeFraction_pos
  have hη := h.pos
  -- `η √ρ < (1 - √ρ) √ρ ≤ 1 / 4`.
  have hηr : η * √((d : ℝ) / n) < 1 / 4 := by
    nlinarith [h.lt_one_sub, sq_nonneg (√((d : ℝ) / n) - 1 / 2)]
  have hsq : (η * √((d : ℝ) / n)) ^ 2 < 1 / 16 := by
    nlinarith [mul_pos hη hr0]
  have : (64 * e : ℝ) < n := by nlinarith
  exact_mod_cast this

/-- The multiplicity is at least `3`. -/
theorem three_le_multiplicity (h : AffineParams d n e η) : 3 ≤ affineMultiplicity η := by
  have : (2 : ℝ) < 2 / η := by
    rw [lt_div_iff₀ h.pos]
    linarith [h.lt_one]
  exact Nat.lt_ceil.mpr (by exact_mod_cast this)

/-- The multiplicity satisfies `2 ≤ m η`. -/
theorem two_le_multiplicity_mul (h : AffineParams d n e η) :
    2 ≤ (affineMultiplicity η : ℝ) * η :=
  (div_le_iff₀ h.pos).mp (Nat.le_ceil _)

/-- The multiplicity satisfies `m η < 2 + η`. -/
theorem multiplicity_mul_lt (h : AffineParams d n e η) :
    (affineMultiplicity η : ℝ) * η < 2 + η := by
  have := Nat.ceil_lt_add_one (div_pos two_pos h.pos).le
  have h' := mul_lt_mul_of_pos_right this h.pos
  rw [add_mul, div_mul_cancel₀ _ h.pos.ne', one_mul] at h'
  exact h'

/-- The `(Y, Z)`-degree budget is at most `(m + 1/2)² / (3 ρ)`. -/
private theorem yzBudget_le_real (h : AffineParams d n e η) :
    (affineYZBudget d n η : ℝ) ≤
      ((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n)) := by
  set X := ((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))
  have hX : 0 < X := div_pos (by positivity) (mul_pos three_pos h.degreeFraction_pos)
  have hceil := Nat.ceil_lt_add_one hX.le
  have h1 : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hX).ne'
  have : (affineYZBudget d n η : ℝ) + 1 = (⌈X⌉₊ : ℕ) := by
    simp only [affineYZBudget]
    exact_mod_cast Nat.sub_add_cancel h1
  linarith

/-- The interpolation budgets fit: `⌈d (m + 1/2) / √ρ⌉ + e D ≤ m A`. -/
theorem ceil_add_mul_yzBudget_le (h : AffineParams d n e η) :
    ⌈(d : ℝ) * (((affineMultiplicity η : ℝ) + 1 / 2) / √((d : ℝ) / n))⌉₊ +
      e * affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η := by
  set m : ℝ := (affineMultiplicity η : ℝ) with hm
  set r := √((d : ℝ) / n) with hr
  have hn := h.card_pos
  have hr0 := h.sqrt_degreeFraction_pos
  have hr1 := h.sqrt_degreeFraction_lt_one
  have hdr : (d : ℝ) = r ^ 2 * n := h.degree_eq
  have hm2 := h.two_le_multiplicity_mul
  have hm3 := h.multiplicity_mul_lt
  have hη := h.pos
  have hη1 := h.lt_one_sub
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  -- The two real quantities behind the ceiling and the budget.
  have hU : (d : ℝ) * ((m + 1 / 2) / r) = (m + 1 / 2) * n * r := by
    rw [hdr]; field_simp
  have hinv : e * (1 / ((d : ℝ) / n)) ≤ n * η ^ 2 / 4 := by
    have := h.four_div_le
    rw [div_eq_mul_one_div 4] at this
    linarith
  have hZ : (e : ℝ) * affineYZBudget d n η ≤ (m + 1 / 2) ^ 2 * (n * η ^ 2 / 4) / 3 := by
    calc (e : ℝ) * affineYZBudget d n η ≤ e * ((m + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))) :=
          mul_le_mul_of_nonneg_left h.yzBudget_le_real he
      _ = (m + 1 / 2) ^ 2 * (e * (1 / ((d : ℝ) / n))) / 3 := by ring
      _ ≤ _ := by gcongr
  -- The real inequality `U + e D + 1 ≤ m (√ρ + η) n`.
  have key : (m + 1 / 2) * n * r + (m + 1 / 2) ^ 2 * (n * η ^ 2 / 4) / 3 + 1 ≤
      m * ((r + η) * n) := by
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
        (Nat.zero_lt_of_lt h.degree_lt_length))
    have ht : (m + 1 / 2) * η < 7 / 2 := by nlinarith
    have hsq : ((m + 1 / 2) * η) ^ 2 ≤ 7 / 2 * ((m + 1 / 2) * η) := by
      nlinarith
    nlinarith
  have hceilU := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (d : ℝ) * ((m + 1 / 2) / r) by positivity)
  have hA : m * ((r + η) * n) ≤ m * (affineThreshold d n η : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
  have hreal : ((⌈(d : ℝ) * ((m + 1 / 2) / r)⌉₊ + e * affineYZBudget d n η : ℕ) : ℝ) <
      (affineMultiplicity η * affineThreshold d n η + 1 : ℕ) := by
    push_cast
    rw [← hm]
    linarith
  exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hreal)

/-- The ceiling `⌈(m + 1/2)² / (3 ρ)⌉` is `D + 1`. -/
theorem ceil_eq_yzBudget_add_one (h : AffineParams d n e η) :
    ⌈((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * √((d : ℝ) / n) ^ 2)⌉₊ =
      affineYZBudget d n η + 1 := by
  rw [Real.sq_sqrt h.degreeFraction_pos.le, affineYZBudget, Nat.sub_add_cancel]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.ceil_pos.mpr (div_pos (by positivity) (mul_pos three_pos h.degreeFraction_pos))))

/-- More unknowns than linear constraints: `n |constraints| < |monomials|`. -/
theorem surplus (h : AffineParams d n e η) :
    n * (constraintSupport (affineMultiplicity η) (affineYZBudget d n η + 1)).card <
      (monomialSupport d
        (affineMultiplicity η * affineThreshold d n η - e * affineYZBudget d n η)
        (affineRootBudget d n e η + 1) (affineYZBudget d n η + 1)).card := by
  have hcount := card_constraints_lt_monomials n d (affineMultiplicity η) √((d : ℝ) / n)
    (Nat.zero_lt_of_lt h.degree_lt_length) h.three_le_multiplicity h.sqrt_degreeFraction_pos
    h.sqrt_degreeFraction_lt_one.le
    (by rw [Real.sq_sqrt h.degreeFraction_pos.le]; field_simp [h.card_pos.ne'])
  rw [h.ceil_eq_yzBudget_add_one] at hcount
  refine hcount.trans_le (Finset.card_le_card ?_)
  have hkey := h.ceil_add_mul_yzBudget_le
  have hd := h.one_le
  have he := h.one_le_multiplierDegree
  have hD : affineYZBudget d n η ≤ e * affineYZBudget d n η := Nat.le_mul_of_pos_left _ he
  rintro ⟨j, i, t⟩ hmem
  simp only [mem_monomialSupport] at hmem ⊢
  refine ⟨Nat.lt_succ_of_le (le_min (by omega) ?_), by omega, hmem.2.2⟩
  rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
  omega

/-- The weighted `(Y, Z)`-degree budget is at most `m A`. -/
theorem mul_yzBudget_le (h : AffineParams d n e η) :
    e * affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η :=
  le_of_add_le_right h.ceil_add_mul_yzBudget_le

/-- The agreement threshold is at most `n`. -/
theorem threshold_le (h : AffineParams d n e η) : affineThreshold d n η ≤ n := by
  refine Nat.ceil_le.mpr ?_
  have := h.lt_one_sub
  nlinarith [h.card_pos]

/-- The ceiling behind the persistence threshold is `B + e`. -/
private theorem persistenceThreshold_add_eq (h : AffineParams d n e η) :
    affinePersistenceThreshold d n e η + e = ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ := by
  have h4 := h.four_mul_le_sqrt
  have hn := h.card_pos
  have hr0 := h.sqrt_degreeFraction_pos
  have hr1 := h.sqrt_degreeFraction_lt_one
  have hη := h.pos
  have hη1 := h.lt_one
  have hle : (e : ℝ) ≤ (√((d : ℝ) / n) + η / 2) * n := by
    have : η ^ 2 * √((d : ℝ) / n) ^ 2 ≤ η := by
      have : η * √((d : ℝ) / n) ^ 2 ≤ 1 := by nlinarith [mul_pos hr0 hr0]
      nlinarith
    nlinarith
  have hceil : e ≤ ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ := Nat.cast_le.mp (hle.trans (Nat.le_ceil _))
  unfold affinePersistenceThreshold
  omega

/-- The thresholds are far apart: `B + e < A`. -/
theorem persistenceThreshold_add_lt (h : AffineParams d n e η) :
    affinePersistenceThreshold d n e η + e < affineThreshold d n η := by
  rw [h.persistenceThreshold_add_eq]
  have hn := h.card_pos
  have hr0 := h.sqrt_degreeFraction_pos
  have hη := h.pos
  -- `η n > 2`, so the two real thresholds differ by more than one.
  have hηn : 2 < η * n := by
    have h4 := h.four_mul_le_sqrt
    have he : (1 : ℝ) ≤ e := by exact_mod_cast h.one_le_multiplierDegree
    have : η * √((d : ℝ) / n) ^ 2 < 1 := by
      nlinarith [h.sqrt_degreeFraction_lt_one, h.lt_one, mul_pos hr0 hr0]
    nlinarith [mul_pos hn hη, mul_pos hr0 hr0]
  have hceil := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ (√((d : ℝ) / n) + η / 2) * n by positivity)
  have hA : (√((d : ℝ) / n) + η) * n ≤ affineThreshold d n η := Nat.le_ceil _
  exact_mod_cast (show (⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ : ℝ) < affineThreshold d n η by
    nlinarith)

/-- The persistence threshold is below the agreement threshold. -/
theorem persistenceThreshold_lt (h : AffineParams d n e η) :
    affinePersistenceThreshold d n e η < affineThreshold d n η :=
  lt_of_le_of_lt (Nat.le_add_right _ _) h.persistenceThreshold_add_lt

/-- The gap between the thresholds is large: `n / (A - B - e + 1) ≤ 2 / η`.

The differences use natural-number subtraction. -/
theorem card_div_sub_le (h : AffineParams d n e η) :
    (n : ℝ) / (affineThreshold d n η - affinePersistenceThreshold d n e η - e + 1 : ℕ) ≤
      2 / η := by
  have hη := h.pos
  have hn := h.card_pos
  have hBA := h.persistenceThreshold_add_lt
  have hceil := h.persistenceThreshold_add_eq
  -- `A - B - e + 1 = A - ⌈(√ρ + η / 2) n⌉ + 1 > η n / 2`.
  have hx := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ (√((d : ℝ) / n) + η / 2) * n by positivity [h.sqrt_degreeFraction_pos])
  have hA : (√((d : ℝ) / n) + η) * n ≤ affineThreshold d n η := Nat.le_ceil _
  have hgap : η * n / 2 <
      ((affineThreshold d n η - affinePersistenceThreshold d n e η - e + 1 : ℕ) : ℝ) := by
    have heq : affineThreshold d n η - affinePersistenceThreshold d n e η - e + 1 +
        ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ = affineThreshold d n η + 1 := by
      omega
    have : ((affineThreshold d n η - affinePersistenceThreshold d n e η - e + 1 : ℕ) : ℝ) +
        (⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ : ℝ) = affineThreshold d n η + 1 := by
      exact_mod_cast heq
    linarith
  rw [div_le_div_iff₀ (by nlinarith) hη]
  linarith

/-- The real form of the side conditions, with `r = √ρ` and `d = r² n`. -/
private theorem persistence_key {n r η e B : ℝ} (hn : 0 < n) (hr0 : 0 < r) (hr1 : r < 1)
    (hη : 0 < η) (hrη : r + η < 1) (he0 : 0 ≤ e) (he : 4 * e ≤ n * η ^ 2 * r ^ 2)
    (hB : (r + η / 2) * n - e ≤ B) :
    0 < B - r ^ 2 * n - e ∧
      η * n * (B - r ^ 2 * n - e) ≤ 4 * (B ^ 2 - n * (r ^ 2 * n + e)) := by
  have hηr : η * r ^ 2 ≤ 1 := by nlinarith [mul_pos hr0 hr0]
  have heη : 4 * e ≤ η * n := by nlinarith [mul_pos hn hη]
  refine ⟨by nlinarith [mul_pos hn (mul_pos hr0 (sub_pos.mpr hr1))], ?_⟩
  -- The bound at the smallest admissible `B`, then monotonicity in `B`.
  set B₀ := (r + η / 2) * n - e with hB₀
  have hlin : e * (8 * r + 2 * η + 4) ≤ n * (3 * r * η + η ^ 2 / 2 + η * r ^ 2) := by
    have h1 : e * (8 * r + 2 * η + 4) ≤ n * η * (η * r ^ 2 * (2 * r + η / 2 + 1)) := by
      nlinarith
    have h2 : η * r ^ 2 * (2 * r + η / 2 + 1) ≤ 3 * r + η / 2 + r ^ 2 := by
      nlinarith [mul_pos hη hr0, mul_pos (mul_pos hη hr0) hr0]
    nlinarith [mul_pos hn hη]
  have hF₀ : η * n * (B₀ - r ^ 2 * n - e) ≤ 4 * (B₀ ^ 2 - n * (r ^ 2 * n + e)) := by
    rw [hB₀]
    nlinarith [sq_nonneg e]
  have hmono : 0 ≤ (B - B₀) * (4 * (B + B₀) - η * n) :=
    mul_nonneg (sub_nonneg.mpr hB) (by nlinarith [mul_pos hn hr0])
  nlinarith

/-- The side conditions in real form: `d + e < B` and
`η n (B - d - e) ≤ 4 (B² - n (d + e))`. -/
private theorem persistence_real (h : AffineParams d n e η) :
    (0 : ℝ) < affinePersistenceThreshold d n e η - d - e ∧
      η * n * ((affinePersistenceThreshold d n e η : ℝ) - d - e) ≤
        4 * ((affinePersistenceThreshold d n e η : ℝ) ^ 2 - n * (d + e)) := by
  have hkey := persistence_key h.card_pos h.sqrt_degreeFraction_pos h.sqrt_degreeFraction_lt_one
    h.pos (by linarith [h.lt_one_sub]) (Nat.cast_nonneg e) h.four_mul_le_sqrt
    (sub_le_affinePersistenceThreshold d n e η)
  rw [← h.degree_eq] at hkey
  exact ⟨by linarith [hkey.1], by linarith [hkey.2]⟩

/-- The persistence threshold exceeds the degree by more than `e`: `d + e < B`. -/
theorem add_lt_persistenceThreshold (h : AffineParams d n e η) :
    d + e < affinePersistenceThreshold d n e η := by
  have := h.persistence_real.1
  exact_mod_cast (show ((d + e : ℕ) : ℝ) < affinePersistenceThreshold d n e η by
    push_cast; linarith)

/-- The Johnson denominator is positive: `n (d + e) < B²`. -/
theorem card_mul_add_lt_sq (h : AffineParams d n e η) :
    n * (d + e) < affinePersistenceThreshold d n e η ^ 2 := by
  obtain ⟨h1, h2⟩ := h.persistence_real
  have := mul_pos (mul_pos h.pos h.card_pos) h1
  exact_mod_cast (show ((n * (d + e) : ℕ) : ℝ) < (affinePersistenceThreshold d n e η : ℝ) ^ 2 by
    push_cast; linarith)

/-- The Johnson factor is at most `4 / η`: `n (B - d - e) / (B² - n (d + e)) ≤ 4 / η`. -/
theorem card_mul_sub_div_sq_sub_le (h : AffineParams d n e η) :
    (n : ℝ) * ((affinePersistenceThreshold d n e η : ℝ) - d - e) /
        ((affinePersistenceThreshold d n e η : ℝ) ^ 2 - n * (d + e)) ≤ 4 / η := by
  obtain ⟨h1, h2⟩ := h.persistence_real
  have := mul_pos (mul_pos h.pos h.card_pos) h1
  rw [div_le_div_iff₀ (by linarith) h.pos]
  linarith

/-- The `(Y, Z)`-degree budget is at most `9 / (2 ρ η²)`. -/
theorem yzBudget_le_nine_div (h : AffineParams d n e η) :
    (affineYZBudget d n η : ℝ) ≤ 9 / (2 * ((d : ℝ) / n) * η ^ 2) := by
  have hη := h.pos
  have hρ := h.degreeFraction_pos
  have hm := h.multiplicity_mul_lt
  have hη1 := h.lt_one
  -- `(m + 1/2) η < 2 + 3 η / 2 ≤ 7 / 2`, so `(m + 1/2)² η² ≤ 49 / 4 ≤ 27 / 2`.
  have hsq : (((affineMultiplicity η : ℝ) + 1 / 2) * η) ^ 2 ≤ 27 / 2 := by
    have h0 : 0 ≤ ((affineMultiplicity η : ℝ) + 1 / 2) * η := by positivity
    nlinarith
  refine h.yzBudget_le_real.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The `Z`-degree budget satisfies `d M ≤ 3 n / η`. -/
theorem mul_rootBudget_le (h : AffineParams d n e η) :
    ((d * affineRootBudget d n e η : ℕ) : ℝ) ≤ 3 * n / η := by
  have hη := h.pos
  have hdM : d * affineRootBudget d n e η ≤ affineMultiplicity η * n := by
    calc d * affineRootBudget d n e η ≤ d * ((affineMultiplicity η * affineThreshold d n η -
          e * affineYZBudget d n η - 1) / d) := Nat.mul_le_mul_left _ (min_le_right _ _)
      _ ≤ affineMultiplicity η * affineThreshold d n η := (Nat.mul_div_le _ _).trans (by omega)
      _ ≤ affineMultiplicity η * n := Nat.mul_le_mul_left _ h.threshold_le
  have hreal : ((d * affineRootBudget d n e η : ℕ) : ℝ) ≤ (affineMultiplicity η : ℝ) * n := by
    exact_mod_cast hdM
  rw [le_div_iff₀ hη]
  nlinarith [h.multiplicity_mul_lt, h.lt_one, h.card_pos]

/-- The order relations between the parameters. -/
theorem bounds (h : AffineParams d n e η) :
    3 ≤ affineMultiplicity η ∧
      e * affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η ∧
      affineThreshold d n η ≤ n ∧ d + e < affinePersistenceThreshold d n e η ∧
      affinePersistenceThreshold d n e η + e < affineThreshold d n η ∧
      (n : ℝ) / (affineThreshold d n η - affinePersistenceThreshold d n e η - e + 1 : ℕ) ≤
        2 / η :=
  ⟨h.three_le_multiplicity, h.mul_yzBudget_le, h.threshold_le, h.add_lt_persistenceThreshold,
    h.persistenceThreshold_add_lt, h.card_div_sub_le⟩

end AffineParams

/-- The constant inequality `81/4 + 2 + 12ᵏ⁺¹ (9/2)ᵏ⁺² ≤ 2⁶ᵏ⁺⁸` for `k ≥ 1`. -/
private theorem constant_le {k : ℕ} (hk : 1 ≤ k) :
    81 / 4 + 2 + (12 : ℝ) ^ (k + 1) * (9 / 2) ^ (k + 2) ≤ 2 ^ (6 * k + 8) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : (12 : ℝ) ^ (1 + j + 1) * (9 / 2) ^ (1 + j + 2) = 13122 * 54 ^ j := by
    rw [show 1 + j + 1 = j + 2 by ring, show 1 + j + 2 = j + 3 by ring, pow_add, pow_add,
      show (54 : ℝ) ^ j = 12 ^ j * (9 / 2) ^ j by rw [← mul_pow]; norm_num]
    ring
  have h2 : (2 : ℝ) ^ (6 * (1 + j) + 8) = 16384 * 64 ^ j := by
    rw [show 6 * (1 + j) + 8 = 6 * j + 14 by ring, pow_add, pow_mul]
    ring
  have h54 : (54 : ℝ) ^ j ≤ 64 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have h64 : (1 : ℝ) ≤ 64 ^ j := one_le_pow₀ (by norm_num)
  rw [h1, h2]
  linarith

/-- The final numerical estimate of the error bound, for `k ≥ 1`.

Read `a` as `1 / η`, `b` as `1 / ρ`, and `n ≥ 1` as the length.
Read `D` as the `(Y, Z)`-degree budget and `v` as `n / (A - B - e + 1)`.
Read `dM` as the degree times the `Z`-degree budget.
Assume `a, b ≥ 1`, `0 ≤ D ≤ 9 b a² / 2`, `0 ≤ v ≤ 2 a` and `0 ≤ dM ≤ 3 a n`.
Then `D² + (2 dM v)ᵏ⁺¹ Dᵏ⁺² + 2 nᵏ⁺¹ a ≤ 2⁶ᵏ⁺⁸ nᵏ⁺¹ bᵏ⁺² a⁴ᵏ⁺⁶`.
Reed–Solomon codes use `k = 1`, and Reed–Muller codes in `k` variables use `k`.
The slack is small at the extreme point for `k = 1`.
There `n = a = b = 1`, `D = 9/2`, `v = 2` and `dM = 3`, and the left side is `13144.25 ≤ 2¹⁴`. -/
theorem affineCount_numerics_le {k : ℕ} (hk : 1 ≤ k) {n a b D v dM : ℝ} (hn : 1 ≤ n)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hD0 : 0 ≤ D) (hD : D ≤ 9 / 2 * b * a ^ 2) (hv0 : 0 ≤ v)
    (hv : v ≤ 2 * a) (hdM0 : 0 ≤ dM) (hdM : dM ≤ 3 * a * n) :
    D ^ 2 + (2 * dM * v) ^ (k + 1) * D ^ (k + 2) + 2 * n ^ (k + 1) * a ≤
      2 ^ (6 * k + 8) * (n ^ (k + 1) * b ^ (k + 2) * a ^ (4 * k + 6)) := by
  set X := n ^ (k + 1) * b ^ (k + 2) * a ^ (4 * k + 6)
  have hn1 : 1 ≤ n ^ (k + 1) := one_le_pow₀ hn
  have hb2 : b ^ 2 ≤ b ^ (k + 2) := pow_le_pow_right₀ hb (by omega)
  have hb0 : 1 ≤ b ^ (k + 2) := one_le_pow₀ hb
  have ha4 : a ^ 4 ≤ a ^ (4 * k + 6) := pow_le_pow_right₀ ha (by omega)
  have ha1 : a ≤ a ^ (4 * k + 6) := le_self_pow₀ ha (by omega)
  have h1 : D ^ 2 ≤ 81 / 4 * X := by
    calc D ^ 2 ≤ (9 / 2 * b * a ^ 2) ^ 2 := by gcongr
      _ = 81 / 4 * (1 * b ^ 2 * a ^ 4) := by ring
      _ ≤ 81 / 4 * (n ^ (k + 1) * b ^ (k + 2) * a ^ (4 * k + 6)) := by gcongr
  have h2 : (2 * dM * v) ^ (k + 1) * D ^ (k + 2) ≤ 12 ^ (k + 1) * (9 / 2) ^ (k + 2) * X := by
    calc (2 * dM * v) ^ (k + 1) * D ^ (k + 2) ≤
          (2 * (3 * a * n) * (2 * a)) ^ (k + 1) * (9 / 2 * b * a ^ 2) ^ (k + 2) := by gcongr
      _ = 12 ^ (k + 1) * (9 / 2) ^ (k + 2) * X := by ring
  have h3 : 2 * n ^ (k + 1) * a ≤ 2 * X := by
    have := mul_le_mul hb0 ha1 (by linarith) (by linarith)
    rw [one_mul] at this
    calc 2 * n ^ (k + 1) * a ≤ 2 * n ^ (k + 1) * (b ^ (k + 2) * a ^ (4 * k + 6)) := by gcongr
      _ = 2 * X := by ring
  have hX : 0 ≤ X := by positivity
  have hc := constant_le hk
  nlinarith

/-- At the threshold `A = ⌈(√ρ + η) n⌉`, the Johnson condition `n d < (A - 1)²` holds.

Here `1 ≤ d < n`, `ρ = d / n`, `0 < η`, and `n η² ≥ 4 / ρ`; the subtraction is in `ℕ`.
The last condition gives `n η > 1`, so `A - 1 > √ρ n = √(n d)`. -/
theorem affineThreshold_johnson {n d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < n)
    (hη : 0 < η) (hn : 4 / ((d : ℝ) / n) ≤ n * η ^ 2) :
    n * d < (affineThreshold d n η - 1) ^ 2 := by
  set A := affineThreshold d n η
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt hdn
  have hρ0 : (0 : ℝ) < (d : ℝ) / n := div_pos (by exact_mod_cast hd) hn0
  have hρ1 : (d : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast hdn.le)
  have h4 : (4 : ℝ) ≤ 4 / ((d : ℝ) / n) := by
    rw [le_div_iff₀ hρ0]
    linarith
  have hηn : 1 < η * n := by
    rcases lt_or_ge η 1 with hη1 | hη1
    · nlinarith
    · have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      nlinarith
  have hAle : (√((d : ℝ) / n) + η) * n ≤ A := Nat.le_ceil _
  have hA1 : 1 ≤ A := by
    have : (0 : ℝ) < A := by nlinarith [Real.sqrt_nonneg ((d : ℝ) / n)]
    exact_mod_cast this
  have hsq : √((d : ℝ) / n) ^ 2 = (d : ℝ) / n := Real.sq_sqrt hρ0.le
  have hlt : √((d : ℝ) / n) * n < (A : ℝ) - 1 := by linarith
  have hreal : (n : ℝ) * d < ((A : ℝ) - 1) ^ 2 := by
    have h0 : 0 ≤ √((d : ℝ) / n) * n := by positivity
    calc (n : ℝ) * d = (√((d : ℝ) / n) * n) ^ 2 := by
          rw [mul_pow, hsq]
          field_simp
      _ < ((A : ℝ) - 1) ^ 2 := by gcongr
  have : ((n * d : ℕ) : ℝ) < (((A - 1) ^ 2 : ℕ) : ℝ) := by
    push_cast [hA1]
    exact hreal
  exact_mod_cast this

end ReedSolomon
