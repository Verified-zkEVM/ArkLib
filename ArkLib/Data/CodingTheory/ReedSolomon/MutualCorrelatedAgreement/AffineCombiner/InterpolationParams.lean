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

end ReedSolomon
