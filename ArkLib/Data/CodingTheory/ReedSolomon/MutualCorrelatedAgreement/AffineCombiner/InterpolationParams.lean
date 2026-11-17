/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.Polynomial.SymbolicInterpolationSurplus
public import Mathlib.Analysis.Real.Sqrt

/-!
# Parameters of the affine interpolation

The interpolation fixes a degree `d`, a length `n`, the degree fraction `ρ = d / n`,
and a slack parameter `η`.
From them it builds a multiplicity, two degree budgets and two agreement thresholds.
Under the standing hypotheses, there are more unknowns than linear constraints.
The parameter definitions use real square roots and ceilings and are noncomputable.

## Main definitions

* `ReedSolomon.AffineParams`: the standing hypotheses on `d`, `n` and `η`.
* `ReedSolomon.affineMultiplicity`: the multiplicity `m = ⌈2 / η⌉`.
* `ReedSolomon.affineYZBudget`: the `(Y, Z)`-degree budget `D = ⌈(m + 1/2)² / (3ρ)⌉ - 1`.
* `ReedSolomon.affineThreshold`: the agreement threshold `A = ⌈(√ρ + η) n⌉`.
* `ReedSolomon.affinePersistenceThreshold`: the threshold `B = ⌈(√ρ + η / 2) n⌉ - 1`.
* `ReedSolomon.affineRootBudget`: the `Z`-degree budget `M = min D ⌊(m A - D - 1) / d⌋`.

## Main statements

* `ReedSolomon.AffineParams.surplus`: more unknowns than constraints.
* `ReedSolomon.AffineParams.bounds`: the order relations, such as `d ≤ B < A ≤ n`.

## References

The parameters are those of Lemma 4.2 and Section 4.1 of [CWYZ26].
The sufficient surplus sums constraints over all `s < m`, whereas (4.5) stops at
`min(m - 1, M)`.
`AffineParams.surplus` proves the full-constraint inequality for these parameters.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial.SymbolicInterpolation

/-- The multiplicity `⌈2 / η⌉`. -/
noncomputable def affineMultiplicity (η : ℝ) : ℕ := ⌈2 / η⌉₊

/-- The `(Y, Z)`-degree budget `⌈(m + 1/2)² / (3 d / n)⌉ - 1`. -/
noncomputable def affineYZBudget (d n : ℕ) (η : ℝ) : ℕ :=
  ⌈((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))⌉₊ - 1

/-- The agreement threshold `⌈(√(d / n) + η) n⌉`. -/
noncomputable def affineThreshold (d n : ℕ) (η : ℝ) : ℕ := ⌈(√((d : ℝ) / n) + η) * n⌉₊

/-- The persistence threshold `⌈(√(d / n) + η / 2) n⌉ - 1`. -/
noncomputable def affinePersistenceThreshold (d n : ℕ) (η : ℝ) : ℕ :=
  ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ - 1

/-- The `Z`-degree budget `min D ⌊(m A - D - 1) / d⌋`. -/
noncomputable def affineRootBudget (d n : ℕ) (η : ℝ) : ℕ :=
  min (affineYZBudget d n η)
    ((affineMultiplicity η * affineThreshold d n η - affineYZBudget d n η - 1) / d)

/-- The standing hypotheses on the degree `d`, the length `n` and the slack parameter `η`. -/
structure AffineParams (d n : ℕ) (η : ℝ) : Prop where
  /-- The degree is positive, so the degree fraction is positive. -/
  one_le : 1 ≤ d
  /-- The degree fraction is below one. -/
  degree_lt_length : d < n
  /-- The slack parameter is positive. -/
  pos : 0 < η
  /-- The threshold `√ρ + η` is below one. -/
  lt_one_sub : η < 1 - √((d : ℝ) / n)
  /-- The paper's condition `4 / ρ ≤ n η²`.
  For positive `d` and `n`, it is equivalent to `4 ≤ d η²`, independently of `n`.
  The separate positivity hypotheses matter because real division by zero is zero. -/
  four_div_le : 4 / ((d : ℝ) / n) ≤ n * η ^ 2

namespace AffineParams

variable {d n : ℕ} {η : ℝ}

/-- The length is positive. -/
theorem card_pos (h : AffineParams d n η) : (0 : ℝ) < n :=
  Nat.cast_pos.mpr (Nat.zero_lt_of_lt h.degree_lt_length)

/-- The degree fraction `d / n` is positive. -/
theorem degreeFraction_pos (h : AffineParams d n η) : (0 : ℝ) < (d : ℝ) / n :=
  div_pos (by exact_mod_cast h.one_le) h.card_pos

/-- The degree fraction `d / n` is below one. -/
theorem degreeFraction_lt_one (h : AffineParams d n η) : (d : ℝ) / n < 1 :=
  (div_lt_one h.card_pos).mpr (by exact_mod_cast h.degree_lt_length)

/-- The square root of the degree fraction is positive. -/
theorem sqrt_degreeFraction_pos (h : AffineParams d n η) : 0 < √((d : ℝ) / n) :=
  Real.sqrt_pos.mpr h.degreeFraction_pos

/-- The square root of the degree fraction is below one. -/
theorem sqrt_degreeFraction_lt_one (h : AffineParams d n η) : √((d : ℝ) / n) < 1 :=
  (Real.sqrt_lt' one_pos).mpr (by simpa using h.degreeFraction_lt_one)

/-- The slack parameter is below one. -/
theorem lt_one (h : AffineParams d n η) : η < 1 := by
  linarith [h.lt_one_sub, h.sqrt_degreeFraction_pos]

/-- The multiplicity is at least `3`. -/
theorem three_le_multiplicity (h : AffineParams d n η) : 3 ≤ affineMultiplicity η := by
  have : (2 : ℝ) < 2 / η := by
    rw [lt_div_iff₀ h.pos]
    linarith [h.lt_one]
  exact Nat.lt_ceil.mpr (by exact_mod_cast this)

/-- The multiplicity satisfies `2 ≤ m η`. -/
theorem two_le_multiplicity_mul (h : AffineParams d n η) :
    2 ≤ (affineMultiplicity η : ℝ) * η :=
  (div_le_iff₀ h.pos).mp (Nat.le_ceil _)

/-- The multiplicity satisfies `m η < 2 + η`. -/
theorem multiplicity_mul_lt (h : AffineParams d n η) :
    (affineMultiplicity η : ℝ) * η < 2 + η := by
  have := Nat.ceil_lt_add_one (div_pos two_pos h.pos).le
  have h' := mul_lt_mul_of_pos_right this h.pos
  rw [add_mul, div_mul_cancel₀ _ h.pos.ne', one_mul] at h'
  exact h'

/-- The interpolation budgets fit: `⌈d (m + 1/2) / √ρ⌉ + D ≤ m A`. -/
theorem ceil_add_yzBudget_le (h : AffineParams d n η) :
    ⌈(d : ℝ) * (((affineMultiplicity η : ℝ) + 1 / 2) / √((d : ℝ) / n))⌉₊ +
      affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η := by
  set m : ℝ := (affineMultiplicity η : ℝ) with hm
  set r := √((d : ℝ) / n) with hr
  have hn := h.card_pos
  have hr0 := h.sqrt_degreeFraction_pos
  have hr1 := h.sqrt_degreeFraction_lt_one
  have hrr : r ^ 2 = (d : ℝ) / n := Real.sq_sqrt h.degreeFraction_pos.le
  have hdr : (d : ℝ) = n * r ^ 2 := by rw [hrr]; field_simp
  have hm2 := h.two_le_multiplicity_mul
  have hm3 := h.multiplicity_mul_lt
  have hη := h.pos
  have hη1 := h.lt_one
  -- The two real quantities behind the ceilings.
  have hU : (d : ℝ) * ((m + 1 / 2) / r) = (m + 1 / 2) * n * r := by
    rw [hdr]; field_simp
  have hinv : 1 / ((d : ℝ) / n) ≤ n * η ^ 2 / 4 := by
    have := h.four_div_le
    rw [div_eq_mul_one_div 4] at this
    linarith
  have hZ : (m + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n)) ≤ (m + 1 / 2) ^ 2 * (n * η ^ 2 / 4) / 3 := by
    have he : (m + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n)) =
        (m + 1 / 2) ^ 2 * (1 / ((d : ℝ) / n)) / 3 := by
      rw [mul_one_div, div_div, mul_comm 3]
    rw [he]
    gcongr
  have hn5 : (4 : ℝ) < n := by
    have h4 : 4 / ((d : ℝ) / n) < n := by
      calc 4 / ((d : ℝ) / n) ≤ n * η ^ 2 := h.four_div_le
        _ < n * 1 := by
          apply mul_lt_mul_of_pos_left _ hn
          nlinarith
        _ = n := mul_one _
    have : (4 : ℝ) < 4 / ((d : ℝ) / n) := by
      rw [lt_div_iff₀ h.degreeFraction_pos]; nlinarith [h.degreeFraction_lt_one]
    linarith
  -- The real inequality `U + D + 1 ≤ m (√ρ + η) n`.
  have key : (m + 1 / 2) * n * r + (m + 1 / 2) ^ 2 * (n * η ^ 2 / 4) / 3 + 1 ≤
      m * ((r + η) * n) := by
    have ht : (m + 1 / 2) * η < 7 / 2 := by nlinarith
    have hsq : ((m + 1 / 2) * η) ^ 2 ≤ 7 / 2 * ((m + 1 / 2) * η) := by
      nlinarith
    nlinarith
  have hceilU := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (d : ℝ) * ((m + 1 / 2) / r) by positivity)
  have hceilZ := Nat.ceil_lt_add_one
    (show (0 : ℝ) ≤ (m + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n)) by positivity)
  have hA : m * ((r + η) * n) ≤ m * (affineThreshold d n η : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
  have hreal : ((⌈(d : ℝ) * ((m + 1 / 2) / r)⌉₊ +
      ⌈(m + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))⌉₊ : ℕ) : ℝ) <
      (affineMultiplicity η * affineThreshold d n η + 1 : ℕ) := by
    push_cast
    rw [← hm]
    linarith
  have hnat := Nat.cast_lt.mp hreal
  unfold affineYZBudget
  rw [← hm]
  omega

/-- The ceiling `⌈(m + 1/2)² / (3 ρ)⌉` is `D + 1`. -/
theorem ceil_eq_yzBudget_add_one (h : AffineParams d n η) :
    ⌈((affineMultiplicity η : ℝ) + 1 / 2) ^ 2 / (3 * √((d : ℝ) / n) ^ 2)⌉₊ =
      affineYZBudget d n η + 1 := by
  rw [Real.sq_sqrt h.degreeFraction_pos.le, affineYZBudget, Nat.sub_add_cancel]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.ceil_pos.mpr (div_pos (by positivity) (mul_pos three_pos h.degreeFraction_pos))))

/-- More unknowns than linear constraints: `n |constraints| < |monomials|`. -/
theorem surplus (h : AffineParams d n η) :
    n * (constraintSupport (affineMultiplicity η) (affineYZBudget d n η + 1)).card <
      (monomialSupport d (affineMultiplicity η * affineThreshold d n η - affineYZBudget d n η)
        (affineRootBudget d n η + 1) (affineYZBudget d n η + 1)).card := by
  have hcount := card_constraints_lt_monomials n d (affineMultiplicity η) √((d : ℝ) / n)
    (Nat.zero_lt_of_lt h.degree_lt_length) h.three_le_multiplicity h.sqrt_degreeFraction_pos
    h.sqrt_degreeFraction_lt_one.le
    (by rw [Real.sq_sqrt h.degreeFraction_pos.le]; field_simp [h.card_pos.ne'])
  rw [h.ceil_eq_yzBudget_add_one] at hcount
  refine hcount.trans_le (Finset.card_le_card ?_)
  have hkey := h.ceil_add_yzBudget_le
  have hd := h.one_le
  rintro ⟨j, i, t⟩ hmem
  simp only [mem_monomialSupport] at hmem ⊢
  refine ⟨Nat.lt_succ_of_le (le_min (by omega) ?_), by omega, hmem.2.2⟩
  rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
  omega

/-- The `(Y, Z)`-degree budget is at most `m A`. -/
theorem yzBudget_le (h : AffineParams d n η) :
    affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η :=
  le_of_add_le_right h.ceil_add_yzBudget_le

/-- The agreement threshold is at most `n`. -/
theorem threshold_le (h : AffineParams d n η) : affineThreshold d n η ≤ n := by
  refine Nat.ceil_le.mpr ?_
  have := h.lt_one_sub
  nlinarith [h.card_pos]

/-- The degree is at most the persistence threshold. -/
theorem le_persistenceThreshold (h : AffineParams d n η) :
    d ≤ affinePersistenceThreshold d n η := by
  have hlt : (d : ℝ) < (√((d : ℝ) / n) + η / 2) * n := by
    have hr0 := h.sqrt_degreeFraction_pos
    have hr1 := h.sqrt_degreeFraction_lt_one
    have hdr : (d : ℝ) = n * √((d : ℝ) / n) ^ 2 := by
      rw [Real.sq_sqrt h.degreeFraction_pos.le]; field_simp [h.card_pos.ne']
    have hn := h.card_pos
    have hη := h.pos
    set r := √((d : ℝ) / n)
    rw [hdr]
    nlinarith [mul_pos hn (mul_pos hr0 (sub_pos.mpr hr1)), mul_pos hn hη]
  have := Nat.lt_ceil.mpr hlt
  unfold affinePersistenceThreshold
  omega

/-- The persistence threshold is below the agreement threshold. -/
theorem persistenceThreshold_lt (h : AffineParams d n η) :
    affinePersistenceThreshold d n η < affineThreshold d n η := by
  have hmono : ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ ≤ affineThreshold d n η :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (by linarith [h.pos]) h.card_pos.le)
  have hpos : 0 < affineThreshold d n η :=
    Nat.ceil_pos.mpr (mul_pos (add_pos h.sqrt_degreeFraction_pos h.pos) h.card_pos)
  unfold affinePersistenceThreshold
  omega

/-- The gap between the thresholds is large: `n / (A - B) ≤ 2 / η`. -/
theorem card_div_sub_le (h : AffineParams d n η) :
    (n : ℝ) / (affineThreshold d n η - affinePersistenceThreshold d n η : ℕ) ≤ 2 / η := by
  have hBA := h.persistenceThreshold_lt
  have hη := h.pos
  have hn := h.card_pos
  -- `B < (√ρ + η / 2) n` and `(√ρ + η) n ≤ A`, so `η n / 2 < A - B`.
  have hB : (affinePersistenceThreshold d n η : ℝ) < (√((d : ℝ) / n) + η / 2) * n := by
    have hceil := Nat.ceil_lt_add_one
      (mul_pos (add_pos h.sqrt_degreeFraction_pos (half_pos hη)) hn).le
    have h1 : 1 ≤ ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ := Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr
        (mul_pos (add_pos h.sqrt_degreeFraction_pos (half_pos hη)) hn)))
    have hle : (affinePersistenceThreshold d n η : ℝ) + 1 =
        (⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ : ℕ) := by
      unfold affinePersistenceThreshold
      exact_mod_cast Nat.sub_add_cancel h1
    linarith
  have hA : (√((d : ℝ) / n) + η) * n ≤ affineThreshold d n η := Nat.le_ceil _
  have hgap : η * n / 2 < ((affineThreshold d n η - affinePersistenceThreshold d n η : ℕ) : ℝ) := by
    rw [Nat.cast_sub hBA.le]
    linarith
  rw [div_le_div_iff₀ (by nlinarith) hη]
  linarith

/-- The order relations between the parameters. -/
theorem bounds (h : AffineParams d n η) :
    3 ≤ affineMultiplicity η ∧
      affineYZBudget d n η ≤ affineMultiplicity η * affineThreshold d n η ∧
      affineThreshold d n η ≤ n ∧ d ≤ affinePersistenceThreshold d n η ∧
      affinePersistenceThreshold d n η < affineThreshold d n η ∧
      (n : ℝ) / (affineThreshold d n η - affinePersistenceThreshold d n η : ℕ) ≤ 2 / η :=
  ⟨h.three_le_multiplicity, h.yzBudget_le, h.threshold_le, h.le_persistenceThreshold,
    h.persistenceThreshold_lt, h.card_div_sub_le⟩

end AffineParams

end ReedSolomon
