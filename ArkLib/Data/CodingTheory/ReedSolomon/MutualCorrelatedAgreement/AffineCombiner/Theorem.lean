/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.ExceptionalCount
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Persistent
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability

/-!
# The affine MCA error of Reed–Solomon codes

Exceptional challenges split into persistent and nonpersistent ones.
The persistent challenges are counted through rational pairs.
The interpolant bounds the others.
For output degree `1 ≤ d < n`, write `ρ = d / n` and assume
`0 < η < 1 - √ρ` and `4 / ρ ≤ n η²`.
At the agreement threshold `⌈(√ρ + η) n⌉` and loss one, the error is at most
`4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.
The domain embedding supplies `n ≤ q`.

The error has type `ENNReal`.
`ReedSolomon.prob_isAffineExceptional_le` connects it to the native probability of an
exceptional candidate for any received word pair.
The counting bounds have no sampler assumptions.

## Main statements

* `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolation` and
  `ReedSolomon.affineMcaError_le_of_interpolation`: the bound for any interpolation parameters.
* `ReedSolomon.exists_affineExceptional_finset_card_le` and `ReedSolomon.affineMcaError_le`:
  the bound `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)` at the threshold `⌈(√ρ + η) n⌉`.

## References

The general bound corresponds to Theorem 4.10 of [CWYZ26], with a stronger sufficient
interpolation condition for freely chosen budgets, as described below.
The full constraint count includes every order `s < m`; (4.5) stops at `min(m - 1, M)`.
`AffineParams.surplus` proves the full condition for the parameter choice used in Theorem 1.1.
The final bound is its Theorem 1.1.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial.SymbolicInterpolation
open scoped Finset

/-- The final numerical estimate, with `a = 1 / η` and `b = 1 / ρ`. -/
private theorem numerics_aux {n a b m D v dM : ℝ} (hn : 1 ≤ n) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : m ≤ 3 * a) (hD0 : 0 ≤ D) (hD : D ≤ 49 / 12 * b * a ^ 2)
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * a) (hdM0 : 0 ≤ dM) (hdM : dM ≤ m * n) :
    D ^ 2 + 4 * dM ^ 2 * D ^ 3 * v ^ 2 + 2 * n ^ 2 * a ≤ 2 ^ 14 * (n ^ 2 * b ^ 3 * a ^ 10) := by
  have hT : 1 ≤ n ^ 2 * b * a ^ 6 := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) hb) (one_le_pow₀ ha)
  have h1 : D ^ 2 ≤ (49 / 12) ^ 2 * (n ^ 2 * b ^ 3 * a ^ 10) := by
    calc D ^ 2 ≤ (49 / 12 * b * a ^ 2) ^ 2 := by gcongr
      _ = (49 / 12) ^ 2 * (b ^ 2 * a ^ 4) * 1 := by ring
      _ ≤ (49 / 12) ^ 2 * (b ^ 2 * a ^ 4) * (n ^ 2 * b * a ^ 6) := by gcongr
      _ = _ := by ring
  have h2 : 4 * dM ^ 2 * D ^ 3 * v ^ 2 ≤
      4 * (3 * a * n) ^ 2 * (49 / 12 * b * a ^ 2) ^ 3 * (2 * a) ^ 2 := by
    have : dM ≤ 3 * a * n := hdM.trans (by gcongr)
    gcongr
  have h3 : 2 * n ^ 2 * a ≤ 2 * (n ^ 2 * b ^ 3 * a ^ 10) := by
    have : a ≤ b ^ 3 * a ^ 10 := by
      calc a = 1 * 1 * a := by ring
        _ ≤ b ^ 3 * a ^ 9 * a := by gcongr <;> [exact one_le_pow₀ hb; exact one_le_pow₀ ha]
        _ = _ := by ring
    nlinarith [sq_nonneg n]
  have hpos : 0 ≤ n ^ 2 * b ^ 3 * a ^ 10 := by positivity
  nlinarith

/-- The persistence threshold `B ≥ (r + η / 2) n - 1` exceeds `r² n + 1`, with a margin. -/
private theorem persistence_key {n r η B : ℝ} (hn : 0 < n) (hr0 : 0 < r) (hr1 : r < 1)
    (hη : 0 < η) (hrη : r + η < 1) (hnrη : 4 ≤ n * r * η) (hB : (r + η / 2) * n - 1 ≤ B) :
    0 < B - r ^ 2 * n - 1 ∧ η * n * (B - r ^ 2 * n - 1) ≤ 4 * (B ^ 2 - n * (r ^ 2 * n + 1)) := by
  have hηn : 4 ≤ η * n := by nlinarith [mul_pos hn hη]
  refine ⟨by nlinarith [mul_pos hn (mul_pos hr0 (sub_pos.mpr hr1))], ?_⟩
  have hB0 : η * n ≤ 4 * (B + ((r + η / 2) * n - 1)) := by nlinarith [mul_pos hn hr0]
  have hmono : 0 ≤ (B - ((r + η / 2) * n - 1)) * (4 * (B + ((r + η / 2) * n - 1)) - η * n) :=
    mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hB0)
  have hquad : n * (8 * r + 2 * η + 4) ≤ n * n * (3 * r * η + η ^ 2 / 2 + η * r ^ 2) := by
    nlinarith [mul_pos hn hη, mul_pos (mul_pos hn hη) (mul_pos hr0 hr0), sq_nonneg η]
  linear_combination hmono + hquad

/-- The thresholds satisfy `B < A ≤ n`. -/
private theorem threshold_facts {d n : ℕ} {η : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / n)) :
    affinePersistenceThreshold d n η < affineThreshold d n η ∧ affineThreshold d n η ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.sqrt_nonneg ((d : ℝ) / n)
  refine ⟨?_, Nat.ceil_le.mpr (by nlinarith)⟩
  have hmono : ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ ≤ affineThreshold d n η :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (by linarith) hn'.le)
  have hpos : 0 < affineThreshold d n η := Nat.ceil_pos.mpr (by positivity)
  unfold affinePersistenceThreshold
  omega

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- At loss one and threshold `A = ⌈(√ρ + η)n⌉`, a finite set contains every exceptional challenge.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, `ρ = d/n`, and
`0 < η < 1 - √ρ`.
The interpolation multiplicity is `m`, the `(Y, Z)`-degree budget is `D`, and the `Z`-degree
budget is `M`.
Set `B = ⌈(√ρ + η/2)n⌉ - 1` and assume `n(d + 1) < B²`.
The real Johnson factor is `J = n(B - d - 1)/(B² - n(d + 1))`, without a floor.
The bound is `#Ex ≤ J max q (n choose 2) + K`, where
`K = D² + 4d²M²D³(n/(A - B))²`.

The sufficient interpolation condition is
`n ∑_{s < m} (m - s)(D + 1 - s) < ∑_{j ≤ M} (mA - D - dj)(D + 1 - j)`,
with subtractions in `ℕ`.
The left sum counts constraints for every `s < m`.
`AffineParams.surplus` supplies this condition from `AffineParams d n η` for the budgets
`affineMultiplicity η`, `affineYZBudget d n η`, and `affineRootBudget d n η`. -/
theorem exists_affineExceptional_finset_card_le_of_interpolation [Fintype F] (domain : ι ↪ F)
    (f g : ι → F) {d m D M : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * affineThreshold d (Fintype.card ι) η - D) (M + 1) (D + 1)).card)
    (hJ : Fintype.card ι * (d + 1) < affinePersistenceThreshold d (Fintype.card ι) η ^ 2) :
    ∃ Ex : Finset (F × F), (#Ex : ℝ) ≤
        (Fintype.card ι : ℝ) * ((affinePersistenceThreshold d (Fintype.card ι) η : ℝ) - d - 1) /
            ((affinePersistenceThreshold d (Fintype.card ι) η : ℝ) ^ 2 -
              Fintype.card ι * (d + 1)) *
          max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) +
        (D ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) /
          (affineThreshold d (Fintype.card ι) η -
            affinePersistenceThreshold d (Fintype.card ι) η : ℕ)) ^ 2) ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d (affineThreshold d (Fintype.card ι) η) 1
        c.1 c.2 P := by
  classical
  set n := Fintype.card ι
  set A := affineThreshold d n η
  set B := affinePersistenceThreshold d n η
  obtain ⟨hBA, hAn⟩ := threshold_facts (Nat.zero_lt_of_lt hdn) hη hη1
  have hdB : d + 1 < B := by
    by_contra h
    have h1 : B ^ 2 ≤ (d + 1) ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    have h2 : (d + 1) ^ 2 ≤ n * (d + 1) := by rw [sq]; exact Nat.mul_le_mul_right _ hdn
    omega
  obtain ⟨Q, hQ⟩ := exists_isAffineInterpolant domain f g hsurplus
  set Pset : Finset (F × F) := {c | ∃ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P ∧
    IsAffinePersistent domain f g d B c.1 c.2 P}
  have hPset : ∀ c ∉ Pset, ∀ P, IsAffineExceptional domain f g d A 1 c.1 c.2 P →
      ¬ IsAffinePersistent domain f g d B c.1 c.2 P := fun c hc P hex hpers ↦
    hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, hex, hpers⟩)
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_le_of_interpolant domain f g
    hQ hd (by omega) hBA hAn Pset hPset
  have hpers := card_isAffineExceptional_persistent_le domain f g (A := A) hdB hJ
  exact ⟨Ex, by linarith, hgood⟩

/-- The affine error at loss one and threshold `A = ⌈(√ρ + η)n⌉` is at most
`ENNReal.ofReal ((J max q (n choose 2) + K)/q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, `ρ = d/n`, and
`0 < η < 1 - √ρ`.
The interpolation multiplicity is `m`, the `(Y, Z)`-degree budget is `D`, and the `Z`-degree
budget is `M`.
Set `B = ⌈(√ρ + η/2)n⌉ - 1` and assume `n(d + 1) < B²`.
The real Johnson factor is `J = n(B - d - 1)/(B² - n(d + 1))`, without a floor, and
`K = D² + 4d²M²D³(n/(A - B))²`.

The sufficient interpolation condition is
`n ∑_{s < m} (m - s)(D + 1 - s) < ∑_{j ≤ M} (mA - D - dj)(D + 1 - j)`,
with subtractions in `ℕ`.
The left sum counts constraints for every `s < m`.
`AffineParams.surplus` supplies this condition from `AffineParams d n η` for the budgets
`affineMultiplicity η`, `affineYZBudget d n η`, and `affineRootBudget d n η`. -/
theorem affineMcaError_le_of_interpolation [Fintype F] (domain : ι ↪ F) {d m D M : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * affineThreshold d (Fintype.card ι) η - D) (M + 1) (D + 1)).card)
    (hJ : Fintype.card ι * (d + 1) < affinePersistenceThreshold d (Fintype.card ι) η ^ 2) :
    affineMcaError domain d (affineThreshold d (Fintype.card ι) η) 1 ≤
      ENNReal.ofReal
        ((Fintype.card ι : ℝ) * ((affinePersistenceThreshold d (Fintype.card ι) η : ℝ) - d - 1) /
            ((affinePersistenceThreshold d (Fintype.card ι) η : ℝ) ^ 2 -
              Fintype.card ι * (d + 1)) *
          max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) / (Fintype.card F : ℝ) ^ 2 +
        (D ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) /
          (affineThreshold d (Fintype.card ι) η -
            affinePersistenceThreshold d (Fintype.card ι) η : ℕ)) ^ 2) /
          (Fintype.card F : ℝ) ^ 2) := by
  rw [← add_div]
  exact affineMcaError_le_of_forall_exists domain fun f g ↦
    exists_affineExceptional_finset_card_le_of_interpolation domain f g hd hdn hη hη1 hsurplus hJ

/-- With one point of agreement loss, few challenges are exceptional.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
At most `4 q / η + 2¹⁴ n² / (ρ³ η¹⁰)` challenges are exceptional at `⌈(√ρ + η) n⌉`. -/
theorem exists_affineExceptional_finset_card_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    {d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    ∃ E : Finset (F × F), (E.card : ℝ) ≤ 4 * Fintype.card F / η +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 / (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10) ∧
      ∀ c ∉ E, ∀ P, ¬ IsAffineExceptional domain f g d
        ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 c.1 c.2 P := by
  have hP : AffineParams d (Fintype.card ι) η := ⟨hd, hdn, hη, hη1, hn⟩
  set n := Fintype.card ι with hn_def
  set q := Fintype.card F
  set m := affineMultiplicity η
  set D := affineYZBudget d n η with hD_def
  set M := affineRootBudget d n η with hM_def
  set A := affineThreshold d n η with hA_def
  set B := affinePersistenceThreshold d n η with hB_def
  set r := √((d : ℝ) / n)
  have hn0 := hP.card_pos
  have hr0 := hP.sqrt_degreeFraction_pos
  have hr1 := hP.sqrt_degreeFraction_lt_one
  have hρ0 := hP.degreeFraction_pos
  have hη1' := hP.lt_one
  have hrr : r ^ 2 * n = d := by rw [Real.sq_sqrt hρ0.le]; field_simp
  -- The persistence threshold is large.
  have hB : (r + η / 2) * n - 1 ≤ (B : ℝ) := by
    have hy : 0 < (r + η / 2) * n := by positivity
    have h1 : 1 ≤ ⌈(r + η / 2) * n⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy).ne'
    have hle : (B : ℝ) + 1 = (⌈(r + η / 2) * n⌉₊ : ℕ) := by
      simp only [B, affinePersistenceThreshold]
      exact_mod_cast Nat.sub_add_cancel h1
    linarith [Nat.le_ceil ((r + η / 2) * n)]
  have hnrη : 4 ≤ n * r * η := by
    have h4 : 4 ≤ n * η ^ 2 * (r ^ 2) := by
      rw [Real.sq_sqrt hρ0.le]
      have := (div_le_iff₀ hρ0).mp hn
      linarith
    have hrη : r * η ≤ 1 := by nlinarith
    nlinarith [mul_pos (mul_pos hn0 hr0) hη]
  obtain ⟨hgap, hkey⟩ := persistence_key hn0 hr0 hr1 hη (by linarith) hnrη hB
  rw [hrr] at hgap hkey
  have hJ : n * (d + 1) < B ^ 2 := by
    have : (n : ℝ) * (d + 1) < (B : ℝ) ^ 2 := by nlinarith [mul_pos hη hn0]
    exact_mod_cast this
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_le_of_interpolation domain f g
    (m := m) (D := D) (M := M) hd hdn hη hη1 hP.surplus hJ
  refine ⟨Ex, hcard.trans ?_, hgood⟩
  rw [← hn_def, ← hA_def, ← hB_def]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- The persistent part: `ℓ ≤ 4 / η` and `max q (n choose 2) ≤ q + n² / 2`.
  have hden : (0 : ℝ) < (B : ℝ) ^ 2 - n * (d + 1) := by nlinarith [mul_pos hη hn0]
  have hℓ : (n : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - n * (d + 1)) ≤ 4 / η := by
    rw [div_le_div_iff₀ hden hη]
    linarith
  have hC : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    simpa using Nat.choose_le_pow_div (α := ℝ) 2 n
  have hmax : max (q : ℝ) ((n.choose 2 : ℕ) : ℝ) ≤ q + (n : ℝ) ^ 2 / 2 :=
    max_le (by linarith [sq_nonneg (n : ℝ)]) (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  have hpers : (n : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - n * (d + 1)) *
      max (q : ℝ) ((n.choose 2 : ℕ) : ℝ) ≤ 4 * q / η + 2 * (n : ℝ) ^ 2 * (1 / η) := by
    calc _ ≤ 4 / η * (q + (n : ℝ) ^ 2 / 2) :=
          mul_le_mul hℓ hmax (by positivity) (by positivity)
      _ = _ := by ring
  -- The nonpersistent part, by the crude bounds on `m`, `D`, `M` and `n / (A - B)`.
  have hm : (m : ℝ) ≤ 3 * (1 / η) := by
    have := hP.multiplicity_mul_lt
    rw [mul_one_div, le_div_iff₀ hη]
    linarith
  have hD : (D : ℝ) ≤ 49 / 12 * (n / d) * (1 / η) ^ 2 := by
    set X := ((m : ℝ) + 1 / 2) ^ 2 / (3 * ((d : ℝ) / n))
    have hX : 0 < X := by positivity
    have hceil := Nat.ceil_lt_add_one hX.le
    have h1 : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hX).ne'
    have hDX : (D : ℝ) ≤ X := by
      have : (D : ℝ) + 1 = (⌈X⌉₊ : ℕ) := by
        simp only [D, affineYZBudget]
        exact_mod_cast Nat.sub_add_cancel h1
      linarith
    have hmη : ((m : ℝ) + 1 / 2) * η ≤ 7 / 2 := by
      nlinarith [hP.multiplicity_mul_lt]
    have hm2 : ((m : ℝ) + 1 / 2) ^ 2 ≤ 49 / 4 * (1 / η) ^ 2 := by
      have hle : (m : ℝ) + 1 / 2 ≤ 7 / 2 * (1 / η) := by
        rw [mul_one_div, le_div_iff₀ hη]
        linarith
      calc ((m : ℝ) + 1 / 2) ^ 2 ≤ (7 / 2 * (1 / η)) ^ 2 := by gcongr
        _ = _ := by ring
    refine hDX.trans ?_
    calc X = ((m : ℝ) + 1 / 2) ^ 2 * (n / d) / 3 := by
          simp only [X]
          field_simp
      _ ≤ 49 / 4 * (1 / η) ^ 2 * (n / d) / 3 := by gcongr
      _ = _ := by ring
  have hv : (n : ℝ) / (A - B : ℕ) ≤ 2 * (1 / η) := by
    rw [mul_one_div]
    exact hP.card_div_sub_le
  have hdM : d * M ≤ m * n := by
    have h1 : M ≤ (m * A - D - 1) / d := min_le_right _ _
    calc d * M ≤ d * ((m * A - D - 1) / d) := Nat.mul_le_mul_left _ h1
      _ ≤ m * A - D - 1 := Nat.mul_div_le _ _
      _ ≤ m * A := by omega
      _ ≤ m * n := Nat.mul_le_mul_left _ hP.threshold_le
  have hdM' : ((d * M : ℕ) : ℝ) ≤ m * n := by exact_mod_cast hdM
  have hnum := numerics_aux (n := n) (a := 1 / η) (b := n / d) (m := m) (D := D)
    (v := (n : ℝ) / (A - B : ℕ)) (dM := ((d * M : ℕ) : ℝ))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (Nat.zero_lt_of_lt hdn)))
    ((one_le_div hη).mpr hP.lt_one.le)
    ((one_le_div hd0).mpr (by exact_mod_cast hdn.le)) hm (Nat.cast_nonneg _) hD
    (by positivity) hv (Nat.cast_nonneg _) hdM'
  have hfin : 2 ^ 14 * ((n : ℝ) ^ 2 * (n / d) ^ 3 * (1 / η) ^ 10) =
      2 ^ 14 * (n : ℝ) ^ 2 / (((d : ℝ) / n) ^ 3 * η ^ 10) := by
    field_simp
  push_cast at hnum
  have hterm : (D : ℝ) ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((n : ℝ) / (A - B : ℕ)) ^ 2 =
      D ^ 2 + 4 * (d * M) ^ 2 * D ^ 3 * ((n : ℝ) / (A - B : ℕ)) ^ 2 := by ring
  linarith [hnum, hpers, hfin, hterm]

/-- With one point of loss, the affine MCA error is at most `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
The threshold is `⌈(√ρ + η) n⌉`. -/
theorem affineMcaError_le [Fintype F] (domain : ι ↪ F) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    affineMcaError domain d ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 ≤
      ENNReal.ofReal (4 / (η * Fintype.card F) + 2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 /
        (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10 * (Fintype.card F : ℝ) ^ 2)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (affineMcaError_le_of_forall_exists domain fun f g ↦
    exists_affineExceptional_finset_card_le domain f g hd hdn hη hη1 hn).trans (le_of_eq ?_)
  congr 1
  field_simp

end ReedSolomon
