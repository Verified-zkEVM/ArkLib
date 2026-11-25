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
The map counts take challenges from a finite type `K` through an injective map `K ↪ E`.
They use `q = |K|`, even when the domain lies in `E`.
A subfield of `E` is the main example.

The error has type `ENNReal`.
`ReedSolomon.prob_isAffineExceptional_le` connects it to the native probability of an
exceptional candidate for any received word pair.
The counting bounds have no sampler assumptions.

## Main statements

* `ReedSolomon.exists_affineExceptional_finset_card_map_le` and
  `ReedSolomon.exists_affineExceptional_finset_card_map_le_of_interpolation`: counts for
  challenges from a finite subset of `E`.
* `ReedSolomon.exists_affineExceptional_finset_card_le_of_interpolation` and
  `ReedSolomon.affineMcaError_le_of_interpolation`: the bound for any interpolation parameters.
* `ReedSolomon.exists_affineExceptional_finset_card_le` and `ReedSolomon.affineMcaError_le`:
  the bound `4 / (η q) + 2¹⁴ n² / (ρ³ η¹⁰ q²)` at the threshold `⌈(√ρ + η) n⌉`.

## References

The general bound corresponds to Theorem 4.10 of [CWYZ26], with a stronger sufficient
interpolation condition for freely chosen budgets, as described below.
The full constraint count includes every order `s < m`; (4.5) stops at `min(m - 1, M)`.
The parameter choice of Theorem 1.1 satisfies the full condition.
The final bound is Theorem 1.1 of [CWYZ26].

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial.SymbolicInterpolation
open scoped Finset

/-- The thresholds satisfy `B < A ≤ n`. -/
private theorem threshold_facts {d n : ℕ} {η : ℝ} (hn : 0 < n) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / n)) :
    affinePersistenceThreshold d n 1 η < affineThreshold d n η ∧ affineThreshold d n η ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.sqrt_nonneg ((d : ℝ) / n)
  refine ⟨?_, Nat.ceil_le.mpr (by nlinarith)⟩
  have hmono : ⌈(√((d : ℝ) / n) + η / 2) * n⌉₊ ≤ affineThreshold d n η :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (by linarith) hn'.le)
  have hpos : 0 < affineThreshold d n η := Nat.ceil_pos.mpr (by positivity)
  unfold affinePersistenceThreshold
  omega

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- At loss one and threshold `A = ⌈(√ρ + η)n⌉`, few challenges from `K` are exceptional.

Let `E` be a finite field and `φ : K ↪ E` an injective map from a finite type.
Challenges come from any finite subset of `E`; a subfield is the main example.
A challenge `(α, β) ∈ K²` is exceptional if `(φ α, φ β)` has an exceptional candidate over `E`.
A finite set `Ex` contains every exceptional challenge.
Here `n` is the domain size, `q = |K|`, `1 ≤ d < n`, `ρ = d/n`, and `0 < η < 1 - √ρ`.
The interpolation multiplicity is `m`, the `(Y, Z)`-degree budget is `D`, and the `Z`-degree
budget is `M`.
Set `B = ⌈(√ρ + η/2)n⌉ - 1` and assume `n(d + 1) < B²`.
The real Johnson factor is `J = n(B - d - 1)/(B² - n(d + 1))`, without a floor.
Set `N = D² + 4d²M²D³(n/(A - B))²`.
The bound is `#Ex ≤ J max q (n choose 2) + N`.

The sufficient interpolation condition is
`n ∑_{s < m} (m - s)(D + 1 - s) < ∑_{j ≤ M} (mA - D - dj)(D + 1 - j)`,
with subtractions in `ℕ`.
The left sum counts constraints for every `s < m`.
`AffineParams.surplus` supplies this condition from `AffineParams d n 1 η` for the budgets
`affineMultiplicity η`, `affineYZBudget d n η`, and `affineRootBudget d n 1 η`. -/
theorem exists_affineExceptional_finset_card_map_le_of_interpolation {K E : Type*}
    [Fintype K] [Field E] [Finite E] [DecidableEq E] (domain : ι ↪ E) (f g : ι → E)
    (φ : K ↪ E) {d m D M : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * affineThreshold d (Fintype.card ι) η - D) (M + 1) (D + 1)).card)
    (hJ : Fintype.card ι * (d + 1) < affinePersistenceThreshold d (Fintype.card ι) 1 η ^ 2) :
    ∃ Ex : Finset (K × K), (#Ex : ℝ) ≤
        (Fintype.card ι : ℝ) * ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) - d - 1) /
            ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) ^ 2 -
              Fintype.card ι * (d + 1)) *
          max (Fintype.card K : ℝ) ((Fintype.card ι).choose 2) +
        (D ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) /
          (affineThreshold d (Fintype.card ι) η -
            affinePersistenceThreshold d (Fintype.card ι) 1 η : ℕ)) ^ 2) ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d (affineThreshold d (Fintype.card ι) η) 1
        (φ c.1) (φ c.2) P := by
  classical
  set n := Fintype.card ι
  set A := affineThreshold d n η
  set B := affinePersistenceThreshold d n 1 η
  obtain ⟨hBA, hAn⟩ := threshold_facts (Nat.zero_lt_of_lt hdn) hη hη1
  have hdB : d + 1 < B := by
    by_contra h
    have h1 : B ^ 2 ≤ (d + 1) ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    have h2 : (d + 1) ^ 2 ≤ n * (d + 1) := by rw [sq]; exact Nat.mul_le_mul_right _ hdn
    omega
  obtain ⟨Q, hQ, -⟩ := exists_isAffineInterpolant domain f g hsurplus
  -- The nonpersistent challenges are counted in `E²`; their preimage in `K²` is no larger.
  obtain ⟨Ex₀, hcard, hgood⟩ := exists_finset_card_le_forall_isAffinePersistent_of_interpolant
    domain f g hQ hd (by omega) hBA hAn
  set Ex₁ : Finset (K × K) := {c | (φ c.1, φ c.2) ∈ Ex₀}
  have h₁ : (#Ex₁ : ℝ) ≤ #Ex₀ := by
    refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun c ↦ (φ c.1, φ c.2))
      (fun c hc ↦ (Finset.mem_filter.mp hc).2) fun c _ c' _ h ↦ ?_)
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (φ.injective h.1) (φ.injective h.2)
  -- The persistent challenges are counted directly in `K²`.
  set Pset : Finset (K × K) := {c | ∃ P, IsAffineExceptional domain f g d A 1 (φ c.1) (φ c.2) P ∧
    IsAffinePersistent domain f g d B (φ c.1) (φ c.2) P}
  have hpers := card_isAffineExceptional_persistent_map_le domain f g φ (A := A) hdB.le hJ
  refine ⟨Pset ∪ Ex₁, ?_, fun c hc P hP ↦ ?_⟩
  · calc (#(Pset ∪ Ex₁) : ℝ) ≤ #Pset + #Ex₁ := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := by linarith
  · have hc₁ : (φ c.1, φ c.2) ∉ Ex₀ := fun h ↦
      hc (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    exact hc (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, P, hP, hgood _ hc₁ P hP⟩))

/-- At loss one and threshold `A = ⌈(√ρ + η)n⌉`, a finite set contains every exceptional challenge.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, `ρ = d/n`, and
`0 < η < 1 - √ρ`.
The interpolation multiplicity is `m`, the `(Y, Z)`-degree budget is `D`, and the `Z`-degree
budget is `M`.
Set `B = ⌈(√ρ + η/2)n⌉ - 1` and assume `n(d + 1) < B²`.
The real Johnson factor is `J = n(B - d - 1)/(B² - n(d + 1))`, without a floor.
The bound is `#Ex ≤ J max q (n choose 2) + N`, where
`N = D² + 4d²M²D³(n/(A - B))²`.

The sufficient interpolation condition is
`n ∑_{s < m} (m - s)(D + 1 - s) < ∑_{j ≤ M} (mA - D - dj)(D + 1 - j)`,
with subtractions in `ℕ`.
The left sum counts constraints for every `s < m`.
`AffineParams.surplus` supplies this condition from `AffineParams d n 1 η` for the budgets
`affineMultiplicity η`, `affineYZBudget d n η`, and `affineRootBudget d n 1 η`. -/
theorem exists_affineExceptional_finset_card_le_of_interpolation [Fintype F] (domain : ι ↪ F)
    (f g : ι → F) {d m D M : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * affineThreshold d (Fintype.card ι) η - D) (M + 1) (D + 1)).card)
    (hJ : Fintype.card ι * (d + 1) < affinePersistenceThreshold d (Fintype.card ι) 1 η ^ 2) :
    ∃ Ex : Finset (F × F), (#Ex : ℝ) ≤
        (Fintype.card ι : ℝ) * ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) - d - 1) /
            ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) ^ 2 -
              Fintype.card ι * (d + 1)) *
          max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) +
        (D ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) /
          (affineThreshold d (Fintype.card ι) η -
            affinePersistenceThreshold d (Fintype.card ι) 1 η : ℕ)) ^ 2) ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d (affineThreshold d (Fintype.card ι) η) 1
        c.1 c.2 P :=
  exists_affineExceptional_finset_card_map_le_of_interpolation domain f g (.refl F) hd hdn hη
    hη1 hsurplus hJ

/-- The affine error at loss one and threshold `A = ⌈(√ρ + η)n⌉` is at most
`ENNReal.ofReal ((J max q (n choose 2) + N)/q²)`.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, `ρ = d/n`, and
`0 < η < 1 - √ρ`.
The interpolation multiplicity is `m`, the `(Y, Z)`-degree budget is `D`, and the `Z`-degree
budget is `M`.
Set `B = ⌈(√ρ + η/2)n⌉ - 1` and assume `n(d + 1) < B²`.
The real Johnson factor is `J = n(B - d - 1)/(B² - n(d + 1))`, without a floor, and
`N = D² + 4d²M²D³(n/(A - B))²`.

The sufficient interpolation condition is
`n ∑_{s < m} (m - s)(D + 1 - s) < ∑_{j ≤ M} (mA - D - dj)(D + 1 - j)`,
with subtractions in `ℕ`.
The left sum counts constraints for every `s < m`.
`AffineParams.surplus` proves the condition for the chosen parameters at `e = 1`. -/
theorem affineMcaError_le_of_interpolation [Fintype F] (domain : ι ↪ F) {d m D M : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * affineThreshold d (Fintype.card ι) η - D) (M + 1) (D + 1)).card)
    (hJ : Fintype.card ι * (d + 1) < affinePersistenceThreshold d (Fintype.card ι) 1 η ^ 2) :
    affineMcaError domain d (affineThreshold d (Fintype.card ι) η) 1 ≤
      ENNReal.ofReal
        ((Fintype.card ι : ℝ) * ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) - d - 1) /
            ((affinePersistenceThreshold d (Fintype.card ι) 1 η : ℝ) ^ 2 -
              Fintype.card ι * (d + 1)) *
          max (Fintype.card F : ℝ) ((Fintype.card ι).choose 2) / (Fintype.card F : ℝ) ^ 2 +
        (D ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((Fintype.card ι : ℝ) /
          (affineThreshold d (Fintype.card ι) η -
            affinePersistenceThreshold d (Fintype.card ι) 1 η : ℕ)) ^ 2) /
          (Fintype.card F : ℝ) ^ 2) := by
  rw [← add_div]
  exact affineMcaError_le_of_forall_exists domain fun f g ↦
    exists_affineExceptional_finset_card_le_of_interpolation domain f g hd hdn hη hη1 hsurplus hJ

/-- With one point of loss, few challenges are exceptional after mapping by `φ`.

Here `φ : K ↪ E` is an injective map from a finite type, so challenges come from any finite
subset of `E`; a subfield is the main example.
Here `n` is the domain size, `q = |K|`, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
At most `4 q / η + 2¹⁴ n² / (ρ³ η¹⁰)` challenges are exceptional at `⌈(√ρ + η) n⌉`. -/
theorem exists_affineExceptional_finset_card_map_le {K E : Type*} [Fintype K]
    [Field E] [Finite E] [DecidableEq E] (domain : ι ↪ E) (f g : ι → E) (φ : K ↪ E)
    {d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    ∃ Ex : Finset (K × K), (Ex.card : ℝ) ≤ 4 * Fintype.card K / η +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 / (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10) ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d
        ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 (φ c.1) (φ c.2) P := by
  have hP : AffineParams d (Fintype.card ι) 1 η :=
    ⟨hd, hdn, le_rfl, hη, hη1, by rwa [Nat.cast_one, one_mul]⟩
  set n := Fintype.card ι with hn_def
  set q := Fintype.card K
  set m := affineMultiplicity η
  set D := affineYZBudget d n η
  set M := affineRootBudget d n 1 η
  set A := affineThreshold d n η with hA_def
  set B := affinePersistenceThreshold d n 1 η with hB_def
  have hJ : n * (d + 1) < B ^ 2 := hP.card_mul_add_lt_sq
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_map_le_of_interpolation
    domain f g φ
    (m := m) (D := D) (M := M) hd hdn hη hη1 (by simpa only [one_mul] using hP.surplus) hJ
  refine ⟨Ex, hcard.trans ?_, hgood⟩
  rw [← hn_def, ← hA_def, ← hB_def]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- The persistent part: `ℓ ≤ 4 / η` and `max q (n choose 2) ≤ q + n² / 2`.
  have hℓ : (n : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - n * (d + 1)) ≤ 4 / η := by
    simpa only [Nat.cast_one] using hP.card_mul_sub_div_sq_sub_le
  have hC : ((n.choose 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    simpa using Nat.choose_le_pow_div (α := ℝ) 2 n
  have hmax : max (q : ℝ) ((n.choose 2 : ℕ) : ℝ) ≤ q + (n : ℝ) ^ 2 / 2 :=
    max_le (by linarith [sq_nonneg (n : ℝ)]) (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  have hpers : (n : ℝ) * ((B : ℝ) - d - 1) / ((B : ℝ) ^ 2 - n * (d + 1)) *
      max (q : ℝ) ((n.choose 2 : ℕ) : ℝ) ≤ 4 * q / η + 2 * (n : ℝ) ^ 2 * (1 / η) := by
    calc _ ≤ 4 / η * (q + (n : ℝ) ^ 2 / 2) :=
          mul_le_mul hℓ hmax (by positivity) (by positivity)
      _ = _ := by ring
  -- The nonpersistent part, by the estimates on `D`, `d M` and `n / (A - B)`.
  have hD : (D : ℝ) ≤ 9 / 2 * (n / d) * (1 / η) ^ 2 := by
    refine hP.yzBudget_le_nine_div.trans (le_of_eq ?_)
    field_simp
  have hv : (n : ℝ) / (A - B : ℕ) ≤ 2 * (1 / η) := by
    have hBA := hP.persistenceThreshold_lt
    have := hP.card_div_sub_le
    rw [show A - B - 1 + 1 = A - B by omega] at this
    rwa [mul_one_div]
  have hdM : ((d * M : ℕ) : ℝ) ≤ 3 * (1 / η) * n := by
    refine hP.mul_rootBudget_le.trans (le_of_eq ?_)
    ring
  have hnum := affineCount_numerics_le (k := 1) le_rfl (n := n) (a := 1 / η) (b := n / d)
    (D := D)
    (v := (n : ℝ) / (A - B : ℕ)) (dM := ((d * M : ℕ) : ℝ))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
      (Nat.zero_lt_of_lt hdn)))
    ((one_le_div hη).mpr hP.lt_one.le)
    ((one_le_div hd0).mpr (by exact_mod_cast hdn.le)) (Nat.cast_nonneg _) hD
    (by positivity) hv (Nat.cast_nonneg _) hdM
  have hfin : 2 ^ 14 * ((n : ℝ) ^ 2 * (n / d) ^ 3 * (1 / η) ^ 10) =
      2 ^ 14 * (n : ℝ) ^ 2 / (((d : ℝ) / n) ^ 3 * η ^ 10) := by
    field_simp
  simp only [Nat.reduceAdd, Nat.reduceMul] at hnum
  push_cast at hnum
  have hterm : (D : ℝ) ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * ((n : ℝ) / (A - B : ℕ)) ^ 2 =
      D ^ 2 + (2 * (d * M) * ((n : ℝ) / (A - B : ℕ))) ^ 2 * D ^ 3 := by ring
  linarith [hnum, hpers, hfin, hterm]

/-- With one point of agreement loss, few challenges are exceptional.

Here `n` is the domain size, `q` is the field size, `1 ≤ d < n`, and `ρ = d / n`.
Assume `0 < η < 1 - √ρ` and `n η² ≥ 4 / ρ`.
At most `4 q / η + 2¹⁴ n² / (ρ³ η¹⁰)` challenges are exceptional at `⌈(√ρ + η) n⌉`. -/
theorem exists_affineExceptional_finset_card_le [Fintype F] (domain : ι ↪ F) (f g : ι → F)
    {d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hdn : d < Fintype.card ι) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card ι))
    (hn : 4 / ((d : ℝ) / Fintype.card ι) ≤ Fintype.card ι * η ^ 2) :
    ∃ Ex : Finset (F × F), (Ex.card : ℝ) ≤ 4 * Fintype.card F / η +
        2 ^ 14 * (Fintype.card ι : ℝ) ^ 2 / (((d : ℝ) / Fintype.card ι) ^ 3 * η ^ 10) ∧
      ∀ c ∉ Ex, ∀ P, ¬ IsAffineExceptional domain f g d
        ⌈(√((d : ℝ) / Fintype.card ι) + η) * Fintype.card ι⌉₊ 1 c.1 c.2 P :=
  exists_affineExceptional_finset_card_map_le domain f g (.refl F) hd hdn hη hη1 hn

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
