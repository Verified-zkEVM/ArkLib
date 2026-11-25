/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.NonpersistentCount
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.InterpolationParams
import ArkLib.ToMathlib.FieldTheory.Finite.Extension

/-!
# The affine MCA error of Reed–Muller codes

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the grid size.
Write `e = q₀ᵏ⁻¹`, with natural-number subtraction, and `ρ = d / q₀`.
The agreement loss is `e`, which is `n / q₀` for `k ≥ 1`.

Exceptional coefficient vectors `α ∈ F^{k+1}` are persistent or not.
Rational pairs and Lemma A.1 count the persistent ones.
An interpolant bounds the others.
It lives on a degree-`k` extension of `K₀`, embedded in the algebraic closure of `F` over `K₀`.
Both the extension and the embedding are chosen inside the proof.

Assume `1 ≤ d`, `0 < η < 1 - √ρ` and `q₀ η² ≥ 4 / ρ`.
The threshold is `⌈(√ρ + η) n⌉`, and the loss is `e`.
The error is then at most `4 / (η qᵏ) + 2⁶ᵏ⁺⁸ nᵏ⁺¹ / (ρᵏ⁺² η⁴ᵏ⁺⁶ qᵏ⁺¹)`.

The error has type `ENNReal`.
The sibling probability module connects it to native uniform sampling.
The counting bounds need no sampler.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation` and
  `ReedMuller.affineMcaError_le_of_interpolation`: the bound for any interpolation parameters.
* `ReedMuller.exists_affineExceptional_finset_card_le` and `ReedMuller.affineMcaError_le`:
  the bound (7.2) at the threshold `⌈(√ρ + η) n⌉`.

## References

The general bound is the Reed–Muller analogue of Theorem 4.10 of [CWYZ26], from Appendix A.
The paper counts `D² + ℓ max{q, (n choose (k + 1))} + (2 ρ n M v)ᵏ⁺¹ Dᵏ⁺²`.
Here `ρ n = d e`, `v = n / (A - B - e + 1)`, and `ℓ` is the real Johnson factor.
The thresholds `A` and `B` are free, subject to `(d + 1) e < B`, `n (d + 1) e < B²` and `B + e ≤ A`.
The difference `A - B - e + 1` uses natural-number subtraction.
It does not truncate, since `B + e ≤ A`.
The interpolation condition sums constraints over every order `s < m`, as for Reed–Solomon codes.

The final bound is Theorem 7.1 of [CWYZ26], with the constant `2⁶ᵏ⁺⁸` of (7.2).
The hypothesis `1 ≤ d` stands for `ρ > 0`, since real division by zero is zero.
The paper's `ρ < 1` follows from `η < 1 - √ρ` and is not assumed.
The paper's `k ≥ 1` is not assumed either: at `k = 0` the bound exceeds one.
The numerics use `81/4 + 2 + 12ᵏ⁺¹ (9/2)ᵏ⁺² ≤ 2⁶ᵏ⁺⁸` for `k ≥ 1`.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open Polynomial.SymbolicInterpolation FiniteField Finset

variable {K₀ : Type*} [Field K₀] [Fintype K₀] {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra K₀ F] {k : ℕ}

/-- Few coefficient vectors carry an exceptional candidate, for any interpolation parameters.

Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ` be the grid size.
Let `e = q₀ᵏ⁻¹`, with natural-number subtraction, and let `1 ≤ d`.
The agreement threshold is `A`, the loss is `e`, and the persistence threshold is `B`.
Assume `(d + 1) e < B`, `n (d + 1) e < B²` and `B + e ≤ A`.

The interpolation multiplicity is `m`.
The `(Y, Z)`-degree budget is `D`, and the `Z`-degree budget is `M`.
Let `c = ∑_{s < m} (m - s)(D + 1 - s)` count the constraints at each point.
Let `u = ∑_{j ≤ M} (m A - e D - d e j)(D + 1 - j)` count the allowed monomials.
Assume `n c < u`, with subtractions in `ℕ`.

The real Johnson factor is `ℓ = n (B - (d + 1) e) / (B² - n (d + 1) e)`, without a floor.
The bound is `ℓ max q (n choose (k + 1)) + K`.
Here `K = D² + (2 d e M n / (A - B - e + 1))ᵏ⁺¹ Dᵏ⁺²`, with subtractions in `ℕ`.
The difference `A - B - e` does not truncate, since `B + e ≤ A`. -/
theorem exists_affineExceptional_finset_card_le_of_interpolation (f g : (Fin k → K₀) → F)
    {d A B m D M : ℕ} (hd : 1 ≤ d) (hdB : (d + 1) * Fintype.card K₀ ^ (k - 1) < B)
    (hJ : Fintype.card K₀ ^ k * ((d + 1) * Fintype.card K₀ ^ (k - 1)) < B ^ 2)
    (hBA : B + Fintype.card K₀ ^ (k - 1) ≤ A)
    (hsurplus : Fintype.card K₀ ^ k * (constraintSupport m (D + 1)).card <
      (monomialSupport (d * Fintype.card K₀ ^ (k - 1))
        (m * A - Fintype.card K₀ ^ (k - 1) * D) (M + 1) (D + 1)).card) :
    ∃ Ex : Finset (Fin (k + 1) → F), (#Ex : ℝ) ≤
        (Fintype.card K₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1)) /
            ((B : ℝ) ^ 2 - (Fintype.card K₀ : ℝ) ^ k *
              ((d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1))) *
          max (Fintype.card F : ℝ) ((Fintype.card K₀ ^ k).choose (k + 1)) +
        (D ^ 2 + (2 * (d * Fintype.card K₀ ^ (k - 1) : ℕ) * M * ((Fintype.card K₀ ^ k : ℕ) /
          (A - B - Fintype.card K₀ ^ (k - 1) + 1 : ℕ))) ^ (k + 1) * D ^ (k + 2)) ∧
      ∀ α ∉ Ex, ∀ P, ¬ IsAffineExceptional f g d A (Fintype.card K₀ ^ (k - 1)) α P := by
  classical
  set q₀ := Fintype.card K₀
  set e := q₀ ^ (k - 1)
  -- The Johnson factor is nonnegative.
  have hℓ : 0 ≤ (q₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (q₀ : ℝ) ^ (k - 1)) /
      ((B : ℝ) ^ 2 - (q₀ : ℝ) ^ k * ((d + 1) * (q₀ : ℝ) ^ (k - 1))) := by
    have h1 : ((d + 1) * q₀ ^ (k - 1) : ℕ) < (B : ℝ) := by exact_mod_cast hdB
    have h2 : ((q₀ ^ k * ((d + 1) * q₀ ^ (k - 1)) : ℕ) : ℝ) < (B : ℝ) ^ 2 := by exact_mod_cast hJ
    push_cast at h1 h2
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  by_cases hAn : A ≤ q₀ ^ k
  swap
  · -- No candidate has more agreements than grid points.
    refine ⟨∅, ?_, fun α _ P ↦ not_isAffineExceptional_of_card_lt (not_le.mp hAn)⟩
    rw [card_empty, Nat.cast_zero]
    positivity
  -- The grid has more than one point, so `k ≠ 0`.
  have hk : k ≠ 0 := by
    rintro rfl
    simp only [pow_zero, zero_tsub, e, q₀] at hAn hBA hdB
    omega
  have : NeZero k := ⟨hk⟩
  -- A degree-`k` extension `L` of `K₀`, embedded in the algebraic closure `E` of `F`.
  let L := FiniteField.Extension K₀ (ringChar K₀) k
  let : Fintype L := Fintype.ofFinite L
  let E := AlgebraicClosure F
  let ι : L →ₐ[K₀] E := IsAlgClosed.lift
  let : Algebra L E := ι.toRingHom.toAlgebra
  have : IsScalarTower K₀ L E := IsScalarTower.of_algHom ι
  let b : Module.Basis (Fin k) K₀ L := FiniteField.Extension.finBasis K₀ k
  have hcardL : Fintype.card L = q₀ ^ k := by
    rw [Module.card_fintype b, Fintype.card_fin]
  -- The interpolant on `L ⊆ E`, for multipliers of degree `e` and candidates of degree `d e`.
  obtain ⟨Q, hQ, -⟩ := ReedSolomon.exists_isMultiplierInterpolant
    (ReedSolomon.algebraMapDomain L E)
    (fun x ↦ algebraMap F E (f (traceCoordinateEquiv K₀ b x)))
    (fun x ↦ algebraMap F E (g (traceCoordinateEquiv K₀ b x))) (e := e) (d := d * e) (A := A)
    (m := m) (D := D) (M := M) (by rwa [hcardL])
  -- Outside few vectors, candidates are persistent.
  obtain ⟨Ex, hEx, hgood⟩ := exists_finset_card_le_isAffinePersistent b f g hQ hd
    (show d * e < B + e by rw [add_mul, one_mul] at hdB; omega) hBA
  -- The persistent vectors.
  set Pset : Finset (Fin (k + 1) → F) := {α | ∃ P, IsAffineExceptional f g d A e α P ∧
    IsAffinePersistent f g d B α P}
  have hPset := card_isAffineExceptional_persistent_le f g (A := A) hdB hJ
  refine ⟨Ex ∪ Pset, ?_, fun α hα P hP ↦ ?_⟩
  · calc (#(Ex ∪ Pset) : ℝ) ≤ #Ex + #Pset := by exact_mod_cast card_union_le _ _
      _ ≤ _ := by linarith
  · simp only [mem_union, not_or] at hα
    exact hα.2 (mem_filter.mpr ⟨mem_univ _, P, hP, hgood α hα.1 P hP.1 hP.2.1⟩)

/-- The Reed–Muller error at loss `e` is at most `(ℓ max q (n choose (k + 1)) + K) / qᵏ⁺¹`.

Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ` be the grid size.
Let `e = q₀ᵏ⁻¹`, with natural-number subtraction, and let `1 ≤ d`.
The agreement threshold is `A`, and the persistence threshold is `B`.
Assume `(d + 1) e < B`, `n (d + 1) e < B²` and `B + e ≤ A`.

The interpolation multiplicity is `m`.
The `(Y, Z)`-degree budget is `D`, and the `Z`-degree budget is `M`.
Let `c = ∑_{s < m} (m - s)(D + 1 - s)` count the constraints at each point.
Let `u = ∑_{j ≤ M} (m A - e D - d e j)(D + 1 - j)` count the allowed monomials.
Assume `n c < u`, with subtractions in `ℕ`.

The real Johnson factor is `ℓ = n (B - (d + 1) e) / (B² - n (d + 1) e)`, without a floor.
Here `K = D² + (2 d e M n / (A - B - e + 1))ᵏ⁺¹ Dᵏ⁺²`, with subtractions in `ℕ`.
The difference `A - B - e` does not truncate, since `B + e ≤ A`. -/
theorem affineMcaError_le_of_interpolation {d A B m D M : ℕ} (hd : 1 ≤ d)
    (hdB : (d + 1) * Fintype.card K₀ ^ (k - 1) < B)
    (hJ : Fintype.card K₀ ^ k * ((d + 1) * Fintype.card K₀ ^ (k - 1)) < B ^ 2)
    (hBA : B + Fintype.card K₀ ^ (k - 1) ≤ A)
    (hsurplus : Fintype.card K₀ ^ k * (constraintSupport m (D + 1)).card <
      (monomialSupport (d * Fintype.card K₀ ^ (k - 1))
        (m * A - Fintype.card K₀ ^ (k - 1) * D) (M + 1) (D + 1)).card) :
    affineMcaError K₀ F k d A (Fintype.card K₀ ^ (k - 1)) ≤ ENNReal.ofReal
      ((Fintype.card K₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1)) /
            ((B : ℝ) ^ 2 - (Fintype.card K₀ : ℝ) ^ k *
              ((d + 1) * (Fintype.card K₀ : ℝ) ^ (k - 1))) *
          max (Fintype.card F : ℝ) ((Fintype.card K₀ ^ k).choose (k + 1)) /
            (Fintype.card F : ℝ) ^ (k + 1) +
        (D ^ 2 + (2 * (d * Fintype.card K₀ ^ (k - 1) : ℕ) * M * ((Fintype.card K₀ ^ k : ℕ) /
          (A - B - Fintype.card K₀ ^ (k - 1) + 1 : ℕ))) ^ (k + 1) * D ^ (k + 2)) /
            (Fintype.card F : ℝ) ^ (k + 1)) := by
  rw [← add_div]
  exact affineMcaError_le_of_forall_exists fun f g ↦
    exists_affineExceptional_finset_card_le_of_interpolation f g hd hdB hJ hBA hsurplus

open ReedSolomon in
/-- With loss `q₀ᵏ⁻¹`, few coefficient vectors carry an exceptional candidate.

Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ` be the grid size.
The loss `q₀ᵏ⁻¹` uses natural-number subtraction.
Let `1 ≤ d`, `ρ = d / q₀`, `0 < η < 1 - √ρ` and `q₀ η² ≥ 4 / ρ`.
The threshold is `⌈(√ρ + η) n⌉`.
At most `4 q / η + 2⁶ᵏ⁺⁸ nᵏ⁺¹ / (ρᵏ⁺² η⁴ᵏ⁺⁶)` vectors carry an exceptional candidate. -/
theorem exists_affineExceptional_finset_card_le (f g : (Fin k → K₀) → F) {d : ℕ} {η : ℝ}
    (hd : 1 ≤ d) (hη : 0 < η) (hη1 : η < 1 - √((d : ℝ) / Fintype.card K₀))
    (hq₀ : 4 / ((d : ℝ) / Fintype.card K₀) ≤ Fintype.card K₀ * η ^ 2) :
    ∃ Ex : Finset (Fin (k + 1) → F), (#Ex : ℝ) ≤ 4 * Fintype.card F / η +
        2 ^ (6 * k + 8) * ((Fintype.card K₀ : ℝ) ^ k) ^ (k + 1) /
          (((d : ℝ) / Fintype.card K₀) ^ (k + 2) * η ^ (4 * k + 6)) ∧
      ∀ α ∉ Ex, ∀ P, ¬ IsAffineExceptional f g d
        ⌈(√((d : ℝ) / Fintype.card K₀) + η) * (Fintype.card K₀ : ℝ) ^ k⌉₊
        (Fintype.card K₀ ^ (k - 1)) α P := by
  classical
  set q₀ := Fintype.card K₀ with hq₀_def
  set q := Fintype.card F with hq_def
  have hq0 : (0 : ℝ) < q₀ := by exact_mod_cast Fintype.card_pos
  have hρ0 : (0 : ℝ) < (d : ℝ) / q₀ := div_pos (by exact_mod_cast hd) hq0
  have hη1' : η < 1 := by linarith [Real.sqrt_nonneg ((d : ℝ) / q₀)]
  have hY : 0 ≤ 2 ^ (6 * k + 8) * ((q₀ : ℝ) ^ k) ^ (k + 1) /
      (((d : ℝ) / q₀) ^ (k + 2) * η ^ (4 * k + 6)) := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- With one grid point, every vector may be counted.
    refine ⟨univ, ?_, fun α hα ↦ absurd (mem_univ α) hα⟩
    have : (q : ℝ) ≤ 4 * q / η := by
      rw [le_div_iff₀ hη]
      nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have hcard : (#(univ : Finset (Fin (0 + 1) → F)) : ℝ) = q := by simp [q]
    linarith
  -- The univariate parameters: degree `d e`, length `n = q₀ e`, multiplier degree `e`.
  set e := q₀ ^ (k - 1) with he_def
  set n := q₀ ^ k with hn_def
  have hn : n = q₀ * e := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have he : 1 ≤ e := Nat.one_le_pow _ _ Fintype.card_pos
  have hρ : ((d * e : ℕ) : ℝ) / (n : ℕ) = (d : ℝ) / q₀ := by
    rw [hn]
    push_cast
    have : (0 : ℝ) < e := by exact_mod_cast he
    field_simp
  have hdq : d < q₀ := by
    have h1 : √((d : ℝ) / q₀) < 1 := by linarith
    have h2 : (d : ℝ) / q₀ < 1 := (Real.sqrt_lt' one_pos).mp h1 |>.trans_le (by norm_num)
    exact_mod_cast (div_lt_one hq0).mp h2
  have hP : AffineParams (d * e) n e η := by
    refine ⟨Nat.mul_le_mul hd he, ?_, he, hη, by rwa [hρ], ?_⟩
    · rw [hn]
      exact Nat.mul_lt_mul_of_pos_right hdq he
    · rw [hρ, hn]
      push_cast
      have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      nlinarith
  set m := affineMultiplicity η
  set D := affineYZBudget (d * e) n η
  set M := affineRootBudget (d * e) n e η
  set A := affineThreshold (d * e) n η with hA_def
  set B := affinePersistenceThreshold (d * e) n e η with hB_def
  have hdB : (d + 1) * e < B := by
    have := hP.add_lt_persistenceThreshold
    rwa [add_mul, one_mul]
  have hJ : n * ((d + 1) * e) < B ^ 2 := by
    have := hP.card_mul_add_lt_sq
    rwa [add_mul, one_mul]
  obtain ⟨Ex, hcard, hgood⟩ := exists_affineExceptional_finset_card_le_of_interpolation f g
    (m := m) (D := D) (M := M) hd hdB hJ hP.persistenceThreshold_add_lt.le hP.surplus
  have hA : A = ⌈(√((d : ℝ) / q₀) + η) * (q₀ : ℝ) ^ k⌉₊ := by
    rw [hA_def, affineThreshold, hρ, Nat.cast_pow]
  refine ⟨Ex, hcard.trans ?_, hA ▸ hgood⟩
  rw [← hq₀_def, ← he_def, ← hn_def, ← hA_def, ← hq_def]
  -- Real forms of `n`, `e`, `1 / ρ` and `1 / η`.
  have hnR : ((n : ℕ) : ℝ) = (q₀ : ℝ) ^ k := by rw [hn_def, Nat.cast_pow]
  have heR : ((e : ℕ) : ℝ) = (q₀ : ℝ) ^ (k - 1) := by rw [he_def, Nat.cast_pow]
  have hn1 : (1 : ℝ) ≤ (q₀ : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast Fintype.card_pos)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 1 ≤ 1 / η := (one_le_div hη).mpr hη1'.le
  have hb : 1 ≤ (q₀ : ℝ) / d := (one_le_div hd0).mpr (by exact_mod_cast hdq.le)
  -- The persistent part: `ℓ ≤ 4 / η` and `max q (n choose (k + 1)) ≤ q + n^(k+1) / 2`.
  have hℓ : (q₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (q₀ : ℝ) ^ (k - 1)) /
      ((B : ℝ) ^ 2 - (q₀ : ℝ) ^ k * ((d + 1) * (q₀ : ℝ) ^ (k - 1))) ≤ 4 / η := by
    have h := hP.card_mul_sub_div_sq_sub_le
    push_cast at h
    rw [hnR, heR, ← hB_def] at h
    convert h using 3 <;> ring
  have hC : ((n.choose (k + 1) : ℕ) : ℝ) ≤ ((q₀ : ℝ) ^ k) ^ (k + 1) / 2 := by
    have h := Nat.choose_le_pow_div (α := ℝ) (k + 1) n
    have hf : (2 : ℕ) ≤ (k + 1).factorial := by
      simpa using Nat.factorial_le (show 2 ≤ k + 1 by omega)
    have hf' : (2 : ℝ) ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast hf
    rw [hnR] at h
    exact h.trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) hf')
  have hmax : max (q : ℝ) ((n.choose (k + 1) : ℕ) : ℝ) ≤ q + ((q₀ : ℝ) ^ k) ^ (k + 1) / 2 :=
    max_le (by linarith [pow_nonneg (pow_nonneg hq0.le k) (k + 1)])
      (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
  have hpers : (q₀ : ℝ) ^ k * ((B : ℝ) - (d + 1) * (q₀ : ℝ) ^ (k - 1)) /
      ((B : ℝ) ^ 2 - (q₀ : ℝ) ^ k * ((d + 1) * (q₀ : ℝ) ^ (k - 1))) *
        max (q : ℝ) ((n.choose (k + 1) : ℕ) : ℝ) ≤
      4 * q / η + 2 * ((q₀ : ℝ) ^ k) ^ (k + 1) * (1 / η) := by
    calc _ ≤ 4 / η * (q + ((q₀ : ℝ) ^ k) ^ (k + 1) / 2) :=
          mul_le_mul hℓ hmax (le_max_of_le_left (Nat.cast_nonneg q)) (by positivity)
      _ = _ := by ring
  -- The nonpersistent part, by the estimates on `D`, `d e M` and `n / (A - B - e + 1)`.
  have hD : (D : ℝ) ≤ 9 / 2 * ((q₀ : ℝ) / d) * (1 / η) ^ 2 := by
    have h := hP.yzBudget_le_nine_div
    rw [hρ] at h
    refine h.trans (le_of_eq ?_)
    field_simp
  have hv : (n : ℝ) / (A - B - e + 1 : ℕ) ≤ 2 * (1 / η) := by
    rw [mul_one_div]
    exact hP.card_div_sub_le
  have hdM : ((d * e * M : ℕ) : ℝ) ≤ 3 * (1 / η) * (q₀ : ℝ) ^ k := by
    refine hP.mul_rootBudget_le.trans (le_of_eq ?_)
    rw [hnR]
    ring
  have hnum := affineCount_numerics_le hk (n := (q₀ : ℝ) ^ k) (a := 1 / η) (b := (q₀ : ℝ) / d)
    (D := D)
    (v := (n : ℝ) / (A - B - e + 1 : ℕ)) (dM := ((d * e * M : ℕ) : ℝ)) hn1 ha hb
    (Nat.cast_nonneg _) hD (by positivity) hv (Nat.cast_nonneg _) hdM
  have hfin : 2 ^ (6 * k + 8) * (((q₀ : ℝ) ^ k) ^ (k + 1) * ((q₀ : ℝ) / d) ^ (k + 2) *
      (1 / η) ^ (4 * k + 6)) =
      2 ^ (6 * k + 8) * ((q₀ : ℝ) ^ k) ^ (k + 1) /
        (((d : ℝ) / q₀) ^ (k + 2) * η ^ (4 * k + 6)) := by
    simp only [div_pow, one_pow]
    field_simp
  have hterm : (2 * ((d * e : ℕ) : ℝ) * M * ((n : ℝ) / (A - B - e + 1 : ℕ))) ^ (k + 1) =
      (2 * ((d * e * M : ℕ) : ℝ) * ((n : ℝ) / (A - B - e + 1 : ℕ))) ^ (k + 1) := by
    push_cast
    ring
  rw [hterm]
  linarith

/-- The Reed–Muller error is at most `4 / (η qᵏ) + 2⁶ᵏ⁺⁸ nᵏ⁺¹ / (ρᵏ⁺² η⁴ᵏ⁺⁶ qᵏ⁺¹)`.

Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ` be the grid size.
Let `1 ≤ d`, `ρ = d / q₀`, `0 < η < 1 - √ρ` and `q₀ η² ≥ 4 / ρ`.
The threshold is `⌈(√ρ + η) n⌉`, and the loss is `q₀ᵏ⁻¹`, with natural-number subtraction. -/
theorem affineMcaError_le {d : ℕ} {η : ℝ} (hd : 1 ≤ d) (hη : 0 < η)
    (hη1 : η < 1 - √((d : ℝ) / Fintype.card K₀))
    (hq₀ : 4 / ((d : ℝ) / Fintype.card K₀) ≤ Fintype.card K₀ * η ^ 2) :
    affineMcaError K₀ F k d ⌈(√((d : ℝ) / Fintype.card K₀) + η) * (Fintype.card K₀ : ℝ) ^ k⌉₊
        (Fintype.card K₀ ^ (k - 1)) ≤
      ENNReal.ofReal (4 / (η * (Fintype.card F : ℝ) ^ k) +
        2 ^ (6 * k + 8) * ((Fintype.card K₀ : ℝ) ^ k) ^ (k + 1) /
          (((d : ℝ) / Fintype.card K₀) ^ (k + 2) * η ^ (4 * k + 6) *
            (Fintype.card F : ℝ) ^ (k + 1))) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (affineMcaError_le_of_forall_exists fun f g ↦
    exists_affineExceptional_finset_card_le f g hd hη hη1 hq₀).trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

end ReedMuller
