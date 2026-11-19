/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.NonpersistentCount
import Mathlib.FieldTheory.Finite.Extension

/-!
# The affine MCA error of Reed–Muller codes

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the grid size.
Write `e = q₀ᵏ⁻¹`, with natural-number subtraction.
The agreement loss is `e`, which is `n / q₀` for `k ≥ 1`.

Exceptional coefficient vectors `α ∈ F^{k+1}` are persistent or not.
Rational pairs and Lemma A.1 count the persistent ones.
An interpolant bounds the others.
It lives on a degree-`k` extension of `K₀`, embedded in the algebraic closure of `F` over `K₀`.
Both the extension and the embedding are chosen inside the proof.

The error has type `ENNReal`.
The sibling probability module connects it to native uniform sampling.
The counting bounds need no sampler.

The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.exists_affineExceptional_finset_card_le_of_interpolation` and
  `ReedMuller.affineMcaError_le_of_interpolation`: the bound for any interpolation parameters.

## References

The general bound is the Reed–Muller analogue of Theorem 4.10 of [CWYZ26], from Appendix A.
The paper counts `D² + ℓ max{q, (n choose (k + 1))} + (2 ρ n M v)ᵏ⁺¹ Dᵏ⁺²`.
Here `ρ n = d e`, `v = n / (A - B - e + 1)`, and `ℓ` is the real Johnson factor.
The thresholds `A` and `B` are free, subject to `(d + 1) e < B`, `n (d + 1) e < B²` and `B + e ≤ A`.
The interpolation condition sums constraints over every order `s < m`, as for Reed–Solomon codes.

Theorem 7.1 itself is not proved here.

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
Here `K = D² + (2 d e M n / (A - B - e + 1))ᵏ⁺¹ Dᵏ⁺²`, with subtractions in `ℕ`. -/
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
  set p := ringChar K₀
  have : Fact p.Prime := ⟨CharP.char_is_prime K₀ p⟩
  let L := FiniteField.Extension K₀ p k
  let : Fintype L := Fintype.ofFinite L
  let E := AlgebraicClosure F
  let ι : L →ₐ[K₀] E := IsAlgClosed.lift
  let : Algebra L E := ι.toRingHom.toAlgebra
  have : IsScalarTower K₀ L E := IsScalarTower.of_algHom ι
  let b : Module.Basis (Fin k) K₀ L :=
    Module.finBasisOfFinrankEq K₀ L (FiniteField.finrank_extension K₀ p k)
  have hcardL : Fintype.card L = q₀ ^ k := by
    rw [Module.card_fintype b, Fintype.card_fin]
  -- The interpolant on `L ⊆ E`, for multipliers of degree `e` and candidates of degree `d e`.
  obtain ⟨Q, hQ⟩ := ReedSolomon.exists_isMultiplierInterpolant
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
Here `K = D² + (2 d e M n / (A - B - e + 1))ᵏ⁺¹ Dᵏ⁺²`, with subtractions in `ℕ`. -/
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

end ReedMuller
