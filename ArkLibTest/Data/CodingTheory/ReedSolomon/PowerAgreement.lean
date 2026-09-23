/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Scalar exact power agreement clients

These clients check that `k ≤ a` cannot be dropped from `determinedByAgreement_code`, compute
the uniform guarantee for a single received word with no exceptional challenge, and transport it
to the code-level predicate. They also compute coordinate polynomials and discrepancies, show that
the exceptional-challenge bound `ℓ * (|ι| - L)` is attained, derive the forms for `Fin n`
coordinates and for an exceptional set over an extension field, and check descent along
`ℚ → ℝ`.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace PowerAgreementTest

/-- The evaluation points `0, 1, 2` in `ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

@[simp] theorem domain3_apply (i : Fin 3) : domain3 i = ((i : ℕ) : ℚ) := rfl

-- `k ≤ a` is needed: the codewords of `X` and `0` agree at the point `0` but differ.
example : ¬ Code.DeterminedByAgreement (code domain3 2) 1 := fun h ↦ by
  have hX : evalOnPoints domain3 X ∈ code domain3 2 :=
    evalOnPoints_mem_code_of_degree_lt (by rw [degree_X]; decide)
  have := congrFun (h _ hX 0 (Submodule.zero_mem _) {0} (by simp)
    (by simp [evalOnPoints])) 1
  simp [evalOnPoints] at this

-- With `k ≤ a` it holds.
example : Code.DeterminedByAgreement (code domain3 2) 2 := determinedByAgreement_code domain3 le_rfl

-- A single received word needs no challenge: the guarantee holds with no exceptional value, for
-- every degree bound and threshold, including `k` larger than the block length.
example : UniformExactPowerAgreement domain3 ![![1, 2, 5]] 7 0 0 :=
  uniformExactPowerAgreement_singleton domain3 _ 7 0

-- The singleton statement with the group size written as `0 + 1`.
example {F ι : Type} [Field F] [Fintype ι] [DecidableEq F] (domain : ι ↪ F)
    (w : Fin (0 + 1) → ι → F) (k L : ℕ) : UniformExactPowerAgreement domain w k L 0 :=
  uniformExactPowerAgreement_singleton domain w k L

-- Unfolded at a challenge: a polynomial of degree below `k` is its own witness.
example (z : ℚ) (Q : ℚ[X]) (hQ : Q.degree < 2) (w : Fin 1 → Fin 3 → ℚ) :
    HasExactPowerAgreement domain3 w (RingHom.id ℚ) 2 z Q := by
  obtain ⟨bad, hbad, hgood⟩ := uniformExactPowerAgreement_singleton domain3 w 2 0
  have : bad = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hbad)
  exact hgood z (by simp [this]) Q hQ (Nat.zero_le _)

-- The same statement at the code level, for `univariatePowersGenerator F 0`.
example {F ι : Type} [Field F] [Fintype ι] [DecidableEq F] (domain : ι ↪ F)
    (w : Fin 1 → ι → F) (k L : ℕ) :
    Code.UniformExactAgreement (univariatePowersGenerator F 0) (code domain k) L 0 w :=
  (uniformExactPowerAgreement_iff_uniformExactAgreement domain w).mp
    (uniformExactPowerAgreement_singleton domain w k L)

-- Batching preserves degree bounds, and evaluation commutes with it, on a concrete pair.
example : (powerBatchedPolynomial ![(1 : ℚ[X]), X] 2).eval 3 = 7 := by
  simp [powerBatchedPolynomial_eval, Fin.sum_univ_two]
  norm_num

-- The coordinate polynomial of `(1, 2, 3)` at `2` is `1 + 2 * 2 + 3 * 2 ^ 2 = 17`.
example : (powerBatchedCoordinate ![(1 : ℚ), 2, 3]).eval 2 = 17 := by
  rw [powerBatchedCoordinate_eval]
  simp [Fin.sum_univ_three]
  norm_num

-- Its coefficients are the coordinates.
example : (powerBatchedCoordinate ![(1 : ℚ), 2, 3]).coeff 1 = 2 :=
  powerBatchedCoordinate_coeff _ 1

/-- The single evaluation point `0`. -/
def domain1 : Fin 1 ↪ ℚ := ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

/-- Words `1` and `-1` at the single coordinate. -/
def words1 : Fin 2 → Fin 1 → ℚ := ![fun _ ↦ 1, fun _ ↦ -1]

-- The zero tuple disagrees with `words1`, so its discrepancy is the nonzero `1 - X`.
theorem curveDiscrepancy_words1 :
    curveDiscrepancy domain1 words1 (fun _ ↦ 0) 0 ≠ 0 := by
  rw [Ne, curveDiscrepancy_eq_zero_iff]
  intro h
  simpa [words1] using h 0

-- The zero tuple has no common agreement with `words1`, but at the challenge `1` the batched word
-- is `1 - 1 = 0` and agrees with the batched polynomial `0`. So the exceptional set in
-- `exists_exceptional_powerBatched_agreement`, of size at most `1 * (1 - 0) = 1`, is nonempty and
-- the bound is attained.
example : polynomialAgreementSet domain1 (powerBatchedWord words1 1)
      (powerBatchedPolynomial (fun _ : Fin 2 ↦ 0) 1) ≠
      commonCurveAgreementSet domain1 words1 (fun _ ↦ 0) := by
  intro h
  have h0 := congrArg (0 ∈ ·) h
  simp [powerBatchedWord, powerBatchedPolynomial, words1, domain1] at h0

-- The form with `Fin n` coordinates and the count `ℓ * (n - L)`.
example {F : Type*} [Field F] [DecidableEq F] {n ℓ : ℕ} (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (L : ℕ)
    (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet domain w P := by
  simpa using exists_exceptional_powerBatched_agreement domain w P L hcommon

-- Interpolation on the sample `{0}` gives a constant tuple agreeing with `words1` there.
example : ∃ P : Fin 2 → ℚ[X], (∀ t, (P t).degree < 1) ∧
    ∀ t, (P t).eval (domain1 0) = words1 t 0 := by
  obtain ⟨P, hP, hs⟩ := exists_polynomialTuple_interpolating domain1 words1 {0} le_rfl
  exact ⟨P, hP, hs 0 (Finset.mem_singleton_self 0)⟩

-- The embedding `ℚ → ℝ` preserves agreement sets.
example (y : Fin 3 → ℚ) (Q : ℚ[X]) :
    polynomialAgreementSet (domain3.trans ⟨algebraMap ℚ ℝ, (algebraMap ℚ ℝ).injective⟩)
        (fun i ↦ algebraMap ℚ ℝ (y i)) (Q.map (algebraMap ℚ ℝ)) =
      polynomialAgreementSet domain3 y Q :=
  polynomialAgreementSet_map domain3 _ _ y Q

-- Exact power agreement at a real challenge `φ z` for `Q.map φ` descends to `ℚ`.
example (w : Fin 2 → Fin 3 → ℚ) (k : ℕ) (z : ℚ) (Q : ℚ[X])
    (h : HasExactPowerAgreement domain3 w (algebraMap ℚ ℝ) k (algebraMap ℚ ℝ z)
      (Q.map (algebraMap ℚ ℝ))) :
    HasExactPowerAgreement domain3 w (RingHom.id ℚ) k z Q :=
  h.descend

-- The form with an explicit base-field exceptional set no larger than the extension-field one.
example {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E]
    {ℓ : ℕ} (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (k A : ℕ)
    (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ Q : E[X], Q.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
        (powerBatchedWord (fun t i ↦ φ (w t i)) z) Q).card →
      HasExactPowerAgreement domain w φ k z Q) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ Q : F[X], Q.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) k z Q :=
  uniformExactPowerAgreement_of_extension domain w φ k A exceptional hgood

-- A zero tuple over a one-point domain has exact agreement at every challenge.
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
    ∀ z ∉ exceptional,
      HasExactPowerAgreement domain1 (fun _ : Fin 1 => fun _ => (0 : ℚ))
        (RingHom.id ℚ) 1 z 0 := by
  have h := exists_exceptional_exactPowerAgreement (ι := Fin 1) (ℓ := 0) (k := 1) (L := 0)
    domain1 (fun _ : Fin 1 => fun _ => (0 : ℚ)) (fun _ => (0 : ℚ[X])) (RingHom.id ℚ)
    (by intro t; norm_num) (by omega)
  simpa [powerBatchedPolynomial, Fintype.card_fin] using h

-- A singleton family of the same tuple uses the same empty exceptional set.
example : ∃ exceptional : Finset ℚ, exceptional.card ≤ 0 ∧
    ∀ P ∈ ({(fun _ : Fin 1 => (0 : ℚ[X]))} : Finset (Fin 1 → ℚ[X])),
      ∀ z ∉ exceptional,
        HasExactPowerAgreement domain1 (fun _ : Fin 1 => fun _ => (0 : ℚ))
          (RingHom.id ℚ) 1 z 0 := by
  have h := exists_exceptional_exactPowerAgreement_family
    (ι := Fin 1) (ℓ := 0) (k := 1) (L := 0) domain1
    (fun _ : Fin 1 => fun _ => (0 : ℚ)) (RingHom.id ℚ)
    {fun _ : Fin 1 => (0 : ℚ[X])} (by
      intro P hP t
      rw [Finset.mem_singleton.mp hP]
      norm_num) (by
      intro P hP
      omega)
  simpa [powerBatchedPolynomial, Fintype.card_fin] using h

end PowerAgreementTest
