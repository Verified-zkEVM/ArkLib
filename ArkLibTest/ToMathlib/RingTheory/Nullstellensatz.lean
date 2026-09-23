/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CutFamily
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Nullstellensatz acceptance examples
-/

open MvPolynomial

local notation "𝕂" => AlgebraicClosure ℚ
local notation "R₁" => MvPolynomial (Fin 1) ℚ

private theorem totalDegree_X_sub_C_le {k : Type*} [Field k] (a : k) :
    (X 0 - C a : MvPolynomial (Fin 1) k).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (by simp)

private theorem subsingleton_linearCuts {k : Type*} [Field k] {n : ℕ} (c : Fin n → k)
    (P : Ideal (MvPolynomial (Fin 1) k)) (s : MvPolynomial (Fin 1) k) (T : Finset (Fin n))
    (hT : T.card = 1) :
    Set.Subsingleton {x : Fin 1 → k | x ∈ zeroLocus k P ∧ aeval x s ≠ 0 ∧
      ∀ i ∈ T, aeval x (X 0 - C (c i) : MvPolynomial (Fin 1) k) = 0} := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hT
  intro x hx y hy
  have hx' := hx.2.2 i (Finset.mem_singleton_self i)
  have hy' := hy.2.2 i (Finset.mem_singleton_self i)
  simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hx' hy'
  funext j
  rw [Subsingleton.elim j 0, hx', hy']

example :
    let S := {x : Fin 1 → 𝕂 | x ∈ zeroLocus 𝕂 (⊥ : Ideal (MvPolynomial (Fin 1) 𝕂)) ∧
      aeval x (1 : MvPolynomial (Fin 1) 𝕂) ≠ 0 ∧
      2 ≤ {i | aeval x (X 0 - C (![0, 0, 1, 1] i) : MvPolynomial (Fin 1) 𝕂) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 2 := by
  intro S
  have h := finite_and_ncard_le_of_agreement_of_subsingleton (P := ⊥) 1
    (fun i : Fin 4 ↦ (X 0 - C (![0, 0, 1, 1] i) : MvPolynomial (Fin 1) 𝕂)) (b := 1) (A := 2)
    (m := 1) (fun _ ↦ totalDegree_X_sub_C_le _) (by norm_num)
    (fun T hT ↦ subsingleton_linearCuts _ _ _ T hT)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp
  norm_num

private def fourPoints : Fin 4 ↪ ℚ := ⟨![0, 1, 2, 3], by decide⟩

example :
    let S := {x : Fin 1 → ℚ | x ∈ zeroLocus ℚ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      aeval x (1 : MvPolynomial (Fin 1) ℚ) ≠ 0 ∧
      2 ≤ {i | aeval x (fixedCoefficientEvaluation 1
        (fourPoints i) (![0, 0, 1, 1] i)) = 0}.ncard}
    S.Finite ∧ (S.ncard : ℚ) ≤ 2 := by
  intro S
  have h := finite_and_ncard_le_dimensionSensitiveIncidenceProduct_of_fixedCoefficientEvaluation
    (K := ℚ) fourPoints ![0, 0, 1, 1] (m := 1) (P := ⊥) 1 (A := 2) (by norm_num)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp [affineDegree_bot, natDegree_affineHilbertPolynomial_bot, dimensionSensitiveIncidenceProduct]
  norm_num

example :
    ∃ Q ∈ Ideal.iteratedRetainedCutFamily {(⊥ : Ideal (MvPolynomial (Fin 2) ℚ))} 1 [X 0],
      (![0, 5] : Fin 2 → ℚ) ∈ zeroLocus ℚ Q := by
  obtain ⟨Q, hQ, -, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
    (Ps := {(⊥ : Ideal (MvPolynomial (Fin 2) ℚ))}) (s := 1) (cuts := [X 0])
    (x := (![0, 5] : Fin 2 → ℚ)) (Finset.mem_singleton_self _) (by simp [zeroLocus]) (by simp)
    (by simp)
  exact ⟨Q, hQ, hxQ⟩

example :
    (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).ncard = 1 ∧
      Module.finrank ℚ (MvPolynomial Empty ℚ ⧸
        (⊥ : Ideal (MvPolynomial Empty ℚ))) = 1 ∧
        (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).Finite ∧
          (zeroLocus ℚ (⊥ : Ideal (MvPolynomial Empty ℚ))).ncard ≤
            Module.finrank ℚ (MvPolynomial Empty ℚ ⧸
              (⊥ : Ideal (MvPolynomial Empty ℚ))) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · calc
      Module.finrank ℚ (MvPolynomial Empty ℚ ⧸ (⊥ : Ideal (MvPolynomial Empty ℚ))) =
          Module.finrank ℚ (MvPolynomial Empty ℚ) :=
        LinearEquiv.finrank_eq (AlgEquiv.quotientBot ℚ (MvPolynomial Empty ℚ)).toLinearEquiv
      _ = Module.finrank ℚ ℚ :=
        LinearEquiv.finrank_eq (MvPolynomial.isEmptyAlgEquiv ℚ Empty).toLinearEquiv
      _ = 1 := by simp
  · exact finite_zeroLocus_of_finite_quotient (K := ℚ) (⊥ : Ideal (MvPolynomial Empty ℚ))
  · exact ncard_zeroLocus_le_finrank_quotient (K := ℚ) (⊥ : Ideal (MvPolynomial Empty ℚ))

example :
    (![1] : Fin 1 → ℚ) ∈ (fun z : Option (Fin 1) → ℚ ↦ z ∘ some) ''
      zeroLocus ℚ (awayPresentationIdeal (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (X 0)) := by
  rw [image_comp_some_zeroLocus_awayPresentationIdeal]
  exact ⟨by simp, by simp⟩

local notation "R₂" => MvPolynomial (Fin 2) ℚ

example : (affineHilbertPolynomial (Ideal.span {(X 1 - X 0 ^ 2 : R₂)})).natDegree ≤ 1 := by
  refine natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range (K := 𝕂)
    (by rw [map_one]; exact isRegular_one.left) ![Polynomial.X, Polynomial.X ^ 2]
    fun x hx _ ↦ ⟨x 0, ?_⟩
  have h := (mem_zeroLocus_iff.mp hx) _ (Ideal.mem_span_singleton_self _)
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero] at h
  funext i
  fin_cases i <;> simp [h]

example : ((zeroLocus ℚ (Ideal.span {(X 0 : R₁)})).ncard : ℚ) ≤ 1 := by
  let I : Ideal R₁ := Ideal.span {X 0}
  have hP : (Polynomial.preHilbertPoly ℚ 1 0).natDegree = 1 :=
    Polynomial.natDegree_preHilbertPoly ℚ 1 0
  have hlc : (Polynomial.preHilbertPoly ℚ 1 0).leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff_preHilbertPoly]
    simp
  have hdegX : 0 < (X 0 : R₁).totalDegree := by
    rw [totalDegree_X]
    norm_num
  have hdiff := Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
    (Nat.cast_ne_zero.mpr hdegX.ne') (by rw [hP]; exact Nat.one_pos)
  have hdegree : (affineHilbertPolynomial I).natDegree = 0 := by
    change (affineHilbertPolynomial (Ideal.span {(X 0 : R₁)})).natDegree = 0
    rw [affineHilbertPolynomial_span_singleton (X_ne_zero (0 : Fin 1)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
    simpa [hP] using hdiff.1
  have hcoeff : (affineHilbertPolynomial I).coeff 0 = 1 := by
    change (affineHilbertPolynomial (Ideal.span {(X 0 : R₁)})).coeff 0 = 1
    rw [affineHilbertPolynomial_span_singleton (X_ne_zero (0 : Fin 1)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hP, Nat.sub_self] at hdiff
    have hc := Polynomial.coeff_natDegree
      (p := Polynomial.backwardDifference ((X 0 : R₁).totalDegree : ℚ)
        (Polynomial.preHilbertPoly ℚ 1 0))
    rw [hdiff.1, hdiff.2, hlc] at hc
    rw [hc]
    simp [totalDegree_X]
  have hfinite : Module.Finite ℚ (R₁ ⧸ I) :=
    (natDegree_affineHilbertPolynomial_eq_zero_iff).mp hdegree
  have h := ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial (K := ℚ) I
  rw [hcoeff] at h
  exact h
