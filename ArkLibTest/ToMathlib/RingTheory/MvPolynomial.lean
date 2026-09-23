/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbert
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCutFamily
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertRadical
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AwayPresentation
import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedDegree
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Multivariate polynomial acceptance examples
-/

open MvPolynomial
open Filter Finsupp
open scoped MonomialOrder

example : affineDegree (Ideal.span {(X 0 ^ 3 : MvPolynomial (Fin 2) ℚ)}) = 3 := by
  rw [affineDegree_span_singleton (pow_ne_zero 3 (X_ne_zero 0)), totalDegree_X_pow]
  norm_num

example :
    affineHilbertFunction ((⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ⊔ Ideal.span {X 0}) 1 +
        affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 0 ≤
      affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1 := by
  simpa using principalCut_affineHilbertFunction_add_le_of_isPrime (σ := Fin 1) (k := ℚ)
    (b := 1) (N := 1) Ideal.isPrime_bot (f := X 0)
    (by rw [Ideal.mem_bot]; exact X_ne_zero 0) (by simp) le_rfl

example :
    affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 3 ≤
      affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) 3 := by
  let incl : (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) →ₐ[ℚ]
      (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) :=
    Ideal.quotientMapₐ ⊥ (rename Fin.castSucc) bot_le
  have hinj : Function.Injective incl :=
    Ideal.quotientMap_injective' (H := bot_le) fun p hp ↦ by
      have hp' : rename Fin.castSucc p = 0 := by simpa using hp
      exact (Submodule.mem_bot _).mpr
        (rename_injective _ (Fin.castSucc_injective 1) (hp'.trans (map_zero _).symm))
  have hX : ∀ i : Fin 1,
      incl (Ideal.Quotient.mk ⊥ (X i)) ∈
        quotientDegreeLE (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) 1 := by
    intro i
    change Ideal.Quotient.mk ⊥ (rename Fin.castSucc (X i)) ∈ _
    rw [rename_X]
    exact mk_X_mem_quotientDegreeLE _ _
  exact affineHilbertFunction_le_of_injective incl hinj hX 3

example : Module.finrank ℚ (quotientBidegreeLE
    (Ideal.span {(X none : MvPolynomial (Option (Fin 1)) ℚ)}) 1 1) ≤ 2 := by
  have hg0 : (X none : MvPolynomial (Option (Fin 1)) ℚ) ≠ 0 := X_ne_zero none
  have hg : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∈ restrictBidegree (Fin 1) ℚ 1 0 := by
    rw [mem_restrictBidegree, support_X]
    simp
  have h := finrank_quotientBidegreeLE_span_singleton_le hg0 hg le_rfl (Nat.zero_le 1)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

example : affineHilbertFunction ((Ideal.span {
    (X none : MvPolynomial (Option (Fin 2)) ℚ)}).comap
    (monomialMap ℚ (cappedBidegreeExponents (Fin 2) 1 1 2 1))) 1 ≤ 5 := by
  have hg0 : (X none : MvPolynomial (Option (Fin 2)) ℚ) ≠ 0 := X_ne_zero none
  have hg : (X none : MvPolynomial (Option (Fin 2)) ℚ) ∈
      restrictCappedBidegree (Fin 2) ℚ 1 1 0 0 := by
    rw [mem_restrictCappedBidegree, support_X]
    simp
  have h := affineHilbertFunction_comap_cappedBidegree_span_singleton_add_le (N := 1)
    (a := 1) (b := 2) (c := 1) hg0 hg le_rfl (Nat.zero_le _) (Nat.zero_le _)
  have hT := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  norm_num at h
  omega

example : affineHilbertFunction ((Ideal.span {
    (X 0 : MvPolynomial (Fin 2) ℚ)}).comap
    (monomialMap ℚ (cappedDegreeExponents (Fin 2) 1 2 1))) 1 ≤ 2 := by
  have hg0 : (X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 := X_ne_zero 0
  have hg : (X 0 : MvPolynomial (Fin 2) ℚ) ∈
      restrictCappedDegree (Fin 2) ℚ 1 1 0 := by
    rw [mem_restrictCappedDegree, support_X]
    simp
  have h := affineHilbertFunction_comap_cappedDegree_span_singleton_add_le (N := 1) (b := 2)
    (c := 1) hg0 hg (by norm_num) (Nat.zero_le _)
  have hT := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  have hT' := two_mul_ncard_cappedDegreeExponents_fin_two 1 1 le_rfl
  norm_num at h
  omega

private noncomputable abbrev collapse : MvPolynomial (Fin 2) ℚ →ₐ[ℚ]
    MvPolynomial (Fin 1) ℚ := aeval fun _ ↦ X 0

private theorem collapse_surjective : Function.Surjective collapse := fun P ↦
  ⟨rename (fun _ ↦ 0) P, by
    have h : ((fun _ ↦ X 0) ∘ fun _ ↦ (0 : Fin 2) : Fin 1 → MvPolynomial (Fin 1) ℚ) = X :=
      funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl
    rw [collapse, aeval_rename, h, aeval_X_left_apply]⟩

example : (affineHilbertPolynomial (RingHom.ker collapse)).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_ker_of_surjective _ collapse_surjective, Nat.card_fin]

example :
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).natDegree = 2 ∧
      (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).eval 1 = 3 := by
  refine ⟨by simp, ?_⟩
  rw [affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin,
    show (1 : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ 2 (Nat.zero_le _)]
  norm_num [Nat.choose]

local notation "B" => (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))

private theorem isLeftRegular_mk_X : IsLeftRegular (Ideal.Quotient.mk B (X 0)) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero fun h ↦
    X_ne_zero (0 : Fin 1) ((Submodule.mem_bot _).mp (Ideal.Quotient.eq_zero_iff_mem.mp h))

example : (affineHilbertPolynomial (awayPresentationIdeal B (X 0))).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal isLeftRegular_mk_X,
    natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin]

example : Module.finrank ℚ (restrictBidegree (Fin 2) ℚ 2 3) = 30 := by
  rw [finrank_restrictBidegree, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

example :
    Module.finrank ℚ (restrictCappedBidegree (Fin 2) ℚ 1 1 2 1) = 10 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  rw [finrank_restrictCappedBidegree]
  omega

example : Module.finrank ℚ (restrictCappedDegree (Fin 2) ℚ 1 2 1) = 5 := by
  have h := two_mul_ncard_cappedDegreeExponents_fin_two 2 1 (by norm_num)
  rw [finrank_restrictCappedDegree]
  omega

private def firstVariable : Fin 1 ↪ Fin 3 :=
  ⟨fun _ ↦ 0, Function.injective_of_subsingleton _⟩

example : (affineHilbertPolynomial
    (Ideal.span {C 2 * X 0 - X 1 * X 2} : Ideal (MvPolynomial (Fin 3) ℚ))).natDegree ≤ 2 := by
  have h := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (I := Ideal.span {C 2 * X 0 - X 1 * X 2}) firstVariable !![(2 : ℚ)] (by simp)
    (fun _ ↦ C 2 * X 0 - X 1 * X 2) (fun _ ↦ Ideal.subset_span rfl) fun i ↦ by
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Fin.sum_univ_one]
      change (C 2 * X 0 - X 1 * X 2 : MvPolynomial (Fin 3) ℚ) - (2 : ℚ) • X 0 ∈
        supported ℚ (Set.range firstVariable)ᶜ
      rw [← C_mul', sub_sub_cancel_left]
      refine Subalgebra.neg_mem _ (Subalgebra.mul_mem _ ?_ ?_) <;>
        exact X_mem_supported.mpr fun ⟨_, h⟩ ↦ by simp [firstVariable] at h
  simpa using h

example : monomialMap ℚ ({Finsupp.single (0 : Fin 1) 2} : Set (Fin 1 →₀ ℕ))
    (X ⟨_, rfl⟩) = X 0 ^ 2 := by
  rw [monomialMap_X, X_pow_eq_monomial]

example :
    {e : Fin 2 →₀ ℕ | e ∈ MonomialOrder.degLex.standardExponents
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ e.degree ≤ 1}.ncard = 3 := by
  rw [← affineHilbertFunction_eq_standard_count, affineHilbertFunction_bot]
  simp
