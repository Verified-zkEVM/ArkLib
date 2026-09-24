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

/-- Enlarging either bidegree bound preserves membership. -/
example : (X none * X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
    restrictBidegree (Fin 1) ℚ 2 3 := by
  have hnone : (X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
      restrictBidegree (Fin 1) ℚ 1 0 := by
    rw [mem_restrictBidegree, support_X]
    simp
  have hsome : (X (some 0) : MvPolynomial (Option (Fin 1)) ℚ) ∈
      restrictBidegree (Fin 1) ℚ 0 1 := by
    rw [mem_restrictBidegree, support_X]
    simp
  exact mem_restrictBidegree_mono (mul_mem_restrictBidegree hnone hsome)
    (by omega) (by omega)
open Filter Finsupp
open scoped MonomialOrder

local notation "R₁" => MvPolynomial (Fin 1) ℚ
local notation "R₂" => MvPolynomial (Fin 2) ℚ

private theorem component_isLeftRegular_mk_of_isUnit_sub {R : Type*} [CommRing R] {g h : R}
    (hgh : IsUnit (h - g)) : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {g}) h) := by
  have hmk : Ideal.Quotient.mk (Ideal.span {g}) h =
      Ideal.Quotient.mk (Ideal.span {g}) (h - g) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g), sub_zero]
  rw [hmk]
  exact (hgh.map _).isRegular.left

private theorem component_span_ne_top_of_eval_eq_zero {g : MvPolynomial (Fin 1) ℚ}
    (a : Fin 1 → ℚ) (hg : eval a g = 0) : Ideal.span {g} ≠ ⊤ := by
  intro h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
  have := congrArg (eval a) hq
  simp [hg] at this

example : 2 ≤ affineHilbertFunction (⨅ i : Fin 2,
    (![Ideal.span {(X 0 : R₁)}, Ideal.span {X 0 - C 1}] : Fin 2 → Ideal R₁) i) 1 := by
  let P : Fin 2 → Ideal R₁ := ![Ideal.span {X 0}, Ideal.span {X 0 - C 1}]
  let s : Fin 2 → R₁ := ![X 0 - C 1, X 0]
  have hreg : ∀ i, IsLeftRegular (Ideal.Quotient.mk (P i) (s i)) := by
    intro i
    fin_cases i
    · change IsLeftRegular (Ideal.Quotient.mk (Ideal.span {X 0}) (X 0 - C 1))
      exact component_isLeftRegular_mk_of_isUnit_sub
        (by rw [sub_sub_cancel_left, map_one]; exact isUnit_one.neg)
    · change IsLeftRegular (Ideal.Quotient.mk (Ideal.span {X 0 - C 1}) (X 0))
      exact component_isLeftRegular_mk_of_isUnit_sub
        (by rw [sub_sub_cancel, map_one]; exact isUnit_one)
  have hmem : ∀ i j, i ≠ j → s i ∈ P j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Ideal.mem_span_singleton_self _
    · exact Ideal.mem_span_singleton_self _
    · exact absurd rfl hij
  have hdeg : ∀ i, (s i).totalDegree ≤ 1 := by
    intro i
    fin_cases i
    · change (X 0 - C 1 : R₁).totalDegree ≤ 1
      exact (totalDegree_sub_C_le _ _).trans (totalDegree_X 0).le
    · exact (totalDegree_X 0).le
  have h := sum_affineHilbertFunction_le_iInf (I := P) (s := s) (b := fun _ ↦ 1)
    hreg hmem hdeg (fun _ ↦ le_rfl) (N := 1)
  have h0 : 1 ≤ affineHilbertFunction (Ideal.span {(X 0 : R₁)}) 0 :=
    one_le_affineHilbertFunction
      (component_span_ne_top_of_eval_eq_zero (g := (X 0 : R₁)) (fun _ ↦ 0) (by simp)) 0
  have h1 : 1 ≤ affineHilbertFunction (Ideal.span {(X 0 - C 1 : R₁)}) 0 :=
    one_le_affineHilbertFunction
      (component_span_ne_top_of_eval_eq_zero (g := (X 0 - C 1 : R₁)) (fun _ ↦ 1) (by simp)) 0
  have hsum : 2 ≤ ∑ i : Fin 2, affineHilbertFunction (P i) 0 := by
    rw [Fin.sum_univ_two]
    simpa [P] using add_le_add h0 h1
  exact hsum.trans (by simpa only [Nat.sub_self] using h)

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

example :
    ∑ Q ∈ Ideal.iteratedRetainedCutFamily {(⊥ : Ideal R₂)} 1 [X 0, X 0 ^ 2],
        affineDegree Q * (2 : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      ∑ P ∈ {(⊥ : Ideal R₂)},
        affineDegree P * (2 : ℚ) ^ (affineHilbertPolynomial P).natDegree := by
  exact sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le
    (Ps := {(⊥ : Ideal R₂)})
    (fun P hP ↦ Finset.mem_singleton.mp hP ▸ Ideal.isPrime_bot) 1 (b := 2)
    (cuts := [X 0, X 0 ^ 2]) (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · rw [totalDegree_X]
        norm_num
      · rw [totalDegree_X_pow])

local notation "B" => (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))

private theorem isLeftRegular_mk_X : IsLeftRegular (Ideal.Quotient.mk B (X 0)) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero fun h ↦
    X_ne_zero (0 : Fin 1) ((Submodule.mem_bot _).mp (Ideal.Quotient.eq_zero_iff_mem.mp h))

example : (affineHilbertPolynomial (awayPresentationIdeal B (X 0))).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal isLeftRegular_mk_X,
    natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin]

example :
    ∑ Q ∈ ((⊥ : Ideal R₁) ⊔ Ideal.span {X 0}).retainedMinimalPrimes 1, affineDegree Q ≤ 1 := by
  have h := principalCut_sum_affineDegree_retainedMinimalPrimes_le (P := (⊥ : Ideal R₁)) 1
    (f := X 0) (fun h ↦ X_ne_zero 0 ((Submodule.mem_bot ℚ).mp h)) (b := 1)
    (by rw [totalDegree_X])
  simpa [affineDegree_bot, Nat.card_eq_fintype_card, Fintype.card_fin] using h

example :
    (affineHilbertPolynomial ((Ideal.span {(X 0 ^ 2 : R₁)}).radical)).natDegree =
      (affineHilbertPolynomial (Ideal.span {(X 0 ^ 2 : R₁)})).natDegree := by
  exact natDegree_affineHilbertPolynomial_radical _

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

example : Function.Surjective
    (monomialMap ℚ ({Finsupp.single (0 : Fin 1) 1} : Set (Fin 1 →₀ ℕ))) := by
  apply monomialMap_surjective
  intro i
  simp

example :
    {e : Fin 2 →₀ ℕ | e ∈ MonomialOrder.degLex.standardExponents
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ e.degree ≤ 1}.ncard = 3 := by
  rw [← affineHilbertFunction_eq_standard_count, affineHilbertFunction_bot]
  simp

example :
    let I : Ideal (MvPolynomial (Option (Fin 2)) ℚ) :=
      Ideal.span {(X (some (0 : Fin 2)) : MvPolynomial (Option (Fin 2)) ℚ)}
    (affineHilbertPolynomial I).natDegree + (Set.univ : Set (Fin 1)).ncard ≤ 3 := by
  intro I
  have hI : ∀ i ∈ (Set.univ : Set (Fin 1)),
      polynomialCoefficientEvaluation 2 (0 : ℚ) (0 : Polynomial ℚ) ∈ I := by
    intro _ _
    simp [polynomialCoefficientEvaluation, I]
  have hprime : I.IsPrime := by
    change (Ideal.span {(X (some (0 : Fin 2)) : MvPolynomial (Option (Fin 2)) ℚ)}).IsPrime
    exact (Ideal.span_singleton_prime (X_ne_zero _)).mpr X_prime
  have hcard : Nat.card (Option (Fin 2)) = 3 := by simp
  have hdegree : (affineHilbertPolynomial I).natDegree = 2 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one
      (f := (X (some (0 : Fin 2)) : MvPolynomial (Option (Fin 2)) ℚ))
      (X_ne_zero _) hprime.ne_top
    have h' : (affineHilbertPolynomial I).natDegree + 1 = 3 := by
      simpa [I, hcard] using h
    omega
  have hdim : 1 < (affineHilbertPolynomial I).natDegree := by rw [hdegree]; omega
  simpa using natDegree_affineHilbertPolynomial_add_ncard_le_of_polynomialCoefficientEvaluation
    (⟨fun _ ↦ (0 : ℚ), fun _ _ _ ↦ Subsingleton.elim _ _⟩ : Fin 1 ↪ ℚ)
    (fun _ ↦ (0 : Polynomial ℚ)) Set.univ hI hdim
