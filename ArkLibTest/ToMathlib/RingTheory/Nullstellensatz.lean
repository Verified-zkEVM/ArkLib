/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedBidegreeIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CappedDegreeIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CutFamily
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
import ArkLib.ToMathlib.RingTheory.MvPolynomial.CoefficientEvaluation
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
    let S := {x : Fin 1 → 𝕂 |
      x ∈ zeroLocus 𝕂 (⊥ : Ideal (MvPolynomial (Fin 1) 𝕂)) ∧
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

namespace CappedBidegreeIncidenceCanary

open MvPolynomial

private theorem X_none_mem_restrictCappedBidegree :
    (X none : MvPolynomial (Option (Fin 2)) ℚ) ∈
      restrictCappedBidegree (Fin 2) ℚ 1 1 1 1 := by
  rw [mem_restrictCappedBidegree, support_X]
  simp [Finsupp.some_single_none]

private theorem span_X_none_ne_top :
    Ideal.span {(X none : MvPolynomial (Option (Fin 2)) ℚ)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro h
  simpa using h.map constantCoeff

private theorem natDegree_zero_of_all_variables_mem
    {J : Ideal (MvPolynomial (Option (Fin 2)) ℚ)}
    (hvars : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J) :
    (affineHilbertPolynomial J).natDegree = 0 := by
  let v : Option (Fin 2) ↪ Option (Fin 2) := ⟨id, fun _ _ h ↦ h⟩
  have h := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (I := J) v (1 : Matrix (Option (Fin 2)) (Option (Fin 2)) ℚ)
    (by simp)
    (fun i ↦ X i) hvars (fun i ↦ by simp [v, Matrix.one_apply])
  exact Nat.le_zero.mp (by simpa using h)

private theorem natDegree_le_one_of_two_variables_mem
    {J : Ideal (MvPolynomial (Option (Fin 2)) ℚ)}
    (h₀ : (X none : MvPolynomial (Option (Fin 2)) ℚ) ∈ J)
    (h₁ : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J) :
    (affineHilbertPolynomial J).natDegree ≤ 1 := by
  let v : Fin 2 ↪ Option (Fin 2) := ⟨![none, some 1], by decide⟩
  have h := natDegree_affineHilbertPolynomial_le_card_sub_of_isUnit_det
    (I := J) v (1 : Matrix (Fin 2) (Fin 2) ℚ) (by simp)
    (fun i ↦ X (v i)) (by
      intro i
      fin_cases i
      · simpa [v] using h₀
      · simpa [v] using h₁) (fun i ↦ by simp [v, Matrix.one_apply])
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_fin] using h

private theorem X_mem_restrictCappedBidegree (i : Option (Fin 2)) :
    (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈
    restrictCappedBidegree (Fin 2) ℚ 1 1 1 1 := by
  rw [mem_restrictCappedBidegree, support_X]
  cases i with
  | none => simp [Finsupp.some_single_none]
  | some i => fin_cases i <;> simp [Finsupp.some_single_some]

/-- The origin on the coordinate line cut from `X none = 0` satisfies the hybrid bound. -/
example :
    (({fun _ : Option (Fin 2) => (0 : ℚ)} : Finset (Option (Fin 2) → ℚ)).card : ℚ) ≤
      (cappedBidegreeMixedVolume 1 1 1 1 1 1 : ℕ) *
        (((4 - 1 + 1 : ℕ) : ℚ) / ((2 - 1 + 1 : ℕ) : ℚ)) *
          (((4 - 0 + 1 : ℕ) : ℚ) / ((2 - 0 + 1 : ℕ) : ℚ)) := by
  let cuts : Fin 4 → MvPolynomial (Option (Fin 2)) ℚ :=
    fun _ ↦ X (some 0)
  have h := MvPolynomial.cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two
    (a := 1) (b := 1) (c := 1) (h := 1) (j := 1) (r := 1) (n := 4)
    (A := 2) (L := 1) (k := 0)
    (ha := by norm_num) (hb := by norm_num) (hc := by norm_num)
    (hLA := by norm_num) (hkA := by norm_num)
    (g := X none) (s := 1)
    (hg0 := X_ne_zero _) (hproper := span_X_none_ne_top)
    (hg := X_none_mem_restrictCappedBidegree)
    (hgAB := X_none_mem_restrictCappedBidegree)
    (hs := by
      rw [mem_restrictCappedBidegree]
      simp)
    (highCuts := [X none, X (some 1)])
    (hhigh := by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> exact X_mem_restrictCappedBidegree _)
    (cuts := cuts)
    (hcuts := by
      intro i
      exact X_mem_restrictCappedBidegree _)
    (excluded := ∅)
    (hdimension := by
      intro J hJ hsJ hX hhigh hd
      have h₁ : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhigh _ (by simp)
      have hdim := natDegree_le_one_of_two_variables_mem hX h₁
      exact ⟨by omega, fun hgt ↦ by omega⟩)
    (hterminal := by
      intro J hJ hsJ hX hhigh hd hL
      have h₁ : (X (some 1) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J :=
        hhigh _ (by simp)
      have hpos : 0 < {i : Fin 4 | cuts i ∈ J}.ncard := by omega
      have h₀ : (X (some 0) : MvPolynomial (Option (Fin 2)) ℚ) ∈ J := by
        obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
        simpa [cuts] using hi
      have hvars : ∀ i, (X i : MvPolynomial (Option (Fin 2)) ℚ) ∈ J := by
        intro i
        cases i with
        | none => exact hX
        | some i =>
          fin_cases i
          · exact h₀
          · exact h₁
      rw [natDegree_zero_of_all_variables_mem hvars] at hd
      omega)
    (S := {fun _ : Option (Fin 2) => (0 : ℚ)})
    (hS := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      simp)
    (hA := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      have hcuts : {i : Fin 4 | aeval (fun _ : Option (Fin 2) ↦ (0 : ℚ))
          (X (some 0) : MvPolynomial (Option (Fin 2)) ℚ) = 0} = Set.univ := by
        ext i
        simp
      rw [hcuts]
      simp)
  have hvolume : cappedBidegreeMixedVolume 1 1 1 1 1 1 = 3 := by
    rw [cappedBidegreeMixedVolume_eq (by norm_num)]
  norm_num [hvolume] at h ⊢

end CappedBidegreeIncidenceCanary

namespace CappedDegreeIncidenceCanary

open MvPolynomial

private theorem X_mem_restrictCappedDegree (i : Fin 2) :
    (X i : MvPolynomial (Fin 2) 𝕂) ∈ restrictCappedDegree (Fin 2) 𝕂 1 1 1 := by
  rw [mem_restrictCappedDegree, support_X]
  intro e he
  rw [Finset.mem_singleton] at he
  subst e
  constructor
  · simp [Finsupp.degree_single]
  · simp [Finsupp.single_apply]
    split_ifs <;> norm_num

private theorem X_zeroSubOne_mem_restrictCappedDegree :
    (X 0 - 1 : MvPolynomial (Fin 2) 𝕂) ∈
      restrictCappedDegree (Fin 2) 𝕂 1 1 1 := by
  apply Submodule.sub_mem
  · exact X_mem_restrictCappedDegree 0
  · rw [mem_restrictCappedDegree]
    simp

private noncomputable def cappedDegreeLinePoint : Fin 2 → 𝕂 := ![1, 0]

/-- The point `(1, 0)` on the line `X 1 = 0` satisfies the capped-degree incidence bound. -/
example :
    ((({cappedDegreeLinePoint} : Finset (Fin 2 → 𝕂)).card : ℚ)) ≤
      (cappedDegreeMixedVolume 1 1 1 1 : ℕ) *
        (((2 - 0 + 1 : ℕ) : ℚ) / ((2 - 0 + 1 : ℕ) : ℚ)) := by
  let cuts : Fin 2 → MvPolynomial (Fin 2) 𝕂 := fun _ ↦ X 0 - 1
  have h := cappedDegreeHypersurface_incidence_sharp
    (b := 1) (c := 1) (j := 1) (r := 1) (n := 2) (A := 2) (k := 0)
    (hb := by norm_num) (hc := by norm_num) (hkA := by norm_num) (hAn := by norm_num)
    (g := X 1) (s := 1) (hg0 := X_ne_zero _)
    (hg := X_mem_restrictCappedDegree 1)
    (hgbc := X_mem_restrictCappedDegree 1)
    (hsbc := by rw [mem_restrictCappedDegree]; simp)
    (highCuts := [X 0 - 1])
    (hhigh := by
      intro f hf
      simp only [List.mem_singleton] at hf
      subst f
      exact X_zeroSubOne_mem_restrictCappedDegree)
    (cuts := cuts)
    (hcuts := by intro i; exact X_zeroSubOne_mem_restrictCappedDegree)
    (S := {cappedDegreeLinePoint})
    (hS := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      simp [cappedDegreeLinePoint])
    (hA := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst x
      simp [cappedDegreeLinePoint, cuts])
    (hunique := by
      intro J hJ hsJ hgJ hhigh U hU x y hx hxs hy hys hcuts
      have hcut : (X 0 - 1 : MvPolynomial (Fin 2) 𝕂) ∈ J :=
        hhigh _ (by simp)
      have hx0 : x 0 = 1 := by
        have h := hx _ hcut
        simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
      have hy0 : y 0 = 1 := by
        have h := hy _ hcut
        simpa only [map_sub, aeval_X, map_one, sub_eq_zero] using h
      have hx1 : x 1 = 0 := by simpa using hx _ hgJ
      have hy1 : y 1 = 0 := by simpa using hy _ hgJ
      funext j
      fin_cases j
      <;> simp [hx0, hy0, hx1, hy1])
  norm_num [cappedDegreeMixedVolume] at h ⊢

end CappedDegreeIncidenceCanary
