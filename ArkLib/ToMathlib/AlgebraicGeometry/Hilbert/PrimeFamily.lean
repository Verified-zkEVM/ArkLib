/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Function

/-!
# Filtered separator injections for finite families of prime components

A separator for each component embeds the product of shifted filtered
component quotients into the quotient by the intersection.
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

variable {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]

def familySeparatorLift (S K : Ideal (MvPolynomial σ F))
    (f : MvPolynomial σ F) (hmul : ∀ p ∈ S, f * p ∈ K) :
    MvPolynomial σ F ⧸ S →ₗ[F] MvPolynomial σ F ⧸ K :=
  (S.restrictScalars F).liftQ
    ((Ideal.Quotient.mkₐ F K).toLinearMap.comp (LinearMap.mulLeft F f))
    (by
      intro p hp
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      change Ideal.Quotient.mk K (f * p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmul p hp))

omit [Finite σ] [Fintype ι] in
private lemma factor_familySeparatorLift (S K : Ideal (MvPolynomial σ F))
    (f : MvPolynomial σ F) (hmul : ∀ p ∈ S, f * p ∈ K) (hKS : K ≤ S)
    (x : MvPolynomial σ F ⧸ S) :
    Ideal.Quotient.factor hKS (familySeparatorLift S K f hmul x) =
      Ideal.Quotient.mk S f * x := by
  induction x using Quotient.inductionOn'
  change Ideal.Quotient.factor hKS
      (Ideal.Quotient.mk K (f * _)) = Ideal.Quotient.mk S f * Ideal.Quotient.mk S _
  rw [Ideal.Quotient.factor_mk, map_mul]

omit [Finite σ] [Fintype ι] in
private lemma factor_familySeparatorLift_eq_zero
    (S K T : Ideal (MvPolynomial σ F))
    (f : MvPolynomial σ F) (hmul : ∀ p ∈ S, f * p ∈ K) (hKT : K ≤ T)
    (hfT : f ∈ T) (x : MvPolynomial σ F ⧸ S) :
    Ideal.Quotient.factor hKT (familySeparatorLift S K f hmul x) = 0 := by
  induction x using Quotient.inductionOn'
  change Ideal.Quotient.factor hKT (Ideal.Quotient.mk K (f * _)) = 0
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact T.mul_mem_right _ hfT

def filteredFamilySeparatorLift (S K : Ideal (MvPolynomial σ F))
    (f : MvPolynomial σ F) (hmul : ∀ p ∈ S, f * p ∈ K) {b N : ℕ}
    (hfdeg : f.totalDegree ≤ b) (hbN : b ≤ N) :
    quotientDegreeLE S (N - b) →ₗ[F] quotientDegreeLE K N :=
  ((familySeparatorLift S K f hmul).domRestrict
    (quotientDegreeLE S (N - b))).codRestrict (quotientDegreeLE K N) (fun x ↦ by
      obtain ⟨p, hp, hpx⟩ := x.property
      refine ⟨f * p, ?_, ?_⟩
      · apply (mem_restrictTotalDegree σ N (f * p)).mpr
        apply (totalDegree_mul f p).trans
        calc
          f.totalDegree + p.totalDegree ≤ b + (N - b) :=
            Nat.add_le_add hfdeg ((mem_restrictTotalDegree σ (N - b) p).mp hp)
          _ = N := Nat.add_sub_of_le hbN
      · change Ideal.Quotient.mk K (f * p) = familySeparatorLift S K f hmul x
        rw [← hpx]
        rfl)

def separatorFamilyMap (P : ι → Ideal (MvPolynomial σ F))
    (s : ι → MvPolynomial σ F) (b : ι → ℕ) {N : ℕ}
    (hsOther : ∀ i j, i ≠ j → s i ∈ P j)
    (hsdeg : ∀ i, (s i).totalDegree ≤ b i) (hbN : ∀ i, b i ≤ N) :
    ((i : ι) → quotientDegreeLE (P i) (N - b i)) →ₗ[F]
      quotientDegreeLE (⨅ i, P i) N := by
  classical
  exact LinearMap.lsum F (fun i : ι ↦ quotientDegreeLE (P i) (N - b i)) F
    (fun i ↦ filteredFamilySeparatorLift (P i) (⨅ j, P j) (s i)
      (fun p hp ↦ Ideal.mem_iInf.mpr (fun j ↦ by
        by_cases hji : j = i
        · subst j
          exact (P i).mul_mem_left (s i) hp
        · exact (P j).mul_mem_right p (hsOther i j (fun hij ↦ hji hij.symm))))
      (hsdeg i) (hbN i))

omit [Finite σ] in
/-- Separators outside their own prime and inside every other prime give an
injective filtered map from all components into their intersection. -/
theorem separatorFamilyMap_injective
    (P : ι → Ideal (MvPolynomial σ F)) (hP : ∀ i, (P i).IsPrime)
    (s : ι → MvPolynomial σ F) (b : ι → ℕ) {N : ℕ}
    (hsOwn : ∀ i, s i ∉ P i) (hsOther : ∀ i j, i ≠ j → s i ∈ P j)
    (hsdeg : ∀ i, (s i).totalDegree ≤ b i) (hbN : ∀ i, b i ≤ N) :
    Function.Injective (separatorFamilyMap P s b hsOther hsdeg hbN) := by
  classical
  intro x y hxy
  apply sub_eq_zero.mp
  have hx : separatorFamilyMap P s b hsOther hsdeg hbN (x - y) = 0 := by
    calc
      separatorFamilyMap P s b hsOther hsdeg hbN (x - y) =
          separatorFamilyMap P s b hsOther hsdeg hbN x -
            separatorFamilyMap P s b hsOther hsdeg hbN y :=
        (separatorFamilyMap P s b hsOther hsdeg hbN).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  funext i
  apply Subtype.ext
  have hvalue := congrArg
    (fun z ↦ (z.1 : MvPolynomial σ F ⧸ (⨅ i, P i))) hx
  simp only [separatorFamilyMap, LinearMap.lsum_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.coe_zero, Submodule.coe_sum,
    filteredFamilySeparatorLift, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      at hvalue
  have hfactor := congrArg (Ideal.Quotient.factor (iInf_le P i)) hvalue
  rw [map_sum, Finset.sum_eq_single i] at hfactor
  · change Ideal.Quotient.factor (iInf_le P i)
        (familySeparatorLift (P i) (⨅ j, P j) (s i) _ ((x - y) i).1) = 0 at hfactor
    rw [factor_familySeparatorLift] at hfactor
    let _ : (P i).IsPrime := hP i
    have hszero : Ideal.Quotient.mk (P i) (s i) ≠ 0 :=
      Ideal.Quotient.eq_zero_iff_mem.not.mpr (hsOwn i)
    exact (mul_eq_zero.mp hfactor).resolve_left hszero
  · intro j _ hj
    change Ideal.Quotient.factor (iInf_le P i)
        (familySeparatorLift (P j) (⨅ k, P k) (s j) _ ((x - y) j).1) = 0
    exact factor_familySeparatorLift_eq_zero (P j) (⨅ k, P k) (P i)
      (s j) _ (iInf_le P i) (hsOther j i hj) ((x - y) j).1
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- A finite family of separated prime components contributes the sum of its
shifted Hilbert functions to the Hilbert function of the intersection. -/
theorem sum_shifted_hilbertFunction_le_iInf
    (P : ι → Ideal (MvPolynomial σ F)) (hP : ∀ i, (P i).IsPrime)
    (s : ι → MvPolynomial σ F) (b : ι → ℕ) {N : ℕ}
    (hsOwn : ∀ i, s i ∉ P i) (hsOther : ∀ i j, i ≠ j → s i ∈ P j)
    (hsdeg : ∀ i, (s i).totalDegree ≤ b i) (hbN : ∀ i, b i ≤ N) :
    ∑ i, hilbertFunction (P i) (N - b i) ≤ hilbertFunction (⨅ i, P i) N := by
  let _ (i : ι) : Module.Free F (quotientDegreeLE (P i) (N - b i)) :=
    Module.Free.of_divisionRing F _
  simp only [hilbertFunction]
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective
    (separatorFamilyMap_injective P hP s b hsOwn hsOther hsdeg hbN)

/-- Pairwise incomparable prime ideals admit a finite family of separators,
and hence a common shift after which all component Hilbert functions inject
simultaneously into the Hilbert function of their intersection. -/
theorem exists_separators_sum_shifted_hilbertFunction_le_iInf
    (P : ι → Ideal (MvPolynomial σ F)) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) :
    ∃ s : ι → MvPolynomial σ F,
      (∀ i, s i ∉ P i) ∧ (∀ i j, i ≠ j → s i ∈ P j) ∧
      ∀ N ≥ Finset.univ.sup (fun i ↦ (s i).totalDegree),
        ∑ i, hilbertFunction (P i) (N - (s i).totalDegree) ≤
          hilbertFunction (⨅ i, P i) N := by
  classical
  have hwexists : ∀ (i j : ι), i ≠ j →
      ∃ w : MvPolynomial σ F, w ∈ P j ∧ w ∉ P i := by
    intro i j hij
    exact SetLike.not_le_iff_exists.mp (hinc hij.symm)
  let w : ι → ι → MvPolynomial σ F := fun i j ↦
    if hij : i ≠ j then Classical.choose (hwexists i j hij) else 1
  have hwmem (i j : ι) (hij : i ≠ j) : w i j ∈ P j := by
    simp only [w, dif_pos hij]
    exact (Classical.choose_spec (hwexists i j hij)).1
  have hwnmem (i j : ι) (hij : i ≠ j) : w i j ∉ P i := by
    simp only [w, dif_pos hij]
    exact (Classical.choose_spec (hwexists i j hij)).2
  let s : ι → MvPolynomial σ F := fun i ↦ ∏ j ∈ Finset.univ.erase i, w i j
  have hsOwn (i : ι) : s i ∉ P i := by
    let _ : (P i).IsPrime := hP i
    dsimp only [s]
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    intro j hj
    exact hwnmem i j (Finset.ne_of_mem_erase hj).symm
  have hsOther (i j : ι) (hij : i ≠ j) : s i ∈ P j := by
    apply Ideal.prod_mem (P j) (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    exact hwmem i j hij
  refine ⟨s, hsOwn, hsOther, ?_⟩
  intro N hN
  apply sum_shifted_hilbertFunction_le_iInf P hP s
    (fun i ↦ (s i).totalDegree) hsOwn hsOther (fun _ ↦ le_rfl)
  intro i
  exact (Finset.le_sup (Finset.mem_univ i)).trans hN

end AffineHilbert
