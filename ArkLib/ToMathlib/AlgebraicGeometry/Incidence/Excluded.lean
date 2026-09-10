/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement

/-!
# Agreement incidence outside an excluded locus

The affine incidence induction also applies when positive-dimensional components supported
on many agreement cuts lie in an excluded set. The exclusion condition is imposed on every
prime extension of the starting ideal, so it persists through retained principal cuts.
The excluded set need not be algebraic and contributes no additional degree factor.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Incidence induction with an explicit dimension and hereditary exclusion condition. -/
private theorem affineAgreementIncidence_bound_off_excluded_aux
    {n A L b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hLA : L ≤ A)
    (excluded : Set (σ → F))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P *
      (((n * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      by_cases hSempty : S = ∅
      · subst S
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (affineDegree_nonneg P) (by positivity)
      obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      cases d with
      | zero =>
          have hfinite := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hcardNat : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1.1) hfinite.1
          have hcardRat : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hcardNat
          simpa only [pow_zero, mul_one] using hcardRat.trans hfinite.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter (fun i ↦ i ∉ Bad)
          let R : ℚ := ((n * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hBad : Bad.card < L := by
            by_contra hnot
            have hcover := hterminal P le_rfl hP hs hdpos (Nat.le_of_not_gt hnot)
            exact (hS x₀ hx₀).2 (hcover (hS x₀ hx₀).1)
          have hlowerNat : S.card * (A - L + 1) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            apply finiteAgreementIncidence_lower S Bad
              (fun x i ↦ aeval x (cuts i) = 0) hLA hBad
            intro x hx
            exact hA x hx
          have hlower : (S.card : ℚ) * (A - L + 1 : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q * R ^ e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            have hQP : P ≤ Q := le_sup_left.trans hQdata.1.le
            have hQdegree : (hilbertPolynomial Q).natDegree = e := by
              have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
                hP hiP hQdata.1
              rw [hd] at hpure
              omega
            apply ih e (by omega) (P := Q) (S := componentPoints S Q)
              hQdata.1.isPrime hQdata.2
            · intro J hQJ hJ hsJ hdJ hcutsJ
              exact hterminal J (hQP.trans hQJ) hJ hsJ hdJ hcutsJ
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨⟨hx.2, (hS x hx.1).1.2⟩, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · exact hQdegree
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              (n : ℚ) * (b : ℚ) * affineDegree P * R ^ e := by
            exact sum_card_cutPoints_le_of_child_bounds hP s cuts S
              (fun x hx ↦ (hS x hx).1) hdeg hchild
          have hcpos : (0 : ℚ) < (A - L + 1 : ℕ) := by positivity
          apply le_of_mul_le_mul_right ?_ hcpos
          calc
            (S.card : ℚ) * (A - L + 1 : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ (n : ℚ) * (b : ℚ) * affineDegree P * R ^ e := hupper
            _ = (affineDegree P * R ^ (e + 1)) * (A - L + 1 : ℕ) := by
              dsimp only [R]
              rw [pow_succ]
              push_cast
              field_simp

/-- A finite set outside an excluded locus obeys the usual affine incidence bound if
every positive-dimensional prime extension supported on at least `L` cuts has its regular
points in that locus. This hypothesis is hereditary through all retained cuts; no point
uniqueness assumption or polynomial equation for the excluded locus is required. -/
theorem affineAgreementIncidence_bound_off_excluded
    {n A L b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hLA : L ≤ A)
    (excluded : Set (σ → F))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      (((n * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_off_excluded_aux hP hs cuts hdeg hb hLA
    excluded hterminal S hS hA rfl

end AffineHilbert
