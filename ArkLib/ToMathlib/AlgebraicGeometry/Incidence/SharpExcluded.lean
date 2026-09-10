/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Excluded
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpRatio

/-!
# Sharp agreement incidence outside an excluded locus

The sharp affine incidence induction also applies when positive-dimensional components supported
on many agreement cuts lie in an excluded set. The exclusion condition is imposed on every
prime extension of the starting ideal, so it persists through retained principal cuts.
The excluded set need not be algebraic and contributes no additional degree factor.
Keeping the actual number of identically vanishing cuts in both incidence counts gives
the ratio `(n-L+1)/(A-L+1)` throughout the recursive argument.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Incidence induction with an explicit dimension and hereditary exclusion condition. -/
private theorem affineAgreementIncidence_bound_off_excluded_sharp_aux
    {n A L b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
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
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
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
          let R : ℚ := (((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hBad : Bad.card < L := by
            by_contra hnot
            have hcover := hterminal P le_rfl hP hs hdpos (Nat.le_of_not_gt hnot)
            exact (hS x₀ hx₀).2 (hcover (hS x₀ hx₀).1)
          have hlowerNat : S.card * (A - Bad.card) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            exact finiteAgreementIncidence_lower_sharp S Bad
              (fun x i ↦ aeval x (cuts i) = 0) (fun x hx ↦ hA x hx)
          have hlower : (S.card : ℚ) * (A - Bad.card : ℕ) ≤
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
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤ b * affineDegree P * R ^ e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S (fun x hx ↦ (hS x hx).1)
            have hsdeg := sum_retained_affineDegree_le (s := s) hP hiP (hdeg i)
            calc
              ((cutPoints S (cuts i)).card : ℚ) ≤
                  ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    ((componentPoints S Q).card : ℚ) := by exact_mod_cast hc
              _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q * R ^ e := Finset.sum_le_sum (fun Q hQ ↦ hchild i hiP Q hQ)
              _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q) * R ^ e := by rw [Finset.sum_mul]
              _ ≤ ((b : ℚ) * affineDegree P) * R ^ e :=
                mul_le_mul_of_nonneg_right hsdeg (by positivity)
              _ = (b : ℚ) * affineDegree P * R ^ e := rfl
          have hgoodcard : good.card = n - Bad.card := by
            rw [show good = Finset.univ \ Bad by ext i; simp [good]]
            rw [Finset.card_sdiff]
            simp
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P * R ^ e) := by
            calc
              _ ≤ ∑ _i ∈ good, ((b : ℚ) * affineDegree P * R ^ e) :=
                Finset.sum_le_sum hone
              _ = _ := by simp [hgoodcard]
          have hden : (0 : ℚ) < (A - Bad.card : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_le hLA)
          have hratio := goodCuts_div_agreements_le hBad hLA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - L + 1 : ℕ) : ℚ) /
                    (A - L + 1 : ℕ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - L + 1) * b : ℕ) : ℚ) / (A - L + 1 : ℕ) := by
                rw [Nat.cast_mul]
                ring
          apply le_of_mul_le_mul_right _ hden
          calc
            (S.card : ℚ) * (A - Bad.card : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ ((n - Bad.card : ℕ) : ℚ) *
                ((b : ℚ) * affineDegree P * R ^ e) := hupper
            _ ≤ (affineDegree P * R ^ (e + 1)) * (A - Bad.card : ℕ) := by
              rw [pow_succ]
              calc
                ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P * R ^ e) =
                    (((n - Bad.card : ℕ) : ℚ) * b) *
                      (affineDegree P * R ^ e) := by ring
                _ ≤ (R * (A - Bad.card : ℕ)) * (affineDegree P * R ^ e) :=
                  mul_le_mul_of_nonneg_right hlocal
                    (mul_nonneg (affineDegree_nonneg P) (pow_nonneg (by positivity) e))
                _ = (affineDegree P * (R ^ e * R)) * (A - Bad.card : ℕ) := by ring

/-- A finite set outside an excluded locus obeys the usual affine incidence bound if
every positive-dimensional prime extension supported on at least `L` cuts has its regular
points in that locus. This hypothesis is hereditary through all retained cuts; no point
uniqueness assumption or polynomial equation for the excluded locus is required. -/
theorem affineAgreementIncidence_bound_off_excluded_sharp
    {n A L b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_off_excluded_sharp_aux hP hs cuts hdeg hb hLA hAn
    excluded hterminal S hS hA rfl

end AffineHilbert
