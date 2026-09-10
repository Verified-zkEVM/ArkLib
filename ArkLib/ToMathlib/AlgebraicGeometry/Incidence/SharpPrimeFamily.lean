/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpRatio

/-!
# Sharp agreement incidence for an initial prime family

This version keeps the actual number of cuts vanishing identically on a component
in both sides of the incidence ratio.  Consequently its numerator is `n-k+1`.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]

private theorem affineAgreementIncidence_bound_sharp_aux
    {n A k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (_hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P *
      ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      cases d with
      | zero =>
          have ht := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hc : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1) ht.1
          have hc' : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by exact_mod_cast hc
          simpa using hc'.trans ht.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter (fun i ↦ i ∉ Bad)
          let R : ℚ := (((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hBad : Bad.card < k := card_cuts_mem_prime_lt hP hs cuts hdpos hunique
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
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨hx.2, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · intro T hT x y hxP hxs hyP hys hz
              exact hunique T hT x y (zeroLocus_anti_mono hQP hxP) hxs
                (zeroLocus_anti_mono hQP hyP) hys hz
            · exact hQdegree
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤ b * affineDegree P * R ^ e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S hS
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
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_le hkA)
          have hratio := goodCuts_div_agreements_le hBad hkA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - k + 1 : ℕ) : ℚ) /
                    (A - k + 1 : ℕ)) := mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - k + 1) * b : ℕ) : ℚ) / (A - k + 1 : ℕ) := by
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

/-- Sharp per-prime agreement incidence bound. -/
theorem affineAgreementIncidence_bound_sharp
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ affineDegree P *
      ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^
        (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_sharp_aux hP hs cuts hdeg hb hk hkA hAn
    S hS hA hunique rfl

/-- Sum the sharp per-prime incidence estimate over a supplied retained prime family.
The family may already incorporate any fixed high cuts; its total degree potential is
therefore supplied directly. -/
theorem retainedPrimeFamily_incidence_bound_sharp
    {n A k b d : ℕ} (T : Finset (Ideal (MvPolynomial σ F)))
    (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ T, P.IsPrime) (hopen : ∀ P ∈ T, s ∉ P)
    (hdim : ∀ P ∈ T, (hilbertPolynomial P).natDegree = d)
    {V : ℚ} (hpotential : ∑ P ∈ T, affineDegree P ≤ V)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (σ → F))
    (hcover : ∀ x ∈ S, ∃ P ∈ T, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hunique : ∀ P ∈ T, ∀ U : Finset (Fin n), U.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ U, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ V *
      ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let R : ℚ := (((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have hcard : S.card ≤ ∑ P ∈ T, (componentPoints S P).card := by
    apply le_trans _ Finset.card_biUnion_le
    apply Finset.card_le_card
    intro x hx
    obtain ⟨P, hPT, hxP, _⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨P, hPT, by
      rw [mem_componentPoints]
      exact ⟨hx, hxP⟩⟩
  have hone (P : Ideal (MvPolynomial σ F)) (hPT : P ∈ T) :
      ((componentPoints S P).card : ℚ) ≤ affineDegree P * R ^ d := by
    rw [← hdim P hPT]
    apply affineAgreementIncidence_bound_sharp (hprime P hPT) (hopen P hPT)
      cuts hdeg hb hk hkA hAn
    · intro x hx
      rw [mem_componentPoints] at hx
      exact ⟨hx.2, (hcover x hx.1).choose_spec.2.2⟩
    · intro x hx
      rw [mem_componentPoints] at hx
      exact hA x hx.1
    · exact hunique P hPT
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
      exact_mod_cast hcard
    _ ≤ ∑ P ∈ T, affineDegree P * R ^ d := Finset.sum_le_sum hone
    _ = (∑ P ∈ T, affineDegree P) * R ^ d := by rw [Finset.sum_mul]
    _ ≤ V * R ^ d := mul_le_mul_of_nonneg_right hpotential (by positivity)
    _ = _ := rfl

end AffineHilbert
