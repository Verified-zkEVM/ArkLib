/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Cuts
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalOpen.Finite
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Bezout
public import ArkLib.ToMathlib.Combinatorics.FiniteAgreementIncidence

/-!
# Incidence bounds on affine principal opens

A finite set of points on the principal open of an affine prime is bounded by repeatedly cutting
with a finite family of bounded-degree equations.  The proof uses the actual Hilbert-polynomial
dimension and affine degree, together with refined principal-cut Bezout.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [IsAlgClosed F] [Finite σ]

/-- Indices of equations that vanish identically on an affine ideal. -/
def cutsInIdeal {n : ℕ} (P : Ideal (MvPolynomial σ F))
    (cuts : Fin n → MvPolynomial σ F) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ cuts i ∈ P

omit [IsAlgClosed F] [Finite σ] in
@[simp] theorem mem_cutsInIdeal {n : ℕ} {P : Ideal (MvPolynomial σ F)}
    {cuts : Fin n → MvPolynomial σ F} {i : Fin n} :
    i ∈ cutsInIdeal P cuts ↔ cuts i ∈ P := by
  classical
  simp [cutsInIdeal]

/-- Points of a finite set on which an additional equation vanishes. -/
def cutPoints (S : Finset (σ → F)) (f : MvPolynomial σ F) : Finset (σ → F) := by
  classical
  exact S.filter fun x ↦ aeval x f = 0

omit [IsAlgClosed F] [Finite σ] in
@[simp] theorem mem_cutPoints {S : Finset (σ → F)} {f : MvPolynomial σ F}
    {x : σ → F} : x ∈ cutPoints S f ↔ x ∈ S ∧ aeval x f = 0 := by
  classical
  change x ∈ S.filter (fun y ↦ MvPolynomial.eval y f = 0) ↔
    x ∈ S ∧ MvPolynomial.eval x f = 0
  exact Finset.mem_filter

/-- Points of a finite set lying on an affine component. -/
def componentPoints (S : Finset (σ → F))
    (Q : Ideal (MvPolynomial σ F)) : Finset (σ → F) := by
  classical
  exact S.filter fun x ↦ x ∈ zeroLocus F Q

omit [IsAlgClosed F] [Finite σ] in
@[simp] theorem mem_componentPoints {S : Finset (σ → F)}
    {Q : Ideal (MvPolynomial σ F)} {x : σ → F} :
    x ∈ componentPoints S Q ↔ x ∈ S ∧ x ∈ zeroLocus F Q := by
  classical
  simp [componentPoints]

/-- Indices of equations vanishing at a point. -/
def agreementIndices {n : ℕ} (cuts : Fin n → MvPolynomial σ F)
    (x : σ → F) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ aeval x (cuts i) = 0

omit [IsAlgClosed F] [Finite σ] in
@[simp] theorem mem_agreementIndices {n : ℕ} {cuts : Fin n → MvPolynomial σ F}
    {x : σ → F} {i : Fin n} :
    i ∈ agreementIndices cuts x ↔ aeval x (cuts i) = 0 := by
  classical
  change i ∈ Finset.univ.filter (fun j ↦ MvPolynomial.eval x (cuts j) = 0) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- If `k` equations identify points on the whole principal open, fewer than `k` of the equations
can vanish identically on a positive-dimensional prime component. -/
theorem card_cuts_mem_prime_lt
    {n k : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (cutsInIdeal P cuts).card < k := by
  classical
  by_contra hnot
  have hk : k ≤ (cutsInIdeal P cuts).card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hk
  have hopen : (principalOpenZeroLocus P s).Subsingleton := by
    intro x hx y hy
    apply hunique T hTcard x y hx.1 hx.2 hy.1 hy.2
    intro i hi
    have hiP : cuts i ∈ P := by
      simpa only [cutsInIdeal, Finset.mem_filter, Finset.mem_univ, true_and] using hTsub hi
    exact ⟨hx.1 (cuts i) hiP, hy.1 (cuts i) hiP⟩
  have hzero := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hopen.finite
  omega

omit [IsAlgClosed F] in
/-- The points of a finite set lying on one additional equation are covered by the retained
minimal components of that cut, with the corresponding cardinality union bound. -/
theorem card_filter_cut_le_sum_retained
    (P : Ideal (MvPolynomial σ F)) (s f : MvPolynomial σ F)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0) :
    (cutPoints S f).card ≤
      ∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s,
        (componentPoints S Q).card := by
  classical
  let C := (P ⊔ Ideal.span {f}).retainedMinimalPrimes s
  let SQ : Ideal (MvPolynomial σ F) → Finset (σ → F) :=
    fun Q => componentPoints S Q
  calc
    (cutPoints S f).card ≤ (C.biUnion SQ).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [cutPoints, Finset.mem_filter] at hx
      obtain ⟨Q, hQC, hxQ, _⟩ :=
        (mem_zeroLocus_and_cut_iff_retained P s f x).mp
          ⟨(hS x hx.1).1, hx.2, (hS x hx.1).2⟩
      exact Finset.mem_biUnion.mpr ⟨Q, hQC, by
        rw [mem_componentPoints]
        exact ⟨hx.1, hxQ⟩⟩
    _ ≤ ∑ Q ∈ C, (SQ Q).card := Finset.card_biUnion_le

omit [IsAlgClosed F] in
/-- Retaining only components meeting a principal open can only decrease the total affine degree
of a proper principal cut. -/
theorem sum_retained_affineDegree_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s f : MvPolynomial σ F} (hf : f ∉ P) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ (P ⊔ Ideal.span {f}).retainedMinimalPrimes s, affineDegree Q ≤
      (b : ℚ) * affineDegree P := by
  classical
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (principalCut_sum_affineDegree_le hP hf hfdeg)
  · intro Q hQ
    exact mem_minimalPrimesFinset.mpr
      ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ).1
  · intro Q _ _
    exact affineDegree_nonneg Q

omit [IsAlgClosed F] in
/-- The geometric upper half of the incidence induction: if every retained child obeys the
dimension-`d` estimate, summing over all non-identically-zero cuts costs at most `n b` times the
parent degree. -/
theorem sum_card_cutPoints_le_of_child_bounds
    {n b d A k : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    (s : MvPolynomial σ F) (cuts : Fin n → MvPolynomial σ F)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hchild : ∀ i, cuts i ∉ P →
      ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
        ((componentPoints S Q).card : ℚ) ≤ affineDegree Q *
          (((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ cutsInIdeal P cuts),
        ((cutPoints S (cuts i)).card : ℚ) ≤
      (n : ℚ) * (b : ℚ) * affineDegree P *
        (((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let R : ℚ := ((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  let good := Finset.univ.filter (fun i ↦ i ∉ cutsInIdeal P cuts)
  have hR : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hproper : ∀ i ∈ good, cuts i ∉ P := by
    intro i hi
    simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_cutsInIdeal, not_false_eq_true] using hi
  have hone : ∀ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
      (b : ℚ) * affineDegree P * R ^ d := by
    intro i hi
    have hiP := hproper i hi
    have hcoverNat := card_filter_cut_le_sum_retained P s (cuts i) S hS
    have hcover : ((cutPoints S (cuts i)).card : ℚ) ≤
        ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
          ((componentPoints S Q).card : ℚ) := by
      exact_mod_cast hcoverNat
    calc
      ((cutPoints S (cuts i)).card : ℚ) ≤
          ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
            ((componentPoints S Q).card : ℚ) := hcover
      _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
            affineDegree Q * R ^ d := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact hchild i hiP Q hQ
      _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
            affineDegree Q) * R ^ d := by rw [Finset.sum_mul]
      _ ≤ ((b : ℚ) * affineDegree P) * R ^ d := by
        exact mul_le_mul_of_nonneg_right
          (sum_retained_affineDegree_le hP hiP (hdeg i)) (pow_nonneg hR d)
      _ = (b : ℚ) * affineDegree P * R ^ d := rfl
  calc
    ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
        ∑ _i ∈ good, ((b : ℚ) * affineDegree P * R ^ d) :=
      Finset.sum_le_sum hone
    _ = (good.card : ℚ) * ((b : ℚ) * affineDegree P * R ^ d) := by simp
    _ ≤ (n : ℚ) * ((b : ℚ) * affineDegree P * R ^ d) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show good.card ≤ n by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp))
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (affineDegree_nonneg P))
          (pow_nonneg hR d)
    _ = (n : ℚ) * (b : ℚ) * affineDegree P * R ^ d := by ring


/-- Incidence bound with an explicit value of the parent Hilbert-polynomial degree. -/
private theorem affineAgreementIncidence_bound_aux
    {n A k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (_hk : 0 < k) (hkA : k ≤ A) (_hAn : A ≤ n)
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
      (((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^ d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      cases d with
      | zero =>
          have hterminal := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hcardNat : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1) hterminal.1
          have hcardRat : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hcardNat
          simpa only [pow_zero, mul_one] using hcardRat.trans hterminal.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter (fun i ↦ i ∉ Bad)
          let R : ℚ := ((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hBad : Bad.card < k := card_cuts_mem_prime_lt hP hs cuts hdpos hunique
          have hlowerNat : S.card * (A - k + 1) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            apply finiteAgreementIncidence_lower S Bad
              (fun x i ↦ aeval x (cuts i) = 0) hkA hBad
            intro x hx
            change A ≤ (agreementIndices cuts x).card
            exact hA x hx
          have hlower : (S.card : ℚ) * (A - k + 1 : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q * R ^ e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            let _ : Q.IsPrime := hQdata.1.isPrime
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
            · intro T hT x y hxP hxs hyP hys hzero
              apply hunique T hT x y
              · exact zeroLocus_anti_mono hQP hxP
              · exact hxs
              · exact zeroLocus_anti_mono hQP hyP
              · exact hys
              · exact hzero
            · exact hQdegree
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              (n : ℚ) * (b : ℚ) * affineDegree P * R ^ e := by
            exact sum_card_cutPoints_le_of_child_bounds hP s cuts S hS hdeg hchild
          have hcpos : (0 : ℚ) < (A - k + 1 : ℕ) := by positivity
          apply (le_of_mul_le_mul_right ?_ hcpos)
          calc
            (S.card : ℚ) * (A - k + 1 : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ (n : ℚ) * (b : ℚ) * affineDegree P * R ^ e := hupper
            _ = (affineDegree P * R ^ (e + 1)) * (A - k + 1 : ℕ) := by
              dsimp only [R]
              rw [pow_succ]
              push_cast
              field_simp

/-- A finite family of bounded-degree equations with `k`-cut uniqueness on an affine principal
open has at most the stated number of points agreeing with at least `A` equations. -/
theorem affineAgreementIncidence_bound
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hb : 0 < b) (_hk : 0 < k) (hkA : k ≤ A) (_hAn : A ≤ n)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hunique : ∀ T : Finset (Fin n), T.card = k →
      ∀ x y : σ → F,
        x ∈ zeroLocus F P → aeval x s ≠ 0 →
        y ∈ zeroLocus F P → aeval y s ≠ 0 →
        (∀ i ∈ T, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ affineDegree P *
      (((n * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^
        (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_aux hP hs cuts hdeg hb _hk hkA _hAn S hS hA hunique rfl

end AffineHilbert
