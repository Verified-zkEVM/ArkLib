/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Function
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Polynomial.Basic

/-!
# Principal cuts and eventual Hilbert polynomial bounds

Eventual comparison on natural inputs compares polynomial degrees and leading
coefficients. Applied to the actual prime-cut filtration inequality, a backward
finite difference bounds the cut polynomial degree and its top possible coefficient.
-/

@[expose] public section

noncomputable section

open Filter MvPolynomial Polynomial
open scoped Topology

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- The finite difference `P(X) - P(X-b)`. -/
def backwardDifference (b : ℕ) (P : ℚ[X]) : ℚ[X] :=
  P - Polynomial.taylor (-(b : ℚ)) P

private theorem leadingCoeff_nonneg_of_eventually_eval_nat_nonneg
    {P : ℚ[X]} (h : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ)) :
    0 ≤ P.leadingCoeff := by
  by_contra hlc
  have hlc' : P.leadingCoeff < 0 := lt_of_not_ge hlc
  have hP : P ≠ 0 := by
    intro hP
    subst P
    simp at hlc'
  by_cases hd : P.natDegree = 0
  · have heval : ∀ N : ℕ, P.eval (N : ℚ) = P.leadingCoeff := by
      intro N
      have hconst := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hd)
      rw [hconst]
      simp
    obtain ⟨N, hN⟩ := h.exists
    exact (not_lt_of_ge hN) (heval N ▸ hlc')
  · have hdeg : 0 < P.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun x : ℚ ↦ P.eval x) atTop atBot :=
      P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc'.le
    have htN : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) < 0 :=
      ((ht.comp tendsto_natCast_atTop_atTop).eventually_lt_atBot 0)
    obtain ⟨N, hN, hN'⟩ := (h.and htN).exists
    exact (not_lt_of_ge hN) hN'

private theorem eventually_eval_nat_nonneg_and_ne_zero_leadingCoeff_pos
    {P : ℚ[X]} (hP : P ≠ 0)
    (h : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ)) :
    0 < P.leadingCoeff := by
  exact (leadingCoeff_nonneg_of_eventually_eval_nat_nonneg h).lt_of_ne'
    (Polynomial.leadingCoeff_ne_zero.mpr hP)

/-- Eventual comparison on natural inputs compares degrees, and compares leading coefficients
when the degrees agree, provided the left polynomial is eventually nonnegative. -/
theorem natDegree_le_of_eventually_eval_nat_le
    {Q R : ℚ[X]} (hQ : Q ≠ 0)
    (hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ))
    (hle : ∀ᶠ N : ℕ in atTop, Q.eval (N : ℚ) ≤ R.eval (N : ℚ)) :
    Q.natDegree ≤ R.natDegree ∧
      (Q.natDegree = R.natDegree → Q.leadingCoeff ≤ R.leadingCoeff) := by
  have hQlc : 0 < Q.leadingCoeff :=
    eventually_eval_nat_nonneg_and_ne_zero_leadingCoeff_pos hQ hQnonneg
  have hdiff : ∀ᶠ N : ℕ in atTop, 0 ≤ (R - Q).eval (N : ℚ) := by
    filter_upwards [hle] with N hN
    simpa using sub_nonneg.mpr hN
  have hlcdiff : 0 ≤ (R - Q).leadingCoeff :=
    leadingCoeff_nonneg_of_eventually_eval_nat_nonneg hdiff
  constructor
  · by_contra hdeg
    have hdeg' : R.degree < Q.degree :=
      Polynomial.degree_lt_degree (Nat.lt_of_not_ge hdeg)
    rw [Polynomial.leadingCoeff_sub_of_degree_lt' hdeg'] at hlcdiff
    linarith
  · intro hdeg
    by_cases hR : R = 0
    · subst R
      simp at hdeg
      simpa [hdeg] using hlcdiff
    · have hdegree : R.degree = Q.degree := by
        rw [Polynomial.degree_eq_natDegree hR, Polynomial.degree_eq_natDegree hQ, hdeg]
      by_cases hlc : R.leadingCoeff = Q.leadingCoeff
      · exact hlc.symm.le
      · rw [Polynomial.leadingCoeff_sub_of_degree_eq hdegree hlc] at hlcdiff
        linarith

theorem natDegree_backwardDifference_le (b : ℕ) (P : ℚ[X]) :
    (backwardDifference b P).natDegree ≤ P.natDegree - 1 := by
  by_cases hd : P.natDegree = 0
  · have ht : (Polynomial.taylor (-(b : ℚ)) P).natDegree = 0 := by simp [hd]
    have := Polynomial.natDegree_sub_le P (Polynomial.taylor (-(b : ℚ)) P)
    simpa [backwardDifference, hd, ht] using this
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    have hdN : P.natDegree ≤ N := by omega
    by_cases heq : N = P.natDegree
    · subst N
      simp [backwardDifference]
    · have hlt : P.natDegree < N := lt_of_le_of_ne hdN (Ne.symm heq)
      rw [backwardDifference, Polynomial.coeff_sub,
        Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      have htdeg : (Polynomial.taylor (-(b : ℚ)) P).natDegree = P.natDegree := by simp
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (htdeg.symm ▸ hlt), sub_zero]

theorem coeff_backwardDifference_pred_natDegree (b : ℕ) {P : ℚ[X]}
    (hd : 0 < P.natDegree) :
    (backwardDifference b P).coeff (P.natDegree - 1) =
      (b : ℚ) * P.natDegree * P.leadingCoeff := by
  let d := P.natDegree
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd.ne')
  have hhasse : (Polynomial.hasseDeriv (d - 1) P).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_hasseDeriv_le P (d - 1)).trans_eq (by omega)
  have hlinear := Polynomial.eq_X_add_C_of_natDegree_le_one hhasse
  have hchoose : d.choose (d - 1) = d := by
    have hchoose' : P.natDegree.choose (P.natDegree - 1) = P.natDegree := by
      obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
      rw [he]
      exact Nat.choose_succ_self_right e
    simpa only [d] using hchoose'
  have hcoeff1 : (Polynomial.hasseDeriv (d - 1) P).coeff 1 =
      (d : ℚ) * P.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff, show 1 + (d - 1) = d by omega,
      hchoose, Polynomial.coeff_natDegree]
  have hcoeff0 : (Polynomial.hasseDeriv (d - 1) P).coeff 0 = P.coeff (d - 1) := by
    rw [Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self]
    norm_num
  rw [backwardDifference, Polynomial.coeff_sub, Polynomial.taylor_coeff]
  rw [hlinear, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_C, hcoeff1, hcoeff0]
  dsimp only [d]
  ring

theorem backwardDifference_natDegree_eq_and_leadingCoeff
    {b : ℕ} (hb : 0 < b) {P : ℚ[X]} (hP : P ≠ 0) (hd : 0 < P.natDegree) :
    (backwardDifference b P).natDegree = P.natDegree - 1 ∧
      (backwardDifference b P).leadingCoeff =
        (b : ℚ) * P.natDegree * P.leadingCoeff := by
  have hcoeff := coeff_backwardDifference_pred_natDegree b hd
  have hcoeffne : (backwardDifference b P).coeff (P.natDegree - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hb.ne')
      (Nat.cast_ne_zero.mpr hd.ne')) (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hdegree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_backwardDifference_le b P) hcoeffne
  exact ⟨hdegree, by rw [Polynomial.leadingCoeff, hdegree, hcoeff]⟩

/-- Constants inject into every degree level of a proper affine quotient. -/
theorem one_le_hilbertFunction (I : Ideal (MvPolynomial σ F)) (hI : I ≠ ⊤) (N : ℕ) :
    1 ≤ hilbertFunction I N := by
  let q : quotientDegreeLE I N :=
    ⟨Ideal.Quotient.mk I 1, ⟨1, (mem_restrictTotalDegree σ N 1).mpr (by simp), rfl⟩⟩
  have hq : q ≠ 0 := by
    intro hq
    have : (1 : MvPolynomial σ F) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp
      (congrArg Subtype.val hq)
    exact hI ((Ideal.eq_top_iff_one I).mpr this)
  let _ : Nontrivial (quotientDegreeLE I N) := ⟨⟨q, 0, hq⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := F)))

/-- A nonzero eventual Hilbert polynomial of a principal cut has degree at most one less than
the ambient Hilbert polynomial. Its coefficient in that top possible degree is at most the
finite-difference coefficient `b * deg(P) * leadingCoeff(P)`. -/
theorem principalCut_eventualPolynomial_degree_and_coeff
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {f : MvPolynomial σ F} (hfI : f ∉ I) {b : ℕ} (hfdeg : f.totalDegree ≤ b)
    {P Q : ℚ[X]}
    (hPev : ∀ᶠ N : ℕ in atTop,
      P.eval (N : ℚ) = (hilbertFunction I N : ℚ))
    (hQev : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) = (hilbertFunction (I ⊔ Ideal.span {f}) N : ℚ))
    (hQ : Q ≠ 0) :
    Q.natDegree ≤ P.natDegree - 1 ∧
      Q.coeff (P.natDegree - 1) ≤
        (b : ℚ) * P.natDegree * P.leadingCoeff := by
  have hPpos : ∀ᶠ N : ℕ in atTop, 0 < P.eval (N : ℚ) := by
    filter_upwards [hPev] with N hN
    rw [hN]
    exact_mod_cast one_le_hilbertFunction I hI.ne_top N
  have hP : P ≠ 0 := by
    intro hzero
    obtain ⟨N, hN⟩ := hPpos.exists
    simp [hzero] at hN
  have hPlc : 0 < P.leadingCoeff :=
    eventually_eval_nat_nonneg_and_ne_zero_leadingCoeff_pos hP (hPpos.mono fun _ ↦ le_of_lt)
  have hQnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ Q.eval (N : ℚ) := by
    filter_upwards [hQev] with N hN
    rw [hN]
    positivity
  have hQlc : 0 < Q.leadingCoeff :=
    eventually_eval_nat_nonneg_and_ne_zero_leadingCoeff_pos hQ hQnonneg
  have hQle : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) ≤ (backwardDifference b P).eval (N : ℚ) := by
    have hPsub : ∀ᶠ N : ℕ in atTop,
        P.eval ((N - b : ℕ) : ℚ) = (hilbertFunction I (N - b) : ℚ) := by
      rw [eventually_atTop] at hPev ⊢
      obtain ⟨K, hK⟩ := hPev
      exact ⟨K + b, fun N hN ↦ hK (N - b) (by omega)⟩
    filter_upwards [hPev, hPsub, hQev, eventually_ge_atTop b] with N hPN hPNsub hQN hbN
    have hcut := principalCut_hilbertFunction_add_le hI hfI hfdeg hbN
    rw [backwardDifference, Polynomial.eval_sub, Polynomial.taylor_apply,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [show (N : ℚ) + -(b : ℚ) = (N - b : ℕ) by
      rw [Nat.cast_sub hbN]
      ring]
    rw [hPN, hPNsub, hQN]
    apply (le_sub_iff_add_le).2
    exact_mod_cast hcut
  obtain ⟨hdegQR, hlcQR⟩ :=
    natDegree_le_of_eventually_eval_nat_le hQ hQnonneg hQle
  have hb : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
    subst b
    have hR0 : backwardDifference 0 P = 0 := by simp [backwardDifference]
    have hQdeg0 : Q.natDegree = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hR0] using hdegQR)
    have hdeg0 : Q.natDegree = (backwardDifference 0 P).natDegree := by
      simpa only [hR0, Polynomial.natDegree_zero] using hQdeg0
    have := hlcQR hdeg0
    rw [hR0, Polynomial.leadingCoeff_zero] at this
    linarith
  have hd : 0 < P.natDegree := by
    by_contra hd
    have hd0 : P.natDegree = 0 := Nat.eq_zero_of_not_pos hd
    have hR0 : backwardDifference b P = 0 := by
      have hconst := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hd0)
      rw [backwardDifference, hconst]
      simp
    have hQdeg0 : Q.natDegree = 0 :=
      Nat.eq_zero_of_le_zero (by simpa [hR0] using hdegQR)
    have hdeg0 : Q.natDegree = (backwardDifference b P).natDegree := by
      simpa only [hR0, Polynomial.natDegree_zero] using hQdeg0
    have := hlcQR hdeg0
    rw [hR0, Polynomial.leadingCoeff_zero] at this
    linarith
  obtain ⟨hRdeg, hRlc⟩ := backwardDifference_natDegree_eq_and_leadingCoeff hb hP hd
  constructor
  · simpa [hRdeg] using hdegQR
  · by_cases heq : Q.natDegree = P.natDegree - 1
    · rw [← heq, Polynomial.coeff_natDegree]
      rw [← hRlc]
      exact hlcQR (heq.trans hRdeg.symm)
    · have hlt : Q.natDegree < P.natDegree - 1 := lt_of_le_of_ne
        (hRdeg ▸ hdegQR) heq
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      positivity

/-- The same consequence with the zero principal-cut polynomial made explicit. -/
theorem principalCut_eventualPolynomial_zero_or_degree_and_coeff
    {I : Ideal (MvPolynomial σ F)} (hI : I.IsPrime)
    {f : MvPolynomial σ F} (hfI : f ∉ I) {b : ℕ} (hfdeg : f.totalDegree ≤ b)
    {P Q : ℚ[X]}
    (hPev : ∀ᶠ N : ℕ in atTop,
      P.eval (N : ℚ) = (hilbertFunction I N : ℚ))
    (hQev : ∀ᶠ N : ℕ in atTop,
      Q.eval (N : ℚ) = (hilbertFunction (I ⊔ Ideal.span {f}) N : ℚ)) :
    Q = 0 ∨
      Q.natDegree ≤ P.natDegree - 1 ∧
        Q.coeff (P.natDegree - 1) ≤
          (b : ℚ) * P.natDegree * P.leadingCoeff := by
  by_cases hQ : Q = 0
  · exact Or.inl hQ
  · exact Or.inr (principalCut_eventualPolynomial_degree_and_coeff
      hI hfI hfdeg hPev hQev hQ)

end AffineHilbert
