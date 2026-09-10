/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Polynomial
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PrimeFamily

/-!
# Coefficient comparison for shifted Hilbert polynomials

Eventual inequalities between degree-bounded rational polynomials compare the
coefficient at the common degree bound, including when either polynomial is zero.
-/

@[expose] public section

noncomputable section

open Filter Polynomial
open scoped Topology

namespace AffineHilbert

/-- An eventually nonnegative rational polynomial has nonnegative coefficient
at any upper bound for its degree. -/
theorem coeff_nonneg_of_natDegree_le_of_eventually_eval_nat_nonneg
    {P : ℚ[X]} {d : ℕ} (hdeg : P.natDegree ≤ d)
    (h : ∀ᶠ N : ℕ in atTop, 0 ≤ P.eval (N : ℚ)) :
    0 ≤ P.coeff d := by
  by_cases hP : P = 0
  · simp [hP]
  by_cases heq : P.natDegree = d
  · rw [← heq, Polynomial.coeff_natDegree]
    by_contra hlc
    have hlc' : P.leadingCoeff < 0 := lt_of_not_ge hlc
    by_cases hd0 : P.natDegree = 0
    · have hconst := Polynomial.eq_C_of_natDegree_le_zero (le_of_eq hd0)
      obtain ⟨N, hN⟩ := h.exists
      rw [hconst, Polynomial.eval_C] at hN
      rw [hconst] at hlc'
      simp only [Polynomial.leadingCoeff_C] at hlc'
      exact (not_lt_of_ge hN) hlc'
    · have hdegree : 0 < P.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd0)
      have ht : Tendsto (fun x : ℚ ↦ P.eval x) atTop atBot :=
        P.tendsto_atBot_of_leadingCoeff_nonpos hdegree hlc'.le
      have htN : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) < 0 :=
        ((ht.comp tendsto_natCast_atTop_atTop).eventually_lt_atBot 0)
      obtain ⟨N, hN, hN'⟩ := (h.and htN).exists
      exact (not_lt_of_ge hN) hN'
  · have hlt : P.natDegree < d := hdeg.lt_of_ne heq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

/-- Eventual comparison of degree-bounded rational polynomials compares their
coefficients at the shared degree bound, without nonzero hypotheses. -/
theorem coeff_le_of_natDegree_le_of_eventually_eval_nat_le
    {P Q : ℚ[X]} {d : ℕ} (hPdeg : P.natDegree ≤ d) (hQdeg : Q.natDegree ≤ d)
    (h : ∀ᶠ N : ℕ in atTop, P.eval (N : ℚ) ≤ Q.eval (N : ℚ)) :
    P.coeff d ≤ Q.coeff d := by
  have hdeg : (Q - P).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le Q P).trans (max_le hQdeg hPdeg)
  have hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ (Q - P).eval (N : ℚ) := by
    filter_upwards [h] with N hN
    simpa using sub_nonneg.mpr hN
  have hc := coeff_nonneg_of_natDegree_le_of_eventually_eval_nat_nonneg hdeg hnonneg
  simpa only [Polynomial.coeff_sub, sub_nonneg] using hc

/-- Translating the input of a polynomial does not change its coefficient at
an upper bound for its degree. -/
theorem coeff_taylor_eq_of_natDegree_le (P : ℚ[X]) (a : ℚ) {d : ℕ}
    (hdeg : P.natDegree ≤ d) :
    (Polynomial.taylor a P).coeff d = P.coeff d := by
  by_cases heq : P.natDegree = d
  · rw [← heq, Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
  · have hlt : P.natDegree < d := hdeg.lt_of_ne heq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt]
    simpa only [Polynomial.natDegree_taylor] using hlt

variable {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]

/-- At any common degree bound, the sum of the Hilbert-polynomial
coefficients of pairwise incomparable prime components is at most the
coefficient of their intersection. Lower-dimensional components contribute
zero automatically. -/
theorem sum_hilbertPolynomial_coeff_le_iInf
    (P : ι → Ideal (MvPolynomial σ F)) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) (d : ℕ)
    (hPdeg : ∀ i, (hilbertPolynomial (P i)).natDegree ≤ d)
    (hInfDeg : (hilbertPolynomial (⨅ i, P i)).natDegree ≤ d) :
    ∑ i, (hilbertPolynomial (P i)).coeff d ≤
      (hilbertPolynomial (⨅ i, P i)).coeff d := by
  classical
  obtain ⟨s, hsOwn, hsOther, hsHF⟩ :=
    exists_separators_sum_shifted_hilbertFunction_le_iInf P hP hinc
  let B : ℕ := Finset.univ.sup (fun i ↦ (s i).totalDegree)
  choose T hT using fun i ↦ hilbertPolynomial_eventually (P i)
  obtain ⟨TInf, hTInf⟩ := hilbertPolynomial_eventually (⨅ i, P i)
  let U : ℕ := Finset.univ.sup (fun i ↦ T i + (s i).totalDegree)
  let S : ℚ[X] := ∑ i, Polynomial.taylor (-(s i).totalDegree : ℚ)
    (hilbertPolynomial (P i))
  have hSdeg : S.natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    simpa only [Polynomial.natDegree_taylor] using hPdeg i
  have hSeval : ∀ᶠ N : ℕ in atTop,
      S.eval (N : ℚ) ≤ (hilbertPolynomial (⨅ i, P i)).eval (N : ℚ) := by
    filter_upwards [eventually_ge_atTop (max B (max TInf U))] with N hN
    have hBN : B ≤ N := (Nat.le_max_left B (max TInf U)).trans hN
    have hTInfN : TInf ≤ N :=
      (Nat.le_max_left TInf U).trans ((Nat.le_max_right B (max TInf U)).trans hN)
    have hUN : U ≤ N :=
      (Nat.le_max_right TInf U).trans ((Nat.le_max_right B (max TInf U)).trans hN)
    calc
      S.eval (N : ℚ) =
          ∑ i, (hilbertPolynomial (P i)).eval ((N - (s i).totalDegree : ℕ) : ℚ) := by
        simp only [S, Polynomial.eval_finsetSum, Polynomial.taylor_apply,
          Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        have hdegN : (s i).totalDegree ≤ N :=
          (Finset.le_sup (Finset.mem_univ i)).trans hBN
        rw [Nat.cast_sub hdegN]
        ring
      _ = ∑ i, (hilbertFunction (P i) (N - (s i).totalDegree) : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply hT i
        apply Nat.le_sub_of_add_le
        exact (Finset.le_sup (Finset.mem_univ i)).trans hUN
      _ ≤ (hilbertFunction (⨅ i, P i) N : ℚ) := by
        exact_mod_cast hsHF N hBN
      _ = (hilbertPolynomial (⨅ i, P i)).eval (N : ℚ) :=
        (hTInf N hTInfN).symm
  have hcoeff := coeff_le_of_natDegree_le_of_eventually_eval_nat_le
    hSdeg hInfDeg hSeval
  have hScoeff : S.coeff d = ∑ i, (hilbertPolynomial (P i)).coeff d := by
    change Polynomial.lcoeff ℚ d
      (∑ i, Polynomial.taylor (-(s i).totalDegree : ℚ) (hilbertPolynomial (P i))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact coeff_taylor_eq_of_natDegree_le _ _ (hPdeg i)
  rwa [hScoeff] at hcoeff

end AffineHilbert
