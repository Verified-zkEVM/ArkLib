/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Resultants and Sylvester matrices for Polishchuk-Spielman

This file contains auxiliary lemmas regarding resultants and Sylvester matrices
of bivariate polynomials, used in the Polishchuk-Spielman lemma [BCIKS20].

## Main results

- `ps_nat_degree_resultant_le`: Bound on the degree of the resultant.
- `ps_resultant_ne_zero_of_is_rel_prime`: The resultant of relatively prime polynomials is non-zero.
- `ps_resultant_dvd_pow_eval_x`, `ps_resultant_dvd_pow_eval_y`: Divisibility properties of the
  resultant related to common roots on lines.

## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]

-/

open Polynomial.Bivariate Polynomial Matrix
open scoped BigOperators

/-- The degree of `Q * X ^ j` is at most `n - 1` when `deg Q ≤ n - m` and `j < m ≤ n`. -/
lemma ps_nat_degree_mul_x_pow_le {F : Type} [Semiring F] [Nontrivial F]
    (Q : F[X]) {m n : ℕ} (j : Fin m)
    (hmn : m ≤ n) (hQdeg : Q.natDegree ≤ n - m) :
    (Q * X ^ (j : ℕ)).natDegree ≤ n - 1 := by
  classical
  refine le_trans (natDegree_mul_le_of_le hQdeg (natDegree_X_pow_le ↑j)) (Nat.le_pred_of_lt ?_)
  simpa [Nat.sub_add_cancel hmn] using Nat.add_lt_add_left j.isLt (n - m)

/-- The degree of `resultant(B, A, n, m)` is at most `m · degX(B) + n · degX(A)`. -/
lemma ps_nat_degree_resultant_le {F : Type} [Field F]
    (A B : F[X][Y]) (m n : ℕ) :
    (resultant B A n m).natDegree ≤
      m * (degreeX B) + n * (degreeX A) := by
  classical
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := sylvester B A n m
  have h_coeff (P : F[X][Y]) (k : ℕ) : (P.coeff k).natDegree ≤ degreeX P := by
    unfold degreeX
    by_cases hk : k ∈ P.support
    · simp [Finset.le_sup (f := fun t ↦ (P.coeff t).natDegree) hk]
    · simp [notMem_support_iff.mp hk]
  let cb : Fin (n + m) → ℕ :=
    Fin.addCases (fun _ : Fin n ↦ degreeX A) (fun _ : Fin m ↦ degreeX B)
  have h_entry (σ : Equiv.Perm (Fin (n + m))) (i : Fin (n + m)) :
      (M (σ i) i).natDegree ≤ cb i := by
    cases i using Fin.addCases with
    | left i0 =>
      simp only [cb, Fin.addCases_left]
      have hM : M (σ (.castAdd m i0)) (.castAdd m i0) =
          if ((σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
          then A.coeff ((σ (.castAdd m i0) : ℕ) - i0) else 0 := by
        simp [M, sylvester, of_apply, Fin.addCases_left]
      by_cases h : (σ (.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)
      · simp only [hM, h, ↓reduceIte, ge_iff_le]; exact h_coeff A _
      · simp [hM, h]
    | right i0 =>
      simp only [cb, Fin.addCases_right]
      have hM : M (σ (.natAdd n i0)) (.natAdd n i0) =
          if ((σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
          then B.coeff ((σ (.natAdd n i0) : ℕ) - i0) else 0 := by
        simp [M, sylvester, of_apply, Fin.addCases_right]
      by_cases h : (σ (.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)
      · simp only [hM, h, ↓reduceIte, ge_iff_le]; exact h_coeff B _
      · simp [hM, h]
  have h_term (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree ≤
        m * degreeX B + n * degreeX A := by
    refine le_trans (natDegree_smul_le _ _) ?_
    have hprod : (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
        ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
      simpa using natDegree_prod_le _ (fun i ↦ M (σ i) i)
    refine le_trans (le_trans hprod (Finset.sum_le_sum fun i _ ↦ h_entry σ i)) ?_
    simp [cb, Fin.sum_univ_add, Nat.add_comm]
  have hdet : M.det.natDegree ≤ m * degreeX B + n * degreeX A := by
    rw [det_apply]
    exact natDegree_sum_le_of_forall_le _ _ (fun σ _ ↦ h_term σ)
  simpa [resultant, M, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hdet

/-- The resultant commutes with ring homomorphisms. -/
lemma ps_resultant_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n : ℕ) :
    f (resultant p q m n) = resultant (p.map f) (q.map f) m n := by
  classical
  simp only [resultant, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1; ext i j
  refine j.addCases (fun j₁ ↦ ?_) (fun j₁ ↦ ?_)
  · by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + n) <;>
      simp [sylvester, of_apply, coeff_map, h]
  · by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + m) <;>
      simp [sylvester, of_apply, coeff_map, h]

/-- The resultant evaluated at `x` equals the resultant of the evaluated polynomials. -/
lemma ps_resultant_eval_x {F : Type} [Field F]
    (x : F) (A B : F[X][Y]) (m n : ℕ) :
    (evalRingHom x) (resultant B A n m) =
      resultant (B.map (evalRingHom x)) (A.map (evalRingHom x)) n m := by
  simp only [coe_evalRingHom, resultant_map_map]

/-- The Sylvester matrix commutes with ring homomorphisms. -/
lemma ps_sylvester_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R[X]) (m n : ℕ) :
    (sylvester B A n m).map f = sylvester (B.map f) (A.map f) n m := by
  ext i j
  cases j using Fin.addCases with
  | left j =>
    by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + m) <;>
      simp [sylvester, of_apply, coeff_map, h]
  | right j =>
    by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + n) <;>
      simp [sylvester, of_apply, coeff_map, h]

/-- The Sylvester matrix–vector product gives coefficients of `A * P + B * Q`. -/
lemma ps_sylvester_mul_vec_eq_coeff_add {R : Type} [CommRing R]
    (A B : R[X]) (m n : ℕ)
    (hm : A.natDegree ≤ m) (hn : B.natDegree ≤ n)
    (v : Fin (n + m) → R) :
    (sylvester B A n m).mulVec v =
      fun i : Fin (n + m) ↦
        (A * (∑ j : Fin n, monomial (j : ℕ) (v (Fin.castAdd m j))) +
          B * (∑ j : Fin m, monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ) := by
  classical
  ext i
  simp [sylvester, mulVec, dotProduct, Fin.sum_univ_add, of_apply, Set.mem_Icc]
  simp [ps_coeff_mul_sum_monomial A m n hm (fun j ↦ v (Fin.castAdd m j)) (i : ℕ),
    ps_coeff_mul_sum_monomial B n m hn (fun j ↦ v (Fin.natAdd n j)) (i : ℕ), add_comm]

/-- If `B(x, Y) = Q · A(x, Y)`, then `(X - x)^(natDegreeY A)` divides `resultant(B, A)`. -/
lemma ps_resultant_dvd_pow_eval_x {F : Type} [Field F]
    (A B : F[X][Y]) (x : F) (Q : F[X]) (n : ℕ)
    (hmn : natDegreeY A ≤ n) (hn : natDegreeY B ≤ n)
    (hQdeg : Q.natDegree ≤ n - natDegreeY A)
    (hQ : evalX x B = Q * evalX x A) :
    (X - C x) ^ (natDegreeY A) ∣ resultant B A n (natDegreeY A) := by
  classical
  set m := natDegreeY A with hm
  let p : F[X] := X - C x
  let M0 : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := sylvester B A n m
  let U : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := fun i j ↦
    j.addCases
      (fun jn ↦ if i = .castAdd m jn then 1 else 0)
      (fun jm ↦ i.addCases
        (fun in_ ↦ -C ((Q * X ^ (jm : ℕ)).coeff in_))
        (fun im_ ↦ if im_ = jm then 1 else 0))
  let M1 := M0 * U
  have h_u_det : U.det = 1 := by
    have h_u_tri : U.BlockTriangular (fun x : Fin (n + m) ↦ x) := by
      intro i j hij
      induction j using Fin.addCases with
      | left jn => simp [U, ne_of_gt hij]
      | right jm =>
        induction i using Fin.addCases with
        | left in_ =>
          exact absurd hij (not_lt_of_ge (Fin.lt_def.2 (by simp; omega) |>.le))
        | right im_ =>
          simp [U, (show im_ ≠ jm from fun hEq ↦ ne_of_gt hij (by simp [hEq]))]
    rw [det_of_upperTriangular h_u_tri]; simp [Fin.prod_univ_add, U]
  have hdet1 : M1.det = M0.det := by simp [M1, det_mul, h_u_det, M0]
  let ev : F[X] →+* F := evalRingHom x
  have hdiv_entry (i : Fin (n + m)) (j' : Fin m) : p ∣ M1 i (.natAdd n j') := by
    let col : Fin (n + m) := .natAdd n j'
    let v_col : Fin (n + m) → F := fun k ↦ ev (U k col)
    suffices hx0 : ev (M1 i col) = 0 by
      exact dvd_iff_isRoot.2 (by simpa [IsRoot] using hx0)
    have hM0map : M0.map (⇑ev) = sylvester (B.map ev) (A.map ev) n m := by
      simpa [M0] using ps_sylvester_map ev A B m n
    have hmA : (A.map ev).natDegree ≤ m :=
      le_trans natDegree_map_le (by simp [hm, natDegreeY])
    have hnB : (B.map ev).natDegree ≤ n :=
      le_trans natDegree_map_le (by simpa [natDegreeY] using hn)
    set q : F[X] := Q * X ^ (j' : ℕ) with hq_def
    have hqdeg_lt : q.natDegree < n :=
      lt_of_le_of_lt (ps_nat_degree_mul_x_pow_le Q j' hmn hQdeg)
        (Nat.sub_lt (lt_of_lt_of_le (Fin.size_positive j') hmn) Nat.one_pos)
    have hBmap : B.map ev = Q * A.map ev := by simpa [ps_eval_x_eq_map, ev] using hQ
    have hsum_left : (∑ j : Fin n, monomial (j : ℕ) (v_col (.castAdd m j))) = -q := by
      have hv : (fun j : Fin n ↦ v_col (.castAdd m j)) = fun j : Fin n ↦ -(toFn n q j) := by
        funext j; simp [v_col, col, U, ev, q, toFn]
      rw [show (∑ j : Fin n, monomial (j : ℕ) (v_col (.castAdd m j))) =
          ofFn n (fun j ↦ v_col (.castAdd m j)) from by
        simpa using (ofFn_eq_sum_monomial <| fun j : Fin n ↦ v_col (.castAdd m j)).symm,
        hv, show ofFn n (fun j : Fin n ↦ -(toFn n q j)) = -ofFn n (toFn n q) from by
          simp [ofFn_eq_sum_monomial], ofFn_comp_toFn_eq_id_of_natDegree_lt hqdeg_lt]
    have hsum_right :
        (∑ j : Fin m, monomial (j : ℕ) (v_col (.natAdd n j))) = X ^ (j' : ℕ) := by
      classical
      have hv (j : Fin m) : v_col (.natAdd n j) = if j = j' then (1 : F) else 0 := by
        by_cases h : j = j' <;> simp [v_col, col, U, ev, h]
      simp_rw [hv]
      have hfun (j : Fin m) : monomial (j : ℕ) (if j = j' then (1 : F) else 0) =
          if j = j' then monomial (j : ℕ) (1 : F) else 0 := by
        by_cases hj : j = j' <;> simp [hj]
      simp_rw [hfun]; simp [monomial_one_right_eq_X_pow]
    have hSylv : ev (M1 i col) = (sylvester (B.map ev) (A.map ev) n m).mulVec v_col i := by
      have := RingHom.map_matrix_mul (M := M0) (N := U) (i := i) (j := col) (f := ev)
      simpa [M1, mul_apply, mulVec, dotProduct, v_col, hM0map] using this
    rw [hSylv, congrArg (fun f : (Fin (n + m) → F) ↦ f i)
      (ps_sylvester_mul_vec_eq_coeff_add (A.map ev) (B.map ev) m n hmA hnB v_col)]
    simp [hsum_left, hsum_right, hBmap, q, mul_assoc, mul_left_comm, mul_comm]
  classical
  let q_mat : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := fun i j ↦
    j.addCases (fun jn ↦ M1 i (.castAdd m jn)) (fun jm ↦ Classical.choose (hdiv_entry i jm))
  have hQs (i : Fin (n + m)) (j' : Fin m) : M1 i (.natAdd n j') = p * q_mat i (.natAdd n j') := by
    simpa [q_mat, Fin.addCases_right] using Classical.choose_spec (hdiv_entry i j')
  let v : Fin (n + m) → F[X] := fun j ↦ j.addCases (fun _ ↦ 1) (fun _ ↦ p)
  have hM1_scale : M1 = fun i j ↦ v j * q_mat i j := by
    apply Matrix.ext; intro i j
    induction j using Fin.addCases with
    | left jn => simp [v, q_mat, Fin.addCases_left]
    | right jm => simpa [v, q_mat, Fin.addCases_right, mul_assoc] using hQs i jm
  have hdivM1 : p ^ m ∣ M1.det :=
    ⟨q_mat.det, by
      rw [show M1.det = (∏ j, v j) * q_mat.det from by
        simpa [hM1_scale] using det_mul_row v q_mat]
      simp [Fin.prod_univ_add, v]⟩
  simpa [p, m, hm, natDegreeY, resultant, M0] using (hdet1 ▸ hdivM1)

/-- If `B(X, y) = Q · A(X, y)`, then `(X - y)^(degreeX A)` divides the swapped resultant. -/
lemma ps_resultant_dvd_pow_eval_y {F : Type} [Field F]
    (A B : F[X][Y]) (y : F) (Q : F[X]) (n : ℕ)
    (hmn : degreeX A ≤ n) (hn : degreeX B ≤ n)
    (hQdeg : Q.natDegree ≤ n - degreeX A)
    (hQ : evalY y B = Q * evalY y A) :
    (X - C y) ^ (degreeX A) ∣
      resultant (swap B) (swap A) n (degreeX A) := by
  classical
  simpa [-swap_apply, ps_nat_degree_y_swap] using
    ps_resultant_dvd_pow_eval_x (swap A) (swap B) y Q n
      (by simpa [-swap_apply, ps_nat_degree_y_swap] using hmn)
      (by simpa [-swap_apply, ps_nat_degree_y_swap] using hn)
      (by simpa [-swap_apply, ps_nat_degree_y_swap] using hQdeg)
      (by simpa [-swap_apply, ps_eval_y_eq_eval_x_swap] using hQ)

/-- The resultant of relatively prime polynomials is nonzero. -/
lemma ps_resultant_ne_zero_of_is_rel_prime {F : Type} [Field F]
    (A B : F[X][Y]) (n : ℕ)
    (hn : natDegreeY B ≤ n) (hA0 : A ≠ 0) (hrel : IsRelPrime A B) :
    resultant B A n (natDegreeY A) ≠ 0 := by
  classical
  set m := natDegreeY A with hm
  intro hres
  rcases (exists_mulVec_eq_zero_iff (M := sylvester B A n m)).2
    (by simpa [resultant] using hres) with ⟨v, hv0, hv⟩
  let P : F[X][Y] := ∑ j : Fin n, monomial (j : ℕ) (v (.castAdd m j))
  let Q : F[X][Y] := ∑ j : Fin m, monomial (j : ℕ) (v (.natAdd n j))
  have hP_ofFn : P = ofFn n (fun j : Fin n ↦ v (.castAdd m j)) := by
    simpa [P] using (ofFn_eq_sum_monomial (fun j ↦ v (.castAdd m j))).symm
  have hQ_ofFn : Q = ofFn m (fun j : Fin m ↦ v (.natAdd n j)) := by
    simpa [Q] using (ofFn_eq_sum_monomial (fun j ↦ v (.natAdd n j))).symm
  have hvcoeff (i : Fin (n + m)) : (A * P + B * Q).coeff (i : ℕ) = 0 := by
    have hsyl := congrFun
      (ps_sylvester_mul_vec_eq_coeff_add A B m n
        (by simp [hm, natDegreeY]) (by simpa [natDegreeY] using hn) v) i
    simpa [P, Q] using (show
      (A * (∑ j : Fin n, monomial (j : ℕ) (v (.castAdd m j))) +
       B * (∑ j : Fin m, monomial (j : ℕ) (v (.natAdd n j)))).coeff (i : ℕ) = 0 from by
        rw [← hsyl]; exact congrFun hv i)
  have hnmpos : 0 < n + m := by
    by_contra h; exact hv0 (funext fun i ↦ absurd i.isLt (by omega))
  have hA_nd : A.natDegree = m := by simpa [natDegreeY] using hm.symm
  have hcomb : A * P + B * Q = 0 := by
    apply Polynomial.ext; intro k
    by_cases hk : k < n + m
    · simpa using hvcoeff ⟨k, hk⟩
    · have hdegAP : (A * P).natDegree < n + m := by
        by_cases hn0 : n = 0
        · subst hn0; simpa [P] using (show 0 < m by omega)
        · exact lt_of_le_of_lt natDegree_mul_le (by
            rw [hA_nd]; have : P.natDegree < n := by
              simpa [hP_ofFn] using
                ofFn_natDegree_lt (show 1 ≤ n by omega) (fun j ↦ v (.castAdd m j))
            omega)
      have hdegBQ : (B * Q).natDegree < n + m := by
        by_cases hm0 : m = 0
        · rw [show Q = 0 from by simp [hm0, hQ_ofFn, ofFn]]; simp; omega
        · have hndeg : B.natDegree ≤ n := by simpa [natDegreeY] using hn
          have hQnat : Q.natDegree < m := by
            simpa [hQ_ofFn] using
              ofFn_natDegree_lt (show 1 ≤ m by omega) (fun j ↦ v (.natAdd n j))
          exact lt_of_le_of_lt natDegree_mul_le (by omega)
      exact coeff_eq_zero_of_natDegree_lt (by
        have := lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hdegAP hdegBQ); omega)
  have hA_dvd_BQ : A ∣ B * Q :=
    ⟨-P, (neg_eq_of_add_eq_zero_left (by rwa [add_comm] at hcomb)).symm.trans (mul_neg A P).symm⟩
  have hA_dvd_Q : A ∣ Q := hrel.dvd_of_dvd_mul_left hA_dvd_BQ
  have hQ0 : Q = 0 := by
    by_cases hm0 : m = 0
    · simp_all only [m, P, Q]
      ext n_1 n_2 : 2
      simp_all only [zero_le, ofFn_coeff_eq_zero_of_ge, coeff_zero]
    · rcases hA_dvd_Q with ⟨R, hR⟩
      by_contra hQ_ne
      have hR0 : R ≠ 0 := by rintro rfl; exact hQ_ne (by simpa using hR)
      have : A.natDegree + R.natDegree < m := by
        rw [← natDegree_mul hA0 hR0, ← hR]
        simpa [hQ_ofFn] using
          ofFn_natDegree_lt (show 1 ≤ m by omega) (fun j ↦ v (.natAdd n j))
      omega
  have hP0 : P = 0 := (mul_eq_zero.mp (by simpa [hQ0] using hcomb)).resolve_left hA0
  exact hv0 (funext ((Fin.forall_fin_add <| fun i ↦ v i = 0).2
    ⟨fun j ↦ by simpa [hP_ofFn] using congrArg (Polynomial.coeff · (j : ℕ)) hP0,
     fun j ↦ by simpa [hQ_ofFn] using congrArg (Polynomial.coeff · (j : ℕ)) hQ0⟩))
