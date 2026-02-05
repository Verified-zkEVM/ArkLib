/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.PolishchukSpielman.Degrees
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

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

lemma ps_nat_degree_mul_x_pow_le {F : Type} [Semiring F] [Nontrivial F]
    (Q : F[X]) {m n : ℕ} (j : Fin m)
    (hmn : m ≤ n) (hQdeg : Q.natDegree ≤ n - m) :
    (Q * X ^ (j : ℕ)).natDegree ≤ n - 1 := by
  classical
  have hdeg : (Q * X ^ (j : ℕ)).natDegree ≤ (n - m) + (j : ℕ) := by
    refine Polynomial.natDegree_mul_le_of_le (p := Q) (q := (X : F[X]) ^ (j : ℕ)) hQdeg ?_
    exact natDegree_X_pow_le ↑j
  have hlt : (n - m) + (j : ℕ) < n := by
    have hj : (j : ℕ) < m := j.isLt
    have hlt' : (n - m) + (j : ℕ) < (n - m) + m :=
      Nat.add_lt_add_left hj (n - m)
    simpa [Nat.sub_add_cancel hmn] using hlt'
  have hle : (n - m) + (j : ℕ) ≤ n - 1 := Nat.le_pred_of_lt hlt
  exact le_trans hdeg hle

lemma ps_nat_degree_resultant_le {F : Type} [Field F]
    (A B : F[X][Y]) (m n : ℕ) :
    (Polynomial.resultant A B m n).natDegree ≤
      m * (Polynomial.Bivariate.degreeX B) + n * (Polynomial.Bivariate.degreeX A) := by
  classical
  -- Work with the Sylvester matrix whose determinant defines the resultant.
  let M : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := Polynomial.sylvester A B m n

  -- Every coefficient of `A` has `X`-degree bounded by `degreeX A`.
  have h_a_coeff : ∀ k : ℕ, (A.coeff k).natDegree ≤ Polynomial.Bivariate.degreeX A := by
    intro k
    classical
    unfold Polynomial.Bivariate.degreeX
    by_cases hk : k ∈ A.support
    · -- use the definition of `Finset.sup`
      simp [Finset.le_sup (s := A.support) (f := fun t : ℕ => (A.coeff t).natDegree) hk]
    · have hk0 : A.coeff k = 0 := by exact notMem_support_iff.mp hk
      simp [hk0]

  -- Every coefficient of `B` has `X`-degree bounded by `degreeX B`.
  have h_b_coeff : ∀ k : ℕ, (B.coeff k).natDegree ≤ Polynomial.Bivariate.degreeX B := by
    intro k
    classical
    unfold Polynomial.Bivariate.degreeX
    by_cases hk : k ∈ B.support
    · simp [Finset.le_sup (s := B.support) (f := fun t : ℕ => (B.coeff t).natDegree) hk]
    · have hk0 : B.coeff k = 0 :=  by exact notMem_support_iff.mp hk
      simp [hk0]

  -- Column-wise `X`-degree bounds for the Sylvester matrix:
  -- first `n` columns come from `A`, last `m` columns come from `B`.
  let col_bound : Fin (n + m) → ℕ :=
    Fin.addCases (fun _ : Fin n => Polynomial.Bivariate.degreeX A)
      (fun _ : Fin m => Polynomial.Bivariate.degreeX B)

  have h_entry (σ : Equiv.Perm (Fin (n + m))) (i : Fin (n + m)) :
      (M (σ i) i).natDegree ≤ col_bound i := by
    -- split according to whether the column is in the `A`-block or the `B`-block
    cases i using Fin.addCases with
    | left i0 =>
        have hM :
            M (σ (Fin.castAdd m i0)) (Fin.castAdd m i0) =
              (if ((σ (Fin.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m)) then
                  A.coeff ((σ (Fin.castAdd m i0) : ℕ) - i0)
                else 0) := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        have hB : col_bound (Fin.castAdd m i0) = Polynomial.Bivariate.degreeX A := by
          simp [col_bound, Fin.addCases_left]
        simpa [hM, hB] using
          (show (M (σ (Fin.castAdd m i0)) (Fin.castAdd m i0)).natDegree ≤
              col_bound (Fin.castAdd m i0) from by
            by_cases h : ((σ (Fin.castAdd m i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + m))
            · simp [hM, hB, h]
              exact h_a_coeff ((σ (Fin.castAdd m i0) : ℕ) - i0)
            · simp [hM, hB, h])
    | right i0 =>
        have hM :
            M (σ (Fin.natAdd n i0)) (Fin.natAdd n i0) =
              (if ((σ (Fin.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n)) then
                  B.coeff ((σ (Fin.natAdd n i0) : ℕ) - i0)
                else 0) := by
          simp [M, Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        have hB : col_bound (Fin.natAdd n i0) = Polynomial.Bivariate.degreeX B := by
          simp [col_bound, Fin.addCases_right]
        simpa [hM, hB] using
          (show (M (σ (Fin.natAdd n i0)) (Fin.natAdd n i0)).natDegree ≤
              col_bound (Fin.natAdd n i0) from by
            by_cases h : ((σ (Fin.natAdd n i0) : ℕ) ∈ Set.Icc (i0 : ℕ) ((i0 : ℕ) + n))
            · simp [hM, hB, h]
              exact h_b_coeff ((σ (Fin.natAdd n i0) : ℕ) - i0)
            · simp [hM, hB, h])

  have h_term (σ : Equiv.Perm (Fin (n + m))) :
      (Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i).natDegree ≤
        m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A := by
    refine le_trans
      (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) (∏ i : Fin (n + m), M (σ i) i)) ?_
    have hprod :
        (∏ i : Fin (n + m), M (σ i) i).natDegree ≤
          ∑ i : Fin (n + m), (M (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin (n + m))))
          (f := fun i : Fin (n + m) => M (σ i) i))
    refine le_trans hprod ?_
    have hsum :
        (∑ i : Fin (n + m), (M (σ i) i).natDegree) ≤ ∑ i : Fin (n + m), col_bound i := by
      classical
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n + m))))
          (by
            intro i hi
            exact h_entry σ i))
    refine le_trans hsum ?_
    -- Compute the sum of the column bounds.
    have hcolSum : (∑ i : Fin (n + m), col_bound i) =
        n * Polynomial.Bivariate.degreeX A + m * Polynomial.Bivariate.degreeX B := by
      -- `Fin.sum_univ_add` splits the sum over `Fin (n + m)`.
      simp [col_bound, Fin.sum_univ_add]
    -- Reorder the two summands to match the target.
    simp [hcolSum, Nat.add_comm]

  have hdet :
      (M.det).natDegree
      ≤ m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A := by
    classical
    rw [Matrix.det_apply]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := (Finset.univ : Finset (Equiv.Perm (Fin (n + m)))))
      (f := fun σ : Equiv.Perm (Fin (n + m)) =>
        Equiv.Perm.sign σ • ∏ i : Fin (n + m), M (σ i) i)
      (n := m * Polynomial.Bivariate.degreeX B + n * Polynomial.Bivariate.degreeX A)
      (by
        intro σ hσ
        simpa using h_term σ)

  -- Finish by unfolding `Polynomial.resultant`.
  simpa [Polynomial.resultant, M, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hdet


lemma ps_resultant_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (p q : R[X]) (m n : ℕ) :
    f (Polynomial.resultant p q m n) = Polynomial.resultant (p.map f) (q.map f) m n := by
  classical
  -- unfold resultant and push `f` through the determinant
  simp [Polynomial.resultant, RingHom.map_det]
  -- reduce to showing the Sylvester matrices agree entrywise after mapping
  congr 1
  ext i j
  -- split on whether the column index `j` lies in the `p`-block or the `q`-block
  refine j.addCases (fun j₁ => ?_) (fun j₁ => ?_)
  · -- `j` in the `p`-block
    by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + m)
    · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
    · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
  · -- `j` in the `q`-block
    by_cases h : ((j₁ : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j₁ : ℕ) + n)
    · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
    · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]

lemma ps_resultant_eval_x {F : Type} [Field F]
    (x : F) (A B : F[X][Y]) (m n : ℕ) :
    (Polynomial.evalRingHom x) (Polynomial.resultant A B m n) =
      Polynomial.resultant (A.map (Polynomial.evalRingHom x))
        (B.map (Polynomial.evalRingHom x)) m n := by
  simpa using
    (ps_resultant_map (f := Polynomial.evalRingHom x) (p := A) (q := B) (m := m) (n := n))


lemma ps_sylvester_map {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (A B : R[X]) (m n : ℕ) :
    (Polynomial.sylvester A B m n).map f =
      Polynomial.sylvester (A.map f) (B.map f) m n := by
  ext i j
  cases j using Fin.addCases with
  | left j =>
      by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + m)
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
  | right j =>
      by_cases h : ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + n)
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]
      · simp [Polynomial.sylvester, Matrix.of_apply, Polynomial.coeff_map, h]

lemma ps_sylvester_mul_vec_eq_coeff_add {R : Type} [CommRing R]
    (A B : R[X]) (m n : ℕ)
    (hm : A.natDegree ≤ m) (hn : B.natDegree ≤ n)
    (v : Fin (n + m) → R) :
    (Polynomial.sylvester A B m n).mulVec v =
      fun i : Fin (n + m) =>
        (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
          B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ) := by
  classical
  ext i
  -- expand the Sylvester matrix-vector product into the two block sums
  simp [Polynomial.sylvester, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.of_apply,
  Set.mem_Icc]
  -- rewrite each block sum as a coefficient of a polynomial product
  · -- first block (A)
    have hA :=
      (ps_coeff_mul_sum_monomial (A := A) (m := m) (n := n) hm
        (c := fun j : Fin n => v (Fin.castAdd m j)) (i := (i : ℕ)))
    have hB :=
      (ps_coeff_mul_sum_monomial (A := B) (m := n) (n := m) hn
        (c := fun j : Fin m => v (Fin.natAdd n j)) (i := (i : ℕ)))
    -- after rewriting, the goal becomes reflexive
    simp [hA, hB, add_comm]


lemma ps_resultant_dvd_pow_eval_x {F : Type} [Field F] [DecidableEq F]
    (A B : F[X][Y]) (x : F) (Q : F[X]) (n : ℕ)
    (hmn : Polynomial.Bivariate.natDegreeY A ≤ n)
    (hn : Polynomial.Bivariate.natDegreeY B ≤ n)
    (hQdeg : Q.natDegree ≤ n - Polynomial.Bivariate.natDegreeY A)
    (hQ : Polynomial.Bivariate.evalX x B = Q * Polynomial.Bivariate.evalX x A) :
    (X - C x) ^ (Polynomial.Bivariate.natDegreeY A) ∣
      Polynomial.resultant A B (Polynomial.Bivariate.natDegreeY A) n := by
  classical
  -- rename `m` for the Y-degree of `A`
  set m : ℕ := Polynomial.Bivariate.natDegreeY A with hm
  have hmn' : m ≤ n := by
    simpa [hm] using hmn
  have hQdeg' : Q.natDegree ≤ n - m := by
    simpa [hm] using hQdeg

  let p : F[X] := X - C x
  let M0 : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := Polynomial.sylvester A B m n

  -- Column-operation matrix: identity on the left block, and subtract a linear combination of
  -- the left block from each right-block column.
  let U : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    fun i j =>
      j.addCases
        (fun jn => if i = Fin.castAdd m jn then 1 else 0)
        (fun jm =>
          i.addCases
            (fun in_ => -C ((Q * X ^ (jm : ℕ)).coeff in_))
            (fun im_ => if im_ = jm then 1 else 0))

  let M1 : Matrix (Fin (n + m)) (Fin (n + m)) F[X] := M0 * U

  -- `U` is upper triangular with ones on the diagonal, hence has determinant `1`.
  have h_u_tri : U.BlockTriangular (fun x : Fin (n + m) => x) := by
    intro i j hij
    -- work by cases on whether indices are in the left/right block
    cases' j using Fin.addCases with jn jm
    · -- `j` in the left block
      have hne : i ≠ Fin.castAdd m jn := ne_of_gt hij
      -- unfold `U` on a left-block column
      simp [U, hne]
    · -- `j` in the right block
      cases' i using Fin.addCases with in_ im_
      · -- `i` in the left block: impossible since then `i < j`
        exfalso
        have hlt : (Fin.castAdd m in_ : Fin (n + m)) < Fin.natAdd n jm := by
          -- compare `val`
          apply Fin.lt_iff_val_lt_val.2
          have : (in_ : ℕ) < n + (jm : ℕ) :=
            lt_of_lt_of_le in_.isLt (Nat.le_add_right n (jm : ℕ))
          simpa using this
        exact (not_lt_of_ge hlt.le hij)
      · -- both in the right block
        have hne : im_ ≠ jm := by
          intro hEq
          apply ne_of_gt hij
          simp [hEq]
        simp [U, hne]

  have h_u_det : U.det = 1 := by
    classical
    have hdet := Matrix.det_of_upperTriangular (M := U) h_u_tri
    have hdiag : (∏ i : Fin (n + m), U i i) = 1 := by
      -- split the diagonal product into the first `n` and last `m` indices
      have hsplit :=
        (Fin.prod_univ_add (a := n) (b := m) (f := fun i : Fin (n + m) => U i i))
      have hleft : (∏ i : Fin n, U (Fin.castAdd m i) (Fin.castAdd m i)) = 1 := by
        simp [U]
      have hright : (∏ i : Fin m, U (Fin.natAdd n i) (Fin.natAdd n i)) = 1 := by
        simp [U]
      simp [hsplit, hleft, hright, mul_one]
    simpa [hdiag] using hdet

  have hdet1 : M1.det = M0.det := by
    classical
    -- det(M0 * U) = det M0 * det U = det M0
    simp [M1, Matrix.det_mul, h_u_det, M0]

  -- show each entry of the right-block columns of `M1` is divisible by `p`
  have hdiv_entry : ∀ (i : Fin (n + m)) (j' : Fin m), p ∣ M1 i (Fin.natAdd n j') := by
    intro i j'
    let ev : F[X] →+* F := Polynomial.evalRingHom x
    let col : Fin (n + m) := Fin.natAdd n j'
    let v_col : Fin (n + m) → F := fun k => ev (U k col)

    -- enough to show the entry evaluates to zero at `x`
    have hx0 : ev (M1 i col) = 0 := by
      -- map the matrix product through `ev`
      have hmapmul : ev (M1 i col) = (M0.map ev * U.map ev) i col := by
        simpa [M1] using
          (RingHom.map_matrix_mul (M := M0) (N := U) (i := i) (j := col) (f := ev))

      have hmulVec : (M0.map ev * U.map ev) i col = (M0.map ev).mulVec v_col i := by
        -- definitional unfolding of `mulVec`/`dotProduct`
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, v_col]

      have hM0map : M0.map ev = Polynomial.sylvester (A.map ev) (B.map ev) m n := by
        simpa [M0] using (ps_sylvester_map (R := F[X]) (S := F) ev A B m n)

      -- rewrite in terms of the Sylvester matrix over `F`
      have hSylv : ev (M1 i col) =
          (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec v_col i := by
        calc
          ev (M1 i col) = (M0.map ev * U.map ev) i col := hmapmul
          _ = (M0.map ev).mulVec v_col i := hmulVec
          _ = (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec v_col i := by
            simp [hM0map]

      -- degree hypotheses for applying `ps_sylvester_mul_vec_eq_coeff_add`
      have hmA : (A.map ev).natDegree ≤ m := by
        have h1 : (A.map ev).natDegree ≤ A.natDegree := by
          simpa using (Polynomial.natDegree_map_le (f := ev) (p := A))
        have h2 : A.natDegree ≤ m := by
          -- `m = natDegreeY A = A.natDegree`
          simp [hm, Polynomial.Bivariate.natDegreeY]
        exact le_trans h1 h2

      have hnB : (B.map ev).natDegree ≤ n := by
        have h1 : (B.map ev).natDegree ≤ B.natDegree := by
          simpa using (Polynomial.natDegree_map_le (f := ev) (p := B))
        have h2 : B.natDegree ≤ n := by
          simpa [Polynomial.Bivariate.natDegreeY] using hn
        exact le_trans h1 h2

      -- compute the `mulVec` entry
      have hmulVecCoeff :=
        congrArg (fun f : (Fin (n + m) → F) => f i)
          (ps_sylvester_mul_vec_eq_coeff_add (A := A.map ev) (B := B.map ev) (m := m) (n := n)
            hmA hnB v_col)

      -- simplify the two sums appearing in the formula
      let q : F[X] := Q * X ^ (j' : ℕ)

      have hqdeg_le : q.natDegree ≤ n - 1 := by
        simpa [q] using (ps_nat_degree_mul_x_pow_le (Q := Q) (j := j') hmn' hQdeg')

      have hqdeg_lt : q.natDegree < n := by
        have hmpos : 0 < m := Fin.size_positive j'
        have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn'
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
        have hlt : n - 1 < n := by
          simpa [hsub] using (Nat.lt_succ_self (n - 1))
        exact lt_of_le_of_lt hqdeg_le hlt

      have hBmap : B.map ev = Q * A.map ev := by
        -- rewrite `evalX` as `map` in the hypothesis `hQ`
        simpa [ps_eval_x_eq_map, ev] using hQ

      have hsum_left
      : (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v_col (Fin.castAdd m j))) = -q := by
        -- identify this sum with `ofFn n` applied to `-toFn n q`
        have hsum1 : (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v_col (Fin.castAdd m j))) =
            Polynomial.ofFn n (fun j : Fin n => v_col (Fin.castAdd m j)) := by
          simpa using
            (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin n => v_col (Fin.castAdd m j))).symm

        -- compute the coefficient vector
        have hv : (fun j : Fin n => v_col (Fin.castAdd m j)) =
            fun j : Fin n => -(Polynomial.toFn n q j) := by
          funext j
          -- on the left block, `U` has constant entries `-C (q.coeff j)`
          simp [v_col, col, U, ev, q, Polynomial.toFn]

        -- reconstruct `q` from its first `n` coefficients
        have hofFn : Polynomial.ofFn n (Polynomial.toFn n q) = q :=
          Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (p := q) hqdeg_lt

        have hofFn_neg :
            Polynomial.ofFn n (fun j : Fin n => -(Polynomial.toFn n q j)) =
              -Polynomial.ofFn n (Polynomial.toFn n q) := by
          classical
          -- convert to sum of monomials and pull out the minus
          simp [Polynomial.ofFn_eq_sum_monomial]

        -- put everything together
        calc
          (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v_col (Fin.castAdd m j)))
              = Polynomial.ofFn n (fun j : Fin n => v_col (Fin.castAdd m j)) := hsum1
          _ = Polynomial.ofFn n (fun j : Fin n => -(Polynomial.toFn n q j)) := by
            simp [hv]
          _ = -Polynomial.ofFn n (Polynomial.toFn n q) := hofFn_neg
          _ = -q := by
            simp [hofFn]

      have hsum_right : (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v_col (Fin.natAdd n j))) =
          X ^ (j' : ℕ) := by
        classical
        have hv : ∀ j : Fin m, v_col (Fin.natAdd n j) = (if j = j' then (1 : F) else 0) := by
          intro j
          by_cases h : j = j'
          · simp [v_col, col, U, ev, h]
          · simp [v_col, col, U, ev, h]

        -- convert to a delta-sum
        have hdelta :
            (∑ j : Fin m, Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0)) =
              X ^ (j' : ℕ) := by
          classical
          calc
            (∑ j : Fin m, Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0))
                = ∑ j : Fin m, (if j = j' then Polynomial.monomial (j : ℕ) (1 : F) else 0) := by
                    classical
                    have hfun :
                        (fun j : Fin m => Polynomial.monomial (j : ℕ) (if j = j' then (1 : F) else 0)) =
                          fun j : Fin m => (if j = j' then Polynomial.monomial (j : ℕ) (1 : F) else 0) := by
                      funext j
                      by_cases hj : j = j'
                      · simp [hj]
                      · simp [hj]
                    simp [hfun]
            _ = Polynomial.monomial (j' : ℕ) (1 : F) := by
                exact Fintype.sum_ite_eq' j' fun j ↦ (monomial ↑j) 1
            _ = X ^ (j' : ℕ) := by exact monomial_one_right_eq_X_pow ↑j'

        simpa [hv] using hdelta

      -- now the coefficient is zero, using `hBmap`
      have hcoeff0 :
          ((A.map ev) * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v_col (Fin.castAdd m j))) +
            (B.map ev) * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v_col (Fin.natAdd n j)))).coeff
              (i : ℕ) = 0 := by
        -- rewrite the two sums
        simp [hsum_left, hsum_right, hBmap, q, mul_assoc, mul_left_comm, mul_comm]

      -- finish
      have : (Polynomial.sylvester (A.map ev) (B.map ev) m n).mulVec v_col i = 0 := by
        -- `hmulVecCoeff` is exactly this coefficient
        simp [hmulVecCoeff, hcoeff0]

      -- use the rewriting of `ev (M1 i col)` via Sylvester
      simpa [hSylv] using this

    -- convert to `IsRoot`, then to divisibility by `X - C x`
    have hroot : Polynomial.IsRoot (M1 i col) x := by
      have : (M1 i col).eval x = 0 := by
        simpa [ev, Polynomial.coe_evalRingHom] using hx0
      simpa [Polynomial.IsRoot, Polynomial.IsRoot.def] using this

    have hdiv : (X - C x) ∣ M1 i col := (Polynomial.dvd_iff_isRoot).2 hroot
    simpa [p, col] using hdiv

  -- build a matrix by dividing the right-block columns by `p`
  classical
  let q_mat : Matrix (Fin (n + m)) (Fin (n + m)) F[X] :=
    fun i j =>
      j.addCases
        (fun jn => M1 i (Fin.castAdd m jn))
        (fun jm => Classical.choose (hdiv_entry i jm))

  have hQmat_spec : ∀ (i : Fin (n + m)) (j' : Fin m),
      M1 i (Fin.natAdd n j') = p * q_mat i (Fin.natAdd n j') := by
    intro i j'
    simpa [q_mat, Fin.addCases_right] using (Classical.choose_spec (hdiv_entry i j'))

  -- express `M1` as column-scaled version of `Qmat`
  let v : Fin (n + m) → F[X] := fun j => j.addCases (fun _ => 1) (fun _ => p)

  have hM1_scale : M1 = fun i j => v j * q_mat i j := by
    apply Matrix.ext
    intro i j
    cases' j using Fin.addCases with jn jm
    · -- left block
      simp [v, q_mat, Fin.addCases_left]
    · -- right block
      have h := hQmat_spec i jm
      simpa [v, q_mat, Fin.addCases_right, mul_assoc] using h

  have hdet_factor : M1.det = (∏ j : Fin (n + m), v j) * q_mat.det := by
    classical
    simpa [hM1_scale] using (Matrix.det_mul_row v q_mat)

  -- compute product of `v`
  have hvprod : (∏ j : Fin (n + m), v j) = p ^ m := by
    classical
    have hsplit := (Fin.prod_univ_add (a := n) (b := m) (f := v))
    have hleft : (∏ i : Fin n, v (Fin.castAdd m i)) = 1 := by
      simp [v]
    have hright : (∏ j' : Fin m, v (Fin.natAdd n j')) = p ^ m := by
      simp [v]
    simp [hsplit, hleft, hright]

  -- conclude divisibility for `M1.det`
  have hdivM1 : p ^ m ∣ M1.det := by
    refine ⟨q_mat.det, ?_⟩
    simp [hdet_factor, hvprod]

  -- transfer back to `M0.det`
  have hdivM0 : p ^ m ∣ M0.det := by
    simpa [hdet1] using hdivM1

  -- rewrite goal
  -- `Polynomial.resultant` is defined as the determinant of the Sylvester matrix
  simpa [p, m, hm, Polynomial.Bivariate.natDegreeY, Polynomial.resultant, M0] using hdivM0

lemma ps_resultant_dvd_pow_eval_y {F : Type} [Field F] [DecidableEq F]
    (A B : F[X][Y]) (y : F) (Q : F[X]) (n : ℕ)
    (hmn : Polynomial.Bivariate.degreeX A ≤ n)
    (hn : Polynomial.Bivariate.degreeX B ≤ n)
    (hQdeg : Q.natDegree ≤ n - Polynomial.Bivariate.degreeX A)
    (hQ : Polynomial.Bivariate.evalY y B = Q * Polynomial.Bivariate.evalY y A) :
    (X - C y) ^ (Polynomial.Bivariate.degreeX A) ∣
      Polynomial.resultant (Polynomial.Bivariate.swap A) (Polynomial.Bivariate.swap B)
        (Polynomial.Bivariate.degreeX A) n := by
  classical
  have hQ' :
      Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap B) =
        Q * Polynomial.Bivariate.evalX y (Polynomial.Bivariate.swap A) := by
    simpa [-Polynomial.Bivariate.swap_apply, ps_eval_y_eq_eval_x_swap] using hQ

  have hmn' : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) ≤ n := by
    simpa [-Polynomial.Bivariate.swap_apply, ps_nat_degree_y_swap] using hmn

  have hn' : Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap B) ≤ n := by
    simpa [-Polynomial.Bivariate.swap_apply, ps_nat_degree_y_swap] using hn

  have hQdeg'
  : Q.natDegree ≤ n - Polynomial.Bivariate.natDegreeY (Polynomial.Bivariate.swap A) := by
    simpa [-Polynomial.Bivariate.swap_apply, ps_nat_degree_y_swap] using hQdeg

  have h :=
    ps_resultant_dvd_pow_eval_x (A := Polynomial.Bivariate.swap A)
      (B := Polynomial.Bivariate.swap B) (x := y) (Q := Q) (n := n)
      (hmn := hmn') (hn := hn') (hQdeg := hQdeg') (hQ := hQ')

  simpa [-Polynomial.Bivariate.swap_apply, ps_nat_degree_y_swap] using h


lemma ps_resultant_ne_zero_of_is_rel_prime {F : Type} [Field F] [DecidableEq F]
    (A B : F[X][Y]) (n : ℕ)
    (hn : Polynomial.Bivariate.natDegreeY B ≤ n)
    (hA0 : A ≠ 0) (hrel : IsRelPrime A B) :
    Polynomial.resultant A B (Polynomial.Bivariate.natDegreeY A) n ≠ 0 := by
  classical
  set m : ℕ := Polynomial.Bivariate.natDegreeY A with hm
  intro hres
  have hdet : (Polynomial.sylvester A B m n).det = 0 := by
    simpa [Polynomial.resultant] using hres
  rcases (Matrix.exists_mulVec_eq_zero_iff (M := Polynomial.sylvester A B m n)).2 hdet with
    ⟨v, hv0, hv⟩
  have hmdeg : A.natDegree ≤ m := by
    simp [hm, Polynomial.Bivariate.natDegreeY]
  have hndeg : B.natDegree ≤ n := by
    simpa [Polynomial.Bivariate.natDegreeY] using hn
  let P : F[X][Y] :=
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))
  let Q : F[X][Y] :=
    ∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j))
  have hvcoeff : ∀ i : Fin (n + m), (A * P + B * Q).coeff (i : ℕ) = 0 := by
    intro i
    have hv_i : (Polynomial.sylvester A B m n).mulVec v i = 0 := by
      simpa using congrArg (fun f => f i) hv
    have hsyl_i :=
      congrArg (fun f => f i)
        (ps_sylvester_mul_vec_eq_coeff_add (R := F[X]) A B m n hmdeg hndeg v)
    have :
        (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
        B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ) = 0 := by
      calc
        (A * (∑ j : Fin n, Polynomial.monomial (j : ℕ) (v (Fin.castAdd m j))) +
              B * (∑ j : Fin m, Polynomial.monomial (j : ℕ) (v (Fin.natAdd n j)))).coeff (i : ℕ)
            = (Polynomial.sylvester A B m n).mulVec v i := by
                simpa using hsyl_i.symm
        _ = 0 := hv_i
    simpa [P, Q] using this

  -- If `n + m = 0`, then `Fin (n + m)` is empty, so `v = 0`, contradicting `hv0`.
  have hnmpos : 0 < n + m := by
    by_contra h
    have hnm0 : n + m = 0 := Nat.eq_zero_of_not_pos h
    have : v = 0 := by
      funext i
      have hlt : (i : ℕ) < 0 := by
        simpa [hnm0] using i.isLt
      exact (False.elim (Nat.not_lt_zero _ hlt))
    exact hv0 this

  have hA_natDegree : A.natDegree = m := by
    simpa [Polynomial.Bivariate.natDegreeY] using hm.symm

  have hP_ofFn : P = Polynomial.ofFn n (fun j : Fin n => v (Fin.castAdd m j)) := by
    simpa [P] using
      (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin n => v (Fin.castAdd m j))).symm

  have hQ_ofFn : Q = Polynomial.ofFn m (fun j : Fin m => v (Fin.natAdd n j)) := by
    simpa [Q] using
      (Polynomial.ofFn_eq_sum_monomial (v := fun j : Fin m => v (Fin.natAdd n j))).symm

  have hdegC : (A * P + B * Q).natDegree < n + m := by
    have hdegAP : (A * P).natDegree < n + m := by
      by_cases hn0 : n = 0
      · subst hn0
        have hmpos : 0 < m := by simpa using hnmpos
        simpa [P] using hmpos
      · have hnpos : 1 ≤ n := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hn0)
        have hPnat : P.natDegree < n := by
          simpa [hP_ofFn] using
            (Polynomial.ofFn_natDegree_lt (R := F[X]) hnpos (fun j : Fin n => v (Fin.castAdd m j)))
        have hmul_le : (A * P).natDegree ≤ A.natDegree + P.natDegree := Polynomial.natDegree_mul_le
        have hmul_le' : (A * P).natDegree ≤ m + P.natDegree := by
          simpa [hA_natDegree] using hmul_le
        have hlt : m + P.natDegree < m + n := Nat.add_lt_add_left hPnat m
        have : (A * P).natDegree < m + n := lt_of_le_of_lt hmul_le' hlt
        simpa [Nat.add_comm] using this

    have hdegBQ : (B * Q).natDegree < n + m := by
      by_cases hm0 : m = 0
      · have hQ0 : Q = 0 := by
          simp [hm0, hQ_ofFn, Polynomial.ofFn]
        rw [hQ0, hm0]
        simp
        simpa [hm0] using hnmpos
      · have hmpos : 1 ≤ m := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hm0)
        have hQnat : Q.natDegree < m := by
          simpa [hQ_ofFn] using
            (Polynomial.ofFn_natDegree_lt (R := F[X]) hmpos (fun j : Fin m => v (Fin.natAdd n j)))
        have hmul_le : (B * Q).natDegree ≤ B.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
        have h1 : B.natDegree + Q.natDegree ≤ n + Q.natDegree := Nat.add_le_add_right hndeg _
        have h2 : n + Q.natDegree < n + m := Nat.add_lt_add_left hQnat n
        exact lt_of_le_of_lt hmul_le (lt_of_le_of_lt h1 h2)

    have hle : (A * P + B * Q).natDegree ≤ max (A * P).natDegree (B * Q).natDegree :=
      Polynomial.natDegree_add_le (A * P) (B * Q)
    have hmaxlt : max (A * P).natDegree (B * Q).natDegree < n + m :=
      max_lt_iff.2 ⟨hdegAP, hdegBQ⟩
    exact lt_of_le_of_lt hle hmaxlt

  have hcomb : A * P + B * Q = 0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < n + m
    · simpa using hvcoeff ⟨k, hk⟩
    · have hk' : n + m ≤ k := Nat.le_of_not_gt hk
      have hdegk : (A * P + B * Q).natDegree < k := lt_of_lt_of_le hdegC hk'
      simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt hdegk)

  have hA_dvd_BQ : A ∣ B * Q := by
    refine ⟨-P, ?_⟩
    have hcomb' : B * Q + A * P = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hcomb
    have hneg : -(A * P) = B * Q := neg_eq_of_add_eq_zero_left hcomb'
    calc
      B * Q = -(A * P) := by simpa using hneg.symm
      _ = A * (-P) := (mul_neg A P).symm

  have hA_dvd_Q : A ∣ Q := hrel.dvd_of_dvd_mul_left hA_dvd_BQ

  have hQ0 : Q = 0 := by
    by_cases hm0 : m = 0
    · simp_all [m, P, Q]
      ext n_1 n_2 : 2
      simp_all only [zero_le, ofFn_coeff_eq_zero_of_ge, coeff_zero]
      -- simp [hm0]
      -- simp [Q]
    · have hmpos : 1 ≤ m := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hm0)
      have hQnat : Q.natDegree < m := by
        simpa [hQ_ofFn] using
          (Polynomial.ofFn_natDegree_lt (R := F[X]) hmpos (fun j : Fin m => v (Fin.natAdd n j)))
      rcases hA_dvd_Q with ⟨R, hR⟩
      by_cases hR0 : R = 0
      · subst hR0
        simp [hR]
      · have hQnat' : (A * R).natDegree < m := by
          exact lt_of_eq_of_lt (congrArg natDegree (id (Eq.symm hR))) hQnat
        have hdegmul : (A * R).natDegree = A.natDegree + R.natDegree :=
          Polynomial.natDegree_mul hA0 hR0
        have hlt : A.natDegree + R.natDegree < m := by
          simpa [hdegmul] using hQnat'
        have hlt' : m + R.natDegree < m := by
          exact lt_of_eq_of_lt (congrFun (congrArg HAdd.hAdd hm) R.natDegree) hlt
        have hge : m ≤ m + R.natDegree := Nat.le_add_right m R.natDegree
        exact (False.elim ((Nat.not_lt_of_ge hge) hlt'))

  have hP0 : P = 0 := by
    have hAP0 : A * P = 0 := by
      simpa [hQ0] using hcomb
    have hmul : A = 0 ∨ P = 0 := mul_eq_zero.mp hAP0
    exact hmul.resolve_left hA0

  have hcoeffP : ∀ j : Fin n, P.coeff (j : ℕ) = v (Fin.castAdd m j) := by
    intro j
    simp [hP_ofFn]

  have hcoeffQ : ∀ j : Fin m, Q.coeff (j : ℕ) = v (Fin.natAdd n j) := by
    intro j
    simp [hQ_ofFn]

  have hv_left : ∀ j : Fin n, v (Fin.castAdd m j) = 0 := by
    intro j
    have : P.coeff (j : ℕ) = 0 := by
      simp [hP0]
    simpa [hcoeffP j] using this

  have hv_right : ∀ j : Fin m, v (Fin.natAdd n j) = 0 := by
    intro j
    have : Q.coeff (j : ℕ) = 0 := by
      simp [hQ0]
    simpa [hcoeffQ j] using this

  have hv_all : ∀ i : Fin (n + m), v i = 0 := by
    exact
      (Fin.forall_fin_add (m := n) (n := m) (P := fun i : Fin (n + m) => v i = 0)).2
        ⟨hv_left, hv_right⟩

  have : v = 0 := by
    funext i
    exact hv_all i

  exact hv0 this
