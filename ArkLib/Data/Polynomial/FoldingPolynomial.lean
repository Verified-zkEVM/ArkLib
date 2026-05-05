/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic) 
-/

import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

/-!
  Proof of Proposition 6.3 from [BS08].

  The statement is taken from [ACFY24]. Namely,
  ```latex
  \textbf{Fact 4.6 (BS08).} \textit{Given a polynomial } $\hat{q} \in \mathbb{F}[X]$:

  \begin{itemize}
      \item For every $\hat{f} \in \mathbb{F}[X]$ there exists a unique bivariate polynomial 
      $\hat{Q} \in \mathbb{F}[X,Y]$ with 
      \[
          \deg_X(\hat{Q}) = \left\lfloor \frac{\deg(\hat{f})}{\deg(\hat{q})} \right\rfloor
          \quad \text{and} \quad
          \deg_Y(\hat{Q}) < \deg(\hat{q})
      \]
      such that 
      \[
          \hat{f}(Z) = \hat{Q}(\hat{q}(Z), Z).
      \]
      Moreover, $\hat{Q}$ can be computed efficiently given $\hat{f}$ and $\hat{q}$. 
      Observe that if $\deg(\hat{f}) < t \cdot \deg(\hat{q})$ then 
      $\deg_X(\hat{Q}) < t$.

      \item For every $\hat{Q} \in \mathbb{F}[X,Y]$ with 
      $\deg_X(\hat{Q}) < t$ and $\deg_Y(\hat{Q}) < \deg(\hat{q})$, 
      the polynomial 
      \[
          \hat{f}(Z) := \hat{Q}(\hat{q}(Z), Z)
      \]
      has degree 
      \[
          \deg(\hat{f}) < t \cdot \deg(\hat{q}).
      \]
  \end{itemize}
  ```

## References

* [Ben-Sasson, E., Madhu, S., *Short PCPs with Polylog Query Complexity*][BS08]
* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E., 
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]

-/

namespace Polynomial.FoldingPolynomial

section

open Polynomial Polynomial.Bivariate 

variable {ι F : Type*} [Field F]   

/-- The definition of the folding polynomial `Q` 
    from the proposition that takes `fuel` value
    as the upper bound of number of steps needed 
    to produce the polynomial `Q`. -/
noncomputable def foldingPolynomialAux (q f : F[X]) (fuel : ℕ) : F[X][Y] :=
  -- The main idea behind the `fuel` argument
  -- is to assure the totality checker that 
  -- the recursive function is indeed total
  -- by providing the upper bound on the number
  -- of iterations.
  -- 
  -- Later on, we eliminate it in the public API `foldingPolynomial`.
  if q.degree ≤ 0 then Polynomial.map C f else
  if f.degree < q.degree then Polynomial.map C f
  else
  match fuel with
  | .zero => Polynomial.map Polynomial.C f
  | .succ fuel => (Polynomial.map Polynomial.C (f % q))
    + Polynomial.C Polynomial.X * (foldingPolynomialAux q (f / q) fuel)

/-- The bivariate polynomial `Q` such that
    `f = Q(q(X), X)`, `Q.degreeX = f.natDegree / q.natDegree`,
    and `Q.natDegreeY < q.natDegree`, if `q` is not a constant polynomial. -/
noncomputable def foldingPolynomial (q f : F[X]) : F[X][Y] := 
  foldingPolynomialAux q f f.natDegree

lemma folding_polynomial_eq_map_of_f_degree_lt_q_degree {q f : F[X]}
  (h : f.degree < q.degree) :
    foldingPolynomial q f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp [h]

@[simp]
lemma folding_polynomial_C_q {q : F} {f : F[X]} :
  foldingPolynomial (C q) f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp only [ite_eq_left_iff, not_le, not_lt]
  intro h 
  have contra : (0 : WithBot ℕ) < 0 := 
    lt_of_lt_of_le h (Polynomial.degree_C_le (a := q)) 
  simp at contra

@[simp]
lemma foldingPolynomial_C_f {f : F} {q : F[X]} :
  foldingPolynomial q (C f) = C (C f) := by
  unfold foldingPolynomial foldingPolynomialAux
  simp

@[simp]
lemma foldingPolynomial_zero {q : F[X]} :
  foldingPolynomial q 0 = 0 := by
  unfold foldingPolynomial foldingPolynomialAux
  simp

private lemma folding_polynomial_def_base_case {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0) :
    foldingPolynomial q f = Polynomial.map C f := by
  rcases h with h | h | h 
    <;> try (
      rw [Polynomial.degree_le_zero_iff] at h 
      rw [h]
      simp [map_C, folding_polynomial_C_q])
  rw [folding_polynomial_eq_map_of_f_degree_lt_q_degree h]

private lemma folding_polynomial_aux_natDegree_fuel_is_enough {q f : F[X]} {fuel : ℕ}
  (h : f.natDegree ≤ fuel) :
  foldingPolynomialAux q f f.natDegree = foldingPolynomialAux q f fuel := by
  have h_foldingPolynomialAux : 
    ∀ (deg₁ deg₂ : ℕ), 
      deg₁ ≥ f.natDegree → 
        deg₂ ≥ f.natDegree →
          foldingPolynomialAux q f deg₁ = foldingPolynomialAux q f deg₂ := by
      intro deg₁ deg₂ h₁ h₂
      induction deg₁ generalizing deg₂ f with
      | zero =>  
        simp_all +decide only [ge_iff_le, nonpos_iff_eq_zero, natDegree_eq_zero_iff_degree_le_zero]
        rw [Polynomial.eq_C_of_degree_le_zero h₁] 
        simp +decide only [foldingPolynomialAux, map_C, ite_self] 
        rcases deg₂ with _ | deg₂ 
          <;> simp_all only 
                [foldingPolynomialAux, 
                 map_C, 
                 left_eq_ite_iff, 
                 not_le, not_lt, nonpos_iff_eq_zero, 
                 foldingPolynomialAux, map_C, ite_self]
        exact fun h₃ h₄ ↦ 
          absurd h₄ 
            (not_le_of_gt (lt_of_le_of_lt (Polynomial.degree_C_le) h₃))
      | succ deg₁ ih => 
        rcases deg₂ with _ | deg₂ 
          <;> simp_all +decide only 
                [ge_iff_le, 
                 nonpos_iff_eq_zero, 
                 foldingPolynomialAux, 
                 ite_self,
                 ite_eq_left_iff, 
                 not_le, 
                 not_lt, 
                 zero_le]
        · obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c := 
            ⟨f.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero h₂⟩
          by_cases hc : c = 0 <;> simp_all +decide [Polynomial.degree_C]
          aesop
        · split_ifs <;> simp_all +decide only [
              not_le, 
              not_lt, 
              add_right_inj, 
              mul_eq_mul_left_iff,
              C_eq_zero, 
              X_ne_zero, 
              or_false]
          have h_div_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
            rw [Polynomial.div_def]
            rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic]
            · rw [Polynomial.natDegree_mul'] <;> aesop
            · exact Polynomial.monic_mul_leadingCoeff_inv (by aesop)
            · aesop
          by_cases hq : q.natDegree = 0
          · rw [Polynomial.degree_eq_natDegree] at * <;> aesop
          · exact ih (by omega) _ (by omega) (by omega)
  exact h_foldingPolynomialAux _ _ le_rfl h

private lemma folding_polynomial_def_ind_case {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0) :
  foldingPolynomial q f = (Polynomial.map Polynomial.C (f % q)) + 
    Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
      have h_fold : 
        ∀ {deg : ℕ}, 
          deg ≥ f.natDegree → 
            foldingPolynomial q f = 
              Polynomial.map Polynomial.C (f % q) + 
                Polynomial.C Polynomial.X * 
                  foldingPolynomial q (f / q) := by
        intros deg hdeg
        rw [foldingPolynomial]
        have h_fold : 
          ∀ {deg : ℕ}, 
            deg ≥ f.natDegree → 
              foldingPolynomialAux q f deg = 
                Polynomial.map Polynomial.C (f % q) + 
                  Polynomial.C Polynomial.X * 
                    foldingPolynomialAux q (f / q) (deg - 1) := by
          intros deg hdeg
          induction deg generalizing f with
          | zero => 
            obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c := 
              ⟨f.coeff 0, Polynomial.eq_C_of_natDegree_le_zero hdeg⟩
            simp_all +decide only [gt_iff_lt, ge_iff_le, natDegree_C, zero_le, zero_tsub]
            exact absurd h₁ (not_le_of_gt (lt_of_le_of_lt (Polynomial.degree_C_le) h₂))
          | succ deg ih => 
            rw [foldingPolynomialAux]
            rw [if_neg h₂.not_ge, if_neg (not_lt_of_ge h₁)]
            rfl
        convert h_fold hdeg using 1
        · exact folding_polynomial_aux_natDegree_fuel_is_enough hdeg
        · have h_fold_eq : 
            foldingPolynomial q (f / q) 
              = foldingPolynomialAux q (f / q) (deg - 1) := by
            have h_deg : (f / q).natDegree ≤ deg - 1 := by
              have h_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
                rw [Polynomial.div_def]
                rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic]
                · rw [Polynomial.natDegree_mul'] <;> aesop
                · exact Polynomial.monic_mul_leadingCoeff_inv (by aesop)
                · aesop
              exact le_trans h_deg (Nat.sub_le_sub_right hdeg _) 
                |> le_trans 
                <| Nat.sub_le_sub_left (Polynomial.natDegree_pos_iff_degree_pos.mpr h₂) _
            apply folding_polynomial_aux_natDegree_fuel_is_enough 
            assumption
          rw [h_fold_eq]
      exact h_fold le_rfl

/-- If the folding polynomial is zero 
  then so is the original polynomial. -/
lemma eq_zero_of_folding_polynomial_eq_zero {q f : F[X]}
  (h : foldingPolynomial q f = 0) : f = 0 := by
    induction n : f.natDegree using Nat.strong_induction_on generalizing f with
    | h n' ih => 
      by_cases h₁ : 
      f.degree < q.degree 
        ∨ f.degree ≤ 0 
        ∨ q.degree ≤ 0 <;> simp_all only [ext_iff, coeff_zero, not_or, not_lt, not_le]
      · rw [folding_polynomial_def_base_case h₁] at h
        intro n
        specialize h n 0
        aesop
      · have h_rem_zero : f % q = 0 := by
          rw [folding_polynomial_def_ind_case h₁.1 h₁.2.2] at h
          ext n
          specialize h n 0
          simp_all +decide [Polynomial.coeff_map] 
        have h_quot_zero : f / q = 0 := by
          have h_quot_zero : foldingPolynomial q (f / q) = 0 := by
            have h_quot_zero : 
            foldingPolynomial q f 
              = (Polynomial.map Polynomial.C (f % q)) 
                + Polynomial.C Polynomial.X 
                    * foldingPolynomial q (f / q) := by
              rw [folding_polynomial_def_ind_case] <;> aesop
            simp_all +decide only [Polynomial.map_zero, zero_add, coeff_C_mul,
            EuclideanDomain.mod_eq_zero, ext_iff, coeff_add, coeff_map, add_zero, coeff_zero]
            intro n n_1
            specialize h n (n_1 + 1) 
            simp_all +decide
          contrapose! ih
          refine 
            ⟨Polynomial.natDegree (f / q), 
            by {
              have h_deg_f : f.natDegree = q.natDegree + (f / q).natDegree := by
                rw [←Polynomial.natDegree_mul']
                · rw [EuclideanDomain.mul_div_cancel'] <;> aesop
                · aesop
              linarith [
                Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.1, 
                Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.2]
            }, 
            f / q, 
            by simp_all +decide, 
            rfl, 
            Polynomial.natDegree (f / q), by simp [ih]⟩ 
        rw [EuclideanDomain.mod_eq_sub_mul_div] at h_rem_zero 
        aesop

lemma folding_polynomial_ne_zero_of_ne_zero {q f : F[X]}
  (h : f ≠ 0) : foldingPolynomial q f ≠ 0 := fun contra ↦ by
  simp_all [eq_zero_of_folding_polynomial_eq_zero contra]

lemma substitution_property_of_folding_polynomial {q f : F[X]} :
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X = f := 
  by 
  revert q f
  intro q f
  induction n : f.natDegree using Nat.strong_induction_on generalizing q f with
  | h n ih => 
    by_cases h_deg : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0
    · rw [folding_polynomial_def_base_case h_deg] 
      simp +decide only [eval_map]
      simp +decide only [eval₂_map]
      simp +decide only 
        [eval₂_eq_sum_range, 
         RingHom.coe_comp, 
         coe_compRingHom, 
         Function.comp_apply,
         C_comp]
      conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow f] 
    · have h_fold_def : 
        foldingPolynomial q f = 
          (Polynomial.map Polynomial.C (f % q)) + 
            Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
        apply folding_polynomial_def_ind_case
        · exact le_of_not_gt fun h ↦ h_deg <| Or.inl h
        · exact lt_of_not_ge fun h ↦ h_deg <| Or.inr <| Or.inr h
      have h_fold_def : 
        Polynomial.eval Polynomial.X 
          (Polynomial.map q.compRingHom (foldingPolynomial q f)) = 
            (f % q) + 
              q * Polynomial.eval Polynomial.X 
                (Polynomial.map q.compRingHom (foldingPolynomial q (f / q))) := by
        simp +decide only 
          [h_fold_def, 
           Polynomial.map_add, 
           Polynomial.map_mul, 
           map_C, 
           coe_compRingHom,
           X_comp, 
           eval_add, 
           eval_map, 
           eval_mul, 
           eval_C, 
           add_left_inj]
        simp +decide only [eval₂_map]
        simp +decide only 
          [eval₂_eq_sum_range, 
           RingHom.coe_comp, 
           coe_compRingHom, 
           Function.comp_apply,
           C_comp]
        conv_rhs => rw [Polynomial.as_sum_range_C_mul_X_pow (f % q)] 
      have h_fold_def : 
        Polynomial.eval Polynomial.X 
          (Polynomial.map q.compRingHom 
            (foldingPolynomial q (f / q))) = f / q := by
        convert ih (Polynomial.natDegree (f / q)) _ rfl using 1
        rw [←n, Polynomial.div_def]
        rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic] <;> norm_num
        · by_cases hq : q = 0 
            <;> simp_all only [not_or, not_lt, not_le, Polynomial.map_add, Polynomial.map_mul,
              map_C, coe_compRingHom, X_comp, eval_add, eval_mul, eval_C, add_left_inj,
              leadingCoeff_C, ne_eq, leadingCoeff_eq_zero, not_false_eq_true, mul_inv_cancel₀,
              one_ne_zero, natDegree_mul', 
              natDegree_C, add_zero, degree_zero, not_lt_bot, bot_le, or_true, not_true_eq_false]
          exact ⟨n.symm 
            ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr 
              h_deg.2.1, 
            Polynomial.natDegree_pos_iff_degree_pos.mpr h_deg.2.2⟩
        · exact Polynomial.monic_mul_leadingCoeff_inv (by aesop)
        · aesop
      rw [
        ‹Polynomial.eval Polynomial.X 
          (Polynomial.map q.compRingHom 
            (foldingPolynomial q f)) = 
              f % q + 
                q * Polynomial.eval Polynomial.X 
                  (Polynomial.map q.compRingHom 
                    (foldingPolynomial q (f / q)))›, 
        h_fold_def, EuclideanDomain.mod_eq_sub_mul_div] 
      ring

/-- A means to evaluate the original polynomial in terms of
  the folding polynomial. -/
lemma eval_property_of_folding_polynomial {q f : F[X]} {x : F} :
  ((foldingPolynomial q f).map (Polynomial.evalRingHom (q.eval x))).eval x = f.eval x := by 
  have h_subst : ((Polynomial.FoldingPolynomial.foldingPolynomial q f).map 
    (Polynomial.compRingHom q)).eval X = f := 
      substitution_property_of_folding_polynomial
  generalize_proofs at *
  (replace h_subst := congr_arg (Polynomial.eval x) h_subst 
   simp_all only [eval_map] 
   convert h_subst using 1 
   simp +decide [Polynomial.eval₂_eq_sum_range] 
   ring_nf
   simp +decide [Polynomial.eval_finset_sum])

/-- A means to evaluate the original polynomial in terms of
  the folding polynomial when `q = X ^ k`. -/
lemma eval_property_of_folding_polynomial_x_k {f : F[X]} {k : ℕ} {x : F} :
  ((foldingPolynomial (X ^ k) f).map (Polynomial.evalRingHom (x ^ k))).eval x =
    f.eval x := by
  have := eval_property_of_folding_polynomial (f := f) (q := X ^ k) (x := x) 
  aesop

/-- The degree of `foldingPolynomial` is less than `q.degree` in the second variable, 
  when `q` is not a constant polynomial.
-/
theorem folding_polynomial_deg_y_bound {q f : F[X]} (h : 0 < q.degree) :
   natDegreeY (foldingPolynomial q f) < q.degree := by 
  simp only [natDegreeY, coe_lt_degree]
  induction n : f.natDegree using Nat.strong_induction_on generalizing f q with
  | h n ih =>
  by_cases hq : f.degree < q.degree 
  · have h_folding_eq_map : foldingPolynomial q f = Polynomial.map Polynomial.C f := 
      folding_polynomial_eq_map_of_f_degree_lt_q_degree hq
    by_cases hf : f = 0 
      <;> simp_all only [natDegree_map, natDegree_zero, degree_zero, foldingPolynomial_zero,
        Polynomial.map_zero, gt_iff_lt]
    · exact n.symm ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr h
    · rw [←n, Polynomial.degree_eq_natDegree hf] at * 
      aesop
  · have h_fold : 
      foldingPolynomial q f = 
        (Polynomial.map Polynomial.C (f % q)) + 
          Polynomial.C Polynomial.X * 
            (foldingPolynomial q (f / q)) := by
      rw [folding_polynomial_def_ind_case]
      · simp only [not_lt] at hq 
        exact hq
      · exact h
    refine h_fold ▸ lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (by {
      have h_deg_mod : (f % q).degree < q.degree := 
        EuclideanDomain.mod_lt f (Polynomial.ne_zero_of_degree_gt h)
      by_cases h : f % q = 0 <;> simp_all +decide only [not_lt, Polynomial.map_zero, zero_add,
        degree_zero, EuclideanDomain.mod_eq_zero, natDegree_map, gt_iff_lt]
      · rw [EuclideanDomain.mod_eq_zero.mpr h]  
        simp +decide [Polynomial.natDegree_pos_iff_degree_pos.mpr ‹_›]
      · exact Polynomial.natDegree_lt_natDegree (by aesop) h_deg_mod
    }) (by {
      apply lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) 
      apply ih _ _ h rfl
      rw [←n, Polynomial.div_def]
      rw [
        Polynomial.natDegree_C_mul, 
        Polynomial.natDegree_divByMonic] 
          <;> norm_num [
            Polynomial.natDegree_mul', 
            Polynomial.natDegree_C, show q ≠ 0 by aesop]
      · simp only [not_lt] at hq 
        exact 
          ⟨Polynomial.natDegree_pos_iff_degree_pos.mpr 
            (lt_of_lt_of_le h hq),
            Polynomial.natDegree_pos_iff_degree_pos.mpr h⟩
      · exact Polynomial.monic_mul_leadingCoeff_inv (by aesop)
    }))
    
/-- The degree of `foldingPolynomial` is less than `k` in the second variable, 
  when `q = X ^ k` and `k ≠ 0`.
-/
theorem folding_polynomial_deg_y_bound_x_k {f : F[X]} {k : ℕ}
  [NeZero k] :
  natDegreeY (foldingPolynomial (X ^ k) f) < k := by 
  simpa using (folding_polynomial_deg_y_bound (q := X ^ k)  
                (f := f) (by aesop 
                              (add safe forward (NeZero.ne k))
                              (add safe (by omega)))
              )

private lemma folding_polynomial_deg_x_base {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0) :
  degreeX (foldingPolynomial q f) = 0 := by
  simp only 
    [folding_polynomial_def_base_case h
      , degreeX
      , coeff_map
      , natDegree_C
      , show 0 = (⊥ : ℕ) by rfl
      , Finset.sup_eq_bot_iff
      , implies_true]

private lemma folding_polynomial_deg_x_ind {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0) :
  degreeX (foldingPolynomial q f)
    = 1 + degreeX (foldingPolynomial q (f / q)) := by
      rw [folding_polynomial_def_ind_case h₁ h₂]
      apply le_antisymm 
      · simp_all only [ge_iff_le, gt_iff_lt, degreeX, coeff_add, coeff_map, coeff_C_mul,
        natDegree_C_add, Finset.sup_le_iff, mem_support_iff, ne_eq]
        intro n hn 
        by_cases h : Polynomial.coeff 
          (foldingPolynomial q (f / q)) n = 0 
            <;> simp_all +decide only [monic_X, Monic.leadingCoeff, one_mul, ne_eq,
              leadingCoeff_eq_zero, not_false_eq_true, natDegree_mul', natDegree_X,
              add_le_add_iff_left, mul_zero, add_zero, map_eq_zero, natDegree_zero, zero_le] 
        exact Finset.le_sup 
          (f := fun n ↦ Polynomial.natDegree 
            (Polynomial.coeff (foldingPolynomial q (f / q)) n)) 
            (by aesop)
      · simp_all only [ge_iff_le, gt_iff_lt, degreeX, coeff_add, coeff_map, coeff_C_mul,
        natDegree_C_add, Nat.bot_eq_zero, add_pos_iff, zero_lt_one, Finset.lt_sup_iff,
        mem_support_iff, ne_eq, true_or, Finset.le_sup_iff]
        obtain ⟨b, hb⟩ : 
          ∃ b ∈ (foldingPolynomial q (f / q)).support, 
          ∀ n ∈ (foldingPolynomial q (f / q)).support, 
            Polynomial.natDegree 
              ((foldingPolynomial q (f / q)).coeff n) 
            ≤ 
            Polynomial.natDegree ((foldingPolynomial q (f / q)).coeff b) := by
          apply_rules [Finset.exists_max_image]
          by_contra h_empty_support
          simp_all +decide only [support_nonempty, ne_eq, not_not]
          have := eq_zero_of_folding_polynomial_eq_zero h_empty_support
          rw [Polynomial.div_eq_zero_iff] at this
          · exact this.not_ge h₁
          · aesop
        exists b
        simp_all only [mem_support_iff, ne_eq, monic_X, Monic.leadingCoeff, one_mul,
          leadingCoeff_eq_zero, not_false_eq_true, natDegree_mul', natDegree_X, add_le_add_iff_left,
          Finset.sup_le_iff, implies_true, and_true]
        intro h 
        have := congr_arg (Polynomial.eval 0) h 
        norm_num at this 
        have := congr_arg (Polynomial.eval 1) h 
        norm_num at this
        simp_all +decide

private lemma folding_polynomial_deg_x_C_q {q : F} {f : F[X]} :
  degreeX (foldingPolynomial (C q) f) = 0 := by
  rw [folding_polynomial_deg_x_base]
  aesop 
    (add simp [Polynomial.degree_C_le])

/-- The degree of the `foldingPolynomial q f` is precisely 
    `f.natDegree / q.natDegree` in the first variable. -/
@[simp]
theorem folding_polynomial_deg_x {q f : F[X]} :
  degreeX (foldingPolynomial q f) = f.natDegree / q.natDegree := by
    by_cases h: q.degree ≤ 0
    · rw [Polynomial.degree_le_zero_iff] at h
      rw [h, folding_polynomial_deg_x_C_q]
      simp only [natDegree_C, Nat.div_zero]
    · simp only [not_le] at h 
      induction n : f.natDegree using Nat.strong_induction_on generalizing f q with
      | h n ih =>
      by_cases h₁ : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0
      · have h_deg_zero : degreeX (foldingPolynomial q f) = 0 := 
          folding_polynomial_deg_x_base h₁
        have h_deg_zero : f.natDegree < q.natDegree := by
          by_cases hf : f = 0 
            <;> by_cases hq : q = 0 
            <;> simp_all +decide [Polynomial.degree_eq_natDegree]
          aesop
        rw [Nat.div_eq_of_lt] <;> aesop
      · have h_deg : 
          degreeX (foldingPolynomial q f) = 1 + degreeX (foldingPolynomial q (f / q)) := by
          apply folding_polynomial_deg_x_ind
          · exact le_of_not_gt fun h₂ ↦ h₁ <| Or.inl h₂
          · exact h
        have h_deg_f_div_q : (f / q).natDegree = f.natDegree - q.natDegree := by
          rw [Polynomial.div_def]
          rw [Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic]
          · rw [Polynomial.natDegree_mul'] <;> aesop
          · exact Polynomial.monic_mul_leadingCoeff_inv (Polynomial.ne_zero_of_degree_gt h)
          · aesop
        rw [h_deg, ih _ _ h h_deg_f_div_q]
        · rw [←n, Nat.add_comm]
          rw [
            ←Nat.sub_add_cancel (show q.natDegree ≤ f.natDegree from ?_), 
            Nat.add_div] 
            <;> norm_num [Polynomial.natDegree_pos_iff_degree_pos.mpr h]
          · exact Nat.mod_lt _ (Polynomial.natDegree_pos_iff_degree_pos.mpr h)
          · exact 
              Polynomial.natDegree_le_natDegree 
                (le_of_not_gt fun h' ↦ 
                    h₁ <| Or.inl 
                      <| by rw [
                        Polynomial.degree_eq_natDegree, 
                        Polynomial.degree_eq_natDegree] at * <;> aesop)
        · rw [←n]
          exact Nat.sub_lt 
            (Polynomial.natDegree_pos_iff_degree_pos.mpr 
                (lt_of_not_ge fun h ↦ h₁
                  <| Or.inr <| Or.inl h)) 
            (Polynomial.natDegree_pos_iff_degree_pos.mpr h)   

/-- A degreeX bound for folding polynomial from the STIR paper. -/
lemma folding_polynomial_deg_x_bound {q f : F[X]} {t : ℕ}
  (h : f.natDegree < t * q.natDegree) :
  degreeX (foldingPolynomial q f) < t := by
  rw [folding_polynomial_deg_x]
  by_cases heq: q.natDegree = 0
  · simp [heq] at h
  · exact Nat.lt_of_mul_lt_mul_right (a := q.natDegree) 
      (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) h)

private lemma satisfies_composition_property_implies_is_the_reminder
  {q f : F[X]}
  {Q : F[X][Y]}
  (h : (Q.map (Polynomial.compRingHom q)).eval X = f) :
  ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + Q := by
      obtain ⟨Q', hQ'⟩ : 
        ∃ Q' : F[X][Y], 
          Q - Polynomial.map (Polynomial.C) f = 
            (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) * Q' := by
        have h_div : 
          (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) ∣ 
            Q - Polynomial.map (Polynomial.C) 
                    (Polynomial.eval Polynomial.X 
                        (Polynomial.map 
                            (Polynomial.compRingHom q) Q)) := by
          have h_div : 
            ∀ p : F[X][Y], 
              (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) ∣ 
                  p - Polynomial.map Polynomial.C 
                        (Polynomial.eval Polynomial.X 
                          (Polynomial.map (Polynomial.compRingHom q) p)) := by
            intro p
            induction p using Polynomial.induction_on' with
            | add p q hp hq =>
              convert dvd_add hp hq using 1 
              simp +decide [sub_add_sub_comm]
            | monomial n p =>
              induction n with
              | zero =>
                simp_all +decide only [←C_mul_X_pow_eq_monomial, Polynomial.map_mul, map_C,
                  coe_compRingHom, Polynomial.map_pow, map_X, eval_mul, eval_C, eval_pow, eval_X]
                induction ‹F[X]› using 
                  Polynomial.induction_on' with
                | add p q hp hq =>
                    
                  simp_all +decide only [pow_zero, mul_one, map_add, add_comp,
                    Polynomial.map_add]
                  convert dvd_add hp hq using 1 
                  ring
                | monomial n p =>
                  simp_all only [pow_zero, mul_one, 
                  ←C_mul_X_pow_eq_monomial, map_mul, map_pow,
                    pow_zero, mul_one, mul_comp, C_comp, pow_comp, X_comp, Polynomial.map_mul,
                    map_C, Polynomial.map_pow]
                  exact dvd_trans 
                    (sub_dvd_pow_sub_pow _ _ _) 
                    ⟨Polynomial.C (Polynomial.C ‹_›), by ring⟩
              | succ n ih => 
                simp_all +decide only [←C_mul_X_pow_eq_monomial, Polynomial.map_mul, map_C,
                  coe_compRingHom, Polynomial.map_pow, map_X, eval_mul, eval_C, eval_pow, eval_X,
                  pow_succ, ←mul_assoc]
                simpa only [sub_mul] using ih.mul_right _
          exact h_div Q
        aesop
      exact ⟨-Q', by linear_combination -hQ'⟩

/-- An alternative description of the folding polynomial
    as the reminder in bivariate polynomial division
    of the form `f = Q' * (X - q(Y)) + Q`. -/
lemma folding_polynomial_is_the_reminder {q f : F[X]} :
  ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + (foldingPolynomial q f) :=  
    satisfies_composition_property_implies_is_the_reminder 
      substitution_property_of_folding_polynomial

/-- The uniqueness of the folding polynomial. -/
theorem folding_polynomial_is_unique {q f : F[X]} {Q : F[X][Y]}
  (h : (Q.map (Polynomial.compRingHom q)).eval X = f)
  (h_x : degreeX Q = f.natDegree / q.natDegree)
  (h_y : natDegreeY Q < q.natDegree) :
  Q = foldingPolynomial q f := by 
    by_contra h_contra
    obtain ⟨Q', hQ'⟩ : 
      ∃ Q' : F[X][Y], 
        Q - foldingPolynomial q f = 
          Q' * (C Polynomial.X - Polynomial.map (Polynomial.C) q) := by
      obtain ⟨Q', hQ'⟩ 
        := satisfies_composition_property_implies_is_the_reminder 
          (show ((Q.map (Polynomial.compRingHom q) 
            |> Polynomial.eval Polynomial.X)) = f from h)
      obtain ⟨Q'', hQ''⟩ 
        := satisfies_composition_property_implies_is_the_reminder 
          (show ((foldingPolynomial q f 
            |> Polynomial.map (Polynomial.compRingHom q) 
            |> Polynomial.eval Polynomial.X)) = f from
              substitution_property_of_folding_polynomial)
      exact ⟨Q'' - Q', by linear_combination' hQ'' - hQ'⟩
    have hQ'_zero : Q' = 0 := by
      have hQ'_deg : natDegreeY (Q - foldingPolynomial q f) < q.natDegree := by
        have hQ'_deg : 
          natDegreeY (Q - foldingPolynomial q f) 
            ≤ max (natDegreeY Q) (natDegreeY (foldingPolynomial q f)) := by
          convert Polynomial.natDegree_sub_le _ _ using 1
        have hQ'_deg : natDegreeY (foldingPolynomial q f) < q.natDegree := by
          by_cases hq : q.degree ≤ 0 
            <;> simp_all +decide only [le_sup_iff, not_le]
          · rw [Polynomial.eq_C_of_degree_le_zero hq] at h_y h_contra hQ' ⊢ 
            aesop
          · convert folding_polynomial_deg_y_bound hq using 1
            · rw [
                Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)]  
              norm_cast
        exact lt_of_le_of_lt ‹_› 
          (max_lt 
            (by aesop) hQ'_deg)
      contrapose! hQ'_deg
      rw [hQ', natDegreeY]
      rw [Polynomial.natDegree_mul'] 
        <;> simp_all +decide only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, false_or]
      · rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt] 
          <;> norm_num [Polynomial.natDegree_C, Polynomial.natDegree_X]
        exact Nat.pos_of_ne_zero fun h ↦ by simp_all +decide [natDegreeY] 
      · intro h
        simp_all +decide [sub_eq_iff_eq_add] 
    simp_all +decide [sub_eq_iff_eq_add]

/-- If we fold a polynomial using a folding polynomial `Q`
    with appropriate degree bounds in each variable we get
    a univariate polynomial with a degree bound.
-/
lemma folded_poly_degree_bound {Q : F[X][Y]} {q : F[X]} {t : ℕ}
  (h_x : degreeX Q < t)
  (h_y : natDegreeY Q < q.natDegree) :
  ((Q.map (Polynomial.compRingHom q)).eval X).natDegree < t * q.natDegree := by
  have h : Q = foldingPolynomial q ((Q.map (Polynomial.compRingHom q)).eval X) := by
    apply folding_polynomial_is_unique
    · aesop
    · by_cases hq : q = 0
      · aesop
      · rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, 
            Polynomial.natDegree_sum_eq_of_disjoint]
        · apply le_antisymm <;> simp_all +decide only [degreeX, coe_compRingHom, Finset.sup_le_iff,
          mem_support_iff, ne_eq]
          · intro n hn
            apply Nat.le_div_iff_mul_le 
              (Nat.pos_of_ne_zero (ne_of_gt (Nat.pos_of_ne_zero (by aesop)))) |>.2 
            · apply le_trans _ 
                (Finset.le_sup 
                    (f := fun i ↦ 
                      Polynomial.natDegree 
                        (Polynomial.comp (Q.coeff i) q * Polynomial.X ^ i)) 
                    (Finset.mem_range.mpr 
                      (Nat.lt_succ_of_le 
                        (Polynomial.le_natDegree_of_ne_zero hn))))  
              simp +decide only 
              rw [Polynomial.natDegree_mul'] 
                <;> simp +decide only [
                  monic_X_pow, Monic.leadingCoeff, mul_one, ne_eq,
                  leadingCoeff_eq_zero,
                  natDegree_comp, natDegree_pow, natDegree_X, mul_one,
                  le_add_iff_nonneg_right, zero_le]
              have h_comp_nonzero : 
                Polynomial.natDegree 
                  (Polynomial.comp (Q.coeff n) q) 
                    = Polynomial.natDegree (Q.coeff n) * Polynomial.natDegree q := by
                rw [Polynomial.natDegree_comp]
              by_contra h_comp_zero
              have h_deg_zero : 
                Polynomial.natDegree (Polynomial.comp (Q.coeff n) q) = 0 := by
                rw [h_comp_zero, Polynomial.natDegree_zero]
              simp_all +decide
              cases h_comp_nonzero 
                <;> simp_all +decide 
                      [Polynomial.natDegree_eq_zero_iff_degree_le_zero]
              rw [
                Polynomial.eq_C_of_degree_le_zero ‹Polynomial.degree (Q.coeff n) ≤ 0›] 
                  at hn h_comp_zero 
              aesop
          · rw [Nat.div_le_iff_le_mul_add_pred] <;> norm_num
            · intro b hb
              have h_deg : 
                Polynomial.natDegree 
                  (Polynomial.comp (Q.coeff b) q) 
                    ≤ Polynomial.natDegree q * Polynomial.natDegree (Q.coeff b) := by
                rw [Polynomial.natDegree_comp, mul_comm]
              by_cases h : 
                Polynomial.comp (Q.coeff b) q = 0 
                  <;> simp_all +decide only [
                    natDegree_zero, zero_le, zero_mul,
                    monic_X_pow, Monic.leadingCoeff, mul_one, ne_eq,
                    leadingCoeff_eq_zero, not_false_eq_true, natDegree_mul', natDegree_pow,
                    natDegree_X, ge_iff_le]
              apply add_le_add (le_trans h_deg (Nat.mul_le_mul_left _ 
                  (Finset.le_sup 
                      (f := fun n ↦ Polynomial.natDegree (Q.coeff n)) 
                      (by aesop))))
              exact Nat.le_sub_one_of_lt 
                  (lt_of_lt_of_le (Nat.lt_succ_of_le hb) 
                      (Nat.succ_le_of_lt 
                          (lt_of_le_of_lt 
                              (Polynomial.le_natDegree_of_mem_supp _ 
                                  (by aesop)) h_y)))
            · exact Nat.pos_of_ne_zero (by aesop) 
        · intro i hi j hj hij
          simp_all +decide only [Finset.mem_range, Order.lt_add_one_iff, coe_compRingHom, ne_eq,
            mul_eq_zero, pow_eq_zero_iff', X_ne_zero, false_and, or_false, Set.mem_setOf_eq,
            Function.comp_apply, monic_X_pow, Monic.leadingCoeff, mul_one, leadingCoeff_eq_zero,
            not_false_eq_true, natDegree_mul', natDegree_comp, natDegree_pow, natDegree_X]
          by_contra h_contra
          exact hij 
            (by nlinarith 
                [show Polynomial.natDegree (Q.coeff i) 
                    = Polynomial.natDegree (Q.coeff j) 
                      by nlinarith 
                        [show i < q.natDegree 
                          from lt_of_le_of_lt 
                          (Polynomial.le_natDegree_of_ne_zero (by aesop)) h_y, 
                          show j < q.natDegree 
                          from lt_of_le_of_lt 
                            (Polynomial.le_natDegree_of_ne_zero 
                              (by aesop)) h_y]])
    · aesop
  contrapose! h_x
  rw [h, folding_polynomial_deg_x]
  exact Nat.le_div_iff_mul_le 
    (Nat.pos_of_ne_zero 
        (by rintro h; simp_all +singlePass)) |>.2 h_x

/-- Alternative uniqueness theorem for the folding polynomial.
    The only difference is the `h_x` condition which in this theorem
    is only and inequality. Handy in practice since `degreeX` is defined
    as a supremum so inequality is much easier to prove for it.
-/
theorem folding_polynomial_is_unique' {q f : Polynomial F} {Q : Polynomial (Polynomial F)}
  (h : (Q.map (Polynomial.compRingHom q)).eval Polynomial.X = f)
  (h_x : degreeX Q ≤ f.natDegree / q.natDegree)
  (h_y : natDegreeY Q < q.natDegree) :
  Q = foldingPolynomial q f := by
    by_cases hq_const : q.degree ≤ 0
    · rw [Polynomial.eq_C_of_degree_le_zero hq_const] at h h_y ⊢ 
      aesop
    · apply folding_polynomial_is_unique h (by
      have h_deg : f.natDegree ≤ degreeX Q * q.natDegree + q.natDegree - 1 := by
        have h_deg : 
          Polynomial.natDegree 
            (Polynomial.eval Polynomial.X (Polynomial.map q.compRingHom Q)) 
              ≤ degreeX Q * q.natDegree + q.natDegree - 1 := by
          have := folded_poly_degree_bound 
            (Nat.lt_succ_self _ : degreeX Q < degreeX Q + 1) 
            h_y
          exact Nat.le_sub_one_of_lt (by linarith)
        generalize_proofs at *
        aesop
      exact le_antisymm h_x <|
        Nat.le_of_lt_succ 
          (Nat.div_lt_of_lt_mul 
              <| by linarith 
                [Nat.sub_add_cancel (
                    show 1 ≤ degreeX Q * q.natDegree 
                      + q.natDegree from Nat.succ_le_iff.mpr 
                      <| by nlinarith 
                          [show q.natDegree > 0 
                            from Polynomial.natDegree_pos_iff_degree_pos.mpr 
                            <| lt_of_not_ge hq_const])]))
                            h_y

/-- Polynomial folding function that turns
    a polynomial of degree `≤n` into a polynomial
    of degree `≤n/k` for given `k`. 
    The key ingridient of FRI-related family of protocols.
-/
noncomputable def polyFold (f : F[X]) (k : ℕ) (r : F) : F[X] := 
  (foldingPolynomial (X ^ k) f).eval (C r)

@[simp high]
lemma polyFold_zero_eq_zero {k : ℕ} {r : F} :
  polyFold 0 k r = 0 := by simp [polyFold]

/-- The degree bound of `polyFold` in terms of the degree of 
    the original polynomial and `k`. -/
lemma polyFold_natDegree_le {f : F[X]} {k : ℕ} {r : F} :
  (polyFold f k r).natDegree ≤ f.natDegree / k := by
    have h_deg_le_degX : ∀ (g : F[X][Y]) (r : F), (g.eval (C r)).natDegree ≤ degreeX g := by
      intro g r
      simp only [degreeX]
      rw [Polynomial.eval_eq_sum]
      apply le_trans (Polynomial.natDegree_sum_le _ _) 
      apply Finset.sup_mono_fun
      by_cases hr : r = 0 <;> simp +decide only [mem_support_iff, ne_eq, hr, map_zero,
        Function.comp_apply]
      · intro n 
        by_cases hn : n = 0 <;> simp +decide [hn]
      · intro n hg 
        rw [Polynomial.natDegree_mul'] <;> aesop
    exact le_trans (h_deg_le_degX _ r) <| by 
      rw [folding_polynomial_deg_x] 
      aesop

end

end FoldingPolynomial
end Polynomial
