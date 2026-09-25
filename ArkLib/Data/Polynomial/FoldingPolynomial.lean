/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic)
-/
module

public import ArkLib.Data.Polynomial.Bivariate

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.LinearCombinationPrime
public import CompPoly.Univariate.ToPoly.Impl

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

@[expose] public section

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

private lemma natDegree_div_eq_sub_of_degree_le {q f : F[X]}
    (hq : q ≠ 0) (hdeg : q.degree ≤ f.degree) :
    (f / q).natDegree = f.natDegree - q.natDegree := by
  have hdiv : f / q ≠ 0 :=
    mt (Polynomial.div_eq_zero_iff hq).mp (not_lt_of_ge hdeg)
  have hadd := Polynomial.degree_add_div hq hdeg
  rw [Polynomial.degree_eq_natDegree hq,
    Polynomial.degree_eq_natDegree hdiv] at hadd
  have hf : f ≠ 0 := by
    intro hf
    subst f
    exact hq (Polynomial.degree_eq_bot.mp (bot_unique hdeg))
  rw [Polynomial.degree_eq_natDegree hf] at hadd
  norm_cast at hadd
  omega

private lemma foldingPolynomialAux_of_base {q f : F[X]} {fuel : ℕ}
    (h : q.degree ≤ 0 ∨ f.degree < q.degree) :
    foldingPolynomialAux q f fuel = Polynomial.map C f := by
  rcases h with h | h <;> cases fuel <;> simp only [foldingPolynomialAux, h, ↓reduceIte, ite_self]

private lemma foldingPolynomialAux_succ {q f : F[X]} {fuel : ℕ}
    (hq : 0 < q.degree) (hf : q.degree ≤ f.degree) :
    foldingPolynomialAux q f (fuel + 1) =
      Polynomial.map C (f % q) + C X * foldingPolynomialAux q (f / q) fuel := by
  rw [foldingPolynomialAux, ite_eq_right hq.not_ge, ite_eq_right hf.not_gt]

private lemma folding_polynomial_aux_natDegree_fuel_is_enough {q f : F[X]} {fuel : ℕ}
  (h : f.natDegree ≤ fuel) :
  foldingPolynomialAux q f f.natDegree = foldingPolynomialAux q f fuel := by
  suffices H : ∀ (fuel₁ fuel₂ : ℕ) (f : F[X]), f.natDegree ≤ fuel₁ → f.natDegree ≤ fuel₂ →
      foldingPolynomialAux q f fuel₁ = foldingPolynomialAux q f fuel₂ from H _ _ f le_rfl h
  intro fuel₁
  induction fuel₁ with
  | zero =>
    intro fuel₂ f h₁ _
    have hb : q.degree ≤ 0 ∨ f.degree < q.degree := by
      by_contra! hb
      exact (natDegree_pos_iff_degree_pos.mpr (hb.1.trans_le hb.2)).ne' (Nat.le_zero.1 h₁)
    rw [foldingPolynomialAux_of_base hb, foldingPolynomialAux_of_base hb]
  | succ fuel₁ ih =>
    intro fuel₂ f h₁ h₂
    by_cases hb : q.degree ≤ 0 ∨ f.degree < q.degree
    · rw [foldingPolynomialAux_of_base hb, foldingPolynomialAux_of_base hb]
    push Not at hb
    obtain ⟨hq, hf⟩ := hb
    have hdiv := natDegree_div_eq_sub_of_degree_le (ne_zero_of_degree_gt hq) hf
    have hqpos := natDegree_pos_iff_degree_pos.mpr hq
    have hfpos := natDegree_pos_iff_degree_pos.mpr (hq.trans_le hf)
    obtain ⟨fuel₂, rfl⟩ : ∃ n, fuel₂ = n + 1 := ⟨fuel₂ - 1, by omega⟩
    rw [foldingPolynomialAux_succ hq hf, foldingPolynomialAux_succ hq hf,
      ih fuel₂ (f / q) (by omega) (by omega)]

private lemma folding_polynomial_def_ind_case {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0) :
  foldingPolynomial q f = (Polynomial.map Polynomial.C (f % q)) +
    Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
  have hqpos := natDegree_pos_iff_degree_pos.mpr h₂
  have hfpos := natDegree_pos_iff_degree_pos.mpr (h₂.trans_le h₁)
  have hdiv := natDegree_div_eq_sub_of_degree_le (ne_zero_of_degree_gt h₂) h₁
  obtain ⟨n, hn⟩ : ∃ n, f.natDegree = n + 1 := ⟨f.natDegree - 1, by omega⟩
  rw [foldingPolynomial, hn, foldingPolynomialAux_succ h₂ h₁, foldingPolynomial,
    folding_polynomial_aux_natDegree_fuel_is_enough (fuel := n) (by omega)]

lemma substitution_property_of_folding_polynomial {q f : F[X]} :
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X = f := by
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
        have hqpos : 0 < q.degree :=
          lt_of_not_ge fun h => h_deg (Or.inr (Or.inr h))
        have hfpos : 0 < f.degree :=
          lt_of_not_ge fun h => h_deg (Or.inr (Or.inl h))
        have hqle : q.degree ≤ f.degree :=
          le_of_not_gt fun h => h_deg (Or.inl h)
        rw [←n, natDegree_div_eq_sub_of_degree_le
          (Polynomial.ne_zero_of_degree_gt hqpos) hqle]
        exact Nat.sub_lt
          (Polynomial.natDegree_pos_iff_degree_pos.mpr hfpos)
          (Polynomial.natDegree_pos_iff_degree_pos.mpr hqpos)
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

/-- If the folding polynomial is zero
  then so is the original polynomial. -/
lemma eq_zero_of_folding_polynomial_eq_zero {q f : F[X]}
    (h : foldingPolynomial q f = 0) : f = 0 := by
  rw [← substitution_property_of_folding_polynomial (q := q) (f := f), h, Polynomial.map_zero,
    eval_zero]

lemma folding_polynomial_ne_zero_of_ne_zero {q f : F[X]}
    (h : f ≠ 0) : foldingPolynomial q f ≠ 0 := fun contra ↦ by
  simp_all [eq_zero_of_folding_polynomial_eq_zero contra]

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
   simp +decide [Polynomial.eval_finsetSum])

/-- A means to evaluate the original polynomial in terms of
  the folding polynomial when `q = X ^ k`. -/
lemma eval_property_of_folding_polynomial_x_k {f : F[X]} {k : ℕ} {x : F} :
    ((foldingPolynomial (X ^ k) f).map (Polynomial.evalRingHom (x ^ k))).eval x =
    f.eval x := by
  simpa only [Polynomial.eval_X_pow] using
    (eval_property_of_folding_polynomial (f := f) (q := X ^ k) (x := x))

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
      have hqle : q.degree ≤ f.degree := le_of_not_gt hq
      rw [←n, natDegree_div_eq_sub_of_degree_le
        (Polynomial.ne_zero_of_degree_gt h) hqle]
      exact Nat.sub_lt
        (Polynomial.natDegree_pos_iff_degree_pos.mpr (lt_of_lt_of_le h hqle))
        (Polynomial.natDegree_pos_iff_degree_pos.mpr h)
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
      have hqpos : 0 < q.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr h
      by_cases h₁ : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0
      · have h_deg_zero : f.natDegree < q.natDegree := by
          by_cases hf : f = 0
          · rw [hf, natDegree_zero]; exact hqpos
          · rcases h₁ with hlt | hle | hqle
            · exact Polynomial.natDegree_lt_natDegree hf hlt
            · rw [Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hle]
              exact hqpos
            · exact (not_lt_of_ge hqle h).elim
        rw [folding_polynomial_deg_x_base h₁, ← n, Nat.div_eq_of_lt h_deg_zero]
      · have hle : q.degree ≤ f.degree := le_of_not_gt fun h' => h₁ (Or.inl h')
        have h_deg_f_div_q : (f / q).natDegree = f.natDegree - q.natDegree :=
          natDegree_div_eq_sub_of_degree_le (Polynomial.ne_zero_of_degree_gt h) hle
        have hfpos : 0 < f.natDegree :=
          Polynomial.natDegree_pos_iff_degree_pos.mpr (h.trans_le hle)
        rw [folding_polynomial_deg_x_ind hle h, ih _ (by omega) h h_deg_f_div_q, ← n,
          Nat.div_eq_sub_div hqpos (Polynomial.natDegree_le_natDegree hle), Nat.add_comm]

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
      obtain ⟨Q', hQ'⟩ := satisfies_composition_property_implies_is_the_reminder
          (show ((Q.map (Polynomial.compRingHom q)
            |> Polynomial.eval Polynomial.X)) = f from h)
      obtain ⟨Q'', hQ''⟩ := satisfies_composition_property_implies_is_the_reminder
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
          unfold natDegreeY
          exact Polynomial.natDegree_sub_le _ _
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
  have hq : 0 < q.natDegree := (Nat.zero_le _).trans_lt h_y
  have h_term : ∀ i ∈ Q.support, ((Q.coeff i).comp q * X ^ i).natDegree ≤
      degreeX Q * q.natDegree + (q.natDegree - 1) := by
    intro i hi
    refine natDegree_mul_le.trans (add_le_add ?_ ?_)
    · rw [natDegree_comp]
      exact Nat.mul_le_mul_right _ (Finset.le_sup (f := fun n ↦ (Q.coeff n).natDegree) hi)
    · have := le_natDegree_of_mem_supp i hi
      rw [natDegree_X_pow]
      unfold natDegreeY at h_y
      omega
  have h_sum : ((Q.map (Polynomial.compRingHom q)).eval X).natDegree ≤
      degreeX Q * q.natDegree + (q.natDegree - 1) := by
    rw [eval_map, eval₂_eq_sum, Polynomial.sum_def]
    exact natDegree_sum_le_of_forall_le _ _ h_term
  calc _ ≤ degreeX Q * q.natDegree + (q.natDegree - 1) := h_sum
    _ < (degreeX Q + 1) * q.natDegree := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ t * q.natDegree := Nat.mul_le_mul_right _ h_x

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
  refine folding_polynomial_is_unique h (le_antisymm h_x (Nat.le_of_lt_succ ?_)) h_y
  have h_deg := folded_poly_degree_bound (Nat.lt_succ_self (degreeX Q)) h_y
  rw [h, Nat.mul_comm] at h_deg
  exact Nat.div_lt_of_lt_mul h_deg

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

section PolyFoldRecurrence

variable {F : Type*} [Field F]

/-- Iterating `Polynomial.divX` shifts coefficients down by the iteration count. -/
private lemma coeff_iterate_divX (f : F[X]) (k n : ℕ) :
    (Polynomial.divX^[k] f).coeff n = f.coeff (n + k) := by
  induction k generalizing f n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, coeff_divX, ih]
    congr 1; omega

/-- Iterating `Polynomial.divX` decreases the natural degree by the iteration count. -/
private lemma natDegree_iterate_divX_le_poly (f : F[X]) (k : ℕ) :
    (Polynomial.divX^[k] f).natDegree ≤ f.natDegree - k := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    refine le_trans (Nat.sub_le_sub_right (ih f) 1) ?_
    omega

/-- Decomposition `f = (low part) + X^k * (Polynomial.divX^[k] f)` matching the
    quotient/remainder pair of dividing by `X^k`. -/
private lemma X_pow_div_mod_decomp (f : F[X]) (k : ℕ) :
    (∑ i ∈ Finset.range k, Polynomial.C (f.coeff i) * X^i)
      + X^k * Polynomial.divX^[k] f = f := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow_mul',
      coeff_iterate_divX]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hnk : n < k
  · have hkn : ¬ k ≤ n := not_le.mpr hnk
    simp only [hkn, ↓reduceIte, add_zero]
    rw [Finset.sum_eq_single n]
    · simp
    · intros b _ hbn; simp [Ne.symm hbn]
    · intro h; exact absurd (Finset.mem_range.mpr hnk) h
  · have hnk : k ≤ n := not_lt.mp hnk
    rw [Finset.sum_eq_zero, zero_add, ite_eq_left hnk]
    · congr 1; omega
    intros i hi
    rw [Finset.mem_range] at hi
    have : ¬ n = i := by omega
    simp [this]

/-- Quotient and remainder of `f` by `X^k`: the quotient is `Polynomial.divX^[k] f`
    and the remainder is `∑ i<k, C (f.coeff i) * X^i`. -/
private lemma divByMonic_modByMonic_X_pow (f : F[X]) (k : ℕ) :
    f /ₘ X^k = Polynomial.divX^[k] f
    ∧ f %ₘ X^k = ∑ i ∈ Finset.range k, Polynomial.C (f.coeff i) * X^i := by
  refine div_modByMonic_unique _ _ (monic_X_pow k) ⟨?_, ?_⟩
  · exact X_pow_div_mod_decomp f k
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Polynomial.degree_X_pow]
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mpr ?_
    intros i hi
    rw [Finset.mem_range] at hi
    exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr hi)

/-- Evaluating `Polynomial.map C f` at `C r` recovers `C (f.eval r)`. -/
private lemma eval_C_map_C (f : F[X]) (r : F) :
    (Polynomial.map Polynomial.C f).eval (Polynomial.C r) = Polynomial.C (f.eval r) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
      Polynomial.eval_eq_sum_range, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow]

/-- Evaluating the remainder `f %ₘ X^k` at `r` is the truncated Horner sum. -/
private lemma modByMonic_X_pow_eval (f : F[X]) (k : ℕ) (r : F) :
    (f %ₘ X^k).eval r = ∑ i ∈ Finset.range k, f.coeff i * r^i := by
  rw [(divByMonic_modByMonic_X_pow f k).2, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

/-- Base case of `polyFold`: when `k = 0` or `f` has degree below `k`,
    `polyFold f k r = C (f.eval r)`. -/
lemma polyFold_base {f : F[X]} {k : ℕ} {r : F} (h : k = 0 ∨ f.natDegree < k) :
    polyFold f k r = Polynomial.C (f.eval r) := by
  unfold polyFold
  have h_deg : f.degree < (X^k : F[X]).degree ∨ f.degree ≤ 0 ∨ (X^k : F[X]).degree ≤ 0 := by
    rcases h with rfl | hlt
    · right; right
      rw [pow_zero]; simp
    · left
      rw [Polynomial.degree_X_pow]
      by_cases hf : f = 0
      · rw [hf, Polynomial.degree_zero]; exact WithBot.bot_lt_coe k
      · rw [Polynomial.degree_eq_natDegree hf]; exact_mod_cast hlt
  rw [folding_polynomial_def_base_case h_deg]
  exact eval_C_map_C f r

/-- Recursive case of `polyFold`: when `0 < k ≤ f.natDegree`,
    `polyFold f k r = C ((f %ₘ X^k).eval r) + X * polyFold (f /ₘ X^k) k r`. -/
lemma polyFold_step {f : F[X]} {k : ℕ} {r : F} (hk : 0 < k) (hf : k ≤ f.natDegree) :
    polyFold f k r =
      Polynomial.C ((f %ₘ X^k).eval r) + X * polyFold (f /ₘ X^k) k r := by
  unfold polyFold
  have h_deg_q : 0 < (X^k : F[X]).degree := by
    rw [Polynomial.degree_X_pow]; exact_mod_cast hk
  have h_deg_f : (X^k : F[X]).degree ≤ f.degree := by
    rw [Polynomial.degree_X_pow]
    have hf0 : f ≠ 0 := by
      rintro rfl; simp at hf; omega
    rw [Polynomial.degree_eq_natDegree hf0]; exact_mod_cast hf
  rw [folding_polynomial_def_ind_case h_deg_f h_deg_q]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, eval_C_map_C]
  rw [show f / X^k = f /ₘ X^k from
        (divByMonic_eq_div f (Polynomial.monic_X_pow k)).symm,
      show f % X^k = f %ₘ X^k from
        (modByMonic_eq_mod f (Polynomial.monic_X_pow k)).symm]

end PolyFoldRecurrence

end

end FoldingPolynomial
end Polynomial

namespace CompPoly.CPolynomial.FoldingPolynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-- Auxiliary fuel-driven recurrence for `cpolyFold`. The recurrence mirrors the
    structure of Mathlib's `Polynomial.FoldingPolynomial.polyFold`, but operates on
    `CPolynomial F` directly so the resulting function is computable. The boundary
    conditions return `C (p.eval r)`; the recursive case decomposes `p` against
    `X^k` using iterated `divX` for the quotient and an explicit Horner sum for
    the low-coefficient part. -/
def cpolyFoldAux (p : CompPoly.CPolynomial F) (k : ℕ) (r : F) : ℕ → CompPoly.CPolynomial F
  | 0 => CompPoly.CPolynomial.C (p.eval r)
  | fuel + 1 =>
    if k = 0 then CompPoly.CPolynomial.C (p.eval r)
    else if p.natDegree < k then CompPoly.CPolynomial.C (p.eval r)
    else
      CompPoly.CPolynomial.C (∑ i ∈ Finset.range k, p.coeff i * r ^ i)
        + CompPoly.CPolynomial.X
            * cpolyFoldAux (CompPoly.CPolynomial.divX^[k] p) k r fuel

/-- Computable polynomial folding for `CPolynomial`. The fuel is set to
    `p.natDegree`, which suffices because each recursive call drops the natural
    degree by at least `k ≥ 1`. -/
def cpolyFold (p : CompPoly.CPolynomial F) (k : ℕ) (r : F) : CompPoly.CPolynomial F :=
  cpolyFoldAux p k r p.natDegree

omit [DecidableEq F] in
private lemma toPoly_iterate_divX (p : CompPoly.CPolynomial F) (k : ℕ) :
    (CompPoly.CPolynomial.divX^[k] p).toPoly = Polynomial.divX^[k] p.toPoly := by
  classical
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, Function.iterate_succ',
        Function.comp_apply, CompPoly.CPolynomial.divX_toPoly, ih]

omit [DecidableEq F] in
private lemma natDegree_iterate_divX_le (p : CompPoly.CPolynomial F) (k : ℕ) :
    (CompPoly.CPolynomial.divX^[k] p).natDegree ≤ p.natDegree - k := by
  classical
  have h_p : p.natDegree = p.toPoly.natDegree := CompPoly.CPolynomial.natDegree_toPoly p
  have h_iter : (CompPoly.CPolynomial.divX^[k] p).natDegree
      = (Polynomial.divX^[k] p.toPoly).natDegree := by
    rw [CompPoly.CPolynomial.natDegree_toPoly, toPoly_iterate_divX]
  rw [h_iter, h_p]
  exact Polynomial.FoldingPolynomial.natDegree_iterate_divX_le_poly p.toPoly k

private lemma cpolyFoldAux_toPoly (p : CompPoly.CPolynomial F) (k : ℕ) (r : F)
    (fuel : ℕ) (h_fuel : p.natDegree ≤ fuel) :
    (cpolyFoldAux p k r fuel).toPoly =
      Polynomial.FoldingPolynomial.polyFold p.toPoly k r := by
  induction fuel generalizing p with
  | zero =>
    rw [Nat.le_zero] at h_fuel
    have h_pdeg : p.toPoly.natDegree = 0 := by
      rw [← CompPoly.CPolynomial.natDegree_toPoly]; exact h_fuel
    simp only [cpolyFoldAux]
    rw [CompPoly.CPolynomial.C_toPoly, CompPoly.CPolynomial.eval_toPoly]
    by_cases hk : k = 0
    · rw [Polynomial.FoldingPolynomial.polyFold_base (Or.inl hk)]
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      rw [Polynomial.FoldingPolynomial.polyFold_base (Or.inr (h_pdeg ▸ hk_pos))]
  | succ fuel ih =>
    by_cases hk : k = 0
    · subst hk
      simp only [cpolyFoldAux, ↓reduceIte]
      rw [CompPoly.CPolynomial.C_toPoly, CompPoly.CPolynomial.eval_toPoly,
          Polynomial.FoldingPolynomial.polyFold_base (Or.inl rfl)]
    · by_cases hsmall : p.natDegree < k
      · have hsmall' : p.toPoly.natDegree < k := by
          rw [← CompPoly.CPolynomial.natDegree_toPoly]; exact hsmall
        simp only [cpolyFoldAux, hk, ↓reduceIte, hsmall]
        rw [CompPoly.CPolynomial.C_toPoly, CompPoly.CPolynomial.eval_toPoly,
            Polynomial.FoldingPolynomial.polyFold_base (Or.inr hsmall')]
      · have hsmall : k ≤ p.natDegree := not_lt.mp hsmall
        have hsmall' : k ≤ p.toPoly.natDegree := by
          rw [← CompPoly.CPolynomial.natDegree_toPoly]; exact hsmall
        have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        have h_not_lt : ¬ p.natDegree < k := not_lt.mpr hsmall
        simp only [cpolyFoldAux]
        rw [ite_eq_right hk, ite_eq_right h_not_lt]
        have h_step : (CompPoly.CPolynomial.divX^[k] p).natDegree ≤ fuel := by
          refine le_trans (natDegree_iterate_divX_le p k) ?_
          omega
        rw [Polynomial.FoldingPolynomial.polyFold_step hk_pos hsmall']
        rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.C_toPoly,
            CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.X_toPoly]
        congr 1
        · rw [Polynomial.FoldingPolynomial.modByMonic_X_pow_eval]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [CompPoly.CPolynomial.coeff_toPoly]
        · rw [ih _ h_step, toPoly_iterate_divX,
              (Polynomial.FoldingPolynomial.divByMonic_modByMonic_X_pow p.toPoly k).1]

/-- Bridge lemma: pushing `cpolyFold` through `toPoly` recovers Mathlib's `polyFold`. This is the
    bridge that turns any theorem stated about Mathlib `polyFold` into one about `cpolyFold`. -/
@[simp]
lemma cpolyFold_toPoly (p : CompPoly.CPolynomial F) (k : ℕ) (r : F) :
    (cpolyFold p k r).toPoly = Polynomial.FoldingPolynomial.polyFold p.toPoly k r :=
  cpolyFoldAux_toPoly p k r p.natDegree le_rfl

@[simp]
lemma cpolyFold_zero_eq_zero {k : ℕ} {r : F} :
    cpolyFold (0 : CompPoly.CPolynomial F) k r = 0 := by
  apply (CompPoly.CPolynomial.toPoly_eq_zero_iff
    (cpolyFold (0 : CompPoly.CPolynomial F) k r)).mp
  rw [cpolyFold_toPoly, CompPoly.CPolynomial.toPoly_zero,
      Polynomial.FoldingPolynomial.polyFold_zero_eq_zero]

/-- The natural-degree bound for `cpolyFold`, transported from the Mathlib version. -/
lemma cpolyFold_natDegree_le {p : CompPoly.CPolynomial F} {k : ℕ} {r : F} :
    (cpolyFold p k r).natDegree ≤ p.natDegree / k := by
  rw [CompPoly.CPolynomial.natDegree_toPoly, cpolyFold_toPoly,
      CompPoly.CPolynomial.natDegree_toPoly]
  exact Polynomial.FoldingPolynomial.polyFold_natDegree_le

end CompPoly.CPolynomial.FoldingPolynomial
