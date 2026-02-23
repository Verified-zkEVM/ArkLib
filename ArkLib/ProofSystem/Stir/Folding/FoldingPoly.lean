import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Cases

section

open Polynomial Polynomial.Bivariate 

variable {ι F : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]

noncomputable def foldingPolynomialAux (q f : F[X]) (deg : ℕ) : F[X][Y] :=
  if q.degree ≤ 0 then Polynomial.map C f else
  if f.degree < q.degree then Polynomial.map C f
  else
  match deg with
  | .zero => Polynomial.map Polynomial.C f
  | .succ deg => (Polynomial.map Polynomial.C (f % q))
    + Polynomial.C Polynomial.X * (foldingPolynomialAux q (f / q) deg)

noncomputable def foldingPolynomial (q f : F[X]) : F[X][Y] := 
  foldingPolynomialAux q f f.natDegree

lemma foldingPolynomial_def₁ {q f : F[X]}
  (h : f.degree < q.degree) :
    foldingPolynomial q f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp [h]

lemma foldingPolynomial_C {q : F} {f : F[X]} :
  foldingPolynomial (C q) f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  simp only [ite_eq_left_iff, not_le, not_lt]
  intro h 
  have hh := Polynomial.degree_C_le (a := q)
  have hh : (0 : WithBot ℕ) < 0 := by
    apply lt_of_lt_of_le h
    simp [hh]
  tauto

lemma foldingPolynomial_def₂ {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0)
  :
    foldingPolynomial q f = Polynomial.map C f := by
  unfold foldingPolynomial foldingPolynomialAux
  rcases h with h | h | h <;> try simp [h] 
  have h := Polynomial.eq_C_of_degree_le_zero h
  rw [h]
  simp

lemma foldingPolynomialAux_zero {q : F[X]} {deg : ℕ} :
    foldingPolynomialAux q 0 deg = 0 := by
    unfold foldingPolynomialAux
    aesop

lemma foldingPolynomialAux_deg_property {q f : F[X]} {deg : ℕ}
  (h : f.natDegree ≤ deg)
  :
  foldingPolynomialAux q f f.natDegree = foldingPolynomialAux q f deg := by
  have h_foldingPolynomialAux : 
    ∀ (deg₁ deg₂ : ℕ), 
      deg₁ ≥ f.natDegree → 
        deg₂ ≥ f.natDegree →
          foldingPolynomialAux q f deg₁ = foldingPolynomialAux q f deg₂ := by
      intro deg₁ deg₂ h₁ h₂
      induction' deg₁ with deg₁ ih generalizing deg₂ f;
      · simp_all +decide [ Polynomial.natDegree_eq_zero_iff_degree_le_zero ];
        rw [ Polynomial.eq_C_of_degree_le_zero h₁ ] ; simp +decide [ foldingPolynomialAux ] ;
        induction' deg₂ with deg₂ ih <;> simp_all +decide [ foldingPolynomialAux ];
        exact fun h₃ h₄ => 
          absurd h₄ 
            ( not_le_of_gt ( lt_of_le_of_lt ( Polynomial.degree_C_le ) h₃ ) );
      · rcases deg₂ with ( _ | deg₂ ) <;> simp_all +decide [ foldingPolynomialAux ];
        · -- Since $f$ is a constant polynomial, we have $f = c$ for some $c \in F$.
          obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c := by
            exact ⟨ f.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero h₂ ⟩;
          by_cases hc : c = 0 <;> simp_all +decide [ Polynomial.degree_C ];
          aesop;
        · split_ifs <;> simp_all +decide [ Polynomial.degree_eq_natDegree ];
          have h_div_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
            rw [ Polynomial.div_def ];
            rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic ];
            · rw [ Polynomial.natDegree_mul' ] <;> aesop;
            · exact Polynomial.monic_mul_leadingCoeff_inv ( by aesop );
            · aesop;
          by_cases hq : q.natDegree = 0;
          · rw [ Polynomial.degree_eq_natDegree ] at * <;> aesop;
          · exact ih ( by omega ) _ ( by omega ) ( by omega );
  exact h_foldingPolynomialAux _ _ le_rfl h

lemma foldingPolynomial_def₃ {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0)
  :
  foldingPolynomial q f = (Polynomial.map Polynomial.C (f % q))
    + Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
      have h_fold : 
        ∀ {deg : ℕ}, 
          deg ≥ f.natDegree → 
            foldingPolynomial q f = 
              Polynomial.map Polynomial.C (f % q) + 
                Polynomial.C Polynomial.X 
                  * foldingPolynomial q (f / q) := by
        intros deg hdeg
        rw [foldingPolynomial];
        have h_fold : 
          ∀ {deg : ℕ}, 
            deg ≥ f.natDegree → 
              foldingPolynomialAux q f deg = 
                Polynomial.map Polynomial.C (f % q) 
                  + Polynomial.C Polynomial.X 
                  * foldingPolynomialAux q (f / q) (deg - 1) := by
          intros deg hdeg
          induction' deg with deg ih generalizing f;
          · obtain ⟨c, hc⟩ : ∃ c : F, f = Polynomial.C c := by
              exact ⟨ f.coeff 0, Polynomial.eq_C_of_natDegree_le_zero hdeg ⟩;
            simp_all +decide;
            exact absurd h₁ ( not_le_of_gt ( lt_of_le_of_lt ( Polynomial.degree_C_le ) h₂ ) );
          · rw [foldingPolynomialAux];
            rw [ if_neg h₂.not_ge, if_neg ( not_lt_of_ge h₁ ) ];
            rfl;
        convert h_fold hdeg using 1;
        · exact foldingPolynomialAux_deg_property hdeg;
        · have h_fold_eq : 
            foldingPolynomial q (f / q) 
              = foldingPolynomialAux q (f / q) (deg - 1) := by
            have h_deg : (f / q).natDegree ≤ deg - 1 := by
              have h_deg : (f / q).natDegree ≤ f.natDegree - q.natDegree := by
                rw [ Polynomial.div_def ];
                rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic ];
                · rw [ Polynomial.natDegree_mul' ] <;> aesop;
                · exact Polynomial.monic_mul_leadingCoeff_inv ( by aesop );
                · aesop;
              exact le_trans h_deg ( Nat.sub_le_sub_right hdeg _ ) 
                |> le_trans 
                <| Nat.sub_le_sub_left ( Polynomial.natDegree_pos_iff_degree_pos.mpr h₂ ) _
            apply foldingPolynomialAux_deg_property; assumption;
          rw [h_fold_eq];
      exact h_fold le_rfl

lemma substitution_property_of_folding_polynomial {q f : F[X]}:
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X
      = f := by 
  revert q f;
  intro q f
  induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing q f
  by_cases h_deg : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0;
  · rw [ foldingPolynomial_def₂ h_deg ] ; simp +decide [ Polynomial.eval_map ];
    simp +decide [ Polynomial.eval₂_map ];
    simp +decide [ Polynomial.eval₂_eq_sum_range ];
    conv_rhs => rw [ Polynomial.as_sum_range_C_mul_X_pow f ] ;
  · have h_fold_def : 
      foldingPolynomial q f = 
        (Polynomial.map Polynomial.C (f % q)) + 
          Polynomial.C Polynomial.X * foldingPolynomial q (f / q) := by
      apply foldingPolynomial_def₃;
      · exact le_of_not_gt fun h => h_deg <| Or.inl h;
      · exact lt_of_not_ge fun h => h_deg <| Or.inr <| Or.inr h;
    have h_fold_def : 
      Polynomial.eval Polynomial.X 
        (Polynomial.map q.compRingHom (foldingPolynomial q f)) = 
          (f % q) + 
            q * Polynomial.eval Polynomial.X 
              (Polynomial.map q.compRingHom (foldingPolynomial q (f / q))) := by
      simp +decide [ h_fold_def, Polynomial.eval_map ];
      simp +decide [ Polynomial.eval₂_map ];
      simp +decide [ Polynomial.eval₂_eq_sum_range ];
      conv_rhs => rw [ Polynomial.as_sum_range_C_mul_X_pow ( f % q ) ] ;
    have h_fold_def : 
      Polynomial.eval Polynomial.X 
        (Polynomial.map q.compRingHom 
          (foldingPolynomial q (f / q))) = f / q := by
      convert ih ( Polynomial.natDegree ( f / q ) ) _ rfl using 1;
      rw [ ← n, Polynomial.div_def ];
      rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic ] <;> norm_num;
      · by_cases hq : q = 0 
          <;> simp_all +decide [ Polynomial.natDegree_mul' ];
        exact ⟨ n.symm 
          ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr 
            h_deg.2.1, 
          Polynomial.natDegree_pos_iff_degree_pos.mpr h_deg.2.2 ⟩;
      · exact Polynomial.monic_mul_leadingCoeff_inv ( by aesop );
      · aesop;
    rw [ 
      ‹Polynomial.eval Polynomial.X 
        ( Polynomial.map q.compRingHom 
          ( foldingPolynomial q f ) ) = 
            f % q + 
              q * Polynomial.eval Polynomial.X 
                ( Polynomial.map q.compRingHom 
                  ( foldingPolynomial q ( f / q ) ) ) ›, 
      h_fold_def, EuclideanDomain.mod_eq_sub_mul_div ] ; ring


lemma folding_polynomial_deg_y_bound {q f : F[X]} (h: 0 < q.degree) :
  Bivariate.natDegreeY (foldingPolynomial q f) < q.degree := by
  simp [natDegreeY]
  by_cases 

  rw [Finset.sup_lt_iff (by {
    simp
    by_contra contra
    simp at contra
    rw [Polynomial.natDegree_eq_zero] at contra
    rcases contra with ⟨x, heq⟩ 
    rw [←heq] at h
    have hh: (0 : WithBot ℕ) < 0 := by
      apply lt_of_lt_of_le h
      apply Polynomial.degree_C_le
    simp at hh
  })]
  intro b hb













    



  
    
end
