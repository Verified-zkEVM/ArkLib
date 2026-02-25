import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

namespace Polynomial.FoldingPolynomial

section

open Polynomial Polynomial.Bivariate 

variable {ι F : Type*} [Field F]   

noncomputable def foldingPolynomialAux (q f : F[X]) (fuel : ℕ) : F[X][Y] :=
  if q.degree ≤ 0 then Polynomial.map C f else
  if f.degree < q.degree then Polynomial.map C f
  else
  match fuel with
  | .zero => Polynomial.map Polynomial.C f
  | .succ fuel => (Polynomial.map Polynomial.C (f % q))
    + Polynomial.C Polynomial.X * (foldingPolynomialAux q (f / q) fuel)

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
  have hh := Polynomial.degree_C_le (a := q)
  have hh : (0 : WithBot ℕ) < 0 := by
    apply lt_of_lt_of_le h
    simp [hh]
  tauto

@[simp]
lemma foldingPolynomial_C_f {f : F} {q : F[X]} :
  foldingPolynomial q (C f) = C (C f) := by
  unfold foldingPolynomial foldingPolynomialAux
  simp

private lemma folding_polynomial_def_base_case {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0)
  :
    foldingPolynomial q f = Polynomial.map C f := by
  rcases h with h | h | h 
  · rw [folding_polynomial_eq_map_of_f_degree_lt_q_degree h]
  · rw [Polynomial.degree_le_zero_iff] at h
    rw [h]
    simp 
  · rw [Polynomial.degree_le_zero_iff] at h
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


lemma folding_polynomial_eq_zero {q f : F[X]}
  (h : foldingPolynomial q f = 0)
  :
  f = 0 := by
    induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing f;
    by_cases h₁ : 
      f.degree < q.degree 
        ∨ f.degree ≤ 0 
        ∨ q.degree ≤ 0 <;> simp_all +decide [ Polynomial.ext_iff ];
    · rw [ folding_polynomial_def_base_case h₁ ] at h;
      intro n; specialize h n 0; aesop;
    · have h_rem_zero : f % q = 0 := by
        rw [ foldingPolynomial_def₃ h₁.1 h₁.2.2 ] at h;
        ext n; specialize h n 0; simp_all +decide [ Polynomial.coeff_map ] ;
      have h_quot_zero : f / q = 0 := by
        have h_quot_zero : foldingPolynomial q (f / q) = 0 := by
          have h_quot_zero : 
            foldingPolynomial q f 
              = (Polynomial.map Polynomial.C (f % q)) 
                + Polynomial.C Polynomial.X 
                    * foldingPolynomial q (f / q) := by
            rw [ foldingPolynomial_def₃ ] <;> aesop;
          simp_all +decide [ Polynomial.ext_iff ];
          intro n n_1; specialize h n ( n_1 + 1 ) ; simp_all +decide [ Polynomial.coeff_X ] ;
        contrapose! ih;
        refine' 
          ⟨ Polynomial.natDegree ( f / q ), 
            _, 
            f / q, 
            _, 
            rfl, 
            Polynomial.natDegree ( f / q ), _ ⟩ 
              <;> simp_all +decide [ Polynomial.natDegree_divByMonic ];
        have h_deg_f : f.natDegree = q.natDegree + (f / q).natDegree := by
          rw [ ← Polynomial.natDegree_mul' ];
          · rw [ EuclideanDomain.mul_div_cancel' ] <;> aesop;
          · aesop;
        linarith [ 
          Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.1, 
          Polynomial.natDegree_pos_iff_degree_pos.mpr h₁.2.2 ];
      rw [ EuclideanDomain.mod_eq_sub_mul_div ] at h_rem_zero ; aesop

lemma substitution_property_of_folding_polynomial {q f : F[X]}:
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X
      = f := by 
  revert q f;
  intro q f
  induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing q f
  by_cases h_deg : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0;
  · rw [ folding_polynomial_def_base_case h_deg ] ; simp +decide [ Polynomial.eval_map ];
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
   natDegreeY (foldingPolynomial q f) < q.degree := by 
  simp [natDegreeY]
  induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing f q;
  by_cases hq : f.degree < q.degree 
  · have h_folding_eq_map : foldingPolynomial q f = Polynomial.map Polynomial.C f := by
      exact folding_polynomial_eq_map_of_f_degree_lt_q_degree hq;
    by_cases hf : f = 0 <;> simp_all +decide [ Polynomial.natDegree_map ];
    · exact n.symm ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr h;
    · rw [ ← n, Polynomial.degree_eq_natDegree hf ] at * ; aesop;
  · have h_fold : 
      foldingPolynomial q f = 
        (Polynomial.map Polynomial.C (f % q)) 
          + Polynomial.C Polynomial.X 
            * (foldingPolynomial q (f / q)) := by
      rw [foldingPolynomial_def₃];
      · simp at hq 
        exact hq
      · exact h;
    refine' h_fold ▸ lt_of_le_of_lt ( Polynomial.natDegree_add_le _ _ ) ( max_lt _ _ );
    · have h_deg_mod : (f % q).degree < q.degree := by
        exact EuclideanDomain.mod_lt f ( Polynomial.ne_zero_of_degree_gt h );
      by_cases h : f % q = 0 <;> simp_all +decide [ Polynomial.natDegree_map ];
      · rw [ EuclideanDomain.mod_eq_zero.mpr h ] ; 
          simp +decide [ Polynomial.natDegree_pos_iff_degree_pos.mpr ‹_› ];
      · exact Polynomial.natDegree_lt_natDegree ( by aesop ) h_deg_mod;
    · refine' lt_of_le_of_lt ( Polynomial.natDegree_C_mul_le _ _ ) _;
      refine' ih _ _ h rfl;
      rw [ ← n, Polynomial.div_def ];
      rw [ 
        Polynomial.natDegree_C_mul, 
        Polynomial.natDegree_divByMonic ] 
          <;> norm_num [ 
            Polynomial.natDegree_mul', 
            Polynomial.natDegree_C, show q ≠ 0 by aesop ];
      · simp at hq 
        exact 
          ⟨ Polynomial.natDegree_pos_iff_degree_pos.mpr 
            ( lt_of_lt_of_le h hq ),
            Polynomial.natDegree_pos_iff_degree_pos.mpr h ⟩;
      · exact Polynomial.monic_mul_leadingCoeff_inv ( by aesop )

lemma folding_polynomial_deg_x_base {q f : F[X]}
  (h : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0)
  :
  degreeX (foldingPolynomial q f) = 0 := by
  rw [folding_polynomial_def_base_case h]
  simp [degreeX]
  have h: (⊥ : ℕ) = 0 := by rfl
  rw [←h, Finset.sup_eq_bot_iff]
  simp

lemma folding_polynomial_deg_x_ind {q f : F[X]}
  (h₁ : f.degree ≥ q.degree)
  (h₂ : q.degree > 0)
  :
  degreeX (foldingPolynomial q f)
    = 1 + degreeX (foldingPolynomial q (f / q)) := by
      rw [ foldingPolynomial_def₃ h₁ h₂ ];
      refine' le_antisymm _ _ <;> simp_all +decide [ degreeX ];
      · intro n hn; 
        by_cases h : Polynomial.coeff 
          ( foldingPolynomial q ( f / q ) ) n = 0 
            <;> simp_all +decide [ Polynomial.natDegree_mul' ] ;
        exact Finset.le_sup 
          ( f := fun n => Polynomial.natDegree 
            ( Polynomial.coeff ( foldingPolynomial q ( f / q ) ) n ) ) 
            ( by aesop );
      · obtain ⟨b, hb⟩ : 
          ∃ b ∈ (foldingPolynomial q (f / q)).support, 
          ∀ n ∈ (foldingPolynomial q (f / q)).support, 
            Polynomial.natDegree 
              ((foldingPolynomial q (f / q)).coeff n) 
            ≤ 
            Polynomial.natDegree ((foldingPolynomial q (f / q)).coeff b) := by
          apply_rules [ Finset.exists_max_image ];
          by_contra h_empty_support;
          simp_all +decide [ Finset.not_nonempty_iff_eq_empty ];
          have := folding_polynomial_eq_zero h_empty_support;
          rw [ Polynomial.div_eq_zero_iff ] at this;
          · exact this.not_ge h₁;
          · aesop;
        refine' ⟨ b, _, _ ⟩ <;> simp_all +decide [ Polynomial.natDegree_mul' ];
        intro h; 
        have := congr_arg ( Polynomial.eval 0 ) h; 
        norm_num at this; 
        have := congr_arg ( Polynomial.eval 1 ) h; 
        norm_num at this; simp_all +decide [ Polynomial.eval ] ;

lemma folding_polynomial_deg_x₀ {q : F} {f : F[X]} :
  degreeX (foldingPolynomial (C q) f) = 0 := by
  rw [folding_polynomial_deg_x_base]
  right; right
  exact Polynomial.degree_C_le

lemma folding_polynomial_deg_x {q f : F[X]} :
  degreeX (foldingPolynomial q f) = f.natDegree / q.natDegree 
  := by
    by_cases h: q.degree ≤ 0
    · rw [Polynomial.degree_le_zero_iff] at h
      rw [h]
      simp
      exact folding_polynomial_deg_x₀
    · simp at h 
      induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing f q;
      by_cases h₁ : f.degree < q.degree ∨ f.degree ≤ 0 ∨ q.degree ≤ 0;
      · have h_deg_zero : degreeX (foldingPolynomial q f) = 0 := by
          exact folding_polynomial_deg_x_base h₁;
        have h_deg_zero : f.natDegree < q.natDegree := by
          by_cases hf : f = 0 
            <;> by_cases hq : q = 0 
            <;> simp_all +decide [ Polynomial.degree_eq_natDegree ];
          aesop;
        rw [ Nat.div_eq_of_lt ] <;> aesop;
      · have h_deg : 
          degreeX (foldingPolynomial q f) = 1 + degreeX (foldingPolynomial q (f / q)) := by
          apply folding_polynomial_deg_x_ind;
          · exact le_of_not_gt fun h₂ => h₁ <| Or.inl h₂;
          · exact h;
        have h_deg_f_div_q : (f / q).natDegree = f.natDegree - q.natDegree := by
          rw [ Polynomial.div_def ];
          rw [ Polynomial.natDegree_C_mul, Polynomial.natDegree_divByMonic ];
          · rw [ Polynomial.natDegree_mul' ] <;> aesop;
          · exact Polynomial.monic_mul_leadingCoeff_inv ( Polynomial.ne_zero_of_degree_gt h );
          · aesop;
        rw [ h_deg, ih _ _ h h_deg_f_div_q ];
        · rw [ ← n, Nat.add_comm ];
          rw [ 
            ← Nat.sub_add_cancel ( show q.natDegree ≤ f.natDegree from ?_ ), 
            Nat.add_div ] 
            <;> norm_num [ Polynomial.natDegree_pos_iff_degree_pos.mpr h ];
          · exact Nat.mod_lt _ ( Polynomial.natDegree_pos_iff_degree_pos.mpr h );
          · exact 
              Polynomial.natDegree_le_natDegree 
                ( le_of_not_gt fun h' => 
                    h₁ <| Or.inl 
                      <| by rw [ 
                        Polynomial.degree_eq_natDegree, 
                        Polynomial.degree_eq_natDegree ] at * <;> aesop );
        · rw [ ← n ];
          exact Nat.sub_lt 
            ( Polynomial.natDegree_pos_iff_degree_pos.mpr 
                ( lt_of_not_ge fun h => h₁
                  <| Or.inr <| Or.inl h ) ) 
            ( Polynomial.natDegree_pos_iff_degree_pos.mpr h )   

lemma folding_polynomial_deg_x_bound {q f : F[X]} {t : ℕ}
  (h : f.natDegree < t * q.natDegree)
  :
  degreeX (foldingPolynomial q f) < t := by
  rw [folding_polynomial_deg_x]
  by_cases heq: q.natDegree = 0
  · simp [heq] at h
  · apply Nat.lt_of_mul_lt_mul_right (a := q.natDegree) 
    apply Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _)
    assumption

lemma satisfies_conditions_implies_is_the_reminder
  {q f : F[X]}
  {Q : F[X][Y]}
  (h : (Q.map (Polynomial.compRingHom q)).eval X = f)
  :
  ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + Q := by
      obtain ⟨Q', hQ'⟩ : 
        ∃ Q' : F[X][Y], 
          Q - Polynomial.map (Polynomial.C) f 
            = (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) * Q' := by
        have h_div : 
          (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) 
            ∣ Q - Polynomial.map (Polynomial.C) 
                    (Polynomial.eval Polynomial.X 
                        (Polynomial.map 
                            (Polynomial.compRingHom q) Q)) := by
          have h_div : 
            ∀ p : F[X][Y], 
              (Polynomial.C Polynomial.X - Polynomial.map Polynomial.C q) 
                ∣ p - Polynomial.map Polynomial.C 
                  (Polynomial.eval Polynomial.X 
                    (Polynomial.map (Polynomial.compRingHom q) p)) := by
            intro p;
            induction' p using Polynomial.induction_on' with p q hp hq;
            · convert dvd_add hp hq using 1 ; simp +decide [ sub_add_sub_comm ];
            · induction' ‹ℕ› with n ih 
                <;> simp_all +decide [ 
                      pow_succ, 
                      ← mul_assoc, 
                      ← Polynomial.C_mul_X_pow_eq_monomial ];
              · induction' ‹F[X]› using 
                  Polynomial.induction_on' with p q hp hq 
                    <;> simp_all +decide [ ← Polynomial.C_mul_X_pow_eq_monomial ];
                · convert dvd_add hp hq using 1 ; ring;
                · exact dvd_trans 
                    ( sub_dvd_pow_sub_pow _ _ _ ) 
                    ( by exact ⟨ Polynomial.C ( Polynomial.C ‹_› ), by ring ⟩ );
              · simpa only [ sub_mul ] using ih.mul_right _;
          exact h_div Q;
        aesop;
      exact ⟨ -Q', by linear_combination -hQ' ⟩

lemma folding_polynomial_is_the_reminder {q f : F[X]} :
  ∃ Q': F[X][Y],
    Polynomial.map C f = Q' * (C X - Polynomial.map C q) + (foldingPolynomial q f) := by 
    apply satisfies_conditions_implies_is_the_reminder
    exact substitution_property_of_folding_polynomial

lemma folding_polynomial_is_unique {q f : F[X]} {Q : F[X][Y]} 
  (h : (Q.map (Polynomial.compRingHom q)).eval X = f)
  (h_x : degreeX Q = f.natDegree / q.natDegree)
  (h_y : natDegreeY Q < q.degree)
  :
  Q = foldingPolynomial q f 
  := by 
    by_contra h_contra;
    obtain ⟨Q', hQ'⟩ : 
      ∃ Q' : F[X][Y], 
        Q - foldingPolynomial q f 
          = Q' * (C Polynomial.X - Polynomial.map (Polynomial.C) q) := by
      obtain ⟨ Q', hQ' ⟩ 
        := satisfies_conditions_implies_is_the_reminder 
          ( show ( ( Q.map ( Polynomial.compRingHom q ) 
            |> Polynomial.eval Polynomial.X ) ) = f from h );
      obtain ⟨ Q'', hQ'' ⟩ 
        := satisfies_conditions_implies_is_the_reminder 
          ( show ( ( foldingPolynomial q f 
            |> Polynomial.map ( Polynomial.compRingHom q ) 
            |> Polynomial.eval Polynomial.X ) ) = f from by exact
              substitution_property_of_folding_polynomial );
      exact ⟨ Q'' - Q', by linear_combination' hQ'' - hQ' ⟩;
    have hQ'_zero : Q' = 0 := by
      have hQ'_deg : natDegreeY (Q - foldingPolynomial q f) < q.natDegree := by
        have hQ'_deg : 
          natDegreeY (Q - foldingPolynomial q f) 
            ≤ max (natDegreeY Q) (natDegreeY (foldingPolynomial q f)) := by
          convert Polynomial.natDegree_sub_le _ _ using 1;
        have hQ'_deg : natDegreeY (foldingPolynomial q f) < q.natDegree := by
          by_cases hq : q.degree ≤ 0 
            <;> simp_all +decide [ Polynomial.degree_eq_natDegree ];
          · rw [ Polynomial.eq_C_of_degree_le_zero hq ] at h_y h_contra hQ' ⊢ ; aesop;
          · convert folding_polynomial_deg_y_bound hq using 1;
            rw [ 
              Polynomial.degree_eq_natDegree ( Polynomial.ne_zero_of_degree_gt hq ) ] ; 
            norm_cast;
        exact lt_of_le_of_lt ‹_› 
          ( max_lt 
            ( by rw [ Polynomial.degree_eq_natDegree ] at h_y <;> aesop ) hQ'_deg );
      contrapose! hQ'_deg;
      rw [ hQ', natDegreeY ];
      rw [ Polynomial.natDegree_mul' ] 
        <;> simp_all +decide [ 
          Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
      · rw [ Polynomial.natDegree_sub_eq_right_of_natDegree_lt ] 
          <;> norm_num [ Polynomial.natDegree_C, Polynomial.natDegree_X ];
        exact Nat.pos_of_ne_zero fun h => by simp_all +decide [ natDegreeY ] ;
      · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
    simp_all +decide [ sub_eq_iff_eq_add ]

lemma folded_poly_degree_bound {Q : F[X][Y]} {q : F[X]} {t : ℕ}
  (h_x : degreeX Q < t)
  (h_y : natDegreeY Q < q.natDegree)
  :
  ((Q.map (Polynomial.compRingHom q)).eval X).natDegree < t * q.natDegree := by
  have h : Q = foldingPolynomial q ((Q.map (Polynomial.compRingHom q)).eval X) := by
    apply folding_polynomial_is_unique; aesop;
    · by_cases hq : q = 0;
      · aesop;
      · rw [ Polynomial.eval_map ];
        rw [ Polynomial.eval₂_eq_sum_range ];
        rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
        · refine' le_antisymm _ _ <;> simp_all +decide [ degreeX ];
          · intro n hn; refine' Nat.le_div_iff_mul_le ( Nat.pos_of_ne_zero _ ) |>.2 _;
            · exact ne_of_gt ( Nat.pos_of_ne_zero ( by aesop ) );
            · refine' le_trans _ 
                ( Finset.le_sup 
                    ( f := fun i => 
                      Polynomial.natDegree 
                        ( Polynomial.comp ( Q.coeff i ) q * Polynomial.X ^ i ) ) 
                    ( Finset.mem_range.mpr 
                      ( Nat.lt_succ_of_le 
                        ( Polynomial.le_natDegree_of_ne_zero hn ) ) ) ) ; 
              simp +decide [ Polynomial.natDegree_comp, Polynomial.natDegree_mul', hq ];
              rw [ Polynomial.natDegree_mul' ] 
                <;> simp +decide [ Polynomial.natDegree_comp, hq ];
              have h_comp_nonzero : 
                Polynomial.natDegree 
                  (Polynomial.comp (Q.coeff n) q) 
                    = Polynomial.natDegree (Q.coeff n) * Polynomial.natDegree q := by
                rw [ Polynomial.natDegree_comp ];
              by_contra h_comp_zero
              have h_deg_zero : 
                Polynomial.natDegree (Polynomial.comp (Q.coeff n) q) = 0 := by
                rw [ h_comp_zero, Polynomial.natDegree_zero ];
              simp_all +decide [ Polynomial.natDegree_comp ];
              cases h_comp_nonzero 
                <;> simp_all +decide 
                      [ Polynomial.natDegree_eq_zero_iff_degree_le_zero ];
              rw [ 
                Polynomial.eq_C_of_degree_le_zero ‹ Polynomial.degree ( Q.coeff n ) ≤ 0 › ] 
                  at hn h_comp_zero ; 
                aesop;
          · rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
            · intro b hb
              have h_deg : 
                Polynomial.natDegree 
                  (Polynomial.comp (Q.coeff b) q) 
                    ≤ Polynomial.natDegree q * Polynomial.natDegree (Q.coeff b) := by
                rw [ Polynomial.natDegree_comp, mul_comm ];
              by_cases h : 
                Polynomial.comp ( Q.coeff b ) q = 0 
                  <;> simp_all +decide [ Polynomial.natDegree_mul' ];
              refine' add_le_add ( le_trans h_deg _ ) _;
              · exact Nat.mul_le_mul_left _ 
                  ( Finset.le_sup 
                      ( f := fun n => Polynomial.natDegree ( Q.coeff n ) ) 
                      ( by aesop ) );
              · exact Nat.le_sub_one_of_lt 
                  ( lt_of_lt_of_le hb 
                      ( Nat.succ_le_of_lt 
                          ( lt_of_le_of_lt 
                              ( Polynomial.le_natDegree_of_mem_supp _ 
                                  ( by aesop ) ) h_y ) ) );
            · exact Nat.pos_of_ne_zero ( by aesop );
        · intro i hi j hj hij; 
          simp_all +decide [ 
            Polynomial.natDegree_mul', 
            Polynomial.natDegree_comp ] ;
          by_contra h_contra;
          exact hij 
            ( by nlinarith 
                [ show Polynomial.natDegree ( Q.coeff i ) 
                    = Polynomial.natDegree ( Q.coeff j ) 
                      by nlinarith 
                        [ show i < q.natDegree 
                          from lt_of_le_of_lt 
                          ( Polynomial.le_natDegree_of_ne_zero ( by aesop ) ) h_y, 
                          show j < q.natDegree 
                          from lt_of_le_of_lt 
                            ( Polynomial.le_natDegree_of_ne_zero 
                              ( by aesop ) ) h_y ] ] );
    · rw [ Polynomial.degree_eq_natDegree ] <;> aesop
  contrapose! h_x;
  rw [ h, folding_polynomial_deg_x ];
  exact Nat.le_div_iff_mul_le 
    ( Nat.pos_of_ne_zero 
        ( by rintro h; simp_all +singlePass ) ) |>.2 h_x

end

end Polynomial.FoldingPolynomial
