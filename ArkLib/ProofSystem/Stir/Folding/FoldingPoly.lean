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


lemma folding_polynomial_eq_zero {q f : F[X]}
  (h : foldingPolynomial q f = 0)
  :
  f = 0 := by
    induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing f;
    by_cases h₁ : 
      f.degree < q.degree 
        ∨ f.degree ≤ 0 
        ∨ q.degree ≤ 0 <;> simp_all +decide [ Polynomial.ext_iff ];
    · rw [ foldingPolynomial_def₂ h₁ ] at h;
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
   natDegreeY (foldingPolynomial q f) < q.degree := by 
  simp [natDegreeY]
  induction' n : f.natDegree using Nat.strong_induction_on with n ih generalizing f q;
  by_cases hq : f.degree < q.degree 
  · have h_folding_eq_map : foldingPolynomial q f = Polynomial.map Polynomial.C f := by
      exact foldingPolynomial_def₁ hq;
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
  rw [foldingPolynomial_def₂ h]
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
end
