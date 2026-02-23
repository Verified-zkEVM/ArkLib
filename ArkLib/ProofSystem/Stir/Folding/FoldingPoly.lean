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
  simp [foldingPolynomial]
  conv =>
    lhs
    unfold foldingPolynomialAux
    rfl
  rw [ite_cond_eq_false] 
  rw [ite_cond_eq_false]
  generalize hdeg: f.natDegree = deg
  rcases deg with _ | deg
  · rw [Polynomial.natDegree_eq_zero] at hdeg
    rcases hdeg with ⟨x, hdeg⟩
    rw [←hdeg] at h₁ 
    simp at h₁ 
    have hqdeg : q.degree < q.degree := by
      apply lt_of_le_of_lt h₁
      apply lt_of_le_of_lt (b := 0)
      apply Polynomial.degree_C_le
      tauto
    simp at hqdeg
  · simp
    rw [foldingPolynomialAux_deg_property]
    apply Nat.le_of_lt_succ
    apply lt_of_lt_of_le (b := f.natDegree)
    apply Polynomial.natDegree_lt_natDegree
    intro contra
    rw [Polynomial.div_eq_zero_iff] at contra
    have h : f.degree < f.degree := by
      apply lt_of_lt_of_le contra
      tauto
    simp at h
    intro contra
    rw [contra] at h₂ 
    simp at h₂ 
    apply Polynomial.degree_div_lt
    intro contra
    rw [contra] at hdeg
    simp at hdeg
    tauto
    rw [hdeg]
  simp
  tauto
  simp
  tauto

lemma substitution_property_of_folding_polynomial {q f : F[X]}  :
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X
      = f := by 
  generalize hdeg : f.natDegree = deg
  revert hdeg
  revert f
  apply Nat.strong_induction_on 
    (p := fun deg => ∀ {f}, f.natDegree = deg → eval X (map q.compRingHom (foldingPolynomial q f)) = f)
  intro deg ih f hdeg
  rcases deg with _ | deg
  · rw [Polynomial.natDegree_eq_zero] at hdeg
    rcases hdeg with ⟨x, hdeg⟩ 
    rw [←hdeg]
    rw [foldingPolynomial_def₂]
    simp
    right; left
    apply Polynomial.degree_C_le
  · by_cases hqdeg: q.degree ≤ 0
    · rw [Polynomial.degree_le_zero_iff] at hqdeg
      rw [hqdeg]
      rw [foldingPolynomial_C]
      rw [Polynomial.eval_eq_sum]
      apply Polynomial.ext
      intro n
      rw [Polynomial.sum_def]
      simp
      tauto
    · by_cases hqf_deg: q.degree ≤ f.degree 
      · rw [foldingPolynomial_def₃ hqf_deg (by {
          simp at hqdeg
          tauto
        })]
        simp
        rw [ih (f / q).natDegree (by {
          rw [←hdeg]
          apply Polynomial.natDegree_lt_natDegree
          intro contra
          rw [Polynomial.div_eq_zero_iff] at contra
          have h: f.degree < f.degree := by
            apply lt_of_lt_of_le contra hqf_deg
          simp at h
          intro contra
          rw [contra] at hqdeg
          simp at hqdeg
          apply Polynomial.degree_div_lt
          intro contra
          rw [contra] at hdeg
          simp at hdeg
          simp at hqdeg
          assumption
        }) (by rfl)]
        conv => 
          rhs
          rw [←EuclideanDomain.mod_add_div f q]
          rfl
        simp
        rw [Polynomial.eval_eq_sum]
        rw [Polynomial.sum_def]
        simp
        apply Polynomial.ext
        intro n
        simp
        tauto
      · rw [foldingPolynomial_def₂ (by {
          left
          simp at hqf_deg
          assumption
        })]
        rw [Polynomial.eval_eq_sum]
        rw [Polynomial.sum_def]
        simp
        apply Polynomial.ext
        intro n
        simp
        tauto

lemma folding_polynomial_deg_x_bound {q f : F[X]} (h: 0 < q.degree) :
  Bivariate.degreeX (foldingPolynomial q f) < q.degree := by
  simp [degreeX]
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
