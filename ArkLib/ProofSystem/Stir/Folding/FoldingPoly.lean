import ArkLib.Data.Polynomial.Bivariate

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Basic

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
  generalize hdeg: f.natDegree = natdeg
  revert f deg
  apply Nat.strong_induction_on
    (p := fun natdeg =>
∀ {f : F[X]} {deg : ℕ},
  f.natDegree ≤ deg → f.natDegree = natdeg → foldingPolynomialAux q f natdeg = foldingPolynomialAux q f deg
    ) natdeg
  · intro natdeg ih f deg hdeg heq
    unfold foldingPolynomialAux
    by_cases hq: q.degree ≤ 0
    · simp [hq]
    · simp [hq]
      by_cases hfdeg: f.degree < q.degree 
      · simp [hfdeg]
      · simp [hfdeg]
        rcases natdeg with _ | natdeg
        · rw [Polynomial.natDegree_eq_zero] at heq
          rcases heq with ⟨f, hf⟩ 
          rw [←hf]
          simp
          have hmod : (C f) % q = C f := by
                rw [Polynomial.mod_eq_self_iff (by aesop)]
                apply lt_of_le_of_lt (b := 0)
                apply Polynomial.degree_C_le
                by_contra contra
                simp at contra
                tauto
          rw [hmod]
          have hdiv : (C f / q) = 0 := by
                rw [Polynomial.div_eq_zero_iff (by aesop)]
                apply lt_of_le_of_lt (b := 0)
                apply Polynomial.degree_C_le
                by_contra contra
                simp at contra
                tauto
          rw [hdiv]
          simp
          cases deg
          · simp
          · simp
            rw [foldingPolynomialAux_zero]
        · simp
          rcases deg with _ | deg
          · omega
          · simp 
            rw [←ih (f / q).natDegree (deg := natdeg)]
            rw [←ih (f / q).natDegree (deg := deg)]
            apply lt_of_lt_of_le (b := f.natDegree)
            apply Polynomial.natDegree_lt_natDegree
            intro contra
            rw [Polynomial.div_eq_zero_iff] at contra
            tauto
            intro contra
            rw [contra] at hq
            simp at hq
            apply Polynomial.degree_div_lt
            intro contra
            rw [contra] at heq
            simp at heq
            by_contra contra
            simp at contra
            tauto
            rw [heq]
            apply Nat.le_of_lt_succ
            apply lt_of_lt_of_le (b := f.natDegree)
            apply Polynomial.natDegree_lt_natDegree
            intro contra
            rw [Polynomial.div_eq_zero_iff] at contra
            tauto
            intro contra
            rw [contra] at hq
            simp at hq
            apply Polynomial.degree_div_lt
            intro contra
            rw [contra] at heq
            simp at heq
            by_contra contra
            simp at contra
            tauto
            omega
            rfl
            apply lt_of_lt_of_le (b := f.natDegree)
            apply Polynomial.natDegree_lt_natDegree
            intro contra
            rw [Polynomial.div_eq_zero_iff] at contra
            tauto
            intro contra
            rw [contra] at hq
            simp at hq
            apply Polynomial.degree_div_lt
            intro contra
            rw [contra] at heq
            simp at heq
            by_contra contra
            simp at contra
            tauto
            rw [heq]
            apply Nat.le_of_lt_succ
            apply lt_of_lt_of_le (b := f.natDegree)
            apply Polynomial.natDegree_lt_natDegree
            intro contra
            rw [Polynomial.div_eq_zero_iff] at contra
            tauto
            intro contra
            rw [contra] at hq
            simp at hq
            apply Polynomial.degree_div_lt
            intro contra
            rw [contra] at heq
            simp at heq
            by_contra contra
            simp at contra
            tauto
            rw [heq]
            rfl

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

lemma substitution_property_of_folding_polynomial {q f : F[X]} {n : ℕ} :
    (f.natDegree.div q.natDegree) = n →
    ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X
      = f := by 
    unfold foldingPolynomial
    revert f
    apply Nat.strong_induction_on
      (p := fun n => ∀ f, (f.natDegree.div q.natDegree) = n → ((foldingPolynomial q f).map (Polynomial.compRingHom q)).eval X
      = f ) 
    intro n
    rcases n with _ | n
    · simp [foldingPolynomial, ]
      unfold foldingPolynomialAux
      intro f h
      simp [h]
      have hh: f.natDegree.div q.natDegree = f.natDegree / q.natDegree := by 
        sorry
      rw [hh] at h
      rw [Nat.div_eq_zero_iff] at h
      rcases h with h | h
      · rw [Polynomial.natDegree_eq_zero] at h
        rcases h with ⟨x, q_eq_c⟩ 
        have hq: map (C x).compRingHom (map C f) = map C f := by
          aesop
        rw [←q_eq_c]
        rw [hq]
        rw [Polynomial.eval_map]
        rw [Polynomial.eval₂_def]
        rw [Polynomial.sum_def]
        apply Polynomial.ext
        aesop
      · rw [Polynomial.eval_map]
        rw [Polynomial.eval₂_def]
        rw [Polynomial.sum_def]
        apply Polynomial.ext
        aesop
    · intro ih f h
      simp [foldingPolynomial]
      unfold foldingPolynomialAux
      simp [h]
      simp [foldingPolynomial] at ih



      
      

    



end
