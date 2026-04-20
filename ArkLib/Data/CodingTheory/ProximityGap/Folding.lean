import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.FoldingPolynomial
import ArkLib.Data.Polynomial.SplitFold
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.Finset.PickSubset
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ReedSolomon.FftDomain
import ArkLib.Data.Polynomial.Indicator
import ArkLib.ToMathlib.Polynomial.EvalExt

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial

variable {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

#check CosetFftDomain.subdomain_roots_card

noncomputable def foldWordAux (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (x : F) : Polynomial F :=
  Lagrange.interpolate {i | domain i ^ k = x}
    (fun i => domain i) f

section

variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

lemma foldWordAux_natDegree {k : ℕ} {x : F}
  [inst : NeZero k]
  :
  (foldWordAux domain f k x).natDegree < k := by
  by_cases heq: foldWordAux domain f k x = 0
  · simp [heq]
    have h := NeZero.ne (h := inst)
    omega
  · unfold foldWordAux at *
    apply lt_of_lt_of_le
    rw [Polynomial.natDegree_lt_iff_degree_lt (by aesop)]
    apply Lagrange.degree_interpolate_lt _ (by {
      intro x hx y hy hxy
      simp at hxy
      apply CosetFftDomain.injective (ω := domain) hxy
    })
    have h : Finset.image domain {i | domain i ^ k = x} =
      @Set.toFinset _ (((Polynomial.X : Polynomial F) ^ k - C x).rootSet F ∩ Finset.image domain Finset.univ) (by sorry) := by
      apply Finset.ext
      intro a
      simp
      apply Iff.intro
      · intro h
        rcases h with ⟨y, ⟨h1, h2⟩⟩
        rw [←h2]
        rw [Polynomial.mem_rootSet]
        simp [h1]
        intro contra
        have h: ( Y ^ k - C x ).coeff k = 0 := by
          rw [contra]
          simp
        simp [Polynomial.coeff_C] at h
        have hk : k ≠ 0 := NeZero.ne (h := inst)
        simp [hk] at h
      · intro h
        rw [Polynomial.mem_rootSet] at h
        simp at h
        rcases h with ⟨h1, ⟨y, h2⟩⟩
        exists y
        simp [h2]
        rcases h1 with ⟨_, h1⟩
        rw [sub_eq_zero] at h1
        simp [h1]
    rw [←Finset.card_image_of_injOn (f := domain) (by {
      intro x hx y hy hxy
      apply CosetFftDomain.injective (ω := domain) hxy
    })]
    rw [h]
    simp
    apply le_trans
    apply Finset.card_le_card (by {
        apply Finset.inter_subset_left
    })
    rw [←Set.ncard_eq_toFinset_card']
    apply le_trans (b := (Y ^ k - C x).natDegree)
    grw [rootSet, Set.ncard_coe_finset, aroots]
    rw [Polynomial.map]
    simp
    apply le_trans
    apply @Multiset.toFinset_card_le F (Classical.decEq F)
    apply le_trans
    apply Polynomial.card_roots'
    apply le_trans
    apply Polynomial.natDegree_sub_le
    simp
    apply le_trans
    apply Polynomial.natDegree_sub_le
    simp

noncomputable def fold (domain : SmoothCosetFftDomain n F) 
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : F)
  (x : F)
  :
  F
  := (foldWordAux domain f (2 ^ k) x).eval α

lemma fold_def {α : F}
  {x : F}
  :
  fold domain f k α x = (foldWordAux domain f (2 ^ k) x).eval α := rfl

lemma fold_pow_x_k 
  {i : Fin (2 ^ n)}
  :
  fold domain f k (domain i) ((domain i) ^ (2 ^ k)) =
    f i := by
  unfold fold foldWordAux
  rw [Lagrange.eval_interpolate_at_node] <;> simp
  intro x hx y hy hxy 
  apply CosetFftDomain.injective hxy

noncomputable def foldWord (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : F)
  :
  Word F (Fin (2 ^ (n - k)))
  := fun x => fold domain f k α (domain.subdomainNatReversed k x)

private lemma eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
  (f.eval (Polynomial.C a)).eval x = (Polynomial.map (evalRingHom x) f).eval a := by
  simp [Polynomial.eval_map];
  have h_eval : Polynomial.eval (Polynomial.C a) f = ∑ i ∈ f.support, f.coeff i * (Polynomial.C a) ^ i := by
    rw [Polynomial.eval_eq_sum];
    rfl;
  simp [h_eval, Polynomial.eval_finset_sum];
  simp [Polynomial.eval₂_eq_sum, Polynomial.sum_def]

theorem foldWord_codeword {d : ℕ}
  {α : F}
  (hk : k ≤ n)
  {p : ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d}
  [NeZero k]
  :
  foldWord domain p k α
    = evalOnPoints (domain.subdomainNatReversed k)
        (FoldingPolynomial.polyFold (ReedSolomon.codewordToPoly p) (2 ^ k) α) := by 
  by_cases hp : p = 0
  · subst hp
    ext x
    simp [foldWord, fold, foldWordAux, evalOnPoints,
      codewordToPoly, FoldingPolynomial.polyFold]
  · ext x
    simp only [foldWord, fold, foldWordAux, evalOnPoints,
      Embedding.coeFn_mk, codewordToPoly, LinearMap.coe_mk, AddHom.coe_mk,
      FoldingPolynomial.polyFold]
    rw [eval_comm]
    obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := CosetFftDomain.subdomainNatReversed_root_exists
      (ω := domain)
      (i := 0) (j := k)
      (x := (CosetFftDomain.subdomainNatReversed domain k) x)
      (by simp [hk])
      (by {
       rw [CosetFftDomain.mem_subdomainNatReversed_of_eq (j := k) (by simp)]
       exact CosetFftDomain.mem_coset_domain_self
      })
    rw [CosetFftDomain.subdomainNatReversed_zero] at hy₁
    conv =>
      rhs
      rw [←hy₂]
    congr
    have h := CosetFftDomain.subdomainNatReversed_roots_card (ω := domain)
          (j := k) (i := 0) (x := (CosetFftDomain.subdomainNatReversed domain k) x)
          (by simp [hk])
          (by {
           rw [CosetFftDomain.mem_subdomainNatReversed_of_eq (j := k) (by simp)]
           exact CosetFftDomain.mem_coset_domain_self
          })
    have hcard : 
          #({i | domain i ^ 2 ^ k = (CosetFftDomain.subdomainNatReversed domain k) x} : Finset _) = 2 ^ k := by
          conv =>
            rhs
            rw [←h]
          exact Finset.card_bij
            (i := fun x _ ↦ domain x)
            (by {
              intro a ha
              simp at ha
              simp only [Nat.sub_zero, mem_filter]
              constructor
              · rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
                  CosetFftDomain.subdomainNatReversed_zero]
                exact CosetFftDomain.mem_coset_domain_self 
              · exact ha })
            (by {
              intro a ha b hb hab
              apply CosetFftDomain.injective (ω := domain)
              simp [hab]
            })
            (by {
              intro b hb 
              simp only [Nat.sub_zero, mem_filter] at hb
              rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
                CosetFftDomain.subdomainNatReversed_zero] at hb
              rcases hb with ⟨hb₁, hb₂⟩
              rw [CosetFftDomain.mem_coset_def] at hb₁
              rcases hb₁ with ⟨i, hb₁⟩
              exists i
              exists (by {
                simp
                rw [←hb₁, hb₂]
              })
              simp 
              rw [hb₁]
            })

    apply poly_eq_of_eval_eq_degree (n := 2 ^ k)
        (s := Finset.image domain {i | domain i ^ 2 ^ k = (CosetFftDomain.subdomainNatReversed domain k) x})
    · rw [Finset.card_image_of_injective _ CosetFftDomain.injective]
      rw [hcard]
    · intro u hu
      simp only [mem_image, mem_filter, mem_univ, true_and] at hu
      rcases hu with ⟨i, hu₁, hu₂⟩
      rw [←hu₂]
      rw [←hy₂] at hu₁ 
      rw [←hu₁]
      rw [Lagrange.eval_interpolate_at_node _ (by {
        intro x hx y hy hxy
        exact CosetFftDomain.injective hxy
      }) (by { 
        simp only [mem_filter, mem_univ, true_and]
        rw [hu₁, ←hy₂]
      })]
      rw [FoldingPolynomial.eval_property_of_folding_polynomial_x_k]
      rw [Lagrange.eval_interpolate_at_node _ (by {
        intro x hx y hy hxy
        exact CosetFftDomain.injective hxy
      }) (by simp)]
    · apply lt_of_le_of_lt
      · apply Lagrange.degree_interpolate_le
        intro x hx y hy hxy
        apply CosetFftDomain.injective (ω := domain)
        simp at hxy
        exact hxy
      · rw [hcard] 
        rw [WithBot.lt_def]
        simp
        exists (2 ^ k - 1)
        exists (2 ^ k)
        simp
        rfl
    · apply lt_of_le_of_lt Polynomial.degree_map_le
      have h := FoldingPolynomial.folding_polynomial_deg_y_bound 
        (f := (Lagrange.interpolate univ ⇑domain) ↑p)
        (q := Y ^ 2 ^ k)
        (by simp)
      simp only [Bivariate.natDegreeY, 
        degree_pow, degree_X, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one] at h
      norm_cast at h
      rw [Polynomial.natDegree_lt_iff_degree_lt (by {
        intro contra
        have h := FoldingPolynomial.eq_zero_of_folding_polynomial_eq_zero contra
        have contra : p = 0 := by
          ext x
          simp
          rw [←Lagrange.eval_interpolate_at_node (s := univ) (v := domain) ↑p
            (by {
              intro x hx y hy hxy
              exact CosetFftDomain.injective (ω := domain) hxy
          }) (by simp)]
          rw [h]
          simp
        exact hp contra
      })] at h
      exact h

@[simp]
lemma fold_zero {k : ℕ} :
  fold domain 0 k = 0 := by
  unfold fold foldWordAux
  ext
  simp

private noncomputable def foldAuxCoeff (domain : SmoothCosetFftDomain n F) 
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (i : Fin k) (x : F)
  : F
  := (foldWordAux domain f k x).coeff i

private lemma foldAux_eq_sum_of_foldAuxCoeff
  [Nonempty ι]
  [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {k : ℕ} {x : F}
  [inst : NeZero k]
  :
  foldWordAux domain f k x
    = ∑ j, Polynomial.C (foldAuxCoeff domain f k j x) * Y ^ j.val := by
  unfold foldAuxCoeff
  ext n
  simp
  by_cases hlt: n < k
  · have h : n = (⟨n, hlt⟩ : Fin k) := by simp
    conv =>
      rhs
      rw [h]
    have h :
      ∀ {j : Fin k},
        (if (↑(⟨n, hlt⟩ : Fin k) : ℕ) = ↑j then
          (foldWordAux domain f k x).coeff ↑j else 0)
            = (if (⟨n, hlt⟩ : Fin k) = j then
              (foldWordAux domain f k x).coeff ↑j
              else 0) := by
      rintro ⟨j, hj⟩
      simp
    conv =>
      rhs
      rhs
      ext x
      rw [h]
    rw [Fintype.sum_ite_eq]
  · simp at hlt
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by {
      apply lt_of_lt_of_le
      exact foldWordAux_natDegree
      simp [hlt]
    })]
    have h :
      ∀ {j : Fin k},
        (if n = ↑j then (foldWordAux domain f k x).coeff ↑j else 0)
            = 0 := by
        rintro ⟨x, hx⟩
        simp
        intro contra
        rw [←contra] at hx
        omega
    conv =>
      rhs
      rhs
      ext x
      rw [h]
    simp

private lemma fold_eq_sum_of_foldAuxCoeff_mul_pow_alpha
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {α : F} {x : F}
  [inst : NeZero k]
  :
  fold domain f k α x =
    ∑ j : Fin k, (foldAuxCoeff domain f k j x) * α ^ j.val := by
  unfold fold
  rw [foldAux_eq_sum_of_foldAuxCoeff]
  rw [Polynomial.eval_finset_sum]
  conv =>
    lhs
    rhs
    ext i
    rw [Polynomial.eval_mul]
    simp

private noncomputable def indicatedPolynomial
  (domain : ι ↪ F) (f : Word F ι) (k : ℕ) (s' : Finset F)
  :
  Polynomial (Polynomial F)
  := ∑ x ∈ s',
    Polynomial.C (singletonIndicator x s') *
      (Polynomial.map Polynomial.C <| foldAux domain f k x)

private lemma indicated_polynomial_degree_x_lt
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  (hs' : s'.Nonempty)
  :
  Bivariate.degreeX (indicatedPolynomial domain f k s')
    < s'.card := by
  simp [Bivariate.degreeX, indicatedPolynomial]
  rw [Finset.sup_lt_iff (by simp [hs'])]
  intro b hb
  rw [Nat.lt_iff_le_pred]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [←Nat.lt_iff_le_pred]
  apply lt_of_le_of_lt
  apply natDegree_mul_le
  simp [singleton_indicator_natDegree_lt_of_mem hi]
  simp [hs']
  simp [hs']

private lemma indicated_polynomial_degree_y_lt
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  [inst : NeZero k]
  :
  Bivariate.natDegreeY (indicatedPolynomial domain f k s')
    < k := by
  simp [Bivariate.natDegreeY, indicatedPolynomial]
  rw [Nat.lt_iff_le_pred (by {
    have h : k ≠ 0 := inst.out
    omega
  })]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [←Nat.lt_iff_le_pred (by {
    have h : k ≠ 0 := inst.out
    omega
  })]
  apply lt_of_le_of_lt
  apply natDegree_mul_le
  simp [foldAux_natDegree]


private lemma indicated_polynomial_eq_foldAux
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  {α : F} {x : F} (hx : x ∈ s')
  :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x
    = (foldAux domain f k x).eval α := by
  simp only [indicatedPolynomial]
  rw [eval_finset_sum, eval_finset_sum]
  simp only [eval_mul, eval_C, eval_map_apply]
  rw [Finset.sum_eq_ite x (by {
    intro b hb hneq
    rw [singleton_indicator_eq_0_on_S_minus_x (by aesop)]
    simp
  })]
  simp [hx]

private lemma indicated_polynomial_eval_eq_combination_of_correlated
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  {u : Fin k → Polynomial F}
  {α : F} {x : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldAuxCoeff domain f k i x))
  (hx : x ∈ s')
  [inst : NeZero k]
  :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x
    = ∑ i : Fin k, (u i).eval x * α ^ i.val := by
  rw [
    indicated_polynomial_eq_foldAux hx,
    ←fold_def,
    fold_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
  conv =>
    rhs
    rhs
    ext i
    rw [hu i _ hx]

private lemma indicated_polynomial_eq_combination_of_correlated
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  {u : Fin k → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card)
  (h_s' : s'.Nonempty)
  [inst : NeZero k]
  :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α))
    = ∑ i : Fin k, (u i) * Polynomial.C (α ^ i.val) := by
  apply Polynomial.poly_eq_of_eval_eq_natDegree (s := s') (n := #s')
  · simp [indicatedPolynomial]
    rw [eval_finset_sum]
    simp
    rw [Nat.lt_iff_le_pred (by simp [h_s'])]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [←Nat.lt_iff_le_pred (by simp [h_s'])]
    apply lt_of_le_of_lt
    apply natDegree_mul_le
    simp [singleton_indicator_natDegree_lt_of_mem hi]
  · rw [Nat.lt_iff_le_pred (by simp [h_s'])]
    apply natDegree_sum_le_of_forall_le
    intro i _
    rw [←Nat.lt_iff_le_pred (by simp [h_s'])]
    apply lt_of_le_of_lt
    apply natDegree_mul_le
    simp [hu_deg i]
  · simp
  · intro x hx
    rw [indicated_polynomial_eval_eq_combination_of_correlated hu hx]
    rw [eval_finset_sum]
    simp only [map_pow, eval_mul, eval_pow, eval_C]


private lemma indicated_polynomial_eq_foldAux'
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  {u : Fin k → Polynomial F}
  {x : F}
  (hx : ∀ i, (u i).eval x = (foldAuxCoeff domain f k i x))
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card)
  (h_s' : s'.Nonempty)
  (h_card : k ≤ Fintype.card F)
  [inst : NeZero k]
  :
  (Polynomial.map
    (Polynomial.evalRingHom x)
    (indicatedPolynomial domain f k s'))
    = foldAux domain f k x := by
  apply Polynomial.poly_eq_of_eval_eq_natDegree (s := Finset.univ) (n := k)
  · simp [h_card]
  · intro α _
    have h : Polynomial.eval α (Polynomial.map (evalRingHom x) (indicatedPolynomial domain f k s'))
      = ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x
      := by
        rw [eval_comm]
    rw [
      h,
      indicated_polynomial_eq_combination_of_correlated hu hu_deg h_s',
      ←fold_def,
      fold_eq_sum_of_foldAuxCoeff_mul_pow_alpha,
      eval_finset_sum]
    conv =>
      lhs
      rhs
      ext j
      rw [eval_mul]
      rw [hx j]
      simp
  · simp [indicatedPolynomial]
    rw [Polynomial.map_sum]
    simp
    rw [Nat.lt_iff_le_pred (by {
      have h := inst.out
      omega
    })]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [←Nat.lt_iff_le_pred (by {
      have h := inst.out
      omega
    })]
    apply lt_of_le_of_lt
    apply natDegree_mul_le
    simp
    rw [Polynomial.map_map]
    simp
    exact foldAux_natDegree
  · exact foldAux_natDegree

lemma indicated_polynomial_comp_x_k_natDegree
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {s' : Finset F}
  (h_s : s'.Nonempty)
  [inst : NeZero k]
  :
  ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ k)) <| indicatedPolynomial domain f k s').eval Polynomial.X).natDegree < k * s'.card := by
  by_cases h_card : 1 < s'.card
  · have h_k := inst.out
    simp [indicatedPolynomial]
    rw [Polynomial.eval_map, eval₂_finset_sum]
    simp
    rw [Nat.lt_iff_le_pred (by {
      simp [h_s]
      omega
    })]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [←Nat.lt_iff_le_pred (by {
      simp [h_s]
      omega
    })]
    apply lt_of_le_of_lt
    apply natDegree_mul_le
    rw [natDegree_comp]
    simp
    rw [eval₂_map]
    rw [eval₂]
    simp
    have h : ((foldAux domain f k i).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e)
      = foldAux domain f k i := by
      conv =>
        rhs
        rw [←Polynomial.sum_monomial_eq (foldAux _ _ _ _) ]
      ext n
      simp
      rw [Polynomial.sum]
      simp
      aesop
    simp
    rw [h]
    have h_ind : (singletonIndicator i s').natDegree
      ≤ s'.card - 1 := by
      rw [←Nat.lt_iff_le_pred (by omega)]
      exact singleton_indicator_natDegree_lt_of_mem hi
    apply lt_of_le_of_lt
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_right _ h_ind
    apply lt_of_lt_of_le
    apply Nat.add_lt_add_left
    exact foldAux_natDegree
    conv =>
      lhs
      rhs
      rw [←Nat.mul_one k, mul_comm]
    rw [←Nat.add_mul]
    rw [Nat.sub_one_add_one]
    rw [mul_comm]
    simp
    intro contra
    rw [contra] at h_s
    simp at h_s
  · simp at h_card
    have h_card : #s' = 1 := by
      by_contra contra
      have h_card : #s' = 0 := by omega
      rw [Finset.card_eq_zero] at h_card
      rw [h_card] at h_s
      simp at h_s
    rw [Finset.card_eq_one] at h_card
    rcases h_card with ⟨a, h_a⟩
    simp [indicatedPolynomial ]
    rw [h_a]
    simp [singletonIndicator, indicator]
    rw [Polynomial.eval_map, Polynomial.eval₂_map, eval₂]
    simp
    have h : ((foldAux domain f k a).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e)
      = foldAux domain f k a := by
      conv =>
        rhs
        rw [←Polynomial.sum_monomial_eq (foldAux _ _ _ _) ]
      ext n
      simp
      rw [Polynomial.sum]
      simp
      aesop
    rw [h]
    exact foldAux_natDegree

private lemma poly_eval_lemma {f : Polynomial (Polynomial F)} {x : F}
  {k : ℕ}
  :
  Polynomial.eval x
    (Polynomial.eval
        Polynomial.X
        (Polynomial.map (Polynomial.X ^ k).compRingHom f)) =
             (Polynomial.eval
               x
               (Polynomial.map
                (Polynomial.evalRingHom (x ^ k))
                f)) := by
  induction f using Polynomial.induction_on ; aesop;
  · aesop;
  · simp_all +decide [ pow_succ, mul_assoc, Polynomial.eval_map ]

private lemma master_lemma
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ}
  {s : Finset ι}
  [inst : NeZero k]
  (h_s : s ⊆ (iotaK domain k))
  {u : Fin k → Polynomial F}
  (h_u : ∀ i, ∀ j ∈ s, (u i).eval (domain j)
      = foldAuxCoeff domain f k i (domain j))
  {d : ℕ}
  (h_d : k < d)
  (h_k_card : k ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / k)
  :
  ∃ f' : Polynomial F,
    f'.natDegree < d
      ∧ hammingDist f (fun x => f'.eval (domain x))
        ≤ Fintype.card ι -
          ({i ∈ Finset.product Finset.univ s | (domain i.1) ^ k = domain i.2} : Finset (ι × ι)).card := by
  let s_f := (Finset.image domain s)
  let s' := s_f.pickSubset (d / k)
  by_cases h_empty : s = ∅
  · simp [h_empty]
    have i := Classical.choice (α := ι) (by aesop)
    exists (C <| f i)
    apply And.intro
    · simp
      omega
    · simp [hammingDist]
      have h : ({i_1 | ¬f i_1 = f i} : Finset _) = Finset.univ \ ({i_1 | f i_1 = f i} : Finset ι) := by
        ext a
        aesop
      rw [h]
      rw [Finset.card_sdiff]
      simp
  · have h_nonempty : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      simp [h_empty]
    have h_k : k ≠ 0 := inst.out
    have h_s_f_non_empty : s_f.Nonempty := by
      simp [s_f, h_nonempty]
    have h_s'_card : s'.card = min s.card (d / k) := by
      simp [s', s_f]
      rw [Finset.card_image_of_injOn (by simp)]
    have h_s'_non_empty : s'.Nonempty := by
      have h_s'_card : 0 < s'.card := by
        rw [h_s'_card]
        simp [h_nonempty]
        omega
      rw [Finset.nonempty_iff_ne_empty]
      intro contra
      rw [contra] at h_s'_card
      simp at h_s'_card
    exists ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ k)) <| indicatedPolynomial domain f k s').eval Polynomial.X)
    apply And.intro
    · apply lt_of_lt_of_le
      apply indicated_polynomial_comp_x_k_natDegree h_s'_non_empty
      apply le_trans
      apply Nat.mul_le_mul_left (m := d / k)
      omega
      apply Nat.mul_div_le
    · simp [hammingDist]
      have h :
        ( {i |
        ¬f i =
            Polynomial.eval (domain i)
              (Polynomial.eval Y (Polynomial.map (Y ^ k).compRingHom (indicatedPolynomial domain f k s')))} : Finset _) =
            Finset.univ \ ({i |
            f i =
                Polynomial.eval (domain i)
                  (Polynomial.eval Y (Polynomial.map (Y ^ k).compRingHom (indicatedPolynomial domain f k s')))} : Finset _)  := by
          ext a
          aesop
      rw [h]
      clear h
      rw [Finset.card_sdiff]
      apply Nat.sub_le_sub_left
      simp
      apply Finset.card_le_card_of_injOn
        (f := fun i => i.1)
      · rintro ⟨a₁, a₂⟩ ha
        simp at ha
        simp
        rw [poly_eval_lemma]
        rcases ha with ⟨h_a_s, h_eq⟩
        rw [h_eq]
        by_cases h_s'_card_le : d / k ≤  s'.card
        · rw [indicated_polynomial_eq_foldAux' (by aesop) ] <;> try assumption
          · rw [←fold_def, ←h_eq, fold_pow_x_k]
          · intro i x hx
            have h_x : ∃ j ∈ s, x = domain j := by
              simp [s'] at hx
              have hx : x ∈ s_f := Finset.mem_of_subset (pick_subset_subset) hx
              simp [s_f] at hx
              tauto
            rcases h_x with ⟨j, ⟨h_j, h_x⟩⟩
            rw [h_x]
            rw [h_u i ]
            assumption
          · intro i
            exact lt_of_lt_of_le (h_u_deg i) h_s'_card_le
        · simp at h_s'_card_le
          have h : s' = s_f := by
            simp only [s'] at h_s'_card_le
            simp only [s']
            apply pick_subset_eq_s_of_card_pick_subset_lt_n h_s'_card_le
          rw [h]
          rw [h] at h_s'_card_le
          rw [←eval_comm, indicated_polynomial_eq_foldAux (by simp [s_f, h_a_s])]
          rw [←h_eq, ←fold_def, fold_pow_x_k]
      · rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy
        aesop

private lemma master_lemma'
  [Nonempty ι]
  [Fintype F]
  {domain : ι ↪ F} {f : Word F ι} {k : ℕ}
  {s : Finset ι}
  [inst : NeZero k]
  (h_s : s ⊆ (iotaK domain k))
  {u : Fin k → Polynomial F}
  (h_u : ∀ i, ∀ j ∈ s, (u i).eval (domain j)
      = foldAuxCoeff domain f k i (domain j))
  {d : ℕ}
  (h_d : k < d)
  (h_k_card : k ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / k)
  :
  Δ₀(f, ReedSolomon.code domain d)
        ≤ Fintype.card ι -
          ({i ∈ Finset.product Finset.univ s | (domain i.1) ^ k = domain i.2} : Finset (ι × ι)).card := by
  simp [distFromCode]
  apply sInf_le_of_le
    (b := ↑ (Fintype.card ι - ({i ∈ Finset.product Finset.univ s | (domain i.1) ^ k = domain i.2} : Finset (ι × ι)).card))
  simp
  have h := master_lemma h_s h_u h_d h_k_card h_u_deg
  rcases h with ⟨f', ⟨h_f'_deg, hdist⟩⟩
  simp [ReedSolomon.code, ReedSolomon.evalOnPoints]
  exists f'
  apply And.intro
  · simp [Polynomial.degreeLT]
    intro i hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    omega
  · have hdist :
     (↑Δ₀(f, fun x ↦ Polynomial.eval (domain x) f') : ℕ∞) ≤ ↑(Fintype.card ι - #({i ∈ univ.product s | domain i.1 ^ k = domain i.2})) := by
      rw [ENat.coe_le_coe]
      assumption
    simp at hdist
    assumption





  simp

lemma folding_proximity {domain : ι ↪ F} {f : Word F ι} {d k : ℕ} [inst: NeZero k] {δ : ℚ≥0}
  (k_div_d : k ∣ d)
  (h_k_d : k < d)
  (h_k_card: k ≤ Fintype.card F)
  (δ_gt_0 : 0 < δ)
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code domain d)) (1 - (ReedSolomonCode.sqrtRate d domain))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r, ReedSolomon.code (domainK domain k) (d / k)) ≤ δ] ≤
        (k - 1) * ProximityGap.errorBound δ (d / k) (domainK domain k) := by
  match k with
  | .zero => aesop
  | .succ k =>
    unfold foldWord
    have bound_tighter : ↑δ ≤ 1 - ReedSolomonCode.sqrtRate (d / (k + 1)) (domainK domain (k + 1)) := by
      sorry
    have h' :=
      @correlatedAgreement_affine_curves (iotaK domain (k + 1)) _ sorry F _ _ _ 
        k (d / (k + 1)) (domainK domain (k + 1)) δ bound_tighter
    unfold δ_ε_correlatedAgreementCurves at h'
    by_contra h
    have eq₁ : ((k + 1 : ℕ) : ENNReal) - 1 = (k : ENNReal) := by norm_cast
    have {a b : ENNReal} : a < b → b > a := id
    simp only [not_le, fold_eq_sum_of_foldAuxCoeff_mul_pow_alpha, bind_pure_comp, Functor.map, PMF.bind_apply,
      PMF.uniformOfFintype_apply, comp_apply, PMF.pure_apply, ULift.up.injEq, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero, tsum_fintype, Nat.succ_eq_add_one, eq₁] at h h'
    have h := this h
    specialize h' (Matrix.of (fun m n ↦ foldAuxCoeff domain f (k + 1) m ((domainK domain (k + 1)) n)))
    have hh {a : F} : (fun x ↦ ∑ j, foldAuxCoeff domain f (k + 1) j ((domainK domain (k + 1)) x) * a ^ (↑j : ℕ))
      =∑ i : Fin (k + 1), a ^ (↑i : ℕ) • Matrix.of (fun m n ↦ foldAuxCoeff domain f (k + 1) m ((domainK domain (k + 1)) n)) i := by 
      ext x
      simp
      conv =>
        lhs
        rhs
        ext y
        rw [mul_comm]
    specialize h' (by {
      conv =>
        lhs
        rhs
        ext a
        rw [←hh]
      assumption
    }) 
    simp [jointAgreement] at h'
    rcases h' with ⟨S, ⟨h_card, ⟨v, h'⟩⟩⟩
    simp [ReedSolomon.code] at h'
    rw [forall_and] at h'
    rcases h' with ⟨h_rs, h'⟩ 
    let u : Fin (k + 1) → Polynomial F :=
      fun i => Classical.choose (h_rs i)
    have contradiction := master_lemma' (k := k + 1) (domain := domain) (f := f)
      (s := Finset.image (fun i => i.val) S)
      (by {
        intro x hx
        simp at hx
        rcases hx with ⟨x', hx'⟩ 
        aesop
      })
      (u := u)
      (by {
        intros i j hj
        have h_spec : u i ∈ F⦃< d / (k + 1)⦄[X] ∧ (ReedSolomon.evalOnPoints (domainK domain (k + 1))) (u i) = v i := Classical.choose_spec (h_rs i)
        simp [ReedSolomon.evalOnPoints] at h_spec
        rcases h_spec with ⟨_, h_spec⟩
        simp [domainK] at h_spec
        simp at hj
        rcases hj with ⟨hj, hj'⟩
        have h_spec := congrFun h_spec ⟨j, hj⟩ 
        simp at h_spec
        rw [h_spec]
        specialize h' i hj'
        simp [domainK] at h'
        rw [←h']
      })
      (d := d)
      (by assumption)
      (by assumption)
      (by {
        intro i
        have h_spec : u i ∈ F⦃< d / (k + 1)⦄[X] ∧ (ReedSolomon.evalOnPoints (domainK domain (k + 1))) (u i) = v i := Classical.choose_spec (h_rs i)
        rcases h_spec with ⟨h_spec, _⟩
        simp [degreeLT] at h_spec
        by_cases heq : u i = 0
        · simp [heq]
          omega
        · rw [Polynomial.natDegree_lt_iff_degree_lt heq]
          rw [Polynomial.degree_lt_iff_coeff_zero]
          exact h_spec
      })
    sorry  

end
end ProximityGap
