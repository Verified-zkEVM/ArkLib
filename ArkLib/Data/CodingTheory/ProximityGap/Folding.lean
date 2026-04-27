/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

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
import ArkLib.ToMathlib.Polynomial.NatDegreeOfSum

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- Given a word `f`, `foldWordAux` is a polynomial `pₓ` 
  of degree < 'k' such that `pₓ(domain i) = f i` for each `i`
  such that `domain i ^ k = x`. -/
noncomputable def foldWordAux (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (x : F) : Polynomial F :=
  Lagrange.interpolate {i | domain i ^ k = x}
    (fun i => domain i) f

section

variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

omit [Fintype F] in
private lemma roots_of_x_in_domain_eq
  (hk : k ≠ 0) :
  ({i | domain i ^ k = x} : Finset (Fin (2 ^ n))) = 
    Finset.preimage 
      (nthRootsFinset k x) 
      domain
      CosetFftDomain.injOn := by
  ext i 
  simp only [mem_filter, mem_univ, true_and, mem_preimage]
  rw [Polynomial.mem_nthRootsFinset (by omega)]

omit [Fintype F] in
private lemma roots_of_x_in_domain_card
  (hk : k ≠ 0) :
  Finset.card {i | domain i ^ k = x} ≤ 
    Finset.card 
      (nthRootsFinset k x) := by
  rw [roots_of_x_in_domain_eq hk, Finset.card_preimage]
  exact Finset.card_le_card (by simp)

omit [Fintype F] in
private lemma roots_of_x_in_domain_le_k
  (hk : k ≠ 0) :
  Finset.card {i | domain i ^ k = x} ≤ k := 
  le_trans (roots_of_x_in_domain_card hk) <| by
  simp only [nthRootsFinset, Multiset.toFinset, card_mk]
  exact le_trans
    (@Multiset.toFinset_card_le F (Classical.decEq F) _)
    (Polynomial.card_nthRoots _ _)
    
omit [Fintype F] in
/-- The natDegree of the auxiliary polynomial `foldWordAux`
  is less than k. -/
lemma foldWordAux_natDegree {k : ℕ} {x : F}
  [inst : NeZero k] :
  (foldWordAux domain f k x).natDegree < k := by
  have hne := NeZero.ne (h := inst)
  by_cases heq: foldWordAux domain f k x = 0
  · aesop 
      (add safe (by omega)) 
  · unfold foldWordAux at *
    apply lt_of_lt_of_le
    · rw [Polynomial.natDegree_lt_iff_degree_lt heq]
      exact Lagrange.degree_interpolate_lt _ CosetFftDomain.injOn
    · exact roots_of_x_in_domain_le_k hne
            
/-- Compute value of the folded word. 
  Takes the auxiliary polynomial `foldWordAux` and evaluates it on `a`,
  the folding randomness. -/
noncomputable def foldValue (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n)))
  (k : ℕ) (α : F) (x : F) : F := 
  (foldWordAux domain f (2 ^ k) x).eval α

omit [Fintype F] in
lemma foldValue_def {α : F} {x : F} :
  foldValue domain f k α x = (foldWordAux domain f (2 ^ k) x).eval α := rfl

omit [Fintype F] in
lemma foldValue_def' {α : F} {x : F} :
  foldValue domain f k α x = (Lagrange.interpolate {i | domain i ^ (2 ^ k) = x}
    (fun i => domain i) f).eval α := rfl

omit [Fintype F] in
@[simp]
lemma foldValue_pow_x_k {i : Fin (2 ^ n)} : 
  foldValue domain f k (domain i) ((domain i) ^ (2 ^ k)) = f i := 
  Lagrange.eval_interpolate_at_node _ CosetFftDomain.injOn (by simp)
  
omit [Fintype F] in
@[simp]
lemma foldValue_zero {k : ℕ} :
  foldValue domain 0 k = 0 := by aesop (add simp [foldValue, foldWordAux])

/-- Fold a word. Takes a word `f` over `Fin (2 ^ n)` and randomness
  `a`, and returns a word over `Fin (2 ^ (n - k))`. -/
noncomputable def foldWord (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : F) :
  Word F (Fin (2 ^ (n - k))) := fun x ↦ 
  foldValue domain f k α (domain.subdomainNatReversed k x)

omit [Fintype F] in
@[simp]
lemma foldWord_zero {k : ℕ} :
  foldWord domain 0 k = 0 := by aesop (add simp [foldWord])

omit [Fintype F] [DecidableEq F] in
/-- TODO: this will go once this https://github.com/Verified-zkEVM/CompPoly/pull/203
  is merged. -/
private lemma eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
  (f.eval (Polynomial.C a)).eval x = (Polynomial.map (evalRingHom x) f).eval a := by
  simp only [Polynomial.eval_map]
  have h_eval : Polynomial.eval (Polynomial.C a) f = 
    ∑ i ∈ f.support, f.coeff i * (Polynomial.C a) ^ i := by
    aesop (add simp [Polynomial.eval_eq_sum])
  simp [h_eval, Polynomial.eval_finset_sum, 
        Polynomial.eval₂_eq_sum, Polynomial.sum_def]

omit [Fintype F] in
private lemma roots_in_domain_card_eq_if_x_in_domain
  (hk : k ≤ n)
  (hx : x ∈ domain.subdomainNatReversed k) :
  Finset.card {i | domain i ^ 2 ^ k = x} = 2 ^ k := by
  have h := CosetFftDomain.subdomainNatReversed_roots_card (ω := domain)
          (j := k) (i := 0) (x := x)
          (by simp [hk])
          (by aesop (add simp [CosetFftDomain.mem_subdomainNatReversed_of_eq]))
  conv_rhs =>
    rw [←h]
  exact Finset.card_bij
    (fun x _ ↦ domain x)
    (by {
      simp only [Nat.sub_zero, mem_filter, CosetFftDomain.mem_coset_finset_iff_mem_coset_domain]
      aesop
        (add simp [Nat.sub_zero, mem_filter, CosetFftDomain.mem_coset_finset_iff_mem_coset_domain]) 
        (add safe [(by rw [CosetFftDomain.subdomainNatReversed_zero])])
    })
    (by aesop (add unsafe (by apply CosetFftDomain.injective (ω := domain))))
    (fun b ↦ by
      simp only [Nat.sub_zero, mem_filter] 
      rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
        CosetFftDomain.subdomainNatReversed_zero,
        CosetFftDomain.mem_coset_def] 
      aesop
    )

omit [Fintype F] in
private lemma interpolate_eq_folding_poly_eval
  (hk : k ≤ n)
  (hx : x ∈ domain.subdomainNatReversed k) :
  ((Lagrange.interpolate {i | domain i ^ 2 ^ k = x} fun i ↦ domain i)
    f) =
  (Polynomial.map (evalRingHom x)
    (FoldingPolynomial.foldingPolynomial (Y ^ 2 ^ k) ((Lagrange.interpolate univ ⇑domain) f))) := 
  by 
  by_cases hf : f = 0 
  · simp [hf]
  · apply poly_eq_of_eval_eq_degree (n := 2 ^ k)
        (s := Finset.image domain {i | domain i ^ 2 ^ k = x})
    · rw [Finset.card_image_of_injOn CosetFftDomain.injOn,
        roots_in_domain_card_eq_if_x_in_domain hk hx]
    · simp only [mem_image, mem_filter, mem_univ, true_and] 
      rintro u ⟨i, hu₁, hu₂⟩
      rw [←hu₂, ←foldValue_def', ←hu₁,
        FoldingPolynomial.eval_property_of_folding_polynomial_x_k]
      aesop 
        (erase Lagrange.interpolate_apply)
        (add safe (by rw [Lagrange.eval_interpolate_at_node]))
        (add simp [
          FoldingPolynomial.eval_property_of_folding_polynomial_x_k,
          CosetFftDomain.injective])
    · exact lt_of_le_of_lt
        (Lagrange.degree_interpolate_le _ CosetFftDomain.injOn)
        (by 
          rw [roots_in_domain_card_eq_if_x_in_domain hk hx,
              show Nat.cast (2 ^ k - 1) = WithBot.some (2 ^ k - 1) by rfl,
              WithBot.coe_lt_coe]
          simp
        )
    · exact lt_of_le_of_lt Polynomial.degree_map_le <| by
        have h := FoldingPolynomial.folding_polynomial_deg_y_bound_x_k 
          (f := (Lagrange.interpolate univ ⇑domain) f)
          (k := 2 ^ k)
        simp only [Bivariate.natDegreeY] at h
        rw [Polynomial.natDegree_lt_iff_degree_lt (
          FoldingPolynomial.folding_polynomial_neq_zero_of_neq_zero <|
            fun contra ↦ hf <| by 
              ext x
              aesop 
                (erase Lagrange.interpolate_apply)
                (add safe (by rw [←Lagrange.eval_interpolate_at_node
                  (s := univ) (v := domain) f]))
                (add simp [CosetFftDomain.injective])
        )] at h
        exact h

omit [Fintype F] in
/-- Perfect completeness of folding: folding a codeword is the same as 
  applying `polyFold` and then encoding.
-/
theorem foldWord_codeword {d : ℕ}
  {α : F}
  (hk : k ≤ n)
  {p : ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d}
  :
  foldWord domain p k α
    = evalOnPoints (domain.subdomainNatReversed k)
        (FoldingPolynomial.polyFold (ReedSolomon.codewordToPoly p) (2 ^ k) α) := by 
  ext x
  simp only [foldWord, foldValue, foldWordAux, evalOnPoints,
    Embedding.coeFn_mk, codewordToPoly, LinearMap.coe_mk, AddHom.coe_mk,
    FoldingPolynomial.polyFold]
  rw [eval_comm, interpolate_eq_folding_poly_eval hk (by simp)]

private noncomputable def foldWordAuxCoeff (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (i : Fin k) (x : F) : F := 
  (foldWordAux domain f k x).coeff i

omit [Fintype F] in
private lemma foldWordAux_coeff_eq_foldWordAuxCoeff_fin
  {i : Fin k} :
  (foldWordAux domain f k x).coeff i =  
    (foldWordAuxCoeff domain f k i x) := by simp [foldWordAux, foldWordAuxCoeff]

omit [Fintype F] in
private lemma foldWordAux_coeff_eq_foldWordAuxCoeff_nat
  [inst : NeZero k]
  {i : ℕ} :
  (foldWordAux domain f k x).coeff i =  
    if h : i < k 
    then (foldWordAuxCoeff domain f k ⟨i, h⟩ x)
    else 0 := by 
  by_cases h : i < k <;> simp only [h, ↓reduceDIte]
  · rw [←foldWordAux_coeff_eq_foldWordAuxCoeff_fin]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt <|
            lt_of_lt_of_le foldWordAux_natDegree <| by simpa using h]

omit [Fintype F] in
private lemma foldWordAux_eq_sum_of_foldWordAuxCoeff
  [inst : NeZero k] :
  foldWordAux domain f k x = 
    ∑ j, Polynomial.C (foldWordAuxCoeff domain f k j x) * Y ^ j.val := by
  ext n
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hlt : n < k
  · aesop 
      (add simp [foldWordAuxCoeff])
      (add safe [(by rw [Finset.sum_eq_single_of_mem ⟨n, hlt⟩])])
  · simp only [foldWordAux_coeff_eq_foldWordAuxCoeff_nat, hlt, ↓reduceDIte]
    exact symm ∘ Finset.sum_eq_zero <| fun x _ ↦ match x with
      | ⟨x, hx⟩ => by aesop (add safe (by omega))

omit [Fintype F] in
private lemma foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha
  {α : F} :
  foldValue domain f k α x =
    ∑ j, (foldWordAuxCoeff domain f (2 ^ k) j x) * α ^ j.val := by
  aesop 
    (add simp 
      [foldValue,
        Polynomial.eval_finset_sum,
        foldWordAux_eq_sum_of_foldWordAuxCoeff])

private noncomputable def indicatedPolynomial
  (domain : SmoothCosetFftDomain n F) (f : Word F (Fin (2 ^ n))) (k : ℕ) (s' : Finset F)
  :
  Polynomial (Polynomial F)
  := ∑ x ∈ s',
    Polynomial.C (singletonIndicator x s') *
      (Polynomial.map Polynomial.C <| foldWordAux domain f k x)

section IndicatedPolynomial

variable {s' : Finset F} 

private instance card_ne_zero (hs' : s'.Nonempty) : NeZero (Finset.card s') where
  out := by aesop

omit [Fintype F] in
private lemma indicated_polynomial_degree_x_lt (hs' : s'.Nonempty) :
  Bivariate.degreeX (indicatedPolynomial domain f k s') < s'.card := by
  simp only [Bivariate.degreeX, indicatedPolynomial, finset_sum_coeff, coeff_C_mul, coeff_map]
  rw [Finset.sup_lt_iff (by simp [hs'])]
  intro b hb
  exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <| 
    fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      aesop 
        (add simp [singleton_indicator_natDegree_lt_of_mem])
  
omit [Fintype F] in
private lemma indicated_polynomial_degree_y_lt
  [inst : NeZero k] :
  Bivariate.natDegreeY (indicatedPolynomial domain f k s') < k := by
  simp only [Bivariate.natDegreeY, indicatedPolynomial]
  exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦ 
    lt_of_le_of_lt natDegree_mul_le <| by
      aesop 
        (add simp [foldWordAux_natDegree])
        (add safe forward [inst.out])
        (add safe (by omega))
        
omit [Fintype F] in
private lemma indicated_polynomial_eq_foldAux
  {α : F} (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x = 
    (foldWordAux domain f k x).eval α := by
  aesop 
    (add simp [indicatedPolynomial, eval_finset_sum])
    (add safe 
      [(by rw [singleton_indicator_eq_0_on_S_minus_x]), 
        (by rw [Finset.sum_eq_ite x])])

omit [Fintype F] in
private lemma indicated_polynomial_eval_eq_combination_of_correlated
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f (2 ^ k) i x))
  (hx : x ∈ s') :
  ((indicatedPolynomial domain f (2 ^ k) s').eval (Polynomial.C α)).eval x = 
    ∑ i, (u i).eval x * α ^ i.val := by
  aesop 
    (add safe (by rw [←foldValue_def]))
    (add simp 
      [indicated_polynomial_eq_foldAux, 
        foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha])  
  
omit [Fintype F] in
private lemma indicated_polynomial_eq_combination_of_correlated
  (hs' : s'.Nonempty)
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f (2 ^ k) i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card) :
  ((indicatedPolynomial domain f (2 ^ k) s').eval (Polynomial.C α)) = 
    ∑ i, (u i) * Polynomial.C (α ^ i.val) := by
  apply Polynomial.poly_eq_of_eval_eq_natDegree (s := s') (n := #s')
    <;> try rfl  
  · simp only [indicatedPolynomial, 
      eval_finset_sum, eval_mul, eval_C, eval_map_apply]
    exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <| 
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by 
        aesop 
          (add simp [singleton_indicator_natDegree_lt_of_mem])
  · exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <| 
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by simp [hu_deg] 
  · aesop 
      (add safe forward 
        [indicated_polynomial_eval_eq_combination_of_correlated])
      (add simp [eval_finset_sum])

private lemma indicated_polynomial_eq_foldAux'
  {s' : Finset F}
  {u : Fin (2 ^ k) → Polynomial F}
  (hx : ∀ i, (u i).eval x = (foldWordAuxCoeff domain f (2 ^ k) i x))
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f (2 ^ k) i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card)
  (h_s' : s'.Nonempty)
  (h_card : 2 ^ k ≤ Fintype.card F) :
  (Polynomial.map
    (Polynomial.evalRingHom x)
    (indicatedPolynomial domain f (2 ^ k) s')) = 
    foldWordAux domain f (2 ^ k) x := by
  apply Polynomial.poly_eq_of_eval_eq_natDegree (s := Finset.univ) (n := (2 ^ k))
    <;> try tauto
  · aesop 
     (add safe [(by rw [←eval_comm]),
      (by rw 
        [indicated_polynomial_eq_combination_of_correlated, 
          ←foldValue_def, 
          foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha])])
     (add simp [eval_finset_sum])  
  · simp only 
      [indicatedPolynomial, Polynomial.map_sum,
        Polynomial.map_mul, map_C, coe_evalRingHom]
    exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦ 
      lt_of_le_of_lt natDegree_mul_le <| by 
        aesop 
          (add simp [Polynomial.map_map])
          (add safe [foldWordAux_natDegree])
  · exact foldWordAux_natDegree

omit [Fintype F] in
private lemma foldWordAux_poly_sum {a : F} : 
  ((foldWordAux domain f (2 ^ k) a).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e) = 
  foldWordAux domain f (2 ^ k) a := by
  aesop (add safe 
    [(by rw [←Polynomial.sum_monomial_eq]),
     (by rw [Polynomial.sum])])

omit [Fintype F] in
private lemma indicated_polynomial_comp_x_k_natDegree
  (hs' : s'.Nonempty) :
  ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ (2 ^ k))) <| 
    indicatedPolynomial domain f (2 ^ k) s').eval Polynomial.X).natDegree < (2 ^ k) * s'.card := by
  by_cases h_card : 1 < s'.card
  · simp only [indicatedPolynomial, 
      Polynomial.eval_map, eval₂_finset_sum,
      eval₂_mul, eval₂_C, coe_compRingHom]
    exact natDegree_sum_lt_of_forall_lt 
      (inst := instNeZeroNatHMul (hm := card_ne_zero hs')) _ _ <| 
      fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      simp only [natDegree_comp, natDegree_pow, natDegree_X, mul_one, eval₂_map, 
        eval₂, RingHom.coe_comp, coe_compRingHom, comp_apply, C_comp, foldWordAux_poly_sum]
      have h_ind := 
        Nat.le_sub_one_of_lt (singleton_indicator_natDegree_lt_of_mem hi)
      exact lt_of_le_of_lt 
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ h_ind) _) <|
          lt_of_lt_of_le 
            (Nat.add_lt_add_left foldWordAux_natDegree _) <| by
            rw [Nat.mul_comm, ←Nat.mul_add_one]
            grind +ring
  · have h_card : #s' = 1 := by grind 
    aesop 
      (add unsafe [(by rw [Polynomial.eval_map, Polynomial.eval₂_map, eval₂])])
      (add simp [Finset.card_eq_one, indicatedPolynomial, 
        singletonIndicator, indicator, 
        foldWordAux_poly_sum])
      (add safe [foldWordAux_natDegree])
    
end IndicatedPolynomial

omit [Fintype F] [DecidableEq F] in
private lemma glorious_poly_eval_lemma {f : Polynomial (Polynomial F)} {x : F}
  {k : ℕ} :
  Polynomial.eval x
    (Polynomial.eval
        Polynomial.X
        (Polynomial.map (Polynomial.X ^ k).compRingHom f)) =
             (Polynomial.eval
               x
               (Polynomial.map
                (Polynomial.evalRingHom (x ^ k))
                f)) := by
  induction f using Polynomial.induction_on 
  · aesop
  · aesop
  · simp_all [pow_succ]

private noncomputable def contradictoryHammingDistBoundC
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ := 
  Finset.card { i ∈ 
    Finset.product 
      Finset.univ 
      (Finset.preimage s (domain.subdomainNatReversed k) CosetFftDomain.injOn) | 
    (domain i.1) ^ (2 ^ k) = domain.subdomainNatReversed k i.2 }


private noncomputable def contradictoryHammingDistBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ := 
  Fintype.card (Fin (2 ^ n)) - contradictoryHammingDistBoundC k domain s 

omit [Fintype F] in
@[simp]
lemma contradictory_hamming_dist_zero :
  contradictoryHammingDistBound k domain ∅ = 2 ^ n := by 
  simp [contradictoryHammingDistBound, contradictoryHammingDistBoundC]

omit [Fintype F] in
private lemma card_helper
  {s : Finset F} :
  contradictoryHammingDistBoundC k domain s ≤
  #{i |
      f i =
        Polynomial.eval (domain i)
          (foldWordAux domain f (2 ^ k) (domain i ^ 2 ^ k))} := by
  unfold contradictoryHammingDistBoundC
  apply Finset.card_le_card_of_injOn (fun i => i.1) 
  · rintro ⟨a₁, a₂⟩ ha
    simp only [product_eq_sprod, coe_filter, mem_product, mem_univ, mem_preimage, true_and,
      Set.mem_setOf_eq] at ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    rcases ha with ⟨h_a_s, h_eq⟩
    rw [←foldValue_def, foldValue_pow_x_k]
  · simp only [Set.InjOn]
    aesop 
      (add unsafe 
        [(by apply CosetFftDomain.injective 
              (ω := domain.subdomainNatReversed k))])

private lemma correlated_agreement_implies_contradictory_hamm_dist
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomainNatReversed k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
    foldWordAuxCoeff domain f (2 ^ k) i x)
  {d : ℕ}
  (h_d : 2 ^ k ≤ d)
  (h_k_card : (2 ^ k) ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k)) :
  ∃ f' : Polynomial F,
    f'.natDegree < d ∧ 
      hammingDist f (fun x => f'.eval (domain x)) ≤ 
        contradictoryHammingDistBound k domain s := by
  by_cases h_empty : s = ∅
  · exists (C <| f 0)
    aesop 
      (add safe (by grind))
      (add unsafe (by rw [←Finset.compl_filter, Finset.card_compl]))
      (add simp [hammingDist, Finset.card_sdiff])
  · let s' := s.pickSubset (d / (2 ^ k))
    have h_nonempty : s.Nonempty := by grind
    have h_s'_card : s'.card = min s.card (d / (2 ^ k)) := by simp [s']
    have h_s'_non_empty : s'.Nonempty := by
      simp_all only [card_pick_subset, ne_eq, 
        Nat.div_eq_zero_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
        false_or, not_lt, nonempty_pick_subset_of_nonempty_of_ne, s']
    exists ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ (2 ^ k))) <| 
      indicatedPolynomial domain f (2 ^ k) s').eval Polynomial.X)
    constructor
    · exact lt_of_lt_of_le 
        (indicated_polynomial_comp_x_k_natDegree h_s'_non_empty)
        (le_trans
          (Nat.mul_le_mul_left (m := d / (2 ^ k)) _ (by omega))
          (Nat.mul_div_le _ _))
    · simp only [hammingDist, ne_eq, contradictoryHammingDistBound, Fintype.card_fin]
      rw [←Finset.compl_filter, Finset.card_compl, Fintype.card_fin]
      apply Nat.sub_le_sub_left
      apply Finset.card_le_card_of_injOn
        (fun i => i.1) (f_inj := by {
          simp only [Set.InjOn]
          aesop 
            (add unsafe [(by apply CosetFftDomain.injective (ω := domain.subdomainNatReversed k))])
})
      rintro ⟨a₁, a₂⟩ ha
      simp_all only [product_eq_sprod, coe_filter, mem_product, mem_univ, mem_preimage, true_and,
        Set.mem_setOf_eq] 
      rcases ha with ⟨h_a_s, h_eq⟩
      rw [glorious_poly_eval_lemma, h_eq]
      by_cases h_s'_s : s' = s
      · rw [h_s'_s,
            ←eval_comm, 
            indicated_polynomial_eq_foldAux (by simp [h_a_s]),
            ←h_eq, 
            ←foldValue_def, 
            foldValue_pow_x_k]
      · rw [indicated_polynomial_eq_foldAux' (u := u) (by aesop) ] <;> try assumption
        · rw [←foldValue_def, ←h_eq, foldValue_pow_x_k]
        · intro i x hx
          have hx := (pick_subset_subset : s' ⊆ s) hx
          rw [h_u _ _ hx]
        · intro i
          exact lt_of_lt_of_le 
            (h_u_deg i) 
            (by rw [pick_subset_card_eq_n_of_ne h_s'_s])
        
private lemma master_lemma'
  [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {k : ℕ}
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomainNatReversed k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x
      = foldWordAuxCoeff domain f (2 ^ k) i x)
  {d : ℕ}
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n)
  (h_k_card : (2 ^ k) ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k))
  :
  ∃ f' : Polynomial F,
    f'.natDegree < d
      ∧ hammingDist f (fun x => f'.eval (domain x))
        ≤ 2 ^ n -
          2 ^ k * (Finset.card s):= by
  obtain ⟨f', h₁, h₂⟩ := master_lemma h_s h_u h_k_d h_k_card h_u_deg
  exists f'
  simp only [h₁, true_and]
  exact le_trans h₂ <| by  
    simp only [Fintype.card_fin, Embedding.coeFn_mk, product_eq_sprod] 
    rw [Nat.sub_le_sub_iff_left (by {
      simp only [CosetFftDomain.subdomainNatReversed, Nat.succ_eq_add_one] at h_s 
      have hcard := Finset.card_le_card h_s
      rw [CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2] at hcard
      apply Nat.le_trans 
      apply Nat.mul_le_mul_left _ hcard
      rw [←Nat.pow_add]
      have hkn : k ≤ n := by
        rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)] 
        omega
      rw [Nat.add_sub_of_le hkn]
    })]
    conv =>
      rhs
      congr
      rw [show @filter _ _ _ _ = 
        (Finset.preimage s (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) (fun x hx y hy hxy ↦ 
        CosetFftDomain.injective (ω := domain.subdomainNatReversed k) hxy)).biUnion 
          (fun i ↦ {j | domain j.1 ^ 2 ^ k = domain.subdomainNatReversed k i ∧ j.2 = i} ) by {
        ext x
        simp
      }]
    rw [Finset.card_biUnion (by {
      intro x hx y hy hxy
      simp only [Disjoint, le_eq_subset, bot_eq_empty, subset_empty]
      simp only [Embedding.coeFn_mk, coe_preimage, Set.mem_preimage, SetLike.mem_coe] at hx
      simp only [Embedding.coeFn_mk, coe_preimage, Set.mem_preimage, SetLike.mem_coe] at hy
      intro a ha₁ ha₂ 
      by_contra contra
      have contra : a ≠ ∅ := by simp [contra]
      rw [←Finset.nonempty_iff_ne_empty] at contra
      rcases contra with ⟨c, hc⟩
      specialize (ha₁ hc)
      specialize (ha₂ hc)
      simp only [mem_filter, mem_univ, true_and] at ha₁ 
      simp only [mem_filter, mem_univ, true_and] at ha₂ 
      aesop
    })]
    conv =>
      rhs
      congr
      rfl
      ext u
      rw [show (Finset.card _) = #{j | domain j ^ 2 ^ k = 
        (CosetFftDomain.subdomainNatReversed domain k) u} by {
        apply Finset.card_bij (fun a _ ↦ a.1)
        · aesop
        · aesop
        · aesop
      }]
    simp
    rw [Finset.sum_bij (t := s) 
      (g := fun x ↦ Finset.card {j | domain j ^ (2 ^ k) = x})
      (i := fun i _ ↦ domain.subdomainNatReversed k i)
      (by aesop)
      (by {
        intro x hx y hy hxy
        apply CosetFftDomain.injective (ω := domain.subdomainNatReversed k)
        simp at hxy
        exact hxy
      })
      (by {
        intro b hb
        specialize (h_s hb)
        rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
          CosetFftDomain.mem_coset_def] at h_s
        rcases h_s with ⟨a, ha⟩
        exists a
        exists (by {
          simp
          rw [←ha]
          exact hb
        })
        simp [ha]
      }) 
      (by {
        intro a ha
        simp
      })]
    rw [Finset.sum_bij (t := s) 
      (g := fun i ↦ 2 ^ k) (fun i _ ↦ i) 
      (by aesop)
      (by {
        intro x hx y hy hxy 
        simp at hxy
        exact hxy
      })
      (by {
        intro b hb
        exists b 
        exists hb
      }) 
      (by {
        intro a ha
        simp
        conv =>
          rhs
          rw [←CosetFftDomain.subdomainNatReversed_roots_card (i := 0) (j := k)
            (ω := domain) (x := a) (by {
              simp only [zero_add]
              rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)] 
              omega     
          }) (by {
            specialize (h_s ha)
            rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at h_s
            rw [CosetFftDomain.mem_subdomainNatReversed_of_eq (j := k) (by simp)]
            exact h_s
          })]
        apply Finset.card_bij 
          (i := fun i _ ↦ domain i)
        · intro j hj
          simp at hj 
          simp only [Finset.mem_filter]
          rw [hj, CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
            CosetFftDomain.subdomainNatReversed_zero]
          constructor
          · exact CosetFftDomain.mem_coset_domain_self 
          · rfl
        · intro x _ y _ hxy
          apply CosetFftDomain.injective (ω := domain)
          exact hxy
        · intro y hy 
          simp only [Nat.sub_zero, mem_filter] at hy
          rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain,
            CosetFftDomain.subdomainNatReversed_zero,
            CosetFftDomain.mem_coset_def] at hy
          rcases hy with ⟨⟨i, hi⟩, hy⟩
          exists i
          exists (by {
            simp
            rw [←hy, hi]
          })
          rw [hi]
      })]
    simp
    rw [mul_comm]

private lemma master_lemma''
  [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {k : ℕ}
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomainNatReversed k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x
      = foldWordAuxCoeff domain f (2 ^ k) i x)
  {d : ℕ}
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n)
  (h_k_card : (2 ^ k) ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k))
  :
  Δ₀(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d)
        ≤ 2 ^ n -
          2 ^ k * (Finset.card s) := by
  simp [distFromCode]
  apply sInf_le_of_le
    (b := ↑(2 ^ n -
          2 ^ k * (Finset.card s)))
  simp
  have h := master_lemma' h_s h_u h_k_d h_d h_k_card h_u_deg
  rcases h with ⟨f', ⟨h_f'_deg, hdist⟩⟩
  simp [ReedSolomon.code, ReedSolomon.evalOnPoints]
  exists f'
  apply And.intro
  · simp [Polynomial.degreeLT]
    intro i hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    omega
  · have hdist :
     (↑Δ₀(f, fun x ↦ Polynomial.eval (domain x) f') : ℕ∞) ≤ ↑(2 ^ n -
          2 ^ k * (Finset.card s)) := by
      rw [ENat.coe_le_coe]
      assumption
    simp at hdist
    assumption
  simp

lemma folding_proximity 
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {d k : ℕ}
  {δ : ℚ≥0}
  (k_div_d : 2 ^ k ∣ d)
  (h_k_d : 2 ^ k ≤ d)
  (h_d_n: d ≤ 2 ^ n)
  (δ_gt_0 : 0 < δ)
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d)) 
    (1 - (ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F)))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r, 
      ReedSolomon.code (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) 
      (d / (2 ^ k))) ≤ δ] ≤
        ((2 ^ k) - 1) * ProximityGap.errorBound δ (d / (2 ^ k)) 
        (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) := by
    have h_k_le_n : k ≤ n := by
      rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
      omega

    have h_k_card : 2 ^ k ≤ Fintype.card F := by
      exact le_trans h_k_d <| by
        exact le_trans h_d_n <| by
          rw [←CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2 (ω := domain)]
          simp only [CosetFftDomain.toFinset]
          apply Finset.card_le_card
          simp
          
    unfold foldWord
    have bound_tighter : 
      (↑δ) ≤ 1 - ReedSolomon.sqrtRate (d / (2 ^ k)) 
        (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) := by
      rw [←ENNReal.coe_le_coe]
      simp [ReedSolomon.sqrtRate]
      rw [ReedSolomon.rateOfLinearCode_eq_min_div]
      simp [ReedSolomon.sqrtRate] at δ_lt
      rw [ReedSolomon.rateOfLinearCode_eq_min_div] at δ_lt
      obtain ⟨_, δ_lt⟩ := δ_lt
      apply le_trans
      · exact le_of_lt δ_lt
      · rw [ENNReal.sub_le_sub_iff_left (by {
          simp
          apply NNReal.div_le_of_le_mul
          apply le_trans
          · apply min_le_right
          · simp
          }) (by simp)]
        simp
        rw [←min_div_div_right (by simp)]
        rw [←min_div_div_right (by simp)]
        simp
        left
        apply div_le_of_le_mul
        conv =>
          lhs
          rw [show Nat.cast (d / 2 ^ k)  = (↑d : NNReal) / 2 ^ k by norm_cast]
        apply div_le_of_le_mul
        rw [mul_assoc, ←pow_add, Nat.sub_add_cancel h_k_le_n]
        rw [←ENNReal.coe_le_coe, ENNReal.coe_mul] 
        rw [←ENNReal.div_le_iff (by simp) (by simp)]
        norm_cast
    have h' :=
      @correlatedAgreement_affine_curves (Fin (2 ^ (n - k))) _ (by {
       constructor 
       exact 0 }) _ F _ _ _ 
        (2 ^ k - 1) (d / (2 ^ k)) 
        (domain := domain.subdomainNatReversed k) (δ := δ) 
        (hδ := bound_tighter)
    unfold δ_ε_correlatedAgreementCurves at h'
    by_contra h
    have {a b : ENNReal} : a < b → b > a := id
    simp only [not_le, fold_eq_sum_of_foldAuxCoeff_mul_pow_alpha, bind_pure_comp, Functor.map, PMF.bind_apply,
      PMF.uniformOfFintype_apply, comp_apply, PMF.pure_apply, ULift.up.injEq, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero, tsum_fintype, Nat.succ_eq_add_one] at h h'
    have h := this h
    let cast (x : Fin (2 ^ k - 1 + 1)) 
      : Fin (2 ^ k) := Fin.cast (by {
        rw [Nat.sub_add_cancel]
        omega
      }) x
    specialize h' 
      (Matrix.of (fun i j ↦ foldWordAuxCoeff domain f (2 ^ k) 
        (cast i) 
        (domain.subdomainNatReversed k j)))
    have hh {a : F} : 
      (fun x ↦ 
        ∑ j, foldWordAuxCoeff domain f (2 ^ k) j 
          (domain.subdomainNatReversed k x) * a ^ (↑j : ℕ))
      =∑ i : Fin (2 ^ k - 1 + 1), a ^ (↑i : ℕ) • 
        Matrix.of (fun i j ↦ 
          foldWordAuxCoeff domain f (2 ^ k) (cast i) (domain.subdomainNatReversed k j)) i := by 
      ext x
      simp
      conv =>
        lhs
        rhs
        ext y
        rw [mul_comm]
      symm
      apply Fintype.sum_bijective cast
      · constructor
        · intro x y hxy
          simp [cast] at hxy
          exact hxy
        · rintro ⟨b, hb⟩
          exists ⟨b, by omega⟩
      · intro y 
        rfl
    specialize h' (by {
      conv =>
        lhs
        rhs
        ext a
        rw [←hh]
      norm_cast at h
    }) 
    simp [jointAgreement] at h'
    rcases h' with ⟨S, ⟨h_card, ⟨v, h'⟩⟩⟩
    simp [ReedSolomon.code] at h'
    rw [forall_and] at h'
    rcases h' with ⟨h_rs, h'⟩ 
    let u : Fin (2 ^ k - 1 + 1) → Polynomial F :=
      fun i => Classical.choose (h_rs i)
    let cast' : Fin (2 ^ k) → Fin (2 ^ k - 1 + 1) :=
      fun x ↦ Fin.cast (by {
        rw [Nat.sub_add_cancel]
        omega
  }) x
    have contradiction := master_lemma'' (k := k) (domain := domain) (f := f)
      (s := Finset.image 
        (domain.subdomainNatReversed k) S)
      (by {
        intro x hx
        simp at hx
        rcases hx with ⟨x', ⟨_, hx'⟩⟩ 
        rw [←hx', CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] 
        exact CosetFftDomain.mem_coset_domain_self
      })
      (u := fun i => u (cast' i))
      (by {
        intros i j hj
        have h_spec : u (cast' i) ∈ F⦃< d / (2 ^ k)⦄[X] ∧ (ReedSolomon.evalOnPoints (domain.subdomainNatReversed k)) (u (cast' i)) = v (cast' i) := Classical.choose_spec (h_rs (cast' i))
        simp [ReedSolomon.evalOnPoints] at h_spec
        rcases h_spec with ⟨_, h_spec⟩
        simp at hj
        rcases hj with ⟨j', hj, hj'⟩
        have h_spec := congrFun h_spec j'
        simp at h_spec
        simp
        rw [←hj', h_spec]
        specialize h' (cast' i) hj 
        simp at h'
        rw [h']
        congr
      })
      (d := d)
      (by assumption)
      (by assumption)
      (by assumption)
      (by {
        intro i
        have h_spec : u (cast' i) ∈ F⦃< d / (2 ^ k)⦄[X] ∧ 
          (ReedSolomon.evalOnPoints (domain.subdomainNatReversed k)) (u (cast' i)) = v (cast' i) := Classical.choose_spec (h_rs (cast' i))
        rcases h_spec with ⟨h_spec, _⟩
        simp [degreeLT] at h_spec
        by_cases heq : u (cast' i) = 0
        · simp [heq]
          omega
        · rw [Polynomial.natDegree_lt_iff_degree_lt heq]
          rw [Polynomial.degree_lt_iff_coeff_zero]
          exact h_spec
      })
    rw [Finset.card_image_of_injective _ (CosetFftDomain.injective)] at contradiction
    have contradiction : (Δ₀(f, code (domain : Fin (2 ^ n) ↪ F) d) : ENNReal)
      ≤ (↑(2 ^ n) : ℚ≥0) * δ := by
      apply le_trans 
      · rewrite [ENat.toENNReal_le]
        exact contradiction
      · apply le_trans (b := (2 ^n : ENNReal) - 2^k * (1 - ↑δ) * 2 ^ (n - k))
        · rewrite [ENat.toENNReal_sub]
          rw [show ENat.toENNReal (2 ^ n) = (2 ^ n : ENNReal) by simp] 
          rw [ENNReal.sub_le_sub_iff_left] <;> try simp
          · apply le_trans
            · rewrite [mul_assoc]
              rewrite [ENNReal.mul_le_mul_iff_right] <;> try simp
              have h_card := ENNReal.coe_le_coe_of_le h_card
              apply (swap le_trans h_card)
              norm_cast
            · norm_cast
          · rw [mul_comm, ←mul_assoc] 
            rw [←pow_add]
            rw [Nat.sub_add_cancel (by {
              rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
              omega
            })]
            apply le_trans (b := 2 ^ n * 1)
            · rw [ENNReal.mul_le_mul_iff_right] <;> try simp
            · simp 
        · rw [mul_comm, ←mul_assoc]
          rw [←pow_add]
          rw [Nat.sub_add_cancel (by {
            rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
            omega
          })]
          conv =>
            lhs
            lhs
            rw [←mul_one (2 ^ n)]
          rw [←ENNReal.mul_sub (by simp)]
          rw [ENNReal.sub_sub_cancel (by simp)
            (by {
              simp at δ_lt
              obtain ⟨_, δ_lt⟩ := δ_lt
              apply le_trans
              · exact le_of_lt δ_lt 
              · simp
            })]
          norm_cast
    have contradiction : δᵣ(f, code (domain : Fin (2 ^ n) ↪ F) d) ≤ δ := by
      rw [relDistFromCode_eq_distFromCode_div]
      rw [ENNReal.div_le_iff_le_mul (by simp) (by simp)]
      apply le_trans contradiction
      simp
      rw [mul_comm]
      norm_cast
    simp at δ_lt
    obtain ⟨δ_lt, _⟩ := δ_lt
    have contradiction := lt_of_lt_of_le δ_lt contradiction 
    simp at contradiction

end
end ProximityGap
