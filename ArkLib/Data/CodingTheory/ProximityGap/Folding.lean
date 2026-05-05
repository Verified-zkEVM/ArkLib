/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
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

/-! This file contains all the definition needed to state
  and prove the lemma 4.9 from [ACFY24] as well as the proof of it.

## Main definitions

* `foldWord`
  : the folding function that is to be used by the verifier to fold
    purported codeword using a random challenge.
* `folding_preserves_distance`
  : lemma 4.9 from [ACFY24]. "Soundness" of the folding operation.
    If a purported codeword `f` 
    has distance `δ` to a given RS-code then, 
    with high probability over the choice of folding randomness, 
    its folding also has distance `δ` to the "k-wise folded" RS-code.
* `foldWord_codeword`
  : a bonus theorem not present in [ACFY24]. "Completeness" of the folding operation.
    folding a codeword is the same RS-encoding folding polynomial applied to
    the message.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E., 
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]
-/

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial

variable {F : Type} [Field F] [DecidableEq F]
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

private lemma roots_of_x_in_domain_card
  (hk : k ≠ 0) :
  Finset.card {i | domain i ^ k = x} ≤ 
    Finset.card 
      (nthRootsFinset k x) := by
  rw [roots_of_x_in_domain_eq hk, Finset.card_preimage]
  exact Finset.card_le_card (by simp)

private lemma roots_of_x_in_domain_le_k
  (hk : k ≠ 0) :
  Finset.card {i | domain i ^ k = x} ≤ k := 
  le_trans (roots_of_x_in_domain_card hk) <| by
  simp only [nthRootsFinset, Multiset.toFinset, card_mk]
  exact le_trans
    (@Multiset.toFinset_card_le F (Classical.decEq F) _)
    (Polynomial.card_nthRoots _ _)
    
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

lemma foldValue_def {α : F} {x : F} :
  foldValue domain f k α x = (foldWordAux domain f (2 ^ k) x).eval α := rfl

lemma foldValue_def' {α : F} {x : F} :
  foldValue domain f k α x = (Lagrange.interpolate {i | domain i ^ (2 ^ k) = x}
    (fun i => domain i) f).eval α := rfl

@[simp]
lemma foldValue_pow_x_k {i : Fin (2 ^ n)} : 
  foldValue domain f k (domain i) ((domain i) ^ (2 ^ k)) = f i := 
  Lagrange.eval_interpolate_at_node _ CosetFftDomain.injOn (by simp)
  
@[simp]
lemma foldValue_zero {k : ℕ} :
  foldValue domain 0 k = 0 := by aesop (add simp [foldValue, foldWordAux])

/-- Fold a word. Takes a word `f` over `Fin (2 ^ n)` and randomness
  `a`, and returns a word over `Fin (2 ^ (n - k))`. -/
noncomputable def foldWord (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : F) :
  Word F (Fin (2 ^ (n - k))) := fun x ↦ 
  foldValue domain f k α (domain.subdomainNatReversed k x)

@[simp]
lemma foldWord_zero {k : ℕ} :
  foldWord domain 0 k = 0 := by aesop (add simp [foldWord])

omit [DecidableEq F] in
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
  · apply eq_of_eval_eq_degree (n := 2 ^ k)
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
          FoldingPolynomial.folding_polynomial_ne_zero_of_ne_zero <|
            fun contra ↦ hf <| by 
              ext x
              aesop 
                (erase Lagrange.interpolate_apply)
                (add safe (by rw [←Lagrange.eval_interpolate_at_node
                  (s := univ) (v := domain) f]))
                (add simp [CosetFftDomain.injective])
        )] at h
        exact h

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

private lemma foldWordAux_coeff_eq_foldWordAuxCoeff_fin
  {i : Fin k} :
  (foldWordAux domain f k x).coeff i =  
    (foldWordAuxCoeff domain f k i x) := by simp [foldWordAux, foldWordAuxCoeff]

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
  (domain : SmoothCosetFftDomain n F) (f : Word F (Fin (2 ^ n))) (k : ℕ) (s' : Finset F) :
  Polynomial (Polynomial F) := ∑ x ∈ s',
    Polynomial.C (singletonIndicator x s') *
      (Polynomial.map Polynomial.C <| foldWordAux domain f k x)

section IndicatedPolynomial

variable {s' : Finset F} 

private instance card_ne_zero (hs' : s'.Nonempty) : NeZero (Finset.card s') where
  out := by aesop

private lemma indicated_polynomial_degree_x_lt (hs' : s'.Nonempty) :
  Bivariate.degreeX (indicatedPolynomial domain f k s') < s'.card := by
  simp only [Bivariate.degreeX, indicatedPolynomial, finset_sum_coeff, coeff_C_mul, coeff_map]
  rw [Finset.sup_lt_iff (by simp [hs'])]
  intro b hb
  exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <| 
    fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      aesop 
        (add simp [singleton_indicator_natDegree_lt_of_mem])
  
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
        
private lemma indicated_polynomial_eq_foldAux
  {α : F} (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x = 
    (foldWordAux domain f k x).eval α := by
  aesop 
    (add simp [indicatedPolynomial, eval_finset_sum])
    (add safe 
      [(by rw [singleton_indicator_eval_eq_zero_of_mem_sdiff]), 
        (by rw [Finset.sum_eq_ite x])])

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
  
private lemma indicated_polynomial_eq_combination_of_correlated
  (hs' : s'.Nonempty)
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f (2 ^ k) i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card) :
  ((indicatedPolynomial domain f (2 ^ k) s').eval (Polynomial.C α)) = 
    ∑ i, (u i) * Polynomial.C (α ^ i.val) := by
  apply Polynomial.eq_of_eval_eq_natDegree (s := s') (n := #s')
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
  [Fintype F]
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
  apply Polynomial.eq_of_eval_eq_natDegree (s := Finset.univ) (n := (2 ^ k))
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

private lemma foldWordAux_poly_sum {a : F} : 
  ((foldWordAux domain f (2 ^ k) a).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e) = 
  foldWordAux domain f (2 ^ k) a := by
  aesop (add safe 
    [(by rw [←Polynomial.sum_monomial_eq]),
     (by rw [Polynomial.sum])])

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

omit [DecidableEq F] in
private lemma eval_comp_x_pow_map_eq {f : Polynomial (Polynomial F)} {x : F}
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

private noncomputable def hammingDistComplementBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ := 
  Finset.card { i ∈ 
    Finset.product 
      Finset.univ 
      (Finset.preimage s (domain.subdomainNatReversed k) CosetFftDomain.injOn) | 
    (domain i.1) ^ (2 ^ k) = domain.subdomainNatReversed k i.2 }

private noncomputable def hammingDistBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ := 
  Fintype.card (Fin (2 ^ n)) - hammingDistComplementBound k domain s 

@[simp]
private lemma contradictory_hamming_dist_zero :
  hammingDistBound k domain ∅ = 2 ^ n := by 
  simp [hammingDistBound, hammingDistComplementBound]

@[simp]
private lemma contradictory_hamming_dist_formula {s : Finset F}
  {d : ℕ}
  (h_s : s ⊆ (domain.subdomainNatReversed k).toFinset)
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n) :
  hammingDistBound k domain s =
    2 ^ n - 2 ^ k * (Finset.card s) := by
    unfold hammingDistBound hammingDistComplementBound 
    simp only [Fintype.card_fin, product_eq_sprod] 
    congr
    rw [show @filter _ _ _ _ = 
        (Finset.preimage s (domain.subdomainNatReversed k) CosetFftDomain.injOn).biUnion 
          (fun i ↦ {j | domain j.1 ^ 2 ^ k = domain.subdomainNatReversed k i ∧ j.2 = i} ) by aesop, 
        Finset.card_biUnion (fun x hx y hy hxy a ha₁ ha₂ ↦ by
          by_contra contra
          obtain ⟨c, hc⟩ : ∃ c, c ∈ a := by 
            aesop 
              (add simp [le_eq_subset])
              (add safe (by grind))
          specialize (ha₁ hc)
          specialize (ha₂ hc)
          aesop
        )]
    conv =>
      lhs
      congr
      rfl
      ext u
      rw [show (Finset.card _) = #{j | domain j ^ 2 ^ k = 
        (CosetFftDomain.subdomainNatReversed domain k) u} by 
        aesop (add safe (by apply Finset.card_bij (fun a _ ↦ a.1)))
      ]
    rw [Finset.sum_bij (t := s) 
      (g := fun x ↦ Finset.card {j | domain j ^ (2 ^ k) = x})
      (i := fun i _ ↦ domain.subdomainNatReversed k i)
      (by aesop)
      CosetFftDomain.injOn
      (by {
        intro b hb
        obtain ⟨a, ha⟩ : ∃ i, b = (CosetFftDomain.subdomainNatReversed domain k) i := by
          rw [←CosetFftDomain.mem_coset_def, 
            ←CosetFftDomain.mem_coset_finset_iff_mem_coset_domain]
          exact h_s hb
        exists a
        aesop
      }) 
      (by simp)]
    rw [Finset.sum_bij (t := s) 
      (g := fun i ↦ 2 ^ k) (fun i _ ↦ i) 
      (by aesop)
      (by aesop)
      (by aesop) 
      (fun a ha ↦ by
        rw [roots_in_domain_card_eq_if_x_in_domain
          (by {
            rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)] 
            omega
        }) (by {
          rw [←CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] 
          exact h_s ha
        })]
      )]
    aesop (add safe (by grind))

private lemma correlated_agreement_implies_contradictory_hamm_dist
  [Fintype F]
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
        hammingDistBound k domain s := by
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
    · simp only [hammingDist, ne_eq, hammingDistBound, Fintype.card_fin]
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
      rw [eval_comp_x_pow_map_eq, h_eq]
      by_cases h_s'_s : s' = s
      · rw [h_s'_s,
            ←eval_comm, 
            indicated_polynomial_eq_foldAux (by simp [h_a_s]),
            ←h_eq, 
            ←foldValue_def, 
            foldValue_pow_x_k]
      · rw [indicated_polynomial_eq_foldAux' (u := u) (by aesop)] <;> try assumption
        · rw [←foldValue_def, ←h_eq, foldValue_pow_x_k]
        · intro i x hx
          have hx := (pick_subset_subset : s' ⊆ s) hx
          rw [h_u _ _ hx]
        · intro i
          exact lt_of_lt_of_le 
            (h_u_deg i) 
            (by rw [pick_subset_card_eq_of_ne h_s'_s])

set_option linter.unusedFintypeInType false in -- false alert
private lemma dist_from_code_bound_of_correlated_agreement
  [Fintype F]
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomainNatReversed k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
      foldWordAuxCoeff domain f (2 ^ k) i x)
  {d : ℕ}
  (h_k_d : 2 ^ k ≤ d)
  (h_d : d ≤ 2 ^ n)
  (h_u_deg : ∀ i, (u i).natDegree < d / (2 ^ k)) :
  Δ₀(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d)
        ≤ 2 ^ n -
          2 ^ k * (Finset.card s) := by
  simp only [distFromCode, SetLike.mem_coe]
  exact sInf_le_of_le
    (b := ↑(hammingDistBound k domain s))
    (h := by 
      aesop 
        (add safe 
          (by rw [contradictory_hamming_dist_formula]))
    ) <| by
    obtain ⟨f', h_f'_deg, hdist⟩ := 
      correlated_agreement_implies_contradictory_hamm_dist h_s h_u h_k_d (by {
    exact le_trans h_k_d <| by
      exact le_trans h_d <| by
        rw [←CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2 (ω := domain)]
        simp only [CosetFftDomain.toFinset]
        exact Finset.card_le_card (by simp)
  }) h_u_deg
    simp only [code, evalOnPoints, Submodule.mem_map, 
      exists_exists_and_eq_and]
    exists f'
    aesop 
      (add simp [Polynomial.degreeLT])
      (add safe (by rw [Polynomial.coeff_eq_zero_of_natDegree_lt]))
      (add safe (by omega))

private lemma folded_rate_div_eq_helper {d : ℕ}
  (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) :
  (↑(d / 2 ^ k) : ℚ≥0) / 2 ^ (n - k) = (↑d : ℚ≥0) / 2 ^ n := by
  obtain ⟨m, rfl⟩ := hkd
  simp +zetaDelta only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
    mul_div_cancel_left₀, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at *
  rw [←Nat.add_sub_cancel' hkn, 
      pow_add, 
      mul_div_mul_left _ _ (by positivity)] 
  norm_num

omit [DecidableEq F] in
/-- The rate of the folded RS-code is the same. -/
lemma folded_rate_eq {d : ℕ} (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) : 
  LinearCode.rate 
      (ReedSolomon.code (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) (d / (2 ^ k))) =
    LinearCode.rate (ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d) := by
  simp only [rateOfLinearCode_eq_min_div, Fintype.card_fin, min_def, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat]
  by_cases hif : d ≤ 2 ^ n
  · simp only [hif, ↓reduceIte]
    have hif : d / 2 ^ k ≤ 2 ^ (n - k) := by
      rw [Nat.div_le_iff_le_mul (by simp)]
      exact le_trans hif <| by
        rw [←pow_add, Nat.sub_add_cancel hkn]
        grind
    aesop (add safe forward [folded_rate_div_eq_helper])
  · simp only [hif, ↓reduceIte, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
    not_false_eq_true, div_self]
    have hif := Nat.div_le_div_right (c := 2 ^ k) (Nat.le_of_lt (not_le.mp hif))
    rw [show 2 ^ n / 2 ^ k = 2 ^ (n - k) by 
      aesop (add safe 
        [(by rw [Nat.div_eq_iff]), 
          (by rw [←pow_add]), 
          (by grind)])
    ] at hif
    rcases (Nat.lt_or_eq_of_le hif) with hif | hif
    · aesop (add safe (by omega)) 
    · aesop 
        (add safe forward [div_eq_one_iff_eq])
        (add safe [(by norm_cast)])

omit [DecidableEq F] in
/-- The square root of the rate of the folded RS-code is the same. -/
lemma folded_sqrtRate_eq {d : ℕ} (hkn : k ≤ n) (hkd : 2 ^ k ∣ d) : 
  ReedSolomon.sqrtRate 
     (d / (2 ^ k)) 
     (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) =
    ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F) := by
  aesop (add simp [ReedSolomon.sqrtRate, folded_rate_eq])


set_option linter.unusedVariables false in -- linter complains about `δ_gt_0`
                                           -- which is a result of it missing
                                           -- from the proximity gap theorem args.
/--
Folding preserves distance from Reed–Solomon codes.

For any word `f` over the smooth coset FFT domain, degree parameter `d`,
folding parameter `k`, and distance threshold `δ` satisfying
`0 < δ < min (δᵣ(f, RS[d])) (1 - sqrtRate(d))`, the probability over a
uniformly random folding challenge `r : F` that the folded word is within
relative distance `δ` of the Reed–Solomon code of reduced degree
`d / 2^k` on the folded subdomain is bounded by the proximity-gap error
term.

This is Lemma 4.9 from [ACFY24]: a random `2^k`-folding step preserves distance from
the corresponding Reed–Solomon code except with probability controlled by
`ProximityGap.errorBound`.
-/
theorem folding_preserves_distance
  [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {d k : ℕ}
  {δ : ℝ≥0}
  (k_div_d : 2 ^ k ∣ d)
  (hd0 : 0 < d)
  (h_d_n : d ≤ 2 ^ n)
  (δ_gt_0 : 0 < δ) -- this one is not used but should be.
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) d))
    (1 - (ReedSolomon.sqrtRate d (domain : Fin (2 ^ n) ↪ F)))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r, 
      ReedSolomon.code (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) 
      (d / (2 ^ k))) ≤ δ] ≤
        ((2 ^ k) - 1) * ProximityGap.errorBound δ (d / (2 ^ k)) 
        (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) := by
    have h_k_d : 2 ^ k ≤ d := by exact Nat.le_of_dvd (by omega) k_div_d
    have h_k_le_n : k ≤ n := by
      rw [←Nat.pow_le_pow_iff_right (a := 2) (by simp)]
      omega
    have bound_tighter : 
      (↑δ) ≤ 1 - ReedSolomon.sqrtRate (d / (2 ^ k)) 
        (domain.subdomainNatReversed k : Fin (2 ^ (n - k)) ↪ F) := 
      le_of_lt <| by
        aesop 
          (add safe [(by rw [folded_sqrtRate_eq])])
          (add safe [(by grind)])
          (add safe (by norm_cast at *))
    have correlated_agreement :=
      @correlatedAgreement_affine_curves (Fin (2 ^ (n - k))) _ _ F _ _ _ 
        (2 ^ k - 1) (d / (2 ^ k)) 
        (domain := domain.subdomainNatReversed k) (δ := δ) 
        (hδ := bound_tighter)
    unfold foldWord δ_ε_correlatedAgreementCurves at *
    by_contra contra
    simp only [not_le, foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha, bind_pure_comp, Functor.map, 
      PMF.bind_apply,
      PMF.uniformOfFintype_apply, 
      comp_apply, PMF.pure_apply, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero, tsum_fintype] at contra correlated_agreement
    let cast (x : Fin (2 ^ k - 1 + 1)) : Fin (2 ^ k) := 
      Fin.cast (by rw [Nat.sub_add_cancel (by omega)]) x
    let cast' (x : Fin (2 ^ k)) : Fin (2 ^ k - 1 + 1) :=
      Fin.cast (by rw [Nat.sub_add_cancel (by omega)]) x
    have bijective_cast : Bijective cast := by
      rw [bijective_iff_has_inverse]
      exists cast'
      simp [LeftInverse, RightInverse, cast, cast']
    specialize correlated_agreement 
      (Matrix.of (fun i j ↦ foldWordAuxCoeff domain f (2 ^ k) 
        (cast i) 
        (domain.subdomainNatReversed k j)))
    have correlated_curve_eq_sum_of_foldWord_coeffs {a : F} : 
      ∑ i : Fin (2 ^ k - 1 + 1), a ^ (↑i : ℕ) • 
        Matrix.of (fun i j ↦ 
          foldWordAuxCoeff domain f (2 ^ k) (cast i) (domain.subdomainNatReversed k j)) i =
      (fun x ↦ 
        ∑ j, foldWordAuxCoeff domain f (2 ^ k) j 
          (domain.subdomainNatReversed k x) * a ^ (↑j : ℕ)) := by
      ext x
      simp only [sum_apply]
      exact Fintype.sum_bijective cast bijective_cast _ _ <| 
        fun i ↦ by simp [cast, mul_comm]
    specialize correlated_agreement (by {
      conv_lhs =>
        rhs
        ext a
        rw [correlated_curve_eq_sum_of_foldWord_coeffs]
      norm_cast at contra
    }) 
    simp only [jointAgreement, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ge_iff_le,
      SetLike.mem_coe, Matrix.of_apply] at correlated_agreement
    obtain ⟨S, h_card, v, h'⟩ := correlated_agreement
    rw [forall_and] at h'
    rcases h' with ⟨h_rs, h'⟩ 
    simp only [code, Submodule.mem_map] at h_rs
    let u : Fin (2 ^ k - 1 + 1) → Polynomial F :=
      fun i => Classical.choose (h_rs i)
    have contradiction := dist_from_code_bound_of_correlated_agreement (domain := domain) (f := f)
      (s := Finset.image 
        (domain.subdomainNatReversed k) S)
      (fun x hx ↦ by
        rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] 
        simp only [mem_image] at hx
        obtain ⟨x', _, hx'⟩ := hx
        aesop
      )
      (u := u ∘ cast')
      (fun i j hj ↦ by
        clear *- hj h'
        let i' := cast' i
        obtain ⟨j', hj, _⟩ := by simpa using hj
        specialize h' i' hj
        have h_spec := congrFun (a := j') <| Classical.choose_spec (h_rs i') |>.2
        aesop (add norm evalOnPoints)
      )
      (d := d)
      h_k_d
      h_d_n
      (fun i ↦ by
        obtain ⟨h_spec, _⟩ : u (cast' i) ∈ F⦃< d / (2 ^ k)⦄[X] ∧ 
          _ := Classical.choose_spec (h_rs (cast' i))
        simp only [degreeLT, ge_iff_le, Submodule.mem_iInf, LinearMap.mem_ker,
          lcoeff_apply] at h_spec
        by_cases heq : u (cast' i) = 0
        · simp [heq, h_k_d]
        · rw [comp_apply, 
              Polynomial.natDegree_lt_iff_degree_lt heq,
              Polynomial.degree_lt_iff_coeff_zero]
          exact h_spec
      )
    rw [Finset.card_image_of_injective _ CosetFftDomain.injective] at contradiction
    have contradiction : (Δ₀(f, code (domain : Fin (2 ^ n) ↪ F) d) : ENNReal)
      ≤ (↑(2 ^ n) : ℚ≥0) * δ := 
      le_trans (ENat.toENNReal_le.mpr contradiction) <| by
        apply le_trans 
          (b := (2 ^ n : ENNReal) - 2 ^ k * (1 - ↑δ) * 2 ^ (n - k))
        · rw [ENat.toENNReal_sub,
              show ENat.toENNReal (2 ^ n) = (2 ^ n : ENNReal) by simp,
              ENNReal.sub_le_sub_iff_left (h' := by simp)
                (h := swap (le_trans (b := 2 ^ n * 1)) (by simp) <| by
                  rw [mul_comm, 
                      ←mul_assoc,
                      ←pow_add,
                      Nat.sub_add_cancel h_k_le_n,
                      ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
                  simp
          )]
          apply le_trans (b := 2 ^ k * ↑↑(#S))
          · rw [mul_assoc,
                ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
            have h_card := ENNReal.coe_le_coe_of_le h_card
            exact (swap le_trans h_card) (by norm_cast)
          · norm_cast
        · rw [mul_comm, 
              ←mul_assoc,
              ←pow_add,
              Nat.sub_add_cancel h_k_le_n]
          conv_lhs =>
            lhs
            rw [←mul_one (2 ^ n)]
          rw [←ENNReal.mul_sub (by simp),
              ENNReal.sub_sub_cancel (by simp)
                (by {
                  simp only [lt_inf_iff] at δ_lt
                  exact le_trans (le_of_lt δ_lt.2) (by simp)
                })]
          norm_cast
    have contradiction : δᵣ(f, code (domain : Fin (2 ^ n) ↪ F) d) ≤ (δ : NNReal) := by
      rw [relDistFromCode_le_iff_distFromCode_toENNReal_le]
      exact le_trans contradiction <| by
        simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        rw [mul_comm]
        norm_cast
    simp only [lt_inf_iff] at δ_lt
    simpa using lt_of_lt_of_le δ_lt.1 contradiction 
    
end
end ProximityGap
