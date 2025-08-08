/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.NovelPolynomialBasis

/-!
# Additive NTT Algorithm (Algorithm 2, LCH14)

This file defines the FRI-Binius ([DP24]) variant of the Additive NTT algorithm originally
introduced in [LCH14]. This variant adopts concrete optimizations and a different proof strategy,
making it highly suitable for the FRI-Binius proof system, while still fully complying with the
original algorithm in [LCH14] through a different interpretation.

## Main Definitions

- `sDomain`: The intermediate evaluation domain `S⁽ⁱ⁾` for
the round `i` in the Additive NTT algorithm
- `qMap`: The quotient map `q⁽ⁱ⁾(X)` that relates successive domains
- `intermediateNormVpoly`: The `i`-th order subspace vanishing
polynomials `Ŵₖ⁽ⁱ⁾` over domain `S⁽ⁱ⁾`
- `intermediateNovelBasisX`: The intermediate novel basis `Xⱼ⁽ⁱ⁾` for
the round `i` in the Additive NTT algorithm
- `intermediateEvaluationPoly`: The intermediate evaluation polynomial `P⁽ⁱ⁾(X)`
  for the round `i` in the Additive NTT algorithm

- `additiveNTT`: The main implementation of the Additive NTT encoding algorithm.
- `NTTStage`: The main implementation of each NTT stage in the Additive NTT encoding algorithm.
- `additiveNTT_correctness`: Main correctness statement of the encoding algorithm.
- `additiveNTTInvariant`: Describes the invariant for each loop in the algorithm,
which states whether the result of an encoding round is correct
- `NTTStage_correctness`: Main correctness statement of each NTT stage in the encoding algorithm,
this proves that if the previous round satisfies the invariant, then the current round also

## TODOs
- Define computable additive NTT and transfer correctness proof to it

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).

- [LCH14] Sian-Jheng Lin, Wei-Ho Chung, and Yunghsiang S. Han. "Novel Polynomial Basis and Its
  Application to Reed–Solomon Erasure Codes". In: IEEE 55th Annual Symposium on Foundations of
  Computer Science. 2014, pp. 316–325. doi: 10.1109/FOCS.2014.41.

- [GGJ96] J. von zur Gathen and J. Gerhard, "Arithmetic and factorization of polynomial
  over F2 (extended abstract)", in Proceedings of the 1996 International Symposium on
  Symbolic and Algebraic Computation, Zurich, Switzerland, 1996, pp. 1–9.
-/

set_option linter.style.longFile 2400

open Polynomial AdditiveNTT
namespace AdditiveNTT

universe u

-- We work over a generic field `L` which is an algebra over a ground field `𝔽q` of prime
-- characteristic.
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q]
(h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))) (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
variable [Algebra 𝔽q L]

-- Let `β` be a basis of `L` over `𝔽q`, indexed by natural numbers.
variable (β : Fin r → L) (hβ_lin_indep : LinearIndependent 𝔽q β)
variable (ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r) -- ℓ ∈ {1, ..., r-1}

section IntermediateStructures

/-! ## 1. Intermediate Structures: Domains, Maps, and Bases

This section defines the intermediate evaluation domains, quotient maps, and the structure
of the subspace vanishing polynomials and their bases. These are the core algebraic objects
underlying the Additive NTT algorithm.
-/

/-- The intermediate evaluation domain `S⁽ⁱ⁾`, defined as the image of the full evaluation space
under the normalized subspace vanishing polynomial `Ŵᵢ(X)`.
`∀ i ∈ {0, ..., r-1}`, we define `Uᵢ:= <β₀, ..., βᵢ₋₁>_{𝔽q}`, note that `Uᵣ` is not used.
`∀ i ∈ {0, ..., r-1}, S⁽ⁱ⁾` is the image of the subspace `U_{ℓ+R}`
  under the `𝔽q`-linear map `x ↦ Ŵᵢ(x)`. -/
noncomputable def sDomain (i : Fin r) : Subspace 𝔽q L :=
  let W_i_norm := normalizedW 𝔽q β i
  let h_W_i_norm_is_additive : IsLinearMap 𝔽q (fun x : L => W_i_norm.eval x) :=
    AdditiveNTT.normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i
  Submodule.map (polyEvalLinearMap W_i_norm h_W_i_norm_is_additive)
    (U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩)

/-- The quotient map `q⁽ⁱ⁾(X)` that relates successive domains.
`q⁽ⁱ⁾(X) := (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)`. Usable range is `∀ i ∈ {0, ..., r-2}` -/
noncomputable def qMap (i : Fin r) : L[X] :=
  let constMultiplier := ((W 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  C constMultiplier * ∏ c: 𝔽q, (X - C (algebraMap 𝔽q L c))

omit [DecidableEq L] in
theorem qMap_eval_𝔽q_eq_0 (i : Fin r):
  ∀ c: 𝔽q, (qMap 𝔽q β i).eval (algebraMap 𝔽q L c) = 0 := by
  intro u
  rw [qMap]
  set vpoly𝔽q := ∏ c: 𝔽q, (X - C ((algebraMap 𝔽q L) c)) with h_vpoly𝔽q

  have h_right_term_vanish: eval ((algebraMap 𝔽q L) u) (vpoly𝔽q) = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C, vpoly𝔽q]
    rw [Finset.prod_eq_zero_iff]
    -- ⊢ ∃ a ∈ Finset.univ, (algebraMap 𝔽q L) u - (algebraMap 𝔽q L) a = 0
    have hu: u ∈ (Finset.univ: Finset 𝔽q) := by simp only [Finset.mem_univ]
    use u
    constructor
    · exact hu
    · simp only [sub_self]
  simp only [eval_mul, eval_C, h_right_term_vanish, mul_zero]

/-- **Lemma 4.2.** The quotient maps compose with the `Ŵ` polynomials.
`q⁽ⁱ⁾ ∘ Ŵᵢ = Ŵᵢ₊₁, ∀ i ∈ {0, ..., r-2}`. -/
lemma qMap_comp_normalizedW
  (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
  (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent (R:=𝔽q) (M:=L) (v:=β)) (i : Fin r) (h_i_add_1 : i + 1 < r):
  (qMap 𝔽q β i).comp (normalizedW 𝔽q β i) = normalizedW 𝔽q β (i + 1) := by
  let q := Fintype.card 𝔽q
  -- `q⁽ⁱ⁾ ∘ Ŵᵢ = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ Ŵᵢ`
  -- `= ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (X^q - X)) ∘ Ŵᵢ` -- X^q - X = ∏_{c ∈ 𝔽q} (X - c)
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Ŵᵢ(X)^q - Ŵᵢ(X))` -- composition
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q/Wᵢ(βᵢ)^q - Wᵢ(X)/Wᵢ(βᵢ))`
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q/Wᵢ(βᵢ)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1)/Wᵢ(βᵢ)^q)`
  -- `= (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * (Wᵢ(X)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1)) / Wᵢ(βᵢ)^q`
  -- `= (Wᵢ(βᵢ)^q * (Wᵢ(X)^q - Wᵢ(X) * Wᵢ(βᵢ)^(q-1))) / (Wᵢ₊₁(βᵢ₊₁) * Wᵢ(βᵢ)^q)`
  -- `= (Wᵢ(X)^q - Wᵢ(βᵢ)^(q-1) * Wᵢ(X)) / Wᵢ₊₁(βᵢ₊₁)`
  -- `= Wᵢ₊₁(X)` -- Q.E.D via AdditiveNTT.W_linear_comp_decomposition

  -- Define aliases for mathematical objects to improve readability
  set q := Fintype.card 𝔽q
  set W_i := W 𝔽q β i with h_W_i
  set W_i_plus_1 := W 𝔽q β (i + 1) with h_W_i_plus_1
  set val_i := W_i.eval (β i) with h_val_i
  set val_i_plus_1 := W_i_plus_1.eval (β (i + 1)) with h_val_i_plus_1

  -- Establish that the denominators in the definitions are non-zero
  have h_val_i_ne_zero : val_i ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β hβ_lin_indep i
  have h_val_i_plus_1_ne_zero : val_i_plus_1 ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero 𝔽q β hβ_lin_indep (i + 1)

  -- The proof proceeds by a chain of equalities
  calc
    (qMap 𝔽q β i).comp (normalizedW 𝔽q β i)
    _ = C (val_i ^ q / val_i_plus_1)
    * (∏ c:𝔽q, (X - C (algebraMap 𝔽q L c))).comp (normalizedW 𝔽q β i) := by
      rw [qMap, mul_comp, C_comp]
    _ = C (val_i ^ q / val_i_plus_1) * ((normalizedW 𝔽q β i) ^ q - normalizedW 𝔽q β i) := by
      simp_rw [prod_comp, sub_comp, X_comp, C_comp]
      rw [prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L h_Fq_card_gt_1]
    _ = C (1 / val_i_plus_1) * (W_i ^ q - C (val_i ^ (q - 1)) * W_i) := by
      rw [normalizedW, mul_sub, mul_pow, C_pow]
      have hq_pos : q > 0 := by linarith
      have h_C: C (val_i ^ q / val_i_plus_1) = C (1 / val_i_plus_1) * C (val_i ^ q) := by
        rw [←C_mul]
        ring_nf
      rw [h_C]
      conv_lhs =>
        rw [mul_assoc, mul_assoc]
        rw [←mul_sub]
      rw [←h_val_i, ←h_W_i]
      rw [←C_pow]
      rw [←mul_assoc, ←C_mul]
      have h_mul: val_i ^ q * (1 / val_i) ^ q = 1 := by
        rw [←mul_pow (n:=q)]
        rw [←inv_eq_one_div]
        rw [mul_inv_cancel₀ (h:=h_val_i_ne_zero), one_pow]
      rw [h_mul, C_1, one_mul]
      rw [←mul_assoc, ←C_mul]
      have h_mul_2: val_i ^ q * (1 / val_i) = val_i ^ (q - 1) := by
        rw [←inv_eq_one_div]
        rw [←mul_pow_sub_one (hn:=by omega), mul_comm (a:=val_i), mul_assoc]
        rw [mul_inv_cancel₀ (h:=h_val_i_ne_zero), mul_one]
      rw [h_mul_2, C_pow]
    _ = C (1 / val_i_plus_1) * W_i_plus_1 := by -- `W_i^q - C(val_i^(q-1)) * W_i` = `W_{i+1}`
      have W_linear := AdditiveNTT.W_linear_comp_decomposition 𝔽q β h_Fq_card_gt_1
        h_Fq_char_prime hβ_lin_indep i (p:=X)
      simp_rw [comp_X] at W_linear
      simp_rw [q, val_i, W_i, W_i_plus_1]
      rw [W_linear]
      · simp only [one_div, map_pow]
      · omega
    _ = normalizedW 𝔽q β (i + 1) := by -- Q.E.D.
      rw [normalizedW]

omit [DecidableEq L] in
/-- The evaluation of the quotient map `q⁽ⁱ⁾(X)` is an `𝔽q`-linear map.
  Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem qMap_is_linear_map
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (i : Fin r):
  IsLinearMap 𝔽q (f:=fun inner_p ↦ (qMap 𝔽q β i).comp inner_p) := by
  set q := Fintype.card 𝔽q
  set constMultiplier := ((W 𝔽q β i).eval (β i))^q / ((W 𝔽q β (i + 1)).eval (β (i + 1)))
  have h_q_poly_form : qMap 𝔽q β i = C constMultiplier * (X ^ q - X) := by
    rw [qMap, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L h_Fq_card_gt_1 (p:=X)]
  -- Linearity of `x ↦ c * (x^q - x)` over `𝔽q`

  constructor
  · intro f g
    -- `q⁽ⁱ⁾ ∘ (f + g) = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ (f + g)` -- definition
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (f + g) := by
        rw [h_q_poly_form]
      _ = ((C constMultiplier).comp (f + g)) * (((X: L[X]) ^ q - X).comp (f+g)) := by
        rw [mul_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f+g) - X.comp (f+g)) := by
        rw [C_comp, sub_comp]
      _ = (C constMultiplier) * ((X ^ q).comp (f+g) - (X.comp f + X.comp g)) := by
        rw [X_comp]
        conv_lhs =>
          enter [2, 2]
          rw [←X_comp (p:=f), ←X_comp (p:=g)]
      _ = (C constMultiplier) * (f^q + g^q - (X.comp f + X.comp g)) := by
        rw [pow_comp, X_comp]
        unfold q
        rw [Polynomial.frobenius_identity_in_algebra
          (h_Fq_char_prime:=h_Fq_char_prime) (f:=f) (g:=g)]
      _ = (C constMultiplier) * (((X^q).comp f - X.comp f) + ((X^q).comp g - X.comp g)) := by
        rw [pow_comp, X_comp, X_comp, pow_comp, X_comp]
        ring
      _ = (C constMultiplier) * (((X: L[X]) ^ q - X).comp (f) + ((X: L[X]) ^ q - X).comp (g)) := by
        rw [←sub_comp, ←sub_comp]
      _ = (qMap 𝔽q β i).comp f + (qMap 𝔽q β i).comp g := by
        rw [h_q_poly_form]
        rw [mul_add]
        rw [mul_comp, mul_comp, C_comp, C_comp]
  · intro c f
      -- `q⁽ⁱ⁾ ∘ (c • f) = ((Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)) ∘ (c • f)` -- definition
    calc
      _ = (C constMultiplier * (X ^ q - X)).comp (c • f) := by
        rw [h_q_poly_form]
      _ = (C constMultiplier).comp (c • f) * ((c • f) ^ q - (c • f)) := by
        rw [mul_comp, sub_comp, pow_comp, X_comp]
      _ = (C constMultiplier).comp (c • f) * (c ^ q • f ^ q - c • f) := by
        rw [C_comp, smul_pow]
      _ = (C constMultiplier).comp (c • f) * (c • f^q - c • f) := by
        rw [FiniteField.pow_card]
      _ = (C constMultiplier).comp (c • f) * (C (algebraMap 𝔽q L c) * (f^q - f)) := by
        conv_lhs =>
          enter [2]
          rw [algebra_compatible_smul L c, algebra_compatible_smul L c]
          rw [smul_eq_C_mul, smul_eq_C_mul]
          rw [←mul_sub]
      _ = c • ((C constMultiplier).comp (c • f) * (f^q - f)) := by
        rw [←mul_assoc, mul_comm (a:=(C constMultiplier).comp (c • f)), mul_assoc]
        rw [←smul_eq_C_mul]
        rw [←algebra_compatible_smul L c]
      _ = c • (((C constMultiplier) * ((X: L[X])^q - X)).comp f) := by
        rw [C_comp]
        conv_lhs =>
          enter [2, 2]
          rw [←X_comp (p:=f)]
        rw [←pow_comp, ←sub_comp]
        rw [C_mul_comp]
      _ = c • (qMap 𝔽q β i).comp f := by
        rw [h_q_poly_form]

/-- **Theorem 4.3.** The quotient map `q⁽ⁱ⁾` maps the domain `S⁽ⁱ⁾` to `S⁽ⁱ⁺¹⁾`.
  Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem qMap_maps_sDomain
(h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
(h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
(hβ_lin_indep : LinearIndependent 𝔽q β)
(ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r)
(i : Fin r) (h_i_add_1 : i + 1 < r) :
  have q_comp_linear_map := qMap_is_linear_map 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime i
  have q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
    (f:=qMap 𝔽q β i) q_comp_linear_map
  let q_i_map := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
  let S_i: Subspace 𝔽q L := sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ R_rate h_ℓ_add_R_rate i
  let S_i_plus_1: Subspace 𝔽q L := sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ R_rate h_ℓ_add_R_rate (i + 1)
  Submodule.map q_i_map S_i = S_i_plus_1 :=
by
  set q_comp_linear_map := qMap_is_linear_map 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime i
  set q_eval_linear_map := linear_map_of_comp_to_linear_map_of_eval
    (f:=qMap 𝔽q β i) q_comp_linear_map
  -- Unfold definitions and apply submodule and polynomial composition properties
  simp_rw [sDomain]
  -- `q⁽ⁱ⁾(S⁽ⁱ⁾) = q⁽ⁱ⁾(Ŵᵢ(⟨β₀, ..., β_{ℓ+R-1}⟩))`
  -- `= Ŵᵢ₊₁(⟨β₀, ..., β_{ℓ+R-1}⟩)`
  -- `= S⁽ⁱ⁺¹⁾`
  -- `⊢ map (q_i_map ∘ₗ Ŵᵢ_map) U = map (Ŵᵢ₊₁) U`
  rw [←Submodule.map_comp] -- for two nested maps (composition) over the same subspace
  -- The goal becomes `q_i_map ∘ₗ Ŵᵢ_map = Ŵᵢ₊₁`
  congr
  -- ⊢ polyEvalLinearMap (qMap 𝔽q β i) ⋯ ∘ₗ polyEvalLinearMap (normalizedW 𝔽q β i) ⋯ =
  -- polyEvalLinearMap (normalizedW 𝔽q β (i + 1)) ⋯

  -- We now have `(qMap ...).eval ((normalizedW ... i).eval x) = (normalizedW ... (i + 1)).eval x`.
  -- The `Polynomial.eval_comp` lemma states `p.eval (q.eval x) = (p.comp q).eval x`.
  set f := polyEvalLinearMap (qMap 𝔽q β i) q_eval_linear_map
  set g := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)
  set t := polyEvalLinearMap (normalizedW 𝔽q β (i + 1))
    (normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep (i + 1))
  change f ∘ₗ g = t -- equality on composition of linear maps
  ext x
  -- => equality on evaluation at x
  -- (this automatically matches linearity of f ∘ g with linearity of t)
  rw [LinearMap.comp_apply]
  -- ⊢ f (g x) = t x
  simp_rw [f, g, t, polyEvalLinearMap]
  -- unfold the linearmaps into their definitions (toFun, map_add, map_smul)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- NOTE: `LinearMap.coe_mk` and `AddHom.coe_mk` convert linear maps into their functions
  -- ⊢ eval (eval x (normalizedW 𝔽q β i)) (qMap 𝔽q β i) = eval x (normalizedW 𝔽q β (i + 1))
  rw [←Polynomial.eval_comp]
  rw [qMap_comp_normalizedW 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i h_i_add_1]

/-- The composition `q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾ ∘ X`. -/
noncomputable def qCompositionChain (i : Fin r) : L[X] :=
  match i with
  | ⟨0, _⟩ => X
  | ⟨k + 1, h_k_add_1⟩ => (qMap 𝔽q β ⟨k, by omega⟩).comp (qCompositionChain ⟨k, by omega⟩)

omit [DecidableEq L] in
/-- Prove the equality between the recursive definition
of `qCompositionChain` and the Fin.foldl form. -/
lemma qCompositionChain_eq_foldl
  (ℓ R_rate : ℕ)
  (i : Fin r) :
  qCompositionChain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i =
  Fin.foldl (n:=i) (fun acc j =>
    (qMap 𝔽q β ⟨j, by omega⟩).comp acc) (X) := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    rw [qCompositionChain.eq_def]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
    rfl
  | succ k k_h i_h =>
    rw [qCompositionChain.eq_def]
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one']
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    simp only [Fin.coe_cast, Fin.foldl_succ_last, Fin.val_last, Fin.eta, Fin.coe_castSucc]
    congr

/--
**Corollary 4.4.** For each `i ∈ {0, ..., r-1}`, we have `Ŵᵢ = q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾`
(with the convention that for `i = 0`, this is just `X`).
-/
lemma normalizedW_eq_qMap_composition
  (h_W₀_eq_X : W 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  -- We also need the hypotheses for qMap_comp_normalizedW
  (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
  (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (ℓ R_rate : ℕ)
  (i : Fin r) :
  normalizedW 𝔽q β i = qCompositionChain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i :=
by
  -- We proceed by induction on i.
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    -- Base case: i = 0
    -- We need to show `normalizedW ... 0 = qCompositionChain 0`.
    -- The RHS is `X` by definition of the chain.
    rw [qCompositionChain.eq_def]
    -- The LHS is `C (1 / eval (β 0) (W ... 0)) * (W ... 0)`.
    rw [normalizedW, h_W₀_eq_X, eval_X, h_β₀_eq_1, div_one, C_1, one_mul]
    rfl
  | succ k k_h i_h =>
    -- Inductive step: Assume the property holds for k, prove for k+1.
    -- The goal is `normalizedW ... (k+1) = qCompositionChain (k+1)`.
    -- The RHS is `(qMap k).comp (qCompositionChain k)` by definition.
    rw [qCompositionChain.eq_def]
    -- From Lemma 4.2, we know `normalizedW ... (k+1) = (qMap k).comp (normalizedW ... k)`.
    -- How to choose the rhs?
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one']
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    have h_res := qMap_comp_normalizedW 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep k k_h
    -- ⊢ normalizedW 𝔽q β ⟨↑k + 1, k_h⟩ = (qMap 𝔽q β k).comp (qCompositionChain 𝔽q β k)
    rw [←i_h]
    rw [h_res]
    simp only [h_eq]

/-- The vectors `y_j^{(i)} = Ŵᵢ(β_j)` for `j ∈ {i, ..., ℓ+R-1}`. -/
noncomputable def sDomainBasisVectors (i : Fin r) : Fin (ℓ + R_rate - i) → L :=
  fun k => (normalizedW 𝔽q β i).eval (β ⟨i + k.val, by omega⟩)

/-- The vectors `sDomainBasisVectors` are indeed elements of the subspace `sDomain`,
  `∀ i ∈ {0, ..., r-1}`. -/
lemma sDomainBasisVectors_mem_sDomain
    (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
    (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β)
    (ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r)
    (i : Fin r) (k : Fin (ℓ + R_rate - i)) :
  sDomainBasisVectors 𝔽q β ℓ R_rate h_ℓ_add_R_rate i k
    ∈ sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i := by
  have h_i_add_k_lt_r : i + k.val < r := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  simp_rw [sDomain, sDomainBasisVectors]
  -- The vector is `eval Ŵᵢ (β (i + k.val))`
  -- We must show it's in the image of U_{ℓ+R} under `eval Ŵᵢ`.
  -- This is true if the input `β (i + k.val)` is in `U_{ℓ+R}`.
  apply Submodule.mem_map_of_mem
  -- ⊢ β (i + ↑k) ∈ U 𝔽q β (ℓ + R_rate)
  have h_β_i_in_U: β ⟨i + k.val, h_i_add_k_lt_r⟩ ∈ β '' Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
    exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨by norm_num, by omega⟩)
  exact Submodule.subset_span h_β_i_in_U

/-- The S basis -/
def sBasis (i : Fin r) (h_i : i < ℓ + R_rate): Fin (ℓ + R_rate - i) → L :=
  fun k => β ⟨i + k.val, by omega⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Algebra 𝔽q L] in
lemma sBasis_range_eq (i : Fin r) (h_i : i < ℓ + R_rate):
    β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    = Set.range (sBasis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i):= by
  ext x
  constructor
  · intro hx -- hx : x ∈ β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    -- ⊢ x ∈ Set.range fun k ↦ β ⟨↑i + ↑k, ⋯⟩
    rcases hx with ⟨j, hj, rfl⟩
    simp only [Set.mem_Ico] at hj
    simp only [Set.mem_range] -- ⊢ ∃ y : Fin (ℓ + R_rate - ↑i), β ⟨↑i + ↑y, ⋯⟩ = β j
    have h_j_sub_i: j.val - i.val < ℓ + R_rate - i.val := by
      apply Nat.lt_sub_of_add_lt
      rw [Nat.sub_add_cancel]
      · exact hj.2
      · omega
    use ⟨j - i, h_j_sub_i⟩
    unfold sBasis
    simp only
    have h_i_add_j_sub_i : i.val + (j.val - i.val) = j.val := by
      omega
    congr
  · intro hx -- hx : x ∈ Set.range fun k ↦ β ⟨↑i + ↑k, ⋯⟩
    -- ⊢ x ∈ β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    rcases hx with ⟨j, hj, rfl⟩ -- hj : β ⟨↑i + ↑j, ⋯⟩ = x
    simp only [Set.mem_image, Set.mem_Ico]
    use ⟨i.val + j.val, by omega⟩
    constructor
    · -- ⊢ i ≤ ⟨↑i + ↑j, ⋯⟩ ∧ ⟨↑i + ↑j, ⋯⟩ < ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
      constructor
      · -- ⊢ i ≤ ⟨↑i + ↑j, ⋯⟩
        have h_j := j.2
        have h_i_add_j: i.val + j.val < ℓ + R_rate := by omega
        have h_i_add_j_lt_r: i.val + j.val < r := by omega
        apply Fin.mk_le_of_le_val
        conv_rhs => simp only -- remove ↑ in rhs
        omega
      · apply Fin.mk_lt_of_lt_val
        conv_rhs => simp only -- remove ↑ in rhs
        omega
    · rfl

/-- S⁽ⁱ⁾ is the image over `Wᵢ(X)` of the the subspace spanned by `{βᵢ, ..., β_{ℓ+R-1}}`.
  Usable range is `∀ i ∈ {0, ..., ℓ+R-1}`. -/
lemma sDomain_eq_image_of_upper_span (i: Fin r) (h_i: i < ℓ + R_rate):
    let V_i := Submodule.span 𝔽q (Set.range (sBasis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
    let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
      (normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)
    sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i
    = Submodule.map W_i_map V_i :=
by
  -- Proof: U_{ℓ+R} is the direct sum of Uᵢ and Vᵢ.
  -- Any x in U_{ℓ+R} can be written as u + v where u ∈ Uᵢ and v ∈ Vᵢ.
  -- Ŵᵢ(x) = Ŵᵢ(u+v) = Ŵᵢ(u) + Ŵᵢ(v) = 0 + Ŵᵢ(v) = Ŵᵢ(v).
  -- So the image of U_{ℓ+R} is the same as the image of Vᵢ.

  -- Define V_i and W_i_map for use in the proof
  set V_i := Submodule.span 𝔽q (Set.range (sBasis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
  set W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i)
    (normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)

  -- First, show that U_{ℓ+R} = U_i ⊔ V_i (direct sum)
  have h_span_supremum_decomposition : U 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
    = U 𝔽q β i ⊔ V_i := by
    unfold U
    -- U_{ℓ+R} is the span of {β₀, ..., β_{ℓ+R-1}}
    -- U_i is the span of {β₀, ..., β_{i-1}}
    -- V_i is the span of {β_i, ..., β_{ℓ+R-1}}
    have h_ico : Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩
      = Set.Ico 0 i ∪ Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
      ext k
      simp only [Set.mem_Ico, Fin.zero_le, true_and, Set.mem_union]
      constructor
      · intro h
        by_cases hk : k < i
        · left; omega
        · right; exact ⟨Nat.le_of_not_lt hk, by omega⟩
      · intro h
        cases h with
        | inl h => exact Fin.lt_trans h h_i
        | inr h => exact h.2

    rw [h_ico, Set.image_union, Submodule.span_union]
    congr
    -- ⊢ β '' Set.Ico i (ℓ + R_rate)
    -- = Set.range (sBasis 𝔽q β (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i h_i)
    -- Now how that the image of Set.Ico i (ℓ + R_rate)
    -- (from the definition of U_{ℓ+R}) is the same as V_i
    rw [sBasis_range_eq 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i]

  -- Now show that the image of U_{ℓ+R} under W_i_map is the same as the image of V_i
  rw [sDomain, h_span_supremum_decomposition, Submodule.map_sup]

  -- The image of U_i under W_i_map is {0} because W_i vanishes on U_i
  have h_U_i_image : Submodule.map W_i_map (U 𝔽q β i) = ⊥ := by
    -- Show that any element in the image is 0
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    -- x ∈ Submodule.map W_i_map (U 𝔽q β i) means x = W_i_map(y) for some y ∈ U_i
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    -- Show that W_i_map y = 0 for any y ∈ U_i
    have h_eval_zero : (normalizedW 𝔽q β i).eval y = 0 :=
      normalizedWᵢ_vanishing 𝔽q β i y hy
    exact h_eval_zero

  -- Combine the results: ⊥ ⊔ V = V
  rw [h_U_i_image]
  rw [bot_sup_eq]

/-- **Corollary 4.5.** The set `{Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})}` is an `𝔽q`-basis for `S⁽ⁱ⁾`. -/
noncomputable def sDomain_basis (i : Fin r) (h_i : i < ℓ + R_rate) :
    Basis (Fin (ℓ + R_rate - i)) 𝔽q (
      sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i) := by
  -- Let V_i be the "upper" subspace spanned by {βᵢ, ..., β_{ℓ+R-1}}.
  let V_i := Submodule.span 𝔽q (Set.range (sBasis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
  -- Let W_i_map be the linear map given by evaluating the polynomial Ŵᵢ.
  let W_i_map := polyEvalLinearMap (normalizedW 𝔽q β i) (
      normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)

  have h_disjoint : Disjoint (U 𝔽q β i) V_i := by
    -- Uᵢ is span of β over Ico 0 i
    -- Vᵢ is span of β over Ico i (ℓ + R_rate)
    -- The index sets are disjoint.
    have h_set_disjoint : Disjoint (Set.Ico 0 i) (Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩) := by
      simp [Set.disjoint_iff]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ico, Fin.zero_le, true_and,
        Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hx hi
      omega
    -- Since β is linearly independent, the spans of its images over disjoint sets are disjoint.
    unfold V_i
    have h_res := hβ_lin_indep.disjoint_span_image h_set_disjoint
    rw [sBasis_range_eq 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i] at h_res
    exact h_res

  have h_ker_eq_U : LinearMap.ker W_i_map = U 𝔽q β i := by
    rw [kernel_normalizedW_eq_U 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i]

  -- The vectors {βᵢ, ...} form a basis for Vᵢ because β is linearly independent.
  let V_i_basis : Basis (Fin (ℓ + R_rate - i)) 𝔽q V_i :=
    Basis.span (by
      -- This is the proof of linear independence for the vectors {βᵢ, ...}.
      -- It follows because they are a subset of the LI family β.
      have h_sub_li : LinearIndependent 𝔽q (
          fun (k : Fin (ℓ + R_rate - i)) => β ⟨i + k.val, by omega⟩) :=
        hβ_lin_indep.comp (fun (k : Fin (ℓ + R_rate - i))
          => ⟨i + k.val, by omega⟩) (by  -- ⊢ Function.Injective fun k ↦ ⟨↑i + ↑k, ⋯⟩
          intro k₁ k₂ h_eq
          simp at h_eq
          apply Fin.eq_of_val_eq
          omega
        )
      exact h_sub_li)

  -- We construct the isomorphism between Vᵢ and S⁽ⁱ⁾.
  -- S⁽ⁱ⁾ is the image of Vᵢ under W_i_map, and the map is injective on Vᵢ.
  set S_i := sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i
  let iso : V_i ≃ₗ[𝔽q] S_i :=
    LinearEquiv.ofBijective
      (LinearMap.codRestrict S_i (W_i_map.comp (Submodule.subtype V_i))
        (by -- ⊢ ∀ (c : ↥V_i), (W_i_map ∘ₗ V_i.subtype) c ∈ S_i
          intro x
          -- ⊢ (W_i_map ∘ₗ V_i.subtype) x ∈ S_i
          have h_x_in_S_i : (W_i_map.comp (Submodule.subtype V_i)) x ∈ S_i := by
            simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, S_i]
            rw [sDomain_eq_image_of_upper_span 𝔽q h_Fq_char_prime
              h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i h_i]
            exact
              Submodule.apply_coe_mem_map
                (polyEvalLinearMap (normalizedW 𝔽q β i)
                  (normalizedW_is_additive 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i))
                x
          exact h_x_in_S_i
        )) (by
        -- ⊢ Function.Bijective ⇑(LinearMap.codRestrict S_i (W_i_map ∘ₗ V_i.subtype) ⋯)
          constructor
          · -- INJECTIVITY
            intro v1 v2 h_v1_v2
            -- ⊢ v1 = v2
          -- First, simplify the hypothesis by unpacking the map definitions.
            simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Submodule.coe_subtype,
              Function.comp_apply, Subtype.ext_iff] at h_v1_v2
            -- The hypothesis is now `W_i_map ↑v1 = W_i_map ↑v2`.
            -- By linearity, this is equivalent to `W_i_map (↑v1 - ↑v2) = 0`.
            rw [← sub_eq_zero, ← LinearMap.map_sub] at h_v1_v2
            -- To show v1 = v2, we show v1 - v2 = 0.
            -- coercion from a subtype is injective => we show the coerced difference is 0
            apply Subtype.ext
            -- The element `↑(v1 - v2)` is in the kernel of `W_i_map`.
            have h_mem_ker : ↑(v1 - v2) ∈ LinearMap.ker W_i_map := h_v1_v2
            -- The kernel of the evaluation map is the vanishing subspace `Uᵢ`.
            -- Add this before the have h_mem_U line:
            have h_mem_U : ↑(v1 - v2) ∈ U 𝔽q β i := h_ker_eq_U ▸ h_mem_ker
            -- The element `v1 - v2` is in `Vᵢ` since it's a submodule.
            have h_mem_V : ↑(v1 - v2) ∈ V_i := Submodule.sub_mem V_i v1.property v2.property
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            have h_mem_inf : ↑(v1 - v2) ∈ (U 𝔽q β i) ⊓ V_i :=
              Submodule.mem_inf.mpr ⟨h_mem_U, h_mem_V⟩

            -- The subspaces `Uᵢ` and `Vᵢ` are disjoint because they are spanned by
            -- disjoint subsets of the linearly independent set `β`.

            -- Since the intersection is the trivial subspace {0}, our element must be 0.
            rw [h_disjoint.eq_bot] at h_mem_inf
            simp only [Submodule.mem_bot] at h_mem_inf
            simp at h_mem_inf
            rw [sub_eq_zero] at h_mem_inf
            exact h_mem_inf
          · -- SURJECTIVITY
            -- We need to prove that for any `y ∈ S_i`,
            -- there exists an `x ∈ V_i` such that `W_i_map x = y`.
            -- This is essentially the definition of the image of a map.
            -- The goal is to show `Submodule.map W_i_map V_i = S_i`.
            intro y
            -- `y` is an element of `S_i` (which is a subtype).
            have h_y_in_image : y.val ∈ Submodule.map W_i_map V_i := by
              have h_y := y.property
              -- From the lemma `sDomain_eq_image_of_upper_span`,
              -- we know that S_i is *exactly* the image of V_i under W_i_map.
              unfold W_i_map V_i
              have h_S_i: S_i = Submodule.map W_i_map V_i := by
                unfold S_i
                rw [sDomain_eq_image_of_upper_span 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
                  ℓ R_rate h_ℓ_add_R_rate i h_i]
              rw [←h_S_i]
              exact h_y
            rcases h_y_in_image with ⟨x, hx_in_Vi, hx_maps_to_y⟩
            -- We have found our `x` in `V_i`.
            -- We need to lift `x` from the submodule `V_i` to a term of the subtype `↥V_i`.
            use ⟨x, hx_in_Vi⟩
            apply Subtype.eq
            exact hx_maps_to_y
        )

  -- A linear isomorphism maps a basis to a basis.
  -- We map the basis of Vᵢ through our isomorphism to get the desired basis for S⁽ⁱ⁾.
  exact V_i_basis.map iso

/-! ### 2. Intermediate Novel Polynomial Bases `Xⱼ⁽ⁱ⁾`  and evaluation polynomials `P⁽ⁱ⁾`-/

/-- `∀ i ∈ {0, ..., ℓ}`, The `i`-th order subspace vanishing polynomials `Ŵₖ⁽ⁱ⁾`,
`Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾` for `k ∈ {1, ..., ℓ - i -1}`, and `X` for `k = 0`.
-- k ∈ {0, ..., ℓ-i-1}
-/
noncomputable def intermediateNormVpoly
    -- Assuming you have this hypothesis available from the context:
    (i: Fin (ℓ+1)) (k : Fin (ℓ - i)) : L[X] :=
  -- This definition requires strict order
  Fin.foldl (n:=k) (fun acc j =>
    (qMap 𝔽q β ⟨(i : ℕ) + (j : ℕ), by omega⟩).comp acc) (X)

-- /--
-- **Corollary 4.4.** For each `i ∈ {0, ..., r-1}`, we have `Ŵᵢ = q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾`
-- (with the convention that for `i = 0`, this is just `X`).
-- -/
-- lemma normalizedW_eq_qMap_composition
--   (h_W₀_eq_X : W 𝔽q β 0 = X)
--   (h_β₀_eq_1 : β 0 = 1)
--   -- We also need the hypotheses for qMap_comp_normalizedW
--   (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
--   (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
--   (hβ_lin_indep : LinearIndependent 𝔽q β)
--   (ℓ R_rate : ℕ)
--   (i : Fin r) :
--   normalizedW 𝔽q β i = qCompositionChain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i :=
-- by

-- Ŵₖ⁽⁰⁾(X) = Ŵ(X)
theorem base_intermediateNormVpoly
  (h_W₀_eq_X : W 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (k : Fin ℓ) :
  intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by
    by_contra ht
    simp only [not_lt, nonpos_iff_eq_zero] at ht
    contradiction
  ⟩ k =
  normalizedW 𝔽q β ⟨k, by omega⟩ := by
  unfold intermediateNormVpoly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, zero_add]
  rw [normalizedW_eq_qMap_composition 𝔽q β h_W₀_eq_X
    h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep ℓ R_rate ⟨k, by omega⟩]
  rw [qCompositionChain_eq_foldl 𝔽q β ℓ R_rate]

-- i = 0->l: Ŵᵢ = q(i-1) ∘ ⋯ ∘ q(0)
-- Ŵᵢ is actually Ŵᵢ⁽⁰⁾ => deg(Ŵᵢ) = 2^i = |Uᵢ|, and it vanishes on Uᵢ = Uᵢ⁽⁰⁾ = ⟨β₀, ..., β_{i-1}⟩

-- `q⁽ⁱ⁾(X) := ( Wᵢ(βᵢ)^{2} / W_{i+1}(β_{i+1}) ) ⬝ X ⬝ (X+1)` => deg(q⁽ⁱ⁾) = 2 = |𝔽q|
-- => each composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q| for the degree
-- => k times of composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q|^k for the degree

-- q⁽ⁱ⁾ ∘ Ŵᵢ⁽⁰⁾ = Ŵᵢ+1⁽⁰⁾
-- Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾: this receives an element at space S⁽ⁱ⁾
-- and returns an element at space S⁽ⁱ⁺ᵏ⁾ => go through k subspaces in transit (fold k times)
-- => deg(Ŵₖ⁽ⁱ⁾) => |𝔽q|^k, vanishes on the |𝔽q|^k-size subspace Uₖ⁽ⁱ⁾ = ⟨β_{i}, ..., β_{i+k-1}⟩???
  -- S⁽ⁱ⁾ := ⟨Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})⟩ => size of S⁽ⁱ⁾ = 2^(ℓ+R-i)
  -- q⁽ⁱ⁾(S⁽ⁱ⁾) = S⁽ⁱ⁺¹⁾

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.foldl_comp (n : ℕ) (f : Fin n → L[X]): ∀ initInner initOuter: L[X],
    Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter.comp initInner)
    = (Fin.foldl (n:=n) (fun acc j => (f j).comp acc) (initOuter)).comp initInner := by
  induction n with
  | zero =>
    simp only [Fin.foldl_zero, implies_true]
  | succ n' ih =>
    intro iIn iOut
    rw [Fin.foldl_succ, Fin.foldl_succ]
    set g := fun i : Fin n' => f i.succ
    have h_left := ih g (iOut.comp iIn) (f 0)
    rw [h_left]
    have h_right := ih g iOut (f 0)
    rw [h_right]
    rw [comp_assoc]

omit [Fintype L] [DecidableEq L] in
theorem Polynomial.comp_same_inner_eq_if_same_outer (f g : L[X]) (h_f_eq_g : f = g):
  ∀ x, f.comp x = g.comp x := by
  intro x
  rw [h_f_eq_g]

omit [DecidableEq L] in
-- ∀ i ∈ {0, ..., ℓ-1}, ∀ k ∈ {0, ..., ℓ-i-2}, `Ŵₖ₊₁⁽ⁱ⁾ = Ŵₖ⁽ⁱ⁺¹⁾ ∘ q⁽ⁱ⁾`
theorem intermediateNormVpoly_comp_qmap (i : Fin (ℓ))
    (k : Fin (ℓ - i - 1)):
    intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨k+1, by
      simp only; omega⟩ =
    (intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨k, by
      simp only; omega;
  ⟩).comp (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNormVpoly
  simp only -- Fin.foldl (↑k+1) ... = Fin.foldl (↑k+1) ...
  rw [Fin.foldl_succ] -- convert Fin.foldl (↑k+1) ... into (Fin.foldl (↑k) ...).comp (init value)
  simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, comp_X]
  conv_lhs =>
    rw [←X_comp (p:=qMap 𝔽q β ⟨↑i, by omega⟩)]
    rw [Polynomial.foldl_comp]
  congr -- convert Fin.foldl equality into equality of accumulator functions
  -- ⊢ (fun acc j ↦ (qMap 𝔽q β ⟨↑i + (↑j + 1), ⋯⟩).comp acc)
  -- = fun acc j ↦ (qMap 𝔽q β ⟨↑(i + 1) + ↑j, ⋯⟩).comp acc
  funext acc j
  have h_id_eq: i.val + (j.val + 1) = i.val + 1 + j.val := by omega
  simp_rw [h_id_eq]

omit [DecidableEq L] in
-- A helper derivation for intermediateNormVpoly_comp_qmap
-- i is now in Fin (ℓ-1) instead of Fin ℓ, and k is in Fin (ℓ - (↑i + 1))
theorem intermediateNormVpoly_comp_qmap_helper (i : Fin (ℓ))
    (k : Fin (ℓ - (↑i + 1))):
    (intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨↑i + 1, by omega⟩ k).comp (qMap 𝔽q β ⟨↑i, by omega⟩) =
    intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨↑i, by omega⟩ ⟨k + 1, by simp only; omega⟩:= by
    simp only [intermediateNormVpoly_comp_qmap 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩
        k]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order novel polynomial basis `Xⱼ⁽ⁱ⁾`.
`Xⱼ⁽ⁱ⁾ := Π_{k=0}^{ℓ-i-1} (Ŵₖ⁽ⁱ⁾)^{jₖ}`, ∀ j ∈ {0, ..., 2^(ℓ-i)-1} -/
noncomputable def intermediateNovelBasisX (i : Fin (ℓ + 1)) (j : Fin (2 ^ (ℓ - i))): L[X] :=
  (Finset.univ: Finset (Fin (ℓ - i)) ).prod (fun k =>
    (intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate i k) ^ (Nat.getBit k j))
-- NOTE: possibly we state some Basis for `(Xⱼ⁽ⁱ⁾)  `

-- Xⱼ⁽⁰⁾ = Xⱼ
theorem base_intermediateNovelBasisX
    (h_W₀_eq_X : W 𝔽q β 0 = X)
    (h_β₀_eq_1 : β 0 = 1)
    (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
    (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β)
    (j : Fin (2 ^ ℓ)) :
  intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by
    by_contra ht
    simp only [not_lt, nonpos_iff_eq_zero] at ht
    contradiction
  ⟩ j =
  Xⱼ 𝔽q β ℓ (by omega) j := by
  unfold intermediateNovelBasisX Xⱼ
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod]
  have h_res := base_intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    h_W₀_eq_X h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
  simp only [Fin.mk_zero'] at h_res
  conv_lhs =>
    enter [2, x, 1]
    rw [h_res]
  congr

omit [DecidableEq L] in
/-- `X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}` -/
lemma even_index_intermediate_novel_basis_decomposition (i : Fin ℓ) (j : Fin (2 ^ (ℓ - i - 1))):
  intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩  = (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
  ⟩).comp (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j)ₖ) = ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2, x]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q]

  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2) =
  -- ∏ x, intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j

  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ x ^ Nat.getBit (↑x) (↑j * 2)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)

  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)

  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]

  have fleft_0_eq_0: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = 1 := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2) = 0 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      have res := Nat.getBit_zero_of_two_mul (n:=j.val)
      rw [mul_comm] at res
      exact res
    rw [h_exp]
    simp only [pow_zero]

  rw [fleft_0_eq_0, one_mul]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

omit [DecidableEq L] in
/-- `X₂ⱼ₊₁⁽ⁱ⁾ = X * (Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}` -/
lemma odd_index_intermediate_novel_basis_decomposition
    (i : Fin ℓ) (j : Fin (2 ^ (ℓ - i - 1))):
    intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
    ⟩  = X * (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
      apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
    ⟩).comp (qMap 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediateNovelBasisX
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j₊₁)ₖ)
  -- = X * ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]

  conv_rhs =>
    enter [2]
    enter [2, x, 1]
    rw [intermediateNormVpoly_comp_qmap_helper 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨i, by omega⟩ ⟨x, by simp only; omega⟩]

  -- ⊢ ∏ x, intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ Nat.getBit (↑x) (↑j * 2 + 1) =
  -- X * ∏ x, intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ Nat.getBit ↑x ↑j

  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediateNormVpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ x ^ Nat.getBit (↑x) (↑j * 2 + 1)
  have h_n_shift: ℓ - (↑i + 1) + 1 = ℓ - ↑i := by omega
  have h_fin_n_shift: Fin (ℓ - (↑i + 1) + 1) = Fin (ℓ - ↑i) := by
    rw [h_n_shift]
  have h_left_prod_shift :=
  Fin.prod_univ_succ (M:=L[X]) (n:=ℓ - (↑i + 1)) (f:=fun x => fleft ⟨x, by omega⟩)

  have h_lhs_prod_eq: ∏ x : Fin (ℓ - ↑i),
    fleft x = ∏ x : Fin (ℓ - (↑i + 1) + 1), fleft ⟨x, by omega⟩ := by
    exact Eq.symm (Fin.prod_congr' fleft h_n_shift)

  rw [←h_lhs_prod_eq] at h_left_prod_shift
  rw [h_left_prod_shift]

  have fleft_0_eq_X: fleft ⟨(0: Fin (ℓ - (↑i + 1) + 1)), by omega⟩ = X := by
    unfold fleft
    simp only
    have h_exp: Nat.getBit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2 + 1) = 1 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      unfold Nat.getBit
      simp only [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_add_mod_self_right, Nat.mod_succ]
    rw [h_exp]
    simp only [pow_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    unfold intermediateNormVpoly
    simp only [Fin.foldl_zero]

  rw [fleft_0_eq_X]
  congr -- apply Finset.prod_congr rfl
  funext x
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: Nat.getBit (↑x + 1) (↑j * 2 + 1) = Nat.getBit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply Nat.getBit_eq_succ_getBit_of_mul_two_add_one (k:=↑x) (n:=↑j)

  rw [h_exp_eq]

/-- ∀ `i` ∈ {0, ..., ℓ}, The `i`-th order evaluation polynomial
`P⁽ⁱ⁾(X) := ∑_{j=0}^{2^(ℓ-i)-1} coeffsⱼ ⋅ Xⱼ⁽ⁱ⁾(X)` over the domain `S⁽ⁱ⁾`.
  where the polynomial `P⁽⁰⁾(X)` over the domain `S⁽⁰⁾` is exactly the original
  polynomial `P(X)` we need to evaluate,
  and `coeffs` is the list of `2^(ℓ-i)` coefficients of the polynomial.
-/
noncomputable def intermediateEvaluationPoly (i : Fin (ℓ + 1))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i))), C (coeffs ⟨j, by omega⟩) *
    (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate i ⟨j, by omega⟩)

/-- The even and odd refinements of `P⁽ⁱ⁾(X)` which are polynomials in the `(i+1)`-th basis.
`P₀⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)`
`P₁⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j+1} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)` -/
noncomputable def evenRefinement (i : Fin (ℓ))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, hj⟩)

noncomputable def oddRefinement (i : Fin (ℓ))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (coeffs ⟨j*2+1, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
  ⟩) * (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, hj⟩)

/-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
`∀ i ∈ {0, ..., ℓ-1}, P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
theorem evaluation_poly_split_identity (i : Fin (ℓ))
    (coeffs : Fin (2 ^ (ℓ - i)) → L) :
  let P_i: L[X] := intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
  let P_even_i_plus_1: L[X] := evenRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate i coeffs
  let P_odd_i_plus_1: L[X] := oddRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate i coeffs
  let q_i: L[X] := qMap 𝔽q β ⟨i, by omega⟩
  P_i = (P_even_i_plus_1.comp q_i) + X * (P_odd_i_plus_1.comp q_i) := by

  simp only [intermediateEvaluationPoly, Fin.eta]
  simp only [evenRefinement, Fin.eta, sum_comp, mul_comp, C_comp, oddRefinement]

  set leftEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
  ⟩
  set leftOddTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs ⟨j * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2 + 1, by
    exact mul_two_add_bit_lt_two_pow j (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
  ⟩

  have h_split_P_i: ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i)), C (coeffs ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i) (ℓ-i) (by omega) (by omega)
  ⟩) * intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j, by omega⟩ =
  leftEvenTerm + leftOddTerm
  := by
    unfold leftEvenTerm leftOddTerm
    simp only [Fin.eta]

    -- ⊢ ∑ k ∈ Fin (2 ^ (ℓ - ↑i)), C (coeffsₖ) * Xₖ⁽ⁱ⁾(X) = -- just pure even odd split
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ) * X₂ₖ⁽ⁱ⁾(X) +
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (coeffs₂ₖ+1) * X₂ₖ+1⁽ⁱ⁾(X)

    set f1 := fun x: ℕ => -- => use a single function to represent the sum
      if hx: x < 2 ^ (ℓ - ↑i) then
        C (coeffs ⟨x, hx⟩) *
          intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x, by omega⟩
      else 0

    have h_x: ∀ x: Fin (2 ^ (ℓ - ↑i)), f1 x.val =
      C (coeffs ⟨x.val, by omega⟩) *
        intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩
          ⟨x.val, by simp only; omega⟩ := by
      intro x
      unfold f1
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

    conv_lhs =>
      enter [2, x]
      rw [←h_x x]

    have h_x_2: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2) =
      C (coeffs ⟨x.val * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
        ⟩ := by
      intro x
      unfold f1
      simp only
      have h_x_lt_2_pow_i_minus_1 :=
        mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨0, by omega⟩ (by omega) (by omega)
      simp at h_x_lt_2_pow_i_minus_1
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]

    conv_rhs =>
      enter [1, 2, x]
      rw [←h_x_2 x]

    have h_x_3: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2+1) =
      C (coeffs ⟨x.val * 2 + 1, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2 + 1, by
          exact mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
        ⟩ := by
      intro x
      unfold f1
      simp only
      have h_x_lt_2_pow_i_minus_1 := mul_two_add_bit_lt_two_pow x.val
        (ℓ-i-1) (ℓ-i) ⟨1, by omega⟩ (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]

    conv_rhs =>
      enter [2, 2, x]
      rw [←h_x_3 x]

    -- ⊢ ∑ x, f1 ↑x = ∑ x, f1 (↑x * 2) + ∑ x, f1 (↑x * 2 + 1)

    have h_1: ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i)), f1 i
      = ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i - 1 + 1)), f1 i := by
      congr
      omega

    have res := Fin.sum_univ_odd_even (f:=f1) (n:=(ℓ - ↑i - 1))
    conv_rhs at res =>
      rw [Fin.sum_univ_eq_sum_range]
      rw [←h_1]
      rw [←Fin.sum_univ_eq_sum_range]

    rw [←res]
    congr
    · funext i
      rw [mul_comm]
    · funext i
      rw [mul_comm]

  conv_lhs => rw [h_split_P_i]

  set rightEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
      C (coeffs ⟨j * 2, by
        calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
          _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
      ⟩) *
        (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x:=j) (i:=ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
        ⟩).comp (qMap 𝔽q β ⟨i, by omega⟩)

  set rightOddTerm :=
    X *
      ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
        C (coeffs ⟨j * 2 + 1, by
          calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
            _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
        ⟩) *
          (intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
            apply lt_two_pow_of_lt_two_pow_exp_le (x:=j)
              (i:=ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
          ⟩).comp (qMap 𝔽q β ⟨i, by omega⟩)

  conv_rhs => change rightEvenTerm + rightOddTerm

  have h_right_even_term: leftEvenTerm = rightEvenTerm := by
    unfold rightEvenTerm leftEvenTerm
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.eta, mul_eq_mul_left_iff, map_eq_zero]
    --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∨ a₂ⱼ = 0
    by_cases h_a_j_eq_0: coeffs ⟨j * 2, by
      calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
        _ = 2 ^ (ℓ - i) := Nat.two_pow_pred_mul_two (w:=ℓ - i) (h:=by omega)
    ⟩ = 0
    · simp only [h_a_j_eq_0, or_true]
    · simp only [h_a_j_eq_0, or_false]
      --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))

      exact even_index_intermediate_novel_basis_decomposition
        𝔽q β ℓ R_rate h_ℓ_add_R_rate (i:=⟨i, by omega⟩) j

  have h_right_odd_term: rightOddTerm = leftOddTerm := by
    unfold rightOddTerm leftOddTerm
    simp only [Fin.eta]
    conv_rhs =>
      simp only [Fin.is_lt, odd_index_intermediate_novel_basis_decomposition, Fin.eta]
      enter [2, x];
      rw [mul_comm (a:=X)]

    rw [Finset.mul_sum]
    congr
    funext x
    ring_nf -- just associativity and commutativity of multiplication in L[X]

  rw [h_right_even_term, h_right_odd_term]

-- P⁽⁰⁾(X) = P(X)
lemma intermediate_poly_P_base
  (h_W₀_eq_X : W 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (h_ℓ : ℓ ≤ r) (coeffs : Fin (2^ℓ) → L) :
  intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by omega⟩ coeffs =
    polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ coeffs := by
  unfold polynomialFromNovelCoeffs intermediateEvaluationPoly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, Fin.eta]
  conv_rhs =>
    enter [2, j]
    rw [←base_intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_W₀_eq_X
      h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep j]
  congr

end IntermediateStructures

section AlgorithmCorrectness

/-! ## 2. The Additive NTT Algorithm and Correctness

This section describes the construction of the evaluation points,
the tiling of coefficients, the main loop invariant, and the final
correctness theorem for the Additive NTT algorithm.
-/

/-- Constructs an evaluation point `ω` in the domain `S⁽ⁱ⁾` from a Nat.getBit representation.
This uses the `𝔽q`-basis of `S⁽ⁱ⁾` from `sDomain_basis`.
`ω_{u,b,i} = b⋅Ŵᵢ(βᵢ) + ∑_{k=0}^{|u|-1} uₖ ⋅ Ŵᵢ(β_{i+1+k})`
where `(u,b)` is a Nat.getBit string of length `ℓ + R - i`.
Computes the twiddle factor `t` for a given stage `i` and high-order bits `u`.
`t := Σ_{k=0}^{ℓ+R-i-1} u_k ⋅ Ŵᵢ(β_{i+k})`.
This corresponds to the `x₀` term in the recursive butterfly identity.
-/
noncomputable def evaluationPointω (i : Fin (ℓ + 1))
    (x : Fin (2 ^ (ℓ + R_rate - i))) : L := -- x = u || b
    -- Add the linear combination of the remaining basis vectors
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i)),
    if Nat.getBit k x.val = 1 then
      (normalizedW 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + k, by omega⟩)
    else
      0

/-- The twiddle factor -/
noncomputable def twiddleFactor (i : Fin ℓ) (u : Fin (2 ^ (ℓ + R_rate - i - 1))) : L :=
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
    if Nat.getBit k u.val = 1 then
      -- this branch maps to the above Nat.getBit = 1 branch
        -- (of evaluationPointω (i+1)) under (qMap i)(X)
      (normalizedW 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + 1 + k, by omega⟩)
    else 0
      -- 0 maps to the below Nat.getBit = 0 branch
        -- (of evaluationPointω (i+1)) under (qMap i)(X)

omit [DecidableEq L] in
lemma evaluationPointω_eq_twiddleFactor_of_div_2 (i : Fin ℓ) (x : Fin (2 ^ (ℓ + R_rate - i))):
  evaluationPointω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ x =
  twiddleFactor 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨x/2, by
    have h := div_two_pow_lt_two_pow (x:=x) (i:=ℓ + R_rate - i - 1) (j:=1) (by
      rw [Nat.sub_add_cancel (by omega)]; omega)
    simp only [pow_one] at h
    calc _ < 2 ^ (ℓ + R_rate - i - 1) := by omega
      _ = _ := by rfl
  ⟩ + (x.val % 2: ℕ) * eval (β ⟨i, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩) := by
  unfold evaluationPointω twiddleFactor
  simp only
  --
  set f_left := fun x_1: Fin (ℓ + R_rate - i) => if Nat.getBit x_1 x = 1
    then eval (β ⟨i + x_1, by omega⟩) (normalizedW 𝔽q β ⟨i, by omega⟩) else 0
  conv_lhs =>
  -- ℓ + R_rate - ↑i
    rw [←Fin.sum_congr' (b:=ℓ + R_rate - i) (a:=ℓ + R_rate - (i + 1) + 1) (f:=f_left) (h:=by omega)]
    rw [Fin.sum_univ_succ (n:=ℓ + R_rate - (i + 1))]
  unfold f_left
  simp only [Fin.coe_cast, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_succ]
  have h_bit_shift: ∀ x_1: Fin (ℓ + R_rate - (↑i + 1)), Nat.getBit (↑x_1 + 1) ↑x = Nat.getBit ↑x_1 (↑x / 2) := by
    intro x_1 -- ⊢ Nat.getBit (↑x_1 + 1) ↑x = Nat.getBit (↑x_1) (↑x / 2)
    rw [←Nat.shiftRight_eq_div_pow (m:=x) (n:=1)]
    exact Nat.getBit_of_shiftRight (n:=x) (p:=1) (k:=x_1).symm

  have h_sum_eq: ∀ x_1: Fin (ℓ + R_rate - (↑i + 1)),
    i.val + (x_1.val + 1) = i.val + 1 + x_1.val := by omega
  conv_lhs =>
    enter [2, 2, x_1]
    rw [h_bit_shift]
    simp only [h_sum_eq x_1]

  set f_right := fun x_1: Fin (ℓ + R_rate - (↑i + 1)) => if Nat.getBit (↑x_1) (↑x / 2) = 1
    then eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩) else 0
  rw [←Fin.sum_congr' (b:=ℓ + R_rate - (↑i + 1)) (a:=ℓ + R_rate - i - 1) (f:=f_right) (h:=by omega)]
  unfold f_right
  simp only [Fin.cast_eq_self] -- remove Fin.cast
  rw [add_comm] -- bring the two Fin sum to the first position of the two sides
  congr -- remove the two exactly equal Fin sum

  have h_i_lt_ℓ_add_R_rate: i < ℓ + R_rate := by omega
  have h_2_le_pow_ℓ_add_R_rate_sub_i: 2 ≤ 2 ^ (ℓ + R_rate - i.val) := by
    have h_2_eq: 2 = 2^1 := by rfl
    conv_lhs => rw [h_2_eq]
    apply Nat.pow_le_pow_right (by omega) (by omega)

  simp only [Nat.getBit, Nat.shiftRight_zero, Nat.and_one_is_mod]

  by_cases h_lsb_of_x_eq_0: x.val % 2 = 0
  · simp only [h_lsb_of_x_eq_0, zero_ne_one, ↓reduceIte, Nat.cast_zero, zero_mul]
  · push_neg at h_lsb_of_x_eq_0
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_lsb_of_x_eq_0
    simp only [h_lsb_of_x_eq_0, ↓reduceIte, Nat.cast_one, one_mul]

lemma eval_point_ω_eq_next_twiddleFactor_comp_qmap
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (i : Fin ℓ) (x : Fin (2 ^ (ℓ + R_rate - (i+1)))):
  -- `j = u||b||v` => x here means u at level i
  evaluationPointω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i.val+1, by omega⟩ x =
  eval (twiddleFactor 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨x.val, by
    calc x.val < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
      _ = 2 ^ (ℓ + R_rate - i.val - 1) := by rfl
  ⟩) (qMap 𝔽q β ⟨i, by omega⟩) := by
  simp [evaluationPointω, twiddleFactor]
  have h_qmap_linear_map :=
    qMap_is_linear_map 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime (i:=⟨i, by omega⟩)
  have h_qmap_additive: IsLinearMap 𝔽q fun x ↦ eval x (qMap 𝔽q β ⟨↑i, by omega⟩) :=
    linear_map_of_comp_to_linear_map_of_eval (f := (qMap 𝔽q β ⟨i, by omega⟩))
    (h_f_linear := h_qmap_linear_map)

  set right_inner_func := fun x_1: Fin (ℓ + R_rate - i - 1) => if Nat.getBit ↑x_1 ↑x = 1
    then eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i, by omega⟩) else 0

  let eval_qmap_linear : L →ₗ[𝔽q] L := {
    toFun    := fun x ↦ eval x (qMap 𝔽q β ⟨i, by omega⟩),
    map_add' := h_qmap_additive.map_add,
    map_smul' := h_qmap_additive.map_smul
  }
  have h_rhs: eval (∑ x_1: Fin (ℓ + R_rate - i - 1), right_inner_func x_1)
      (qMap 𝔽q β ⟨↑i, by omega⟩) = ∑ x_1: Fin (ℓ + R_rate - i - 1),
      (eval (right_inner_func x_1) (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
    change eval_qmap_linear (∑ x_1, right_inner_func x_1) = _
    rw [map_sum (g:=eval_qmap_linear) (f:=right_inner_func)
      (s:=(Finset.univ: Finset ( Fin (ℓ + R_rate - i - 1))))]
    congr

  rw [h_rhs]

  set left_inner_func := fun x_1: Fin (ℓ + R_rate - (i.val + 1)) => if Nat.getBit ↑x_1 ↑x = 1
    then eval (β ⟨↑i + 1 + ↑x_1, by omega⟩) (normalizedW 𝔽q β ⟨↑i + 1, by omega⟩) else 0

  conv_lhs =>
    rw [←Fin.sum_congr' (b:=ℓ + R_rate - (i.val + 1))
      (a:=ℓ + R_rate - i - 1) (f:=left_inner_func) (h:=by omega)]
    simp only [Fin.cast_eq_self]

  congr
  funext x1

--   `q⁽ⁱ⁾ ∘ Ŵᵢ = Ŵᵢ₊₁`. -/
  have h_normalized_comp_qmap: normalizedW 𝔽q β ⟨i + 1, by omega⟩ =
    (qMap 𝔽q β ⟨i, by omega⟩).comp (normalizedW 𝔽q β ⟨i, by omega⟩) := by
    have res := qMap_comp_normalizedW 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime
      hβ_lin_indep (i:=⟨i, by omega⟩) (h_i_add_1:=by simp only; omega;)
    rw [res]
    congr
    simp only [Nat.add_mod_mod]
    rw [Nat.mod_eq_of_lt]
    omega

  simp only [left_inner_func, right_inner_func]
  by_cases h_bit_of_x_eq_0: Nat.getBit x1 x = 0
  · simp only [h_bit_of_x_eq_0, zero_ne_one, ↓reduceIte]
    have h_0_is_algebra_map: (0: L) = (algebraMap 𝔽q L) 0 := by
      simp only [map_zero]
    conv_rhs => rw [h_0_is_algebra_map]
    have h_res := qMap_eval_𝔽q_eq_0 𝔽q β (i:=⟨i, by omega⟩) (c:=0)
    rw [h_res]
  · push_neg at h_bit_of_x_eq_0
    have h_bit_lt_2 := Nat.getBit_lt_2 (k:=x1) (n:=x)
    have bit_eq_1: Nat.getBit x1 x = 1 := by
      interval_cases Nat.getBit x1 x
      · contradiction
      · rfl
    simp only [bit_eq_1, ↓reduceIte]
    rw [h_normalized_comp_qmap]
    rw [eval_comp]

/--
The `2^R_rate`-fold tiling of coefficients `a` into the initial buffer `b`.
`b(v) = aⱼ`, where `j` are the `ℓ` LSBs of `v`.
-/
def tileCoeffs (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  fun v => a (Fin.mk (v.val % (2^ℓ)) (Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)))

/--
A single stage of the Additive NTT for a given `i`.
It takes the buffer `b` from the previous stage and applies the butterfly operations.
This function implements one step of the `for i from ℓ-1 down to 0` loop.
-/
noncomputable def NTTStage (i : Fin ℓ) (b : Fin (2 ^ (ℓ + R_rate)) → L) :
    Fin (2^(ℓ + R_rate)) → L :=
  have h_2_pow_i_lt_2_pow_ℓ_add_R_rate: 2^i.val < 2^(ℓ + R_rate) := by
    calc
      2^i.val < 2 ^ (ℓ) := by
        have hr := Nat.pow_lt_pow_right (a:=2) (m:=i.val) (n:=ℓ) (ha:=by omega) (by omega)
        exact hr
      _ ≤ 2 ^ (ℓ + R_rate) := by
        exact Nat.pow_le_pow_right (n:=2) (i:=ℓ) (j:=ℓ + R_rate) (by omega) (by omega)
  fun (j : Fin (2^(ℓ + R_rate))) =>
    let u_b_v := j.val
    have h_u_b_v : u_b_v = j.val := by rfl
    let v: Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=u_b_v)
      simp only [res]
    ⟩ -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high (ℓ + R_rate - i) bits
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      -- {m n k : Nat} (h : m < n * k) : m / n < k :=
      have res := Nat.div_lt_of_lt_mul (m:=u_b_v) (n:=2^i.val) (k:=2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a:=2) (m:=i.val) (n:=ℓ + R_rate) (by omega))
      )
      rw [h_u_b]
      exact res
    let u: ℕ := u_b / 2 -- the remaining high bits
    let b_bit := u_b % 2 -- the LSB of the high bits, i.e. the `i`-th Nat.getBit
    have h_u : u = u_b / 2 := by rfl
    have h_u_lt_2_pow: u < 2 ^ (ℓ + R_rate - (i + 1)) := by
      have h_u_eq: u = j.val / (2 ^ (i.val + 1)) := by
        rw [h_u, h_u_b, h_u_b_v]
        rw [Nat.div_div_eq_div_mul]
        rfl
      rw [h_u_eq]
      -- ⊢ ↑j / 2 ^ (↑i + 1) < 2 ^ (ℓ + R_rate - (↑i + 1))
      exact div_two_pow_lt_two_pow (x:=j.val) (i:=ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
        rw [Nat.sub_add_cancel (by omega)]
        omega
      )
    let twiddleFactor: L := twiddleFactor 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨u, by
      simp only; exact h_u_lt_2_pow
    ⟩
    let x0 := twiddleFactor -- since the last Nat.getBit of u||0 is 0
    let x1: L := x0 + 1 -- since the last Nat.getBit of u||1 is 1 and 1 * Ŵᵢ(βᵢ) = 1

    have h_b_bit : b_bit = Nat.getBit i.val j.val := by
      simp only [Nat.getBit, Nat.and_one_is_mod, b_bit, u_b, u_b_v]
      rw [←Nat.shiftRight_eq_div_pow (m:=j.val) (n:=i.val)]
    -- b remains unchanged through this whole function cuz we create new buffer
    if h_b_bit_zero: b_bit = 0 then -- This is the `b(u||0||v)` case
      let odd_split_index := u_b_v + 2^i.val
      have h_lt: odd_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [gt_iff_lt, odd_split_index, u_b_v]
        -- ⊢ ↑j + 2 ^ ↑i < 2 ^ (ℓ + R_rate)
        exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow (n:=j.val) (m:=ℓ + R_rate)
          (i:=i.val) (h_n:=by omega) (h_i:=by omega) (h_getBit_at_i_eq_zero:=by
          rw [h_b_bit_zero] at h_b_bit
          exact h_b_bit.symm
        )
      b j + x0 * b ⟨odd_split_index, h_lt⟩
    else -- This is the `b(u||1||v)` case
      let even_split_index := u_b_v ^^^ 2^i.val
      have h_lt: even_split_index < 2^(ℓ + R_rate) := by
        have h_exp_eq: (↑i + (ℓ + R_rate - i)) = ℓ + R_rate := by omega
        simp only [even_split_index, u_b_v]
        apply Nat.xor_lt_two_pow (by omega) (by omega)
      -- b j is now the odd refinement P₁,₍₁ᵥ₎⁽ⁱ⁺¹⁾(X),
      -- b (j - 2^i) stores the even refinement P₀,₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)
      b ⟨even_split_index, h_lt⟩ + x1 * b j

/--
**The Additive NTT Algorithm (Algorithm 2)**

Computes the Additive NTT on a given set of coefficients from the novel basis.
- `a`: The initial coefficient array `(a₀, ..., a_{2^ℓ-1})`.
-/
noncomputable def additiveNTT (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs ℓ R_rate a -- Note: can optimize on this
  Fin.foldl (n:=ℓ) (f:= fun current_b i  =>
    NTTStage 𝔽q β ℓ R_rate h_ℓ_add_R_rate (i:=⟨ℓ - 1 - i, by omega⟩) current_b
  ) (init:=b)

-- `∀ i ∈ {0, ..., ℓ}, coeffsBySuffix a i` represents the list of `2^(ℓ-i)` novel coefficients.
-- Note that `i=ℓ` means the result of the initial coefficient tiling process at the beginning.
-- for a specific suffix (LSBs) `v` of `i` bits at the `i-th` NTT stage
def coeffsBySuffix (a : Fin (2 ^ ℓ) → L) (i : Fin (ℓ + 1)) (v : Fin (2 ^ i.val)):
  Fin (2 ^ (ℓ - i)) → L :=
  fun ⟨j, hj⟩ => by
    set originalIndex := (j <<< i.val) ||| v;
    have h_originalIndex_lt_2_pow_ℓ: originalIndex < 2 ^ ℓ := by
      unfold originalIndex
      have res := Nat.append_lt (y:=j) (x:=v) (m:=ℓ - i.val) (n:=i.val) (by omega) (by omega)
      have h_exp_eq: (↑i + (ℓ - ↑i)) = ℓ := by omega
      rw [h_exp_eq] at res
      exact res
    exact a ⟨originalIndex, h_originalIndex_lt_2_pow_ℓ⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Algebra 𝔽q L] in
lemma base_coeffsBySuffix (a : Fin (2 ^ ℓ) → L):
  coeffsBySuffix (r:=r) 𝔽q ℓ R_rate a 0 0 = a := by
  unfold coeffsBySuffix
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.shiftLeft_zero, Fin.isValue,
    Nat.or_zero, Fin.eta]

omit [DecidableEq L] in
/-- `P₀, ₍ᵥ₎⁽ⁱ⁺¹⁾(X) = P₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)`, where `v` consists of exactly `i` bits
Note that the even refinement `P₀, ₍ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of
stage `i`, while the novel polynomial `P₍₀ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i+1`.
-/
theorem evenRefinement_eq_novel_poly_of_0_leading_suffix (i : Fin ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L):
    have h_v: v.val < 2 ^ (i.val + 1) := by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    evenRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate i (coeffsBySuffix (r:=r) 𝔽q ℓ
      R_rate original_coeffs ⟨i, by omega⟩ v) =
    intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩
      (coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs ⟨i + 1, by omega⟩ ⟨v, h_v⟩) := by
  simp only [evenRefinement, Fin.eta, intermediateEvaluationPoly]

  set right_inner_func := fun x: Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix 𝔽q ℓ R_rate original_coeffs ⟨i.val + 1, by omega⟩ ⟨v.val, by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩ x) *
      intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩ x

  have h_right_sum_eq := Fin.sum_congr' (M:=L[X]) (b:=2^(ℓ - (i.val + 1)))
    (a:=2^(ℓ - i - 1)) (f:=right_inner_func) (h:=by rfl)

  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [←h_right_sum_eq]
    simp only [Fin.cast_eq_self]

  congr
  funext x
  simp only [right_inner_func]

  have h_coeffs_eq: coeffsBySuffix (r:=r) 𝔽q ℓ R_rate
      original_coeffs (i:=⟨i.val, by omega⟩) v ⟨↑x * 2, by
    have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i)
      ⟨0, by omega⟩ (by omega) (by omega)
    simp only [add_zero] at h_x_mul_2_lt
    simp only [gt_iff_lt]
    exact h_x_mul_2_lt
  ⟩
    = coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs (i:=⟨i.val + 1, by omega⟩) (v:=⟨v, by
      calc v.val < 2 ^ i.val := by omega
        _ < 2 ^ (i.val + 1) := by apply Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩) x := by
    simp only [coeffsBySuffix]
    -- ⊢ original_coeffs ⟨(↑x * 2) <<< ↑i ||| ↑v, ⋯⟩ = original_coeffs ⟨↑x <<< (↑i + 1) ||| ↑v, ⋯⟩
    have h_index_eq: (x.val * 2) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val := by
      change (x.val * 2^1) <<< i.val ||| v.val = x.val <<< (i.val + 1) ||| v.val
      rw [←Nat.shiftLeft_eq, ←Nat.shiftLeft_add]
      conv_lhs => rw [add_comm]
    simp_rw [h_index_eq]

  rw [h_coeffs_eq]

omit [DecidableEq L] in
/-- `P₁, ₍ᵥ₎⁽ⁱ⁺¹⁾(X) = P₍₁ᵥ₎⁽ⁱ⁺¹⁾(X)`, where `v` consists of exactly `i` bits
Note that the odd refinement `P₁,₍ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i`,
while the novel polynomial `P₍₁ᵥ₎⁽ⁱ⁺¹⁾(X)` is constructed from the view of stage `i+1`.
-/
theorem oddRefinement_eq_novel_poly_of_1_leading_suffix (i : Fin ℓ) (v : Fin (2 ^ i.val))
    (original_coeffs : Fin (2 ^ ℓ) → L):
    have h_v: v.val ||| (1 <<< i.val) < 2 ^ (i.val + 1) := by
      apply Nat.or_lt_two_pow (x:=v.val) (y:=1 <<< i.val) (n:=i.val + 1) (by omega)
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    oddRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate i (coeffsBySuffix (r:=r) 𝔽q ℓ
      R_rate original_coeffs ⟨i, by omega⟩ v) =
    intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩
      (coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs ⟨i + 1, by omega⟩
        ⟨v ||| (1 <<< i.val), h_v⟩) := by
  simp only [oddRefinement, Fin.eta, intermediateEvaluationPoly]

  set right_inner_func := fun x: Fin (2^(ℓ - (i.val + 1))) =>
    C (coeffsBySuffix 𝔽q ℓ R_rate original_coeffs
      ⟨i.val + 1, by omega⟩ ⟨v.val ||| (1 <<< i.val), by
      simp only;
      apply Nat.or_lt_two_pow
      · omega
      · rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩ x) *
      intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i + 1, by omega⟩ x

  have h_right_sum_eq := Fin.sum_congr' (M:=L[X]) (b:=2^(ℓ - (i.val + 1)))
    (a:=2^(ℓ - i - 1)) (f:=right_inner_func) (h:=by rfl)

  conv_rhs =>
    simp only [Fin.cast_eq_self]
    rw [←h_right_sum_eq]
    simp only [Fin.cast_eq_self]

  congr
  funext x
  simp only [right_inner_func]

  have h_coeffs_eq: coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs
      (i:=⟨i.val, by omega⟩) v ⟨↑x * 2 + 1, by
    have h_x_mul_2_lt := mul_two_add_bit_lt_two_pow x.val (ℓ-i-1) (ℓ-i)
      ⟨1, by omega⟩ (by omega) (by omega)
    simp only at h_x_mul_2_lt
    simp only [gt_iff_lt]
    exact h_x_mul_2_lt
  ⟩
    = coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs (i:=⟨i.val + 1, by omega⟩)
      (v:=⟨v.val ||| (1 <<< i.val), by
      simp only
      apply Nat.or_lt_two_pow (x:=v.val) (y:=1 <<< i.val) (n:=i.val + 1) (by omega)
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    ⟩) x := by
    simp only [coeffsBySuffix]
    -- ⊢ original_coeffs ⟨(↑x * 2 + 1) <<< ↑i ||| ↑v, ⋯⟩
    -- = original_coeffs ⟨↑x <<< (↑i + 1) ||| (↑v ||| 1 <<< ↑i), ⋯⟩
    have h_index_eq: (x.val * 2 + 1) <<< i.val ||| v.val
        = x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val)) := by
      change (x.val * 2^1 + 1) <<< i.val ||| v.val
        = x.val <<< (i.val + 1) ||| (v.val ||| (1 <<< i.val))
      rw [←Nat.shiftLeft_eq]
      conv_lhs =>
        rw [add_comm]
      conv_rhs =>
        rw [Nat.or_comm v.val (1 <<< i.val), ←Nat.or_assoc]
      congr
      -- ⊢ (1 + ↑x <<< 1) <<< ↑i = ↑x <<< (↑i + 1) ||| 1 <<< ↑i
      have h_left: 1 + (x.val <<< 1) = 1 ||| (x.val <<< 1) := by
        apply Nat.sum_of_and_eq_zero_is_or
        simp only [Nat.one_and_eq_mod_two, Nat.shiftLeft_eq]
        simp only [pow_one, Nat.mul_mod_left]
      rw [h_left, Nat.shiftLeft_add, Nat.shiftLeft_or_distrib, Nat.or_comm]
      rw [←Nat.shiftLeft_add, ←Nat.shiftLeft_add, Nat.add_comm]

    simp_rw [h_index_eq]

  rw [h_coeffs_eq]

/--
The main loop invariant for the `additiveNTT` algorithm: the evaluation buffer `b`
at the end of stage `i` (`i ∈ {0, ..., ℓ}`, `i=ℓ` means the initial tiled buffer)
holds the value `P⁽ⁱ⁾(ω_{u, b, v})` for all Nat.getBit mask index `(u||b||v) ∈ {0, ..., 2^(ℓ+R_rate)-1}`,
where the points `ω_{u, b, v}` are in the domain `S⁽ⁱ⁾`.

**Main statement:**
After round `i ∈ {ℓ-1, ℓ-2, ..., 0}`: the buffer `b` at index `j` (which can be
decomposed as `j = (u || b || v)` in little-endian order, where
- `u` is a bitstring of length `ℓ + R_rate - i - 1`,
- `b` is a single Nat.getBit (the LSB of the high bits),
- `v` is a bitstring of length `i` (the LSBs),
holds the value `P⁽ⁱ⁾(ω_{u, b, i})`,
where:
  - `P⁽ⁱ⁾` is the intermediate polynomial at round `i` (in the novel basis),
  - `ω_{u, b, i}` is the evaluation point in the subspace `S⁽ⁱ⁾` constructed
  as a linear combination of the basis elements of `S⁽ⁱ⁾`:
    - the Nat.getBit `b` is the coefficient for `Ŵᵢ(βᵢ)` (the LSB),
    - the LSB of `u` is the coefficient for `Ŵᵢ(β_{i+1})`, ..., the MSB of `u` is
    the coefficient for `Ŵᵢ(β_{ℓ+R_rate-1})`.
  - The value is replicated `2^i` times for each `v`
    (i.e., the last `i` bits do not affect the value).

More precisely, for all `j : Fin (2^(ℓ + R_rate))`,
let `u_b_v := j.val` (as a natural number),
- let `v := u_b_v % 2^i` (the `i` LSBs),
- let `u_b := u_b_v / 2^i` (the high bits),
- let `b := u_b % 2` (the LSB of the high bits),
- let `u := u_b / 2` (the remaining high bits),
then:
  b j = P⁽ⁱ⁾(ω_{u, b, i})
-/
def additiveNTTInvariant (evaluation_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (original_coeffs : Fin (2 ^ ℓ) → L) (i : Fin (ℓ + 1)): Prop :=
  ∀ (j : Fin (2^(ℓ + R_rate))),
    let u_b_v := j.val
    let v: Fin (2^i.val) := ⟨Nat.getLowBits i.val u_b_v, by
      have res := Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=u_b_v)
      simp only [res]
    ⟩ -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high (ℓ + R_rate - i) bits
    have h_u_b : u_b = u_b_v / (2^i.val) := by rfl
    have h_u_b_lt_2_pow : u_b < 2 ^ (ℓ + R_rate - i) := by
      -- {m n k : Nat} (h : m < n * k) : m / n < k :=
      have res := Nat.div_lt_of_lt_mul (m:=u_b_v) (n:=2^i.val) (k:=2^(ℓ + R_rate - i)) (by
        calc _ < 2 ^ (ℓ + R_rate) := by omega
          _ = 2 ^ i.val * 2 ^ (ℓ + R_rate - i.val) := by
            exact Eq.symm (pow_mul_pow_sub (a:=2) (m:=i.val) (n:=ℓ + R_rate) (by omega))
      )
      rw [h_u_b]
      exact res
    let b_bit := Nat.getLowBits 1 u_b_v -- the LSB of the high bits, i.e. the `i`-th Nat.getBit
    let u := u_b / 2 -- the remaining high bits
    let coeffs_at_j: Fin (2 ^ (ℓ - i)) → L :=
      coeffsBySuffix (r:=r) 𝔽q ℓ R_rate original_coeffs i v
    let P_i: L[X] := intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate i coeffs_at_j
    let ω := evaluationPointω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ (Fin.mk u_b (by omega))
    evaluation_buffer j = P_i.eval ω

lemma initial_tiled_coeffs_correctness
    (h_W₀_eq_X : W 𝔽q β 0 = X) (h_β₀_eq_1 : β 0 = 1)
    (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1) (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β) (h_ℓ : ℓ ≤ r)
    (a : Fin (2 ^ ℓ) → L) :
    let b: Fin (2^(ℓ + R_rate)) → L := tileCoeffs ℓ R_rate a
    additiveNTTInvariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate b a (i:=⟨ℓ, by omega⟩) := by
    unfold additiveNTTInvariant
    simp only
    intro j
    unfold coeffsBySuffix
    simp only [tileCoeffs, evaluationPointω, intermediateEvaluationPoly, Fin.eta]
    have h_ℓ_sub_ℓ: 2^(ℓ - ℓ) = 1 := by norm_num

    set f_right: Fin (2^(ℓ - ℓ)) → L[X] :=
      fun ⟨x, hx⟩ => C (a ⟨↑x <<< ℓ ||| Nat.getLowBits ℓ (↑j), by
        simp only [tsub_self, pow_zero, Nat.lt_one_iff] at hx
        simp only [hx, Nat.zero_shiftLeft, Nat.zero_or]
        exact Nat.getLowBits_lt_two_pow (numLowBits:=ℓ) (n:=j.val)
      ⟩) * intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨ℓ, by omega⟩ ⟨x, by omega⟩

    have h_sum_right : ∑ (x: Fin (2^(ℓ - ℓ))), f_right x =
      C (a ⟨Nat.getLowBits ℓ (↑j), by exact Nat.getLowBits_lt_two_pow ℓ⟩) *
    intermediateNovelBasisX 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨ℓ, by omega⟩ 0 := by
      have h_sum_eq := Fin.sum_congr' (b:=2^(ℓ - ℓ)) (a:=1) (f:=f_right) (by omega)
      rw [←h_sum_eq]
      rw [Fin.sum_univ_one]
      unfold f_right
      simp only [Fin.isValue, Fin.cast_zero, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero,
        Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
      congr

    rw [h_sum_right]

    set f_left: Fin (ℓ + R_rate - ℓ) → L := fun x =>
      if Nat.getBit (x.val) (j.val / 2 ^ ℓ) = 1 then
        eval (β ⟨ℓ + x.val, by omega⟩) (normalizedW 𝔽q β ⟨ℓ, by omega⟩)
      else 0

    simp only [eval_mul, eval_C]

    have h_eval : eval (Finset.univ.sum f_left) (intermediateNovelBasisX 𝔽q β ℓ R_rate
      h_ℓ_add_R_rate ⟨ℓ, by omega⟩ 0) = 1 := by
      have h_base_novel_basis := base_intermediateNovelBasisX 𝔽q β ℓ R_rate
        h_ℓ_add_R_rate h_W₀_eq_X h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep ⟨ℓ, by exact
        Nat.lt_two_pow_self⟩
      simp only [intermediateNovelBasisX, Fin.coe_ofNat_eq_mod, tsub_self, pow_zero,
        Nat.zero_mod]

      set f_inner : Fin (ℓ - ℓ) → L[X] := fun x => intermediateNormVpoly 𝔽q β ℓ R_rate
        h_ℓ_add_R_rate ⟨ℓ, by omega⟩ x ^ Nat.getBit (x.val) 0

      have h_sum_eq := Fin.prod_congr' (b:=ℓ - ℓ) (a:=0) (f:=f_inner) (by omega)
      simp_rw [←h_sum_eq, Fin.prod_univ_zero]
      simp only [eval_one]

    rw [h_eval, mul_one]
    simp only [Nat.getLowBits_eq_mod_two_pow]

-- /-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
-- butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
-- its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
-- ∀ i ∈ {0, ..., ℓ-1}, `P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
/--
The correctness theorem for the `NTTStage` function. This is the inductive step
in the main proof. It asserts that if the invariant holds for `i+1`, then after
applying `NTTStage i`, the invariant holds for `i ∈ {0, ..., ℓ-1}`.
-/
lemma NTTStage_correctness
    (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1) (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β)
    (i : Fin (ℓ))
    (input_buffer: Fin (2^(ℓ + R_rate)) → L) (original_coeffs : Fin (2 ^ ℓ) → L) :
    additiveNTTInvariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    (evaluation_buffer:=input_buffer) (original_coeffs:=original_coeffs) (i:=⟨i.val+1, by omega⟩) →
    additiveNTTInvariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    (evaluation_buffer:=NTTStage 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer)
    (original_coeffs:=original_coeffs) ⟨i, by omega⟩ :=
  by
  -- This proof is the core of the work, using the `key_polynomial_identity`.
  intro h_prev
  simp [additiveNTTInvariant] at h_prev
  -- unfold NTTStage
  set output_buffer := NTTStage 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer
  unfold additiveNTTInvariant at *
  simp only at *
  intro j
  -- prove that at any `j ∈ {0, ..., 2^(ℓ+R_rate)-1}`,
  -- output_buffer j = P⁽ⁱ⁾(ω_{u, b, i}) where coeffs of P⁽ⁱ⁾ at j = `coeffsBySuffix a i v`

  have h_j_div_2_pow_i_lt := div_two_pow_lt_two_pow (x:=j.val)
    (i:=ℓ + R_rate - i.val) (j:=i.val) (by
    rw [Nat.sub_add_cancel (by omega)]; omega)
  set cur_evaluation_point := evaluationPointω 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    ⟨↑i, by omega⟩ ⟨↑j / 2 ^ i.val, by simp only; exact h_j_div_2_pow_i_lt⟩ -- ω_{u, b, i}
  set cur_coeffs := coeffsBySuffix 𝔽q ℓ R_rate original_coeffs ⟨↑i, by omega⟩
    ⟨Nat.getLowBits i.val (↑j), by exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ -- coeffs of P⁽ⁱ⁾ at j

  -- identity (39): `P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))`
  have h_P_i_split_even_odd := evaluation_poly_split_identity 𝔽q β ℓ R_rate
    h_ℓ_add_R_rate ⟨i, by omega⟩ cur_coeffs

  simp at h_P_i_split_even_odd

  set P_i := intermediateEvaluationPoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ cur_coeffs
  set even_coeffs_poly := evenRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate i cur_coeffs
  set odd_coeffs_poly := oddRefinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ cur_coeffs

  conv_lhs =>
    unfold output_buffer NTTStage
    simp only [beq_iff_eq, Fin.eta]

  have h_bit: Nat.getBit i.val j.val = (j.val / (2 ^ i.val)) % 2 := by
    simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

  have h_qmap_linear_map := qMap_is_linear_map 𝔽q β h_Fq_card_gt_1
    h_Fq_char_prime (i:=⟨i, by omega⟩)

  have h_qmap_additive: IsLinearMap 𝔽q fun x ↦ eval x (qMap 𝔽q β ⟨↑i, by omega⟩)
    := linear_map_of_comp_to_linear_map_of_eval
      (f := (qMap 𝔽q β ⟨i, by omega⟩)) (h_f_linear := h_qmap_linear_map)

  let eval_qmap_linear : L →ₗ[𝔽q] L := {
    toFun    := fun x ↦ eval x (qMap 𝔽q β ⟨i, by omega⟩),
    map_add' := h_qmap_additive.map_add,
    map_smul' := h_qmap_additive.map_smul
  }

  have h_lsb_and_two_pow_eq_zero : (Nat.getLowBits i.val j.val) &&& (1 <<< i.val) = 0 := by
    rw [Nat.shiftLeft_eq, one_mul]
    apply Nat.and_two_pow_eq_zero_of_getBit_0
    rw [Nat.getBit_of_lowBits];
    simp only [lt_self_iff_false, ↓reduceIte]

  have h_j_div_2_pow_i_add_1_lt := div_two_pow_lt_two_pow (x:=j.val)
    (i:=ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
    rw [Nat.sub_add_cancel (by omega)]; omega)

  have h_j_div_2_pow_left: j.val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
    simp only [Nat.div_div_eq_div_mul]
    congr

  have h_j_div_2_pow_div_2_left_lt: j.val / 2 ^ i.val / 2 < 2 ^ (ℓ + R_rate - (i.val + 1)) := by
    rw [←h_j_div_2_pow_left]
    exact h_j_div_2_pow_i_add_1_lt

  have h_eval_qmap_at_1: eval 1 (qMap 𝔽q β ⟨↑i, by omega⟩) = 0 := by
    have h_1_is_algebra_map: (1: L) = algebraMap 𝔽q L 1 := by rw [map_one]
    rw [h_1_is_algebra_map]
    apply qMap_eval_𝔽q_eq_0 𝔽q β (i:=⟨i, by omega⟩) (c:=1)

  have h_msb_eq_j_xor_lsb: (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val ^^^ Nat.getLowBits (i.val + 1) j.val := by
    have h_xor: j.val = Nat.getHighBits (i.val + 1) j.val ^^^ Nat.getLowBits (i.val + 1) j.val
      := Nat.num_eq_highBits_xor_lowBits (n:=j.val) (i.val + 1)
    conv_lhs => rw [←Nat.shiftLeft_eq]; rw [←Nat.shiftRight_eq_div_pow]
    change Nat.getHighBits (i.val + 1) j.val = _
    conv_rhs => enter [1]; rw [h_xor]
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

  have h_msb_eq_j_sub_lsb: (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
      = j.val - Nat.getLowBits (i.val + 1) j.val := by
    have h_msb := Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1)
    conv_rhs => enter [1]; rw [h_msb]
    norm_num; rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

  by_cases h_b_bit_eq_0: (j.val / (2 ^ i.val)) % 2 = 0
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    simp only at h_b_bit_eq_0
    have bit_i_j_eq_0: Nat.getBit i.val j.val = 0 := by omega
    set x0 := twiddleFactor 𝔽q β ℓ R_rate h_ℓ_add_R_rate i ⟨j.val / 2 ^ i.val / 2, by
      rw [h_j_div_2_pow_left.symm]; exact h_j_div_2_pow_i_add_1_lt⟩

    have h_j_add_2_pow_i: j.val + 2 ^ i.val < 2 ^ (ℓ + R_rate):= by
      exact Nat.add_two_pow_of_getBit_eq_zero_lt_two_pow
        (n:=j.val) (m:=ℓ + R_rate) (i:=i.val) (h_n:=by omega)
        (h_i:=by omega) (h_getBit_at_i_eq_zero:=by
        rw [←h_b_bit_eq_0]
        simp only [Nat.getBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow])

    -- EVEN REFINEMENT coeffs correspondence at index j of level i--
    have h_even_split: input_buffer j =
      eval x0 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]

      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β ℓ R_rate h_ℓ_add_R_rate h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
          (i:=⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by
        rw [←h_j_div_2_pow_left]; simp only [h_j_div_2_pow_i_add_1_lt]
      ⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)

      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [←h_twiddle_comp_qmap_eq_left]

      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this

      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs

      congr

      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β ℓ R_rate h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]

      have h_v_eq: Nat.getLowBits i.val j.val = Nat.getLowBits (i.val + 1) j.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0, Nat.zero_shiftLeft, Nat.add_zero]

      simp_rw [h_v_eq]

    -- ODD REFINEMENT coeffs correspondence at index j of level i--
    have h_odd_split: input_buffer ⟨↑j + 2 ^ i.val, h_j_add_2_pow_i⟩
      = eval x0 (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val + 2^i.val, by omega⟩]

      have h_j_div_2_pow_right: (⟨j.val + 2^i.val, by omega⟩: Fin (2^(ℓ + R_rate))).val
        / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ←Nat.pow_add (a:=2) (m:=i.val) (n:=1)]
        -- ⊢ (↑j + 2 ^ ↑i) / 2 ^ (↑i + 1) = ↑j / 2 ^ (↑i + 1)
        apply Nat.div_eq_of_lt_le (m:=(j.val + 2 ^ i.val))
          (n:=2 ^ (i.val + 1)) (k:=j.val / 2 ^ (i.val + 1))
        · -- ⊢ ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) ≤ ↑j + 2 ^ ↑i:
          -- the lhs is basically erasing (i+1) lsb bits from j
          calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1)) ≤ j.val := by
              simp only [Nat.div_mul_le_self (m:=j.val) (n:=2^(i.val + 1))]
            _ ≤ _ := by exact Nat.le_add_right j.val (2 ^ i.val)
        · -- ⊢ ↑j + 2 ^ ↑i < (↑j / 2 ^ (↑i + 1) + 1) * 2 ^ (↑i + 1)
          rw [add_mul]; rw [one_mul];
          conv_rhs => enter [2]; rw [Nat.pow_succ, mul_two];
          rw [←Nat.add_assoc];
          apply Nat.add_lt_add_right;
          -- ⊢ ↑j < ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) + 2 ^ ↑i
          have h_j: j = j / 2^(i.val + 1) * 2^(i.val + 1) + Nat.getLowBits i.val j.val := by
            conv_lhs => rw [Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1)]
            rw [Nat.getHighBits, Nat.getHighBits_no_shl, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
            apply Nat.add_left_cancel_iff.mpr
            rw [Nat.getLowBits_succ]
            conv_rhs => rw [←Nat.add_zero (n:=Nat.getLowBits i.val j.val)]
            apply Nat.add_left_cancel_iff.mpr
            rw [bit_i_j_eq_0, Nat.zero_shiftLeft]
          conv_lhs => rw [h_j];
          apply Nat.add_lt_add_left;
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=j.val)

      have h_twiddle_comp_qmap_eq_right := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β ℓ R_rate h_ℓ_add_R_rate h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
          (i:=⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_right
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)

      conv_rhs =>
        rw [eval_comp]
        simp only [x0]
        rw [←h_twiddle_comp_qmap_eq_right]
      -- ⊢ eval (ω_ᵢ₊₁((⟨j.val + 2 ^ i.val, h_j_add_2_pow_i⟩: Fin (2^(ℓ + R_rate))).val
      -- / 2 ^ (↑i + 1), ⋯⟩))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j + 2^i) (i+1)))) =
      -- eval (ω_ᵢ₊₁(↑⟨j.val / 2 ^ i.val / 2, ⋯⟩))) odd_coeffs_poly
      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_right] -- change the index of lhs to same as rhs

      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β ℓ R_rate h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]

      have h_j_and_2_pow_i_eq_0 : j.val &&& 2 ^ i.val = 0 := by
        apply Nat.and_two_pow_eq_zero_of_getBit_0
        omega

      have h_bit1: Nat.getBit (i.val) (j.val + 2 ^ i.val) = 1 := by
        rw [Nat.sum_of_and_eq_zero_is_or h_j_and_2_pow_i_eq_0]
        rw [Nat.getBit_of_or]
        rw [Nat.getBit_two_pow]
        rw [bit_i_j_eq_0]
        simp only [BEq.rfl, ↓reduceIte, Nat.zero_or]

      have h_v_eq: Nat.getLowBits (i.val + 1) (j.val + 2^i.val)
        = (Nat.getLowBits i.val j.val) ||| 1 <<< i.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit1]
        have h_get_lsb_eq: Nat.getLowBits i.val (j.val + 2^i.val) = Nat.getLowBits i.val j.val := by
          apply Nat.eq_iff_eq_all_getBits.mpr; unfold Nat.getBit
          intro k
          change Nat.getBit k (Nat.getLowBits i.val (j.val + 2^i.val)) = Nat.getBit k (Nat.getLowBits i.val j.val)
          rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
          if h_k: k < i.val then
            simp only [h_k, ↓reduceIte]
            rw [Nat.getBit_of_add_distrib h_j_and_2_pow_i_eq_0]
            rw [Nat.getBit_two_pow]
            simp only [beq_iff_eq, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false]
            omega
          else
            simp only [h_k, ↓reduceIte]
        rw [h_get_lsb_eq]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero

      congr
      simp_rw [h_v_eq]

    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x0_eq_cur_evaluation_point: x0 = cur_evaluation_point := by
      unfold x0 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 𝔽q]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_zero, zero_mul, add_zero]

    rw [h_x0_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]
  · simp only [h_b_bit_eq_0, ↓reduceDIte]
    push_neg at h_b_bit_eq_0
    have bit_i_j_eq_1: Nat.getBit i.val j.val = 1 := by omega
    simp only [ne_eq, Nat.mod_two_not_eq_zero] at h_b_bit_eq_0
    set x1 := twiddleFactor 𝔽q β ℓ R_rate h_ℓ_add_R_rate i
      ⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩ + 1

    have h_j_xor_2_pow_i: j.val ^^^ 2 ^ i.val < 2 ^ (ℓ + R_rate):= by
      exact Nat.xor_lt_two_pow (by omega) (by
        apply Nat.pow_lt_pow_right (by omega) (by omega)
      )

    have h_2_pow_i_le_lsb_succ: 2 ^ i.val ≤ Nat.getLowBits (i.val + 1) j.val := by
      rw [Nat.getLowBits_succ]; rw [bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]; omega

    have h_2_pow_i_le_j: 2 ^ i.val ≤ j.val := by
      rw [Nat.num_eq_highBits_add_lowBits (n:=j.val) (numLowBits:=i.val + 1), add_comm]
      apply Nat.le_add_right_of_le -- ⊢ 2 ^ ↑i ≤ get_lsb (↑j) (↑i + 1)
      exact h_2_pow_i_le_lsb_succ

    have h_j_and_2_pow_i_eq_2_pow_i : j.val &&& 2 ^ i.val = 2 ^ i.val := by
      rw [Nat.and_two_pow_eq_two_pow_of_getBit_1 (n:=j.val) (i:=i.val) (by omega)]

    have h_j_xor_2_pow_i_eq_sub: j.val ^^^ 2 ^ i.val = j.val - 2 ^ i.val := by
      exact Nat.xor_eq_sub_iff_submask (n:=j.val) (m:=2^i.val)
        (h:=h_2_pow_i_le_j).mpr h_j_and_2_pow_i_eq_2_pow_i

    have h_2_pow_i_le_lsb_succ_2: Nat.getLowBits i.val j.val < 2 ^ i.val := by
      exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val) (n:=j.val)

    have h_even_split: input_buffer ⟨↑j ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩
      = eval x1 (even_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev ⟨j.val ^^^ 2 ^ i.val, by omega⟩]
      -- left (top) is the full poly of level (i+1),
      -- right (bottom) is the even refinement of current level i

      have h_j_div_2_pow_right: (⟨j.val ^^^ 2 ^ i.val, h_j_xor_2_pow_i⟩:
        Fin (2^(ℓ + R_rate))).val / 2 ^ (i.val + 1) = (j.val / 2 ^ i.val) / 2 := by
        simp only
        rw [Nat.div_div_eq_div_mul, ←Nat.pow_add (a:=2) (m:=i.val) (n:=1)]
        -- ⊢ (↑j ^^^ 2 ^ ↑i) / 2 ^ (↑i + 1) = ↑j / 2 ^ (↑i + 1)
        apply Nat.div_eq_of_lt_le (m:=(j.val ^^^ 2 ^ i.val))
          (n:=2 ^ (i.val + 1)) (k:=j.val / 2 ^ (i.val + 1))
        · -- ⊢ ↑j / 2 ^ (↑i + 1) * 2 ^ (↑i + 1) ≤ ↑j ^^^ 2 ^ ↑i
          -- the lhs is basically erasing (i+1) msb bits from j
          calc
            (j.val) / (2 ^ (i.val + 1)) * (2 ^ (i.val + 1))
              = j.val - Nat.getLowBits (i.val + 1) j.val := by
              rw [h_msb_eq_j_sub_lsb]
            _ ≤ j.val ^^^ 2 ^ i.val := by
              rw [h_j_xor_2_pow_i_eq_sub]
              apply Nat.sub_le_sub_left (k:=j.val) (h:=h_2_pow_i_le_lsb_succ)
        · -- ⊢ ↑j ^^^ 2 ^ ↑i < (↑j / 2 ^ (↑i + 1) + 1) * 2 ^ (↑i + 1)
          rw [add_mul]; rw [one_mul];
          conv_rhs =>
            rw [h_msb_eq_j_sub_lsb] -- | ↑j - get_lsb (↑j) (↑i + 1) + 2 ^ (↑i + 1)
            rw [←Nat.sub_add_comm (h:=Nat.getLowBits_le_self (n:=j.val)
              (numLowBits:=i.val + 1)), Nat.pow_succ, mul_two]
            rw [←Nat.add_assoc]
            rw [Nat.getLowBits_succ, bit_i_j_eq_1, Nat.shiftLeft_eq, one_mul]
            rw [Nat.add_comm (Nat.getLowBits i.val j.val) (2 ^ i.val), ←Nat.sub_sub]
            rw [Nat.add_sub_cancel (m:=2^i.val)]
          rw [Nat.add_sub_assoc (n:=j.val) (m:=2^i.val) (k:=Nat.getLowBits i.val j.val) (h:=by omega)]
          -- ⊢ ↑j ^^^ 2 ^ ↑i < ↑j + (2 ^ ↑i - get_lsb ↑j ↑i)
          omega

      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β ℓ R_rate h_ℓ_add_R_rate h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
          (i:=⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)

      conv_rhs =>
        rw [eval_comp]
        simp only [x1]

      set t := twiddleFactor (r:=r) 𝔽q β ℓ R_rate h_ℓ_add_R_rate
        (i:=i) (u:=⟨j.val / 2 ^ i.val / 2, by
        exact h_j_div_2_pow_div_2_left_lt⟩) with ht

      have hh := eval_qmap_linear.map_add' (x:=t) (y:=1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x:=t) (y:=1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [←h_twiddle_comp_qmap_eq_left]

      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this

      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs
        simp only [h_j_div_2_pow_right] -- change the index of lhs to same as rhs

      -- congr

      simp only [even_coeffs_poly, cur_coeffs]
      have h_res := evenRefinement_eq_novel_poly_of_0_leading_suffix 𝔽q β ℓ R_rate h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]

      congr
      rw [h_eval_qmap_at_1, add_zero]

      have h_bit0: Nat.getBit (i.val) (j.val ^^^ 2 ^ i.val) = 0 := by
        rw [Nat.getBit_of_xor (n:=j.val) (m:=2^i.val) (k:=i.val)]
        rw [bit_i_j_eq_1, Nat.getBit_two_pow]
        simp only [BEq.rfl, ↓reduceIte, Nat.xor_self]

      have h_v_eq: Nat.getLowBits (i.val + 1) (j.val ^^^ 2^i.val) = Nat.getLowBits i.val j.val := by
        -- i.e. 0||v (i+1 bits) = v (i bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit0, Nat.zero_shiftLeft, Nat.add_zero]
        apply Nat.eq_iff_eq_all_getBits.mpr; unfold Nat.getBit
        intro k
        change Nat.getBit k (Nat.getLowBits i.val (j.val ^^^ 2^i.val)) = Nat.getBit k (Nat.getLowBits i.val j.val)
        rw [Nat.getBit_of_lowBits, Nat.getBit_of_lowBits]
        if h_k: k < i.val then
          simp only [h_k, ↓reduceIte]
          -- ⊢ Nat.getBit k (↑j ^^^ 2 ^ ↑i) = Nat.getBit k ↑j (precondition that Nat.getBit i j = 1)
          rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
          have h_ne_i_eq_k: ¬(i.val = k) := by omega
          simp only [beq_iff_eq, h_ne_i_eq_k, ↓reduceIte, Nat.xor_zero]
        else
          simp only [h_k, ↓reduceIte]

      simp_rw [h_v_eq]

    have h_odd_split: input_buffer j = eval x1
      (odd_coeffs_poly.comp (qMap 𝔽q β ⟨↑i, by omega⟩)) := by
      rw [h_prev j]
      -- left (top) is the full poly of level (i+1),
      -- right (bottom) is the odd refinement of current level i

      have h_twiddle_comp_qmap_eq_left := eval_point_ω_eq_next_twiddleFactor_comp_qmap
        𝔽q β ℓ R_rate h_ℓ_add_R_rate h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
          (i:=⟨i, by omega⟩) (x:=⟨j.val / 2 ^ i.val / 2, by
        rw [←h_j_div_2_pow_left]
        have h := div_two_pow_lt_two_pow (x:=j.val) (i:=ℓ + R_rate - (i.val + 1)) (j:=i.val + 1) (by
          rw [Nat.sub_add_cancel (by omega)]; omega)
        calc _ < 2 ^ (ℓ + R_rate - (i.val + 1)) := by omega
          _ = _ := by rfl
      ⟩)
      simp only [Fin.eta] at h_twiddle_comp_qmap_eq_left
      -- relation between ω and twiddle factor at level i and at point (j.val / 2 ^ i.val / 2)

      conv_rhs =>
        rw [eval_comp]
        simp only [x1]

      set t := twiddleFactor (r:=r) 𝔽q β ℓ R_rate h_ℓ_add_R_rate (i:=i)
        (u:=⟨j.val / 2 ^ i.val / 2, by exact h_j_div_2_pow_div_2_left_lt⟩) with ht

      have hh := eval_qmap_linear.map_add' (x:=t) (y:=1)
      conv_rhs =>
        enter [1]
        change eval_qmap_linear.toFun (t + 1)
        rw [eval_qmap_linear.map_add' (x:=t) (y:=1)]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, t]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, eval_qmap_linear]
        rw [←h_twiddle_comp_qmap_eq_left]

      -- ⊢ eval (ω_ᵢ₊₁(j / 2 ^ (i + 1))) (Pᵢ₊₁ (coeffsBySuffix (i+1) (get_lsb (j) (i+1)))) =
      -- eval (ω_ᵢ₊₁(j / 2 ^ i /2)) even_coeffs_poly => `h_j_div_2_pow_left` is dervied for this

      conv_lhs =>
        enter [1]
        simp only [h_j_div_2_pow_left] -- change the index of lhs to same as rhs

      simp only [odd_coeffs_poly, cur_coeffs]
      have h_res := oddRefinement_eq_novel_poly_of_1_leading_suffix 𝔽q β ℓ R_rate h_ℓ_add_R_rate
        ⟨i, by omega⟩ ⟨Nat.getLowBits i.val j.val, by
          exact Nat.getLowBits_lt_two_pow (numLowBits:=i.val)⟩ original_coeffs
      simp only [Fin.eta] at h_res
      rw [h_res]

      congr

      rw [h_eval_qmap_at_1, add_zero]

      have h_v_eq: Nat.getLowBits (i.val + 1) j.val = Nat.getLowBits i.val j.val ||| 1 <<< i.val := by
        -- i.e. v (i bits) = 0||v (i+1 bits)
        rw [Nat.getLowBits_succ]
        rw [h_bit, h_b_bit_eq_0]
        apply Nat.sum_of_and_eq_zero_is_or h_lsb_and_two_pow_eq_zero

      simp_rw [h_v_eq]

    rw [h_even_split, h_odd_split]
    rw [h_P_i_split_even_odd]
    have h_x1_eq_cur_evaluation_point: x1 = cur_evaluation_point := by
      unfold x1 cur_evaluation_point
      simp only
      rw [evaluationPointω_eq_twiddleFactor_of_div_2 𝔽q]
      simp only [Fin.eta, h_b_bit_eq_0, Nat.cast_one, one_mul, add_right_inj]
      rw [normalizedWᵢ_eval_βᵢ 𝔽q β hβ_lin_indep]

    rw [h_x1_eq_cur_evaluation_point]
    simp only [eval_comp, eval_add, eval_mul, eval_X]

-- foldl k times would result in the additiveNTTInvariant holding for the `ℓ - k`-th stage
lemma foldl_NTTStage_inductive_aux
    (h_W₀_eq_X : W 𝔽q β 0 = X) (h_β₀_eq_1 : β 0 = 1)
    (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1) (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β)
    (h_ℓ : ℓ ≤ r) (k : Fin (ℓ + 1))
    (original_coeffs : Fin (2 ^ ℓ) → L):
    additiveNTTInvariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    (Fin.foldl k (fun current_b i ↦ NTTStage 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨ℓ - i -1, by omega⟩ current_b) (tileCoeffs ℓ R_rate original_coeffs))
    original_coeffs ⟨ℓ - k, by omega⟩ := by
  have invariant_init := initial_tiled_coeffs_correctness 𝔽q β ℓ R_rate
    h_ℓ_add_R_rate h_W₀_eq_X h_β₀_eq_1 h_Fq_card_gt_1
    h_Fq_char_prime hβ_lin_indep h_ℓ original_coeffs
  simp only at invariant_init
  induction k using Fin.succRecOnSameFinType with
  | zero =>
    exact invariant_init
  | succ k k_h i_h =>
    have h_k_add_one := Fin.val_add_one' (a:=k) (by omega)
    simp only [h_k_add_one, Fin.coe_cast]
    simp only [Fin.foldl_succ_last, Fin.val_last, Fin.coe_castSucc]
    set ntt_round := ℓ - (k + 1)
    set input_buffer := Fin.foldl k (fun current_b i ↦ NTTStage 𝔽q β ℓ R_rate
      h_ℓ_add_R_rate ⟨ℓ - i -1, by omega⟩ current_b) (tileCoeffs ℓ R_rate original_coeffs)
    have correctness_transition := NTTStage_correctness 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      (i:=⟨ntt_round, by omega⟩) (input_buffer:=input_buffer) (original_coeffs:=original_coeffs)
    simp only at correctness_transition
    have h_ℓ_sub_k : ℓ - k = ntt_round + 1 := by omega
    simp_rw [h_ℓ_sub_k] at i_h
    have res := correctness_transition h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i_h
    exact res

/--
**Main Correctness Theorem for Additive NTT**

If `b` is the output of `additiveNTT` on input `a`, then for all `j`, `b j`
is the evaluation of the polynomial `P` (from the novel basis coefficients `a`)
at the evaluation point `ω_{0, j}` in the domain `S⁰`.
-/
theorem additiveNTT_correctness
    (h_W₀_eq_X : W 𝔽q β 0 = X) (h_β₀_eq_1 : β 0 = 1)
    (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1) (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β) (h_ℓ : ℓ ≤ r)
    (original_coeffs : Fin (2 ^ ℓ) → L)
    (output_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
    (h_alg : output_buffer = additiveNTT 𝔽q β ℓ R_rate h_ℓ_add_R_rate original_coeffs) :
    let P := polynomialFromNovelCoeffs 𝔽q β ℓ h_ℓ original_coeffs
    ∀ (j : Fin (2^(ℓ + R_rate))),
      output_buffer j = P.eval (evaluationPointω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by omega⟩ j) :=
  by
  simp only [Fin.zero_eta]
  intro j
  simp only [h_alg]
  unfold additiveNTT
  set output_foldl := Fin.foldl ℓ (fun current_b i ↦ NTTStage 𝔽q β ℓ R_rate
    h_ℓ_add_R_rate ⟨ℓ - i -1, by omega⟩ current_b) (tileCoeffs ℓ R_rate original_coeffs)

  have output_foldl_correctness : additiveNTTInvariant 𝔽q β ℓ R_rate
    h_ℓ_add_R_rate output_foldl original_coeffs ⟨0, by omega⟩ := by
    have res := foldl_NTTStage_inductive_aux 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_W₀_eq_X h_β₀_eq_1
      h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep h_ℓ
      (k:=⟨ℓ, by omega⟩) original_coeffs
    simp only [tsub_self, Fin.zero_eta] at res
    exact res

  have h_nat_point_ω_eq_j: j.val / 2 * 2 + j.val % 2 = j := by
    have h_j_mod_2_eq_0: j.val % 2 < 2 := by omega
    exact Nat.div_add_mod' (↑j) 2

  simp only [additiveNTTInvariant] at output_foldl_correctness
  have res := output_foldl_correctness j
  unfold output_foldl at res
  simp only [Fin.zero_eta, Nat.sub_zero, pow_zero, Nat.div_one, Fin.eta,
    Nat.pow_zero, Nat.getLowBits_zero_eq_zero (n := j.val), Fin.isValue, base_coeffsBySuffix] at res
  simp only [←
    intermediate_poly_P_base 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_W₀_eq_X h_β₀_eq_1 h_Fq_card_gt_1
      h_Fq_char_prime hβ_lin_indep h_ℓ original_coeffs,
    Fin.zero_eta]
  rw [←res]
  simp_rw [Nat.sub_right_comm] -- ℓ - 1 - ↑i = ℓ - ↑i - 1

end AlgorithmCorrectness
end AdditiveNTT
