import ArkLib.Data.FieldTheory.BinaryField.AdditiveNTT.NovelPolynomialBasis
import ArkLib.Data.Classes.DCast

/-!
# Additive NTT Algorithm (Algorithm 2, LCH14)

This file defines the FRI-Binius ([DP24]) variant of the Additive NTT algorithm originally
introduced in [LCH14]. This variant adopts concrete optimizations and a different proof strategy,
making it highly suitable for the FRI-Binius proof system, while still fully complying with the
original algorithm in [LCH14] through a different interpretation.

## Main Definitions

- `additive_ntt`: The main implementation of the Additive NTT algorithm.
- `additive_ntt_correctness`: Main correctness statement of the algorithm.
- `additive_ntt_invariant`: Describes the invariant for each loop in the algorithm,
serving as the core of the correctness proof of the algorithm.

## TODOs
- Define computable additive NTT and transfer correctness proof to it
- Define an optimized declarative version of the forward additive NTT algorithm, where at
  level `i` we only need to compute the first block of size `2^{l+R-i}` evaluations instead
  of whole `2^{l+R}` evaluations across `2^i` blocks.

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

open Polynomial AdditiveNTT
namespace AdditiveNTT

universe u

-- We work over a generic field `L` of characteristic 2.
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
(h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))) (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
variable [Algebra 𝔽q L]

-- Let `β` be a basis of `L` over `𝔽q`, indexed by natural numbers.
variable (β : Fin r → L) (hβ_lin_indep : LinearIndependent 𝔽q β)
variable (ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r) -- ℓ ∈ {1, ..., r-1}

/-! ## 1. Intermediate Structures: Domains, Maps, and Bases

This section defines the intermediate evaluation domains, quotient maps, and the structure of the subspace vanishing polynomials and their bases. These are the core algebraic objects underlying the Additive NTT algorithm.
-/

section IntermediateStructures

/-! ### 1. Intermediate Domains `S⁽ⁱ⁾` and Quotient Maps `q⁽ⁱ⁾` -/

/-- The intermediate evaluation domain `S⁽ⁱ⁾`, defined as the image of the full evaluation space
under the normalized subspace vanishing polynomial `Ŵᵢ(X)`.
`∀ i ∈ {0, ..., r-1}`, we define `Uᵢ:= <β₀, ..., βᵢ₋₁>_{𝔽q}`, note that `Uᵣ` is not used.
`∀ i ∈ {0, ..., r-1}, S⁽ⁱ⁾` is the image of the subspace `U_{ℓ+R}` under the `𝔽q`-linear map `x ↦ Ŵᵢ(x)`. -/
noncomputable def S_domain (i : Fin r) : Subspace 𝔽q L :=
  let W_i_norm := normalizedW L 𝔽q β i
  let h_W_i_norm_is_additive : IsLinearMap 𝔽q (fun x : L => W_i_norm.eval x) :=
    AdditiveNTT.normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i
  Submodule.map (poly_eval_linear_map W_i_norm h_W_i_norm_is_additive)
    (U L 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩)

/-- The quotient map `q⁽ⁱ⁾(X)` that relates successive domains.
`q⁽ⁱ⁾(X) := (Wᵢ(βᵢ)^q / Wᵢ₊₁(βᵢ₊₁)) * ∏_{c ∈ 𝔽q} (X - c)`. Usable range is `∀ i ∈ {0, ..., r-2}` -/
noncomputable def q_map (i : Fin r) : L[X] :=
  let constMultiplier := ((W L 𝔽q β i).eval (β i))^(Fintype.card 𝔽q)
    / ((W L 𝔽q β (i + 1)).eval (β (i + 1)))
  C constMultiplier * ∏ c: 𝔽q, ((X: L[X]) - C (algebraMap 𝔽q L c))

/-- **Lemma 4.2.** The quotient maps compose with the `Ŵ` polynomials.
`q⁽ⁱ⁾ ∘ Ŵᵢ = Ŵᵢ₊₁, ∀ i ∈ {0, ..., r-2}`. -/
lemma q_map_comp_normalizedW
  (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
  (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent (R:=𝔽q) (M:=L) (v:=β)) (i : Fin r) (h_i_add_1 : i + 1 < r):
  (q_map 𝔽q β i).comp (normalizedW L 𝔽q β i) = normalizedW L 𝔽q β (i + 1) := by
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
  set W_i := W L 𝔽q β i with h_W_i
  set W_i_plus_1 := W L 𝔽q β (i + 1) with h_W_i_plus_1
  set val_i := W_i.eval (β i) with h_val_i
  set val_i_plus_1 := W_i_plus_1.eval (β (i + 1)) with h_val_i_plus_1

  -- Establish that the denominators in the definitions are non-zero
  have h_val_i_ne_zero : val_i ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero L 𝔽q β hβ_lin_indep i
  have h_val_i_plus_1_ne_zero : val_i_plus_1 ≠ 0 :=
    AdditiveNTT.Wᵢ_eval_βᵢ_neq_zero L 𝔽q β hβ_lin_indep (i + 1)

  -- The proof proceeds by a chain of equalities
  calc
    (q_map 𝔽q β i).comp (normalizedW L 𝔽q β i)
    _ = C (val_i ^ q / val_i_plus_1)
    * (∏ c:𝔽q, (X - C (algebraMap 𝔽q L c))).comp (normalizedW L 𝔽q β i) := by
      rw [q_map, mul_comp, C_comp]
    _ = C (val_i ^ q / val_i_plus_1) * ((normalizedW L 𝔽q β i) ^ q - normalizedW L 𝔽q β i) := by
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
      have W_linear := AdditiveNTT.W_linear_comp_decomposition L 𝔽q β h_Fq_card_gt_1
        h_Fq_char_prime hβ_lin_indep i (p:=X)
      simp_rw [comp_X] at W_linear
      simp_rw [q, val_i, W_i, W_i_plus_1]
      rw [W_linear]
      · simp only [one_div, map_pow]
      · omega
    _ = normalizedW L 𝔽q β (i + 1) := by -- Q.E.D.
      rw [normalizedW]

/-- The evaluation of the quotient map `q⁽ⁱ⁾(X)` is an `𝔽q`-linear map. Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem q_map_is_linear_map
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (i : Fin r):
  IsLinearMap 𝔽q (f:=fun inner_p ↦ (q_map 𝔽q β i).comp inner_p) := by
  set q := Fintype.card 𝔽q
  set constMultiplier := ((W L 𝔽q β i).eval (β i))^q / ((W L 𝔽q β (i + 1)).eval (β (i + 1)))
  have h_q_poly_form : q_map 𝔽q β i = C constMultiplier * (X ^ q - X) := by
    rw [q_map, prod_poly_sub_C_eq_poly_pow_card_sub_poly_in_L h_Fq_card_gt_1 (p:=X)]
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
        rw [AdditiveNTT.frobenius_identity_in_algebra (h_Fq_char_prime:=h_Fq_char_prime) (f:=f) (g:=g)]
      _ = (C constMultiplier) * (((X^q).comp f - X.comp f) + ((X^q).comp g - X.comp g)) := by
        rw [pow_comp, X_comp, X_comp, pow_comp, X_comp]
        ring
      _ = (C constMultiplier) * (((X: L[X]) ^ q - X).comp (f) + ((X: L[X]) ^ q - X).comp (g)) := by
        rw [←sub_comp, ←sub_comp]
      _ = (q_map 𝔽q β i).comp f + (q_map 𝔽q β i).comp g := by
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
      _ = c • (q_map 𝔽q β i).comp f := by
        rw [h_q_poly_form]

/-- **Theorem 4.3.** The quotient map `q⁽ⁱ⁾` maps the domain `S⁽ⁱ⁾` to `S⁽ⁱ⁺¹⁾`. Usable range is `∀ i ∈ {0, ..., r-2}`. -/
theorem q_map_maps_S_domain
(h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
(h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
(hβ_lin_indep : LinearIndependent 𝔽q β)
(ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r)
(i : Fin r) (h_i_add_1 : i + 1 < r) :
  have q_comp_linear_map := q_map_is_linear_map 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime i
  have q_eval_linear_map := AdditiveNTT.linear_map_of_comp_to_linear_map_of_eval (f:=q_map 𝔽q β i) q_comp_linear_map
  let q_i_map := poly_eval_linear_map (q_map 𝔽q β i) q_eval_linear_map
  let S_i: Subspace 𝔽q L := S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ R_rate h_ℓ_add_R_rate i
  let S_i_plus_1: Subspace 𝔽q L := S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ R_rate h_ℓ_add_R_rate (i + 1)
  Submodule.map q_i_map S_i = S_i_plus_1 :=
by
  set q_comp_linear_map := q_map_is_linear_map 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime i
  set q_eval_linear_map := AdditiveNTT.linear_map_of_comp_to_linear_map_of_eval (f:=q_map 𝔽q β i) q_comp_linear_map
  -- Unfold definitions and apply submodule and polynomial composition properties
  simp_rw [S_domain]
  -- `q⁽ⁱ⁾(S⁽ⁱ⁾) = q⁽ⁱ⁾(Ŵᵢ(⟨β₀, ..., β_{ℓ+R-1}⟩))`
  -- `= Ŵᵢ₊₁(⟨β₀, ..., β_{ℓ+R-1}⟩)`
  -- `= S⁽ⁱ⁺¹⁾`
  -- `⊢ map (q_i_map ∘ₗ Ŵᵢ_map) U = map (Ŵᵢ₊₁) U`
  rw [←Submodule.map_comp] -- for two nested maps (composition) over the same subspace
  -- The goal becomes `q_i_map ∘ₗ Ŵᵢ_map = Ŵᵢ₊₁`
  congr
  -- ⊢ poly_eval_linear_map (q_map 𝔽q β i) ⋯ ∘ₗ poly_eval_linear_map (normalizedW L 𝔽q β i) ⋯ =
  -- poly_eval_linear_map (normalizedW L 𝔽q β (i + 1)) ⋯

  -- We now have `(q_map ...).eval ((normalizedW ... i).eval x) = (normalizedW ... (i + 1)).eval x`.
  -- The `Polynomial.eval_comp` lemma states `p.eval (q.eval x) = (p.comp q).eval x`.
  set f := poly_eval_linear_map (q_map 𝔽q β i) q_eval_linear_map
  set g := poly_eval_linear_map (normalizedW L 𝔽q β i) (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)
  set t := poly_eval_linear_map (normalizedW L 𝔽q β (i + 1)) (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep (i + 1))
  show f ∘ₗ g = t -- equality on composition of linear maps
  ext x
  -- => equality on evaluation at x
  -- (this automatically matches linearity of f ∘ g with linearity of t)
  rw [LinearMap.comp_apply]
  -- ⊢ f (g x) = t x
  simp_rw [f, g, t, poly_eval_linear_map]
  -- unfold the linearmaps into their definitions (toFun, map_add, map_smul)
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  -- NOTE: `LinearMap.coe_mk` and `AddHom.coe_mk` convert linear maps into their functions
  -- ⊢ eval (eval x (normalizedW L 𝔽q β i)) (q_map 𝔽q β i) = eval x (normalizedW L 𝔽q β (i + 1))
  rw [←Polynomial.eval_comp]
  rw [q_map_comp_normalizedW 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i h_i_add_1]

/-- The composition `q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾ ∘ X`. -/
noncomputable def q_composition_chain (i : Fin r) : L[X] :=
  match i with
  | ⟨0, _⟩ => X
  | ⟨k + 1, h_k_add_1⟩ => (q_map 𝔽q β ⟨k, by omega⟩).comp (q_composition_chain ⟨k, by omega⟩)

omit [DecidableEq L] [DecidableEq 𝔽q] in
/-- Prove the equality between the recursive definition
of `q_composition_chain` and the Fin.foldl form. -/
lemma q_composition_chain_eq_foldl
  (ℓ R_rate : ℕ)
  (i : Fin r) :
  q_composition_chain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i =
  Fin.foldl (n:=i) (fun acc j =>
    (q_map 𝔽q β ⟨j, by omega⟩).comp acc) (X) := by
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    rw [q_composition_chain.eq_def]
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Fin.foldl_zero]
    rfl
  | succ k k_h i_h =>
    rw [q_composition_chain.eq_def]
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one]
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    simp only [Fin.coe_cast, Fin.foldl_succ_last, Fin.val_last, Fin.eta, Fin.coe_castSucc]
    congr

/--
**Corollary 4.4.** For each `i ∈ {0, ..., r-1}`, we have `Ŵᵢ = q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾`
(with the convention that for `i = 0`, this is just `X`).
-/
lemma normalizedW_eq_q_map_composition
  (h_W₀_eq_X : W L 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  -- We also need the hypotheses for q_map_comp_normalizedW
  (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
  (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (ℓ R_rate : ℕ)
  (i : Fin r) :
  normalizedW L 𝔽q β i = q_composition_chain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i :=
by
  -- We proceed by induction on i.
  induction i using Fin.succRecOnSameFinType with
  | zero =>
    -- Base case: i = 0
    -- We need to show `normalizedW ... 0 = q_composition_chain 0`.
    -- The RHS is `X` by definition of the chain.
    rw [q_composition_chain.eq_def]
    -- The LHS is `C (1 / eval (β 0) (W ... 0)) * (W ... 0)`.
    rw [normalizedW, h_W₀_eq_X, eval_X, h_β₀_eq_1, div_one, C_1, one_mul]
    rfl
  | succ k k_h i_h =>
    -- Inductive step: Assume the property holds for k, prove for k+1.
    -- The goal is `normalizedW ... (k+1) = q_composition_chain (k+1)`.
    -- The RHS is `(q_map k).comp (q_composition_chain k)` by definition.
    rw [q_composition_chain.eq_def]
    -- From Lemma 4.2, we know `normalizedW ... (k+1) = (q_map k).comp (normalizedW ... k)`.
    -- How to choose the rhs?
    have h_eq: ⟨k.val.succ, k_h⟩ = k + 1 := by
      rw [Fin.mk_eq_mk]
      rw [Fin.val_add_one]
      exact k_h
    simp only [h_eq.symm, Nat.succ_eq_add_one, Fin.eta]
    have h_res := q_map_comp_normalizedW 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep k k_h
    -- ⊢ normalizedW L 𝔽q β ⟨↑k + 1, k_h⟩ = (q_map 𝔽q β k).comp (q_composition_chain 𝔽q β k)
    rw [←i_h]
    rw [h_res]
    simp only [h_eq]

/-- The vectors `y_j^{(i)} = Ŵᵢ(β_j)` for `j ∈ {i, ..., ℓ+R-1}`. -/
noncomputable def s_domain_basis_vectors (i : Fin r) : Fin (ℓ + R_rate - i) → L :=
  fun k => (normalizedW L 𝔽q β i).eval (β ⟨i + k.val, by omega⟩)

/-- The vectors `s_domain_basis_vectors` are indeed elements of the subspace `S_domain`, `∀ i ∈ {0, ..., r-1}`. -/
lemma s_domain_basis_vectors_mem_S_domain
    (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
    (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
    (hβ_lin_indep : LinearIndependent 𝔽q β)
    (ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r)
    (i : Fin r) (k : Fin (ℓ + R_rate - i)) :
  s_domain_basis_vectors 𝔽q β ℓ R_rate h_ℓ_add_R_rate i k
    ∈ S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i := by
  have h_i_add_k_lt_r : i + k.val < r := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  have h_i_add_k_lt_ℓ_add_R_rate : i + k.val < ℓ + R_rate := by
    omega
  simp_rw [S_domain, s_domain_basis_vectors]
  -- The vector is `eval Ŵᵢ (β (i + k.val))`
  -- We must show it's in the image of U_{ℓ+R} under `eval Ŵᵢ`.
  -- This is true if the input `β (i + k.val)` is in `U_{ℓ+R}`.
  apply Submodule.mem_map_of_mem
  -- ⊢ β (i + ↑k) ∈ U L 𝔽q β (ℓ + R_rate)
  have h_β_i_in_U: β ⟨i + k.val, h_i_add_k_lt_r⟩ ∈ β '' Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
    exact Set.mem_image_of_mem β (Set.mem_Ico.mpr ⟨by norm_num, by omega⟩)
  exact Submodule.subset_span h_β_i_in_U

def S_basis (i : Fin r) (h_i : i < ℓ + R_rate): Fin (ℓ + R_rate - i) → L :=
  fun (k : Fin (ℓ + R_rate - i)) => β ⟨i + k.val, by omega⟩

lemma S_basis_range_eq (i : Fin r) (h_i : i < ℓ + R_rate):
  β '' Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ = Set.range (S_basis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i):= by
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
    unfold S_basis
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

/-- S⁽ⁱ⁾ is the image over `Wᵢ(X)` of the the subspace spanned by `{βᵢ, ..., β_{ℓ+R-1}}`. Usable range is `∀ i ∈ {0, ..., ℓ+R-1}`. -/
lemma S_domain_eq_image_of_upper_span (i: Fin r) (h_i: i < ℓ + R_rate):
  let V_i := Submodule.span 𝔽q (Set.range (S_basis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
  let W_i_map := poly_eval_linear_map (normalizedW L 𝔽q β i) (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)
  S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep (ℓ:=ℓ) (R_rate:=R_rate) (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i = Submodule.map W_i_map V_i :=
by
  -- Proof: U_{ℓ+R} is the direct sum of Uᵢ and Vᵢ.
  -- Any x in U_{ℓ+R} can be written as u + v where u ∈ Uᵢ and v ∈ Vᵢ.
  -- Ŵᵢ(x) = Ŵᵢ(u+v) = Ŵᵢ(u) + Ŵᵢ(v) = 0 + Ŵᵢ(v) = Ŵᵢ(v).
  -- So the image of U_{ℓ+R} is the same as the image of Vᵢ.

  -- Define V_i and W_i_map for use in the proof
  set V_i := Submodule.span 𝔽q (Set.range (S_basis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
  set W_i_map := poly_eval_linear_map (normalizedW L 𝔽q β i) (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)

  -- First, show that U_{ℓ+R} = U_i ⊔ V_i (direct sum)
  have h_span_supremum_decomposition : U L 𝔽q β ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ = U L 𝔽q β i ⊔ V_i := by
    unfold U
    -- U_{ℓ+R} is the span of {β₀, ..., β_{ℓ+R-1}}
    -- U_i is the span of {β₀, ..., β_{i-1}}
    -- V_i is the span of {β_i, ..., β_{ℓ+R-1}}
    have h_ico : Set.Ico 0 ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ = Set.Ico 0 i ∪ Set.Ico i ⟨ℓ + R_rate, h_ℓ_add_R_rate⟩ := by
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
    -- ⊢ β '' Set.Ico i (ℓ + R_rate) = Set.range (S_basis 𝔽q β (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i h_i)
    -- Show that the image of Set.Ico i (ℓ + R_rate) (from the definition of U_{ℓ+R}) is the same as V_i

    rw [S_basis_range_eq 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i]

  -- Now show that the image of U_{ℓ+R} under W_i_map is the same as the image of V_i
  rw [S_domain, h_span_supremum_decomposition, Submodule.map_sup]

  -- The image of U_i under W_i_map is {0} because W_i vanishes on U_i
  have h_U_i_image : Submodule.map W_i_map (U L 𝔽q β i) = ⊥ := by
    -- Show that any element in the image is 0
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    -- x ∈ Submodule.map W_i_map (U L 𝔽q β i) means x = W_i_map(y) for some y ∈ U_i
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    -- Show that W_i_map y = 0 for any y ∈ U_i
    have h_eval_zero : (normalizedW L 𝔽q β i).eval y = 0 :=
      normalizedWᵢ_vanishing L 𝔽q β i y hy
    exact h_eval_zero

  -- Combine the results: ⊥ ⊔ V = V
  rw [h_U_i_image]
  rw [bot_sup_eq]

/-- **Corollary 4.5.** The set `{Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})}` is an `𝔽q`-basis for `S⁽ⁱ⁾`. -/
noncomputable def S_domain_basis (i : Fin r) (h_i: i < ℓ + R_rate) :
  Basis (Fin (ℓ + R_rate - i)) 𝔽q (S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep (ℓ:=ℓ) (R_rate:=R_rate) (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i) :=
by
  -- Let V_i be the "upper" subspace spanned by {βᵢ, ..., β_{ℓ+R-1}}.
  let V_i := Submodule.span 𝔽q (Set.range (S_basis 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i))
  -- Let W_i_map be the linear map given by evaluating the polynomial Ŵᵢ.
  let W_i_map := poly_eval_linear_map (normalizedW L 𝔽q β i) (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i)

  have h_disjoint : Disjoint (U L 𝔽q β i) V_i := by
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
    rw [S_basis_range_eq 𝔽q β ℓ R_rate h_ℓ_add_R_rate i h_i] at h_res
    exact h_res

  have h_ker_eq_U : LinearMap.ker W_i_map = U L 𝔽q β i := by
    rw [kernel_normalizedW_eq_U L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i]

  -- The vectors {βᵢ, ...} form a basis for Vᵢ because β is linearly independent.
  let V_i_basis : Basis (Fin (ℓ + R_rate - i)) 𝔽q V_i :=
    Basis.span (by
      -- This is the proof of linear independence for the vectors {βᵢ, ...}.
      -- It follows because they are a subset of the LI family β.
      have h_sub_li : LinearIndependent 𝔽q (fun (k : Fin (ℓ + R_rate - i)) => β ⟨i + k.val, by omega⟩) :=
        hβ_lin_indep.comp (fun (k : Fin (ℓ + R_rate - i)) => ⟨i + k.val, by omega⟩) (by  -- ⊢ Function.Injective fun k ↦ ⟨↑i + ↑k, ⋯⟩
          intro k₁ k₂ h_eq
          simp at h_eq
          apply Fin.eq_of_val_eq
          omega
        )
      exact h_sub_li)

  -- We construct the isomorphism between Vᵢ and S⁽ⁱ⁾.
  -- S⁽ⁱ⁾ is the image of Vᵢ under W_i_map, and the map is injective on Vᵢ.
  set S_i := S_domain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep (ℓ:=ℓ) (R_rate:=R_rate) (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) i
  let iso : V_i ≃ₗ[𝔽q] S_i :=
    LinearEquiv.ofBijective
      (LinearMap.codRestrict S_i (W_i_map.comp (Submodule.subtype V_i))
        (by -- ⊢ ∀ (c : ↥V_i), (W_i_map ∘ₗ V_i.subtype) c ∈ S_i
          intro x
          -- ⊢ (W_i_map ∘ₗ V_i.subtype) x ∈ S_i
          have h_x_in_S_i : (W_i_map.comp (Submodule.subtype V_i)) x ∈ S_i := by
            simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, S_i]
            rw [S_domain_eq_image_of_upper_span 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate i h_i]
            exact
              Submodule.apply_coe_mem_map
                (poly_eval_linear_map (normalizedW L 𝔽q β i)
                  (normalizedW_is_additive L 𝔽q β h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep i))
                x
          exact h_x_in_S_i
        )) (by
        -- ⊢ Function.Bijective ⇑(LinearMap.codRestrict S_i (W_i_map ∘ₗ V_i.subtype) ⋯)
          constructor
          · -- INJECTIVITY
            intro v1 v2 h_v1_v2
            -- h_v1_v2 : (LinearMap.codRestrict S_i (W_i_map ∘ₗ V_i.subtype) ⋯) v1 = (LinearMap.codRestrict S_i (W_i_map ∘ₗ V_i.subtype) ⋯) v2
            -- ⊢ v1 = v2
-- First, simplify the hypothesis by unpacking the map definitions.
            simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, Subtype.ext_iff] at h_v1_v2
            -- The hypothesis is now `W_i_map ↑v1 = W_i_map ↑v2`.
            -- By linearity, this is equivalent to `W_i_map (↑v1 - ↑v2) = 0`.
            rw [← sub_eq_zero, ← LinearMap.map_sub] at h_v1_v2
            -- To show v1 = v2, we show v1 - v2 = 0.
            -- The coercion from a subtype is injective, so we just need to show the coerced difference is 0.
            apply Subtype.ext
            -- The element `↑(v1 - v2)` is in the kernel of `W_i_map`.
            have h_mem_ker : ↑(v1 - v2) ∈ LinearMap.ker W_i_map := h_v1_v2
            -- The kernel of the evaluation map is the vanishing subspace `Uᵢ`.
            -- Add this before the have h_mem_U line:
            have h_mem_U : ↑(v1 - v2) ∈ U L 𝔽q β i := h_ker_eq_U ▸ h_mem_ker
            -- The element `v1 - v2` is in `Vᵢ` since it's a submodule.
            have h_mem_V : ↑(v1 - v2) ∈ V_i := Submodule.sub_mem V_i v1.property v2.property
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            -- Thus, the element is in the intersection of `Uᵢ` and `Vᵢ`.
            have h_mem_inf : ↑(v1 - v2) ∈ (U L 𝔽q β i) ⊓ V_i :=
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
            -- We need to prove that for any `y ∈ S_i`, there exists an `x ∈ V_i` such that `W_i_map x = y`.
            -- This is essentially the definition of the image of a map.
            -- The goal is to show `Submodule.map W_i_map V_i = S_i`.
            intro y
            -- `y` is an element of `S_i` (which is a subtype).
            have h_y_in_image : y.val ∈ Submodule.map W_i_map V_i := by
              have h_y := y.property
              -- From the lemma `S_domain_eq_image_of_upper_span`, we know that S_i is *exactly* the image of V_i under W_i_map.
              unfold W_i_map V_i
              have h_S_i: S_i = Submodule.map W_i_map V_i := by
                unfold S_i
                rw [S_domain_eq_image_of_upper_span 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
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

/-- `∀ i ∈ {0, ..., ℓ-1}`, The `i`-th order subspace vanishing polynomials `Ŵₖ⁽ⁱ⁾`,
`Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾` for `k ∈ {1, ..., ℓ - i -1}`, and `X` for `k = 0`.
-- k ∈ {0, ..., ℓ-i-1}
-/
noncomputable def intermediate_norm_vpoly
    -- Assuming you have this hypothesis available from the context:
    (i: Fin (ℓ)) (k : Fin (ℓ - i)) : L[X] :=
  -- This definition requires strict order
  Fin.foldl (n:=k) (fun acc j =>
    (q_map 𝔽q β ⟨(i : ℕ) + (j : ℕ), by omega⟩).comp acc) (X)

-- /--
-- **Corollary 4.4.** For each `i ∈ {0, ..., r-1}`, we have `Ŵᵢ = q⁽ⁱ⁻¹⁾ ∘ ... ∘ q⁽⁰⁾`
-- (with the convention that for `i = 0`, this is just `X`).
-- -/
-- lemma normalizedW_eq_q_map_composition
--   (h_W₀_eq_X : W L 𝔽q β 0 = X)
--   (h_β₀_eq_1 : β 0 = 1)
--   -- We also need the hypotheses for q_map_comp_normalizedW
--   (h_Fq_card_gt_1: Fintype.card 𝔽q > 1)
--   (h_Fq_char_prime: Fact (Nat.Prime (ringChar 𝔽q)))
--   (hβ_lin_indep : LinearIndependent 𝔽q β)
--   (ℓ R_rate : ℕ)
--   (i : Fin r) :
--   normalizedW L 𝔽q β i = q_composition_chain 𝔽q β (ℓ:=ℓ) (R_rate:=R_rate) i :=
-- by

-- Ŵₖ⁽⁰⁾(X) = Ŵ(X)
theorem base_intermediate_norm_vpoly [NeZero ℓ]
  (h_W₀_eq_X : W L 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (k : Fin (ℓ)):
  intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by
    by_contra ht
    simp only [not_lt, nonpos_iff_eq_zero] at ht
    have h_ℓ_ne_0: ℓ ≠ 0 := NeZero.ne ℓ
    contradiction
  ⟩ k =
  normalizedW L 𝔽q β ⟨k, by omega⟩ := by
  unfold intermediate_norm_vpoly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, zero_add]
  rw [normalizedW_eq_q_map_composition 𝔽q β h_W₀_eq_X
    h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep ℓ R_rate ⟨k, by omega⟩]
  rw [q_composition_chain_eq_foldl 𝔽q β ℓ R_rate]

-- i = 0->l: Ŵᵢ = q(i-1) ∘ ⋯ ∘ q(0)
-- Ŵᵢ is actually Ŵᵢ⁽⁰⁾ => deg(Ŵᵢ) = 2^i = |Uᵢ|, and it vanishes on Uᵢ = Uᵢ⁽⁰⁾ = ⟨β₀, ..., β_{i-1}⟩

-- `q⁽ⁱ⁾(X) := ( Wᵢ(βᵢ)^{2} / W_{i+1}(β_{i+1}) ) ⬝ X ⬝ (X+1)` => deg(q⁽ⁱ⁾) = 2 = |𝔽q|
-- => each composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q| for the degree
-- => k times of composition of q⁽ⁱ⁾(X) brings a multiplicity of |𝔽q|^k for the degree

-- q⁽ⁱ⁾ ∘ Ŵᵢ⁽⁰⁾ = Ŵᵢ+1⁽⁰⁾
-- Ŵₖ⁽ⁱ⁾ := q⁽ⁱ⁺ᵏ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾: this receives an element at space S⁽ⁱ⁾ and returns an element at space S⁽ⁱ⁺ᵏ⁾ => go through k subspaces in transit (fold k times)
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
theorem Polynomial.comp_same_inner_eq_if_same_outer (f g: L[X]) (h_f_eq_g: f = g):
  ∀ x, f.comp x = g.comp x := by
  intro x
  rw [h_f_eq_g]

omit [DecidableEq L] [DecidableEq 𝔽q] in
-- ∀ i ∈ {0, ..., ℓ-1}, ∀ k ∈ {0, ..., ℓ-i-2}, `Ŵₖ₊₁⁽ⁱ⁾ = Ŵₖ⁽ⁱ⁺¹⁾ ∘ q⁽ⁱ⁾`
theorem intermediate_norm_vpoly_comp_qmap [NeZero ℓ] (i : Fin (ℓ))
    (h_i_lt_ℓ_minus_1 : i < ℓ - 1) (k : Fin (ℓ - i - 1)):
    intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate i ⟨k+1, by omega⟩ =
    (intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate (i+1) ⟨k, by
    rw [Fin.val_add_one (a:=i) (by omega)]
    omega
  ⟩).comp (q_map 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediate_norm_vpoly
  simp only -- Fin.foldl (↑k+1) ... = Fin.foldl (↑k+1) ...
  rw [Fin.foldl_succ] -- convert Fin.foldl (↑k+1) ... into (Fin.foldl (↑k) ...).comp (init value)
  simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, comp_X]
  conv_lhs =>
    rw [←X_comp (p:=q_map 𝔽q β ⟨↑i, by omega⟩)]
    rw [Polynomial.foldl_comp]
  congr -- convert Fin.foldl equality into equality of accumulator functions
  -- ⊢ (fun acc j ↦ (q_map 𝔽q β ⟨↑i + (↑j + 1), ⋯⟩).comp acc)
  -- = fun acc j ↦ (q_map 𝔽q β ⟨↑(i + 1) + ↑j, ⋯⟩).comp acc
  funext acc j
  have h_id_eq: i.val + (↑j + 1) = ↑(i + 1) + ↑j := by
    rw [Fin.val_add_one (a:=i) (by omega)]
    omega
  simp_rw [h_id_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] in
-- A helper derivation for intermediate_norm_vpoly_comp_qmap
-- i is now in Fin (ℓ-1) instead of Fin ℓ, and k is in Fin (ℓ - (↑i + 1))
theorem intermediate_norm_vpoly_comp_qmap_helper [NeZero ℓ] (i : Fin (ℓ - 1))
    (h_i_lt_ℓ_minus_1 : i < ℓ - 1) (k : Fin (ℓ - (↑i + 1))):
    (intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨↑i + 1, by omega⟩ k).comp (q_map 𝔽q β ⟨↑i, by omega⟩) =
    intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
      ⟨↑i, by omega⟩ ⟨k + 1, by simp only; omega⟩:= by
    simp only [Fin.is_lt, intermediate_norm_vpoly_comp_qmap]
    simp only [intermediate_norm_vpoly] -- write cast lemma for intermediate_norm_vpoly instead?
    congr
    funext acc j
    congr
    rw [Fin.val_add_one] -- ⊢ ↑⟨↑i, ⋯⟩ + 1 < ℓ
    have h_cast_eq: (⟨i.val, by omega⟩: Fin ℓ).val = i.val := by rfl
    rw [h_cast_eq]
    omega

/-- ∀ `i` ∈ {0, ..., ℓ-1}, The `i`-th order novel polynomial basis `Xⱼ⁽ⁱ⁾`.
`Xⱼ⁽ⁱ⁾ := Π_{k=0}^{ℓ-i-1} (Ŵₖ⁽ⁱ⁾)^{jₖ}`, ∀ j ∈ {0, ..., 2^(ℓ-i)-1} -/
noncomputable def intermediate_novel_basis_X (i : Fin (ℓ)) (j : Fin (2 ^ (ℓ - i))): L[X] :=
  (Finset.univ: Finset (Fin (ℓ - i)) ).prod (fun k =>
    (intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate i k) ^ (bit k j))
-- NOTE: possibly we state some Basis for `(Xⱼ⁽ⁱ⁾)  `




-- -- Ŵₖ⁽⁰⁾(X) = Ŵ(X)
-- theorem base_intermediate_norm_vpoly [NeZero ℓ]
--   (h_W₀_eq_X : W L 𝔽q β 0 = X)
--   (h_β₀_eq_1 : β 0 = 1)
--   (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
--   (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
--   (hβ_lin_indep : LinearIndependent 𝔽q β)
--   (k : Fin (ℓ)):
--   intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by
--     by_contra ht
--     simp only [not_lt, nonpos_iff_eq_zero] at ht
--     have h_ℓ_ne_0: ℓ ≠ 0 := NeZero.ne ℓ
--     contradiction
--   ⟩ k =
--   normalizedW L 𝔽q β ⟨k, by omega⟩ := by
--   unfold intermediate_norm_vpoly
--   simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, zero_add]
--   rw [normalizedW_eq_q_map_composition 𝔽q β h_W₀_eq_X
--     h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep ℓ R_rate ⟨k, by omega⟩]
--   rw [q_composition_chain_eq_foldl 𝔽q β ℓ R_rate]

-- Xⱼ⁽⁰⁾ = Xⱼ
theorem base_intermediate_novel_basis_X [NeZero ℓ]
  (h_W₀_eq_X : W L 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (j : Fin (2 ^ ℓ)):
  intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by
    by_contra ht
    simp only [not_lt, nonpos_iff_eq_zero] at ht
    have h_ℓ_ne_0: ℓ ≠ 0 := NeZero.ne ℓ
    contradiction
  ⟩ j =
  Xⱼ L 𝔽q β ℓ (by omega) j := by
  unfold intermediate_novel_basis_X Xⱼ
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod]
  have h_res := base_intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate
    h_W₀_eq_X h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep
  simp only [Fin.mk_zero'] at h_res
  conv_lhs =>
    enter [2, x, 1]
    rw [h_res]
  congr

lemma mul_two_lt_two_pow (a b c: ℕ) (h_a_lt_2_pow_b: a < 2^b) (h_b_lt_c: b < c): a * 2 < 2^c := by
  if h_b_eq_0: b = 0 then
    rw [h_b_eq_0, pow_zero] at h_a_lt_2_pow_b
    interval_cases a
    · norm_num;
  else
    have h_le: 2^(b+1) ≤ 2^c := by
      rw [pow_le_pow_iff_right₀ (a:=2) (n:=b+1) (m:=c) (by omega)]
      omega
    calc
      _ ≤ 2^(b+1) - 1 := by omega
      _ ≤ 2^c - 1 := by omega
      _ < 2^c := by omega

lemma mul_two_add_one_lt_two_pow (a b c: ℕ) (h_a_lt_2_pow_b: a < 2^b) (h_b_lt_c: b < c): a * 2 + 1 < 2^c := by
  if h_b_eq_0: b = 0 then
    rw [h_b_eq_0, pow_zero] at h_a_lt_2_pow_b
    interval_cases a
    · norm_num; omega;
  else
    have h_le: 2^(b+1) ≤ 2^c := by
      rw [pow_le_pow_iff_right₀ (a:=2) (n:=b+1) (m:=c) (by omega)]
      omega
    have h_a_mul_2_add_1_lt_2_pow_c: a * 2 + 1 ≤ 2^c - 1 := by
      calc
        _ ≤ 2^(b+1) - 1 := by omega
        _ ≤ 2^c - 1 := by omega
    exact Nat.add_lt_of_lt_sub h_a_mul_2_add_1_lt_2_pow_c

lemma lt_two_pow_of_lt_two_pow_exp_le (x i j: ℕ) (h_x_lt_2_pow_i: x < 2^i) (h_i_le_j: i ≤ j): x < 2^j := by
  calc
    _ < 2^i := by omega
    _ ≤ 2^j := by apply pow_le_pow_right' (by omega) (by omega)

-- X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}
lemma even_index_intermediate_novel_basis_decomposition [NeZero ℓ] (i : Fin (ℓ-1))  (h_i_lt_ℓ_minus_1 : i < ℓ - 1) (j : Fin (2 ^ (ℓ - i - 1))):
  intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2, by
    apply mul_two_lt_two_pow j (ℓ-i-1) (ℓ-i) (by omega) (by omega)
  ⟩  = (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
  ⟩).comp (q_map 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediate_novel_basis_X
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j)ₖ) = ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]
  conv_rhs =>
    enter [2, x]
    rw [intermediate_norm_vpoly_comp_qmap_helper 𝔽q (h_i_lt_ℓ_minus_1:=by omega)]

  -- ⊢ ∏ x, intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ bit (↑x) (↑j * 2) =
  -- ∏ x, intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ bit ↑x ↑j

  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ x ^ bit (↑x) (↑j * 2)
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
    have h_exp: bit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2) = 0 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      have res := lsb_of_multiple_of_two (n:=j.val)
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
  have h_exp_eq: bit (↑x + 1) (↑j * 2) = bit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply bit_eq_succ_bit_of_mul_two (k:=↑x) (n:=↑j)
  rw [h_exp_eq]

omit [DecidableEq L] [DecidableEq 𝔽q] in
-- X₂ⱼ₊₁⁽ⁱ⁾ = X * (Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))) ∀ j ∈ {0, ..., 2^(ℓ-i)-1}, ∀ i ∈ {0, ..., ℓ-1}
lemma odd_index_intermediate_novel_basis_decomposition [NeZero ℓ]
    (i : Fin (ℓ-1)) (h_i_lt_ℓ_minus_1 : i < ℓ - 1) (j : Fin (2 ^ (ℓ - i - 1))):
    intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ ⟨j * 2 + 1, by
      apply mul_two_add_one_lt_two_pow j (ℓ-i-1) (ℓ-i) (by omega) (by omega)
    ⟩  = X * (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
      apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i-1) (ℓ-(i+1)) (by omega) (by omega)
    ⟩).comp (q_map 𝔽q β ⟨i, by omega⟩) := by
  unfold intermediate_novel_basis_X
  rw [prod_comp]
  -- ∏ k ∈ Fin (ℓ - i), (Wₖ⁽ⁱ⁾(X))^((2j₊₁)ₖ)
  -- = X * ∏ k ∈ Fin (ℓ - (i+1)), (Wₖ⁽ⁱ⁺¹⁾(X))^((j)ₖ) ∘ q⁽ⁱ⁾(X)
  simp only [pow_comp]

  conv_rhs =>
    enter [2]
    enter [2, x]
    rw [intermediate_norm_vpoly_comp_qmap_helper 𝔽q (h_i_lt_ℓ_minus_1:=by omega)]

  -- ⊢ ∏ x, intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ x ^ bit (↑x) (↑j * 2 + 1) =
  -- X * ∏ x, intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, ⋯⟩ ⟨↑x + 1, ⋯⟩ ^ bit ↑x ↑j

  set fleft := fun x : Fin (ℓ - ↑i) =>
    intermediate_norm_vpoly 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ x ^ bit (↑x) (↑j * 2 + 1)
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
    have h_exp: bit (0: Fin (ℓ - (↑i + 1) + 1)) (↑j * 2 + 1) = 1 := by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      unfold bit
      simp only [Nat.shiftRight_zero, Nat.and_one_is_mod, Nat.mul_add_mod_self_right, Nat.mod_succ]
    rw [h_exp]
    simp only [pow_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod]
    unfold intermediate_norm_vpoly
    simp only [Fin.foldl_zero]

  rw [fleft_0_eq_X]
  congr -- apply Finset.prod_congr rfl
  funext x
  simp only [Fin.val_succ]
  unfold fleft
  simp only
  have h_exp_eq: bit (↑x + 1) (↑j * 2 + 1) = bit ↑x ↑j := by
    have h_num_eq: j.val * 2 = 2 * j.val := by omega
    rw [h_num_eq]
    apply bit_eq_succ_bit_of_mul_two_add_one (k:=↑x) (n:=↑j)

  rw [h_exp_eq]

/-- ∀ `i` ∈ {0, ..., ℓ-1}, The `i`-th order evaluation polynomial
`P⁽ⁱ⁾(X) := ∑_{j=0}^{2^(ℓ-i)-1} aⱼ ⋅ Xⱼ⁽ⁱ⁾(X)` over the domain `S⁽ⁱ⁾`.
  where the polynomial `P⁽⁰⁾(X)` over the domain `S⁽⁰⁾` is exactly the original
  polynomial `P(X)` we need to evaluate.
-/
noncomputable def intermediate_evaluation_poly (a : Fin (2 ^ ℓ) → L) (i : Fin (ℓ)) : L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i))), C (a ⟨j, by
    calc _ < 2 ^ (ℓ - i) := by omega
      _ ≤ 2 ^ ℓ := by simp only [Nat.one_le_ofNat, tsub_le_iff_right, le_add_iff_nonneg_right,
        zero_le, pow_le_pow_right₀];
    ⟩) * (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate i ⟨j, by omega⟩)

/-- The even and odd refinements of `P⁽ⁱ⁾(X)` which are polynomials in the `(i+1)`-th basis.
`P₀⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)`
`P₁⁽ⁱ⁺¹⁾(Y) = ∑_{j=0}^{2^{ℓ-i-1}-1} a_{2j+1} ⋅ Xⱼ⁽ⁱ⁺¹⁾(Y)` -/
noncomputable def even_refinement [NeZero ℓ] (a : Fin (2 ^ ℓ) → L) (i : Fin (ℓ - 1)): L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (a ⟨j*2, by
    calc _ < 2 ^ (ℓ - i - 1) * 2 := by omega
      _ ≤ 2 ^ (ℓ - 1) * 2 := by
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by omega) (by omega)
      _ = _ := by rw [pow_sub_one_mul (by exact NeZero.ne ℓ) 2]
    ⟩) * (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
      calc _ < 2 ^ (ℓ - i - 1):= by omega
        _ = _ := rfl
    ⟩)

noncomputable def odd_refinement [NeZero ℓ] (a : Fin (2 ^ ℓ) → L) (i : Fin (ℓ - 1)): L[X] :=
  ∑ (⟨j, hj⟩: Fin (2^(ℓ-i-1))), C (a ⟨j*2+1, mul_two_add_one_lt_two_pow j (ℓ-i-1) ℓ (hj) (by omega)
    ⟩)
    * (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i+1, by omega⟩ ⟨j, by
      calc _ < 2 ^ (ℓ - i - 1):= by omega
        _ = _ := rfl
    ⟩)

-- lemma lt_two_pow_succ (x i: ℕ) (h_i: i > 0): x < 2^(i-1) → x * 2 < 2^i := by
--   intro h_x_lt_2_pow_i_minus_1
--   have h_x_mul_2_lt_2_pow_i: x * 2 < 2^i := by
--     calc
--       _ < 2^(i-1) * 2 := by omega
--       _ = 2^i := by exact Nat.two_pow_pred_mul_two h_i
--   exact h_x_mul_2_lt_2_pow_i

/-- **Key Polynomial Identity (Equation 39)**. This identity is the foundation for the
butterfly operation in the Additive NTT. It relates a polynomial in the `i`-th basis to
its even and odd parts expressed in the `(i+1)`-th basis via the quotient map `q⁽ⁱ⁾`.
∀ i ∈ {0, ..., ℓ-1}, `P⁽ⁱ⁾(X) = P₀⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) + X ⋅ P₁⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))` -/
theorem evaluation_poly_split_identity [NeZero ℓ] (i : Fin (ℓ - 1)) (a : Fin (2 ^ ℓ) → L) :
  let P_i: L[X] := intermediate_evaluation_poly 𝔽q β ℓ R_rate h_ℓ_add_R_rate a ⟨i, by omega⟩
  let P_even_i_plus_1: L[X] := even_refinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate a i
  let P_odd_i_plus_1: L[X] := odd_refinement 𝔽q β ℓ R_rate h_ℓ_add_R_rate a i
  let q_i: L[X] := q_map 𝔽q β ⟨i, by omega⟩
  P_i = (P_even_i_plus_1.comp q_i) + X * (P_odd_i_plus_1.comp q_i) := by

  dsimp only [Lean.Elab.WF.paramLet]
  simp only [intermediate_evaluation_poly, Fin.eta]
  simp only [even_refinement, Fin.eta, sum_comp, mul_comp, C_comp, odd_refinement]

  set leftEvenTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (a ⟨j * 2, by
    exact mul_two_lt_two_pow j (ℓ-i-1) ℓ (by omega) (by omega)
  ⟩) * intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2, by
    exact mul_two_lt_two_pow j (ℓ-i-1) (ℓ-i) (by omega) (by omega)
  ⟩
  set leftOddTerm := ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)), C (a ⟨j * 2 + 1, by
    apply mul_two_add_one_lt_two_pow j (ℓ-i-1) ℓ (by omega) (by omega)
  ⟩) * intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j * 2 + 1, by
    exact mul_two_add_one_lt_two_pow j (ℓ-i-1) (ℓ-↑i) (by omega) (by omega)
  ⟩

  have h_split_P_i: ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i)), C (a ⟨j, by
    apply lt_two_pow_of_lt_two_pow_exp_le j (ℓ-i) ℓ (by omega) (by omega)
  ⟩) * intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨j, by omega⟩ =
  leftEvenTerm + leftOddTerm
  := by
    unfold leftEvenTerm leftOddTerm
    simp only [Fin.eta]

    -- ⊢ ∑ k ∈ Fin (2 ^ (ℓ - ↑i)), C (aₖ) * Xₖ⁽ⁱ⁾(X) = -- just pure even odd split
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (a₂ₖ) * X₂ₖ⁽ⁱ⁾(X) +
    -- ∑ k ∈ Fin (2 ^ (ℓ - ↑i - 1)), C (a₂ₖ+1) * X₂ₖ+1⁽ⁱ⁾(X)

    set f1 := fun x: ℕ => -- => use a single function to represent the sum
      if hx: x < 2 ^ (ℓ - ↑i) then
        C (a ⟨x, by apply lt_two_pow_of_lt_two_pow_exp_le x (ℓ-i) ℓ (by omega) (by omega)⟩) *
          intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x, by omega⟩
      else 0

    have h_x: ∀ x: Fin (2 ^ (ℓ - ↑i)), f1 x.val =
      C (a ⟨x.val, by apply lt_two_pow_of_lt_two_pow_exp_le x.val (ℓ-i) ℓ (by omega) (by omega)⟩) *
        intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val, by simp only; omega⟩ := by
      intro x
      unfold f1
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

    conv_lhs =>
      enter [2, x]
      rw [←h_x x]

    have h_x_2: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2) =
      C (a ⟨x.val * 2, by apply mul_two_lt_two_pow x.val (ℓ-i-1) ℓ (by omega) (by omega)⟩) *
        intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2, by
          exact mul_two_lt_two_pow x.val (ℓ-i-1) (ℓ-i) (by omega) (by omega)
        ⟩ := by
      intro x
      unfold f1
      simp only [dite_mul, zero_mul]
      have h_x_lt_2_pow_i_minus_1 := mul_two_lt_two_pow x.val (ℓ-i-1) (ℓ-i) (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]

    conv_rhs =>
      enter [1, 2, x]
      rw [←h_x_2 x]

    have h_x_3: ∀ x: Fin (2 ^ (ℓ - ↑i - 1)), f1 (x*2+1) =
      C (a ⟨x.val * 2 + 1, by apply mul_two_add_one_lt_two_pow x.val (ℓ-i-1) ℓ (by omega) (by omega)⟩) *
        intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨↑i, by omega⟩ ⟨x.val * 2 + 1, by
          exact mul_two_add_one_lt_two_pow x.val (ℓ-i-1) (ℓ-i) (by omega) (by omega)
        ⟩ := by
      intro x
      unfold f1
      simp only [dite_mul, zero_mul]
      have h_x_lt_2_pow_i_minus_1 := mul_two_add_one_lt_two_pow x.val (ℓ-i-1) (ℓ-i) (by omega) (by omega)
      simp only [h_x_lt_2_pow_i_minus_1, ↓reduceDIte]

    conv_rhs =>
      enter [2, 2, x]
      rw [←h_x_3 x]

    -- ⊢ ∑ x, f1 ↑x = ∑ x, f1 (↑x * 2) + ∑ x, f1 (↑x * 2 + 1)

    have h_1: ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i)), f1 i = ∑ i ∈ Finset.range (2 ^ (ℓ - ↑i - 1 + 1)), f1 i := by
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
      C (a ⟨j * 2, by
        apply mul_two_lt_two_pow j (ℓ-i-1) ℓ (by omega) (by omega)
      ⟩) *
        (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
          apply lt_two_pow_of_lt_two_pow_exp_le (x:=j) (i:=ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
        ⟩).comp (q_map 𝔽q β ⟨i, by omega⟩)

  set rightOddTerm :=
    X *
      ∑ ⟨j, hj⟩ : Fin (2 ^ (ℓ - ↑i - 1)),
        C (a ⟨j * 2 + 1, by
          apply mul_two_add_one_lt_two_pow j (ℓ-i-1) ℓ (by omega) (by omega)
        ⟩) *
          (intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i + 1, by omega⟩ ⟨j, by
            apply lt_two_pow_of_lt_two_pow_exp_le (x:=j) (i:=ℓ-↑i-1) (j:=ℓ-↑i-1) (by omega) (by omega)
          ⟩).comp (q_map 𝔽q β ⟨i, by omega⟩)

  conv_rhs => change rightEvenTerm + rightOddTerm

  have h_right_even_term: leftEvenTerm = rightEvenTerm := by
    unfold rightEvenTerm leftEvenTerm
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Fin.eta, mul_eq_mul_left_iff, map_eq_zero]
    --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X)) ∨ a₂ⱼ = 0
    by_cases h_a_j_eq_0: a ⟨j * 2, by apply mul_two_lt_two_pow j (ℓ-i-1) ℓ (by omega) (by omega)⟩ = 0
    · simp only [h_a_j_eq_0, or_true]
    · simp only [h_a_j_eq_0, or_false]
      --  X₂ⱼ⁽ⁱ⁾ = Xⱼ⁽ⁱ⁺¹⁾(q⁽ⁱ⁾(X))
      exact even_index_intermediate_novel_basis_decomposition 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ (by omega) j

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
lemma intermediate_poly_P_base [NeZero ℓ]
  (h_W₀_eq_X : W L 𝔽q β 0 = X)
  (h_β₀_eq_1 : β 0 = 1)
  (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
  (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q)))
  (hβ_lin_indep : LinearIndependent 𝔽q β)
  (h_ℓ : ℓ ≤ r) (a : Fin (2^ℓ) → L) :
  intermediate_evaluation_poly 𝔽q β ℓ R_rate h_ℓ_add_R_rate a ⟨0, Nat.pos_of_neZero ℓ⟩ =
    polynomial_from_novel_coeffs L 𝔽q β ℓ h_ℓ a := by
  unfold polynomial_from_novel_coeffs intermediate_evaluation_poly
  simp only [Fin.mk_zero', Fin.coe_ofNat_eq_mod, Fin.eta]
  conv_rhs =>
    enter [2, j]
    rw [←base_intermediate_novel_basis_X 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_W₀_eq_X
      h_β₀_eq_1 h_Fq_card_gt_1 h_Fq_char_prime hβ_lin_indep j]
  congr

end IntermediateStructures

section AlgorithmCorrectness

/-! ## 3. The Additive NTT Algorithm and Correctness

This section describes the construction of the evaluation points, the tiling of coefficients, the main loop invariant, and the final correctness theorem for the Additive NTT algorithm.
-/

/-- Constructs an evaluation point `ω` in the domain `S⁽ⁱ⁾` from a bit representation.
This uses the `𝔽q`-basis of `S⁽ⁱ⁾` from `S_domain_basis`.
`ω_{u,b,i} = b⋅Ŵᵢ(βᵢ) + ∑_{k=0}^{|u|-1} uₖ ⋅ Ŵᵢ(β_{i+1+k})`
where `(u,b)` is a bit string of length `ℓ + R - i`.
-/
noncomputable def evaluation_point_ω (i : Fin (ℓ + R_rate)) (v_bits : Fin (2^(ℓ + R_rate - i))) : L :=
  let v_val := v_bits.val
  let b_bit := v_val % 2 -- the LSB
  let u_val := v_val / 2 -- the remaining bits

  -- Start with the coefficient for Ŵᵢ(βᵢ)
  let base_term := if b_bit = 1 then
    (normalizedW L 𝔽q β ⟨i, by omega⟩).eval (β ⟨i, by omega⟩)
  else 0

    -- Add the linear combination of the remaining basis vectors
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
    if bit k u_val = 1 then
      (normalizedW L 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + 1 + k, by
        have h_i_lt_r := i.isLt
        have h_k_lt_range := k < (ℓ + R_rate - i - 1)
        have h_range := ℓ + R_rate - i - 1
        have h_k_lt_range_nat := k < h_range
        have h_i_add_1_add_k_lt_r := by
          calc i + 1 + k < i + 1 + (ℓ + R_rate - i - 1) := by omega
            _ = ℓ + R_rate := by omega
            _ ≤ r := by omega
        exact h_i_add_1_add_k_lt_r⟩)
    else
      0

/--
The `2^R_rate`-fold tiling of coefficients `a` into the initial buffer `b`.
`b(v) = aⱼ`, where `j` are the `ℓ` LSBs of `v`.
-/
def tile_coeffs (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  fun v => a (Fin.mk (v.val % (2^ℓ)) (Nat.mod_lt v.val (pow_pos (zero_lt_two) ℓ)))

/--
Computes the twiddle factor `t` for a given stage `i` and high-order bits `u`.
`t := Σ_{k=0}^{ℓ+R-i-2} u_k ⋅ Ŵᵢ(β_{i+1+k})`.
This corresponds to the `x₀` term in the recursive butterfly identity.
-/
noncomputable def twiddle_factor (i : Fin (ℓ + R_rate)) (u_val : Nat) : L :=
  let range_end := ℓ + R_rate - i - 1
  ∑ (⟨k, hk⟩: Fin (ℓ + R_rate - i - 1)),
    if bit k u_val = 1 then
      (normalizedW L 𝔽q β ⟨i, by omega⟩).eval (β ⟨i + 1 + k, by omega⟩)
    else
      0

/--
A single stage of the Additive NTT for a given `i`.
It takes the buffer `b` from the previous stage and applies the butterfly operations.
This function implements one step of the `for i from ℓ-1 down to 0` loop.
-/
noncomputable def ntt_stage (i : Fin (ℓ + R_rate)) (b : Fin (2 ^ (ℓ + R_rate)) → L) : Fin (2^(ℓ + R_rate)) → L :=
  fun (j : Fin (2^(ℓ + R_rate))) =>
    let j_val := j.val
    let pow2i := 2^i.val
    let is_upper_wing := (j_val / pow2i) % 2 == 0

    if is_upper_wing then -- This is the `b(u||0||v)` case
      let u_val := j_val / (2 * pow2i)
      let t := twiddle_factor 𝔽q β ℓ R_rate h_ℓ_add_R_rate i u_val
      let partner_idx_val := j_val + pow2i
      if h : partner_idx_val < 2^(ℓ + R_rate) then
        let partner_idx := Fin.mk partner_idx_val h
        b j + t * b partner_idx
      else b j -- Unreachable under normal conditions
    else -- This is the `b(u||1||v)` case
      let partner_idx_val := j_val - pow2i
      if h : partner_idx_val < 2^(ℓ + R_rate) then
        let u_val := partner_idx_val / (2 * pow2i)
        let t := twiddle_factor 𝔽q β ℓ R_rate h_ℓ_add_R_rate i u_val
        let partner_idx := Fin.mk partner_idx_val h
        let b_upper_old := b partner_idx
        let b_lower_old := b j
        let b_upper_new := b_upper_old + t * b_lower_old
        b_lower_old + b_upper_new
      else b j -- Unreachable

/--
**The Additive NTT Algorithm (Algorithm 2)**

Computes the Additive NTT on a given set of coefficients from the novel basis.
- `a`: The initial coefficient array `(a₀, ..., a_{2^ℓ-1})`.
-/
noncomputable def additive_ntt (a : Fin (2 ^ ℓ) → L) : Fin (2^(ℓ + R_rate)) → L :=
  let b: Fin (2^(ℓ + R_rate)) → L := tile_coeffs ℓ R_rate a -- Note: can optimize on this
  Fin.foldr (n:=ℓ) (f:= fun i current_b =>
    ntt_stage 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ current_b
  ) (init:=b)

/--
The main loop invariant for the `additive_ntt` algorithm.

**Main statement:**
After round `i ∈ {ℓ-1, ℓ-2, ..., 0}`: the buffer `b` at index `j` (which can be decomposed as `j = (u || b || v)` in little-endian order, where
- `u` is a bitstring of length `ℓ + R_rate - i - 1`,
- `b` is a single bit (the LSB of the high bits),
- `v` is a bitstring of length `i` (the LSBs),
holds the value `P⁽ⁱ⁾(ω_{u, b, i})`,
where:
  - `P⁽ⁱ⁾` is the intermediate polynomial at round `i` (in the novel basis),
  - `ω_{u, b, i}` is the evaluation point in the subspace `S⁽ⁱ⁾` constructed as a linear combination of the basis elements of `S⁽ⁱ⁾`:
    - the bit `b` is the coefficient for `Ŵᵢ(βᵢ)` (the LSB),
    - the LSB of `u` is the coefficient for `Ŵᵢ(β_{i+1})`, ..., the MSB of `u` is the coefficient for `Ŵᵢ(β_{ℓ+R_rate-1})`.
  - The value is replicated `2^i` times for each `v` (i.e., the last `i` bits do not affect the value).

More precisely, for all `j : Fin (2^(ℓ + R_rate))`,
let `u_b_v := j.val` (as a natural number),
- let `v := u_b_v % 2^i` (the `i` LSBs),
- let `u_b := u_b_v / 2^i` (the high bits),
- let `b := u_b % 2` (the LSB of the high bits),
- let `u := u_b / 2` (the remaining high bits),
then:
  b j = P⁽ⁱ⁾(ω_{u, b, i})
-/
def additive_ntt_invariant (h_ℓ : ℓ ≤ r) (input_buffer : Fin (2^(ℓ + R_rate)) → L) (original_coeffs : Fin (2^ℓ) → L) (i : Fin ℓ): Prop :=
  ∀ (j : Fin (2^(ℓ + R_rate))),
    let u_b_v := j.val
    let v := u_b_v % (2^i.val) -- the i LSBs
    let u_b := u_b_v / (2^i.val) -- the high bits
    let b_bit := u_b % 2 -- the LSB of the high bits
    let u := u_b / 2 -- the remaining high bits
    let P_i := intermediate_evaluation_poly 𝔽q β ℓ R_rate h_ℓ_add_R_rate original_coeffs ⟨i, by omega⟩
    let output_buffer := ntt_stage 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer
    let ω := evaluation_point_ω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ (Fin.mk (u * 2 + b_bit) (by
      -- u has length ℓ + R_rate - i - 1 bits, b_bit is 0 or 1, so u * 2 + b_bit < 2^(ℓ + R_rate - i)
      have h1 : u < 2^(ℓ + R_rate - i - 1) := by
        -- u_b < 2^(ℓ + R_rate - i), so u = u_b / 2 < 2^(ℓ + R_rate - i - 1)
        sorry
      have h2 : b_bit < 2 := by sorry
      have : u * 2 + b_bit < 2^(ℓ + R_rate - i) := by
        -- 2 * 2^(ℓ + R_rate - i - 1) = 2^(ℓ + R_rate - i)
        sorry
      exact this
    ))
    output_buffer j = P_i.eval ω

/--
The correctness theorem for the `ntt_stage` function. This is the inductive step
in the main proof. It asserts that if the invariant holds for `i+1`, then after
applying `ntt_stage i`, the invariant holds for `i`.
-/
lemma ntt_stage_correctness (h_ℓ : ℓ ≤ r) (i : Fin ℓ) (h_i: i + 1 < ℓ) (input_buffer: Fin (2^(ℓ + R_rate)) → L) (original_coeffs : Fin (2 ^ ℓ) → L) :
  additive_ntt_invariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_ℓ input_buffer original_coeffs (i:=⟨i.val+1, by omega⟩) →
  additive_ntt_invariant 𝔽q β ℓ R_rate h_ℓ_add_R_rate h_ℓ (input_buffer:=ntt_stage 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨i, by omega⟩ input_buffer) (original_coeffs:=original_coeffs) i :=
by
  -- This proof is the core of the work, using the `key_polynomial_identity`.
  sorry

/--
**Main Correctness Theorem for Additive NTT**

If `b` is the output of `additive_ntt` on input `a`, then for all `j`, `b j` is the evaluation of the polynomial `P` (from the novel basis coefficients `a`) at the evaluation point `ω_{0, j}` in the domain `S⁰`.
-/
theorem additive_ntt_correctness [NeZero ℓ]
  (hβ_lin_indep : LinearIndependent 𝔽q β) (h_ℓ : ℓ ≤ r)
  (original_coeffs : Fin (2 ^ ℓ) → L)
  (output_buffer : Fin (2 ^ (ℓ + R_rate)) → L)
  (h_alg : output_buffer = additive_ntt 𝔽q β ℓ R_rate h_ℓ_add_R_rate original_coeffs) :
  let P := polynomial_from_novel_coeffs L 𝔽q β ℓ h_ℓ original_coeffs
  ∀ (j : Fin (2^(ℓ + R_rate))),
    output_buffer j = P.eval (evaluation_point_ω 𝔽q β ℓ R_rate h_ℓ_add_R_rate ⟨0, by exact Nat.pos_of_neZero (ℓ + R_rate)⟩ j) :=
by
  -- The proof proceeds by induction on `i` from `ℓ` down to `0`, using `(List.range ℓ).foldr`.
  -- It relies on `ntt_stage_correctness` for the inductive step.
  sorry

end AlgorithmCorrectness
end AdditiveNTT
