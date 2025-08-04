/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT
import ArkLib.Data.FieldTheory.AdditiveNTT.NovelPolynomialBasis
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# The (FRI-)Binius polynomial commitment scheme, as a Vector IOP

This file develops the FRI-Binius PCS and its components including the
Binary Basefold protocol and the ring-switching protocol, both as oracle reductions.

## Main Definitions

## TODOs
- Define the Binary Basefold main protocol
- Define the ring-switching protocol

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).
-/

namespace Binius

/-!
This file contains the definitions for the algebraic components of the Binary Basefold protocol,
specifically the `fold` operation.
-/
namespace BinaryBasefold

/-!
# The Binary Basefold polynomial commitment scheme

We describe the Binary Basefold protocol as a composition of many single oracle reduction rounds.

## Protocol Description

The Binary Basefold protocol is parameterized by the following parameters:
- `L`: the underlying semiring, which is a extension of `𝔽q` of degree `r`, with basis `β`
- `ℓ`: the number of variables in the multilinear polynomial `t` to be committed
- `𝓡`: the exponent of base `2` which represents the blowup factor of the RS code
- `S⁽⁰⁾, ..., S⁽ⁿ⁻¹⁾`: the evaluation domains used in the protocol
- `ϑ`: the folding factor, where `ϑ ∣ ℓ`
- `γ`: the repetition parameter, where `γ = ω(log λ)`

### Commit Phase
- Initially, the `𝒫` holds a multilinear polynomial in `L⦃< 2^(ℓ)⦄[X]` as the witness:
  `t(X₀, …, X_{ℓ-1}) ∈ L⦃< 2^(ℓ)⦄[X]`.
- `𝒫` computes the Reed-Solomon codeword `f: S⁽⁰⁾ → L` of
  `P(X) = ∑_{w ∈ 𝓑_ℓ} t(w) · X_{w}(X)` where `X_{w}(X)` is the novel polynomial basis indexed by
  `w ∈ 𝓑_ℓ`. `𝒫` then submits `f` to the vector oracle `ℱᴸ_Vec` which returns a handle `[f]`.

### Interactive Proof Phase

`𝒫` and `𝒱` have the common input `[f]`, `s ∈ L`, and `(r₀, …, r_{ℓ-1}) ∈ L^ℓ`.

- `𝒫` writes `h(X₀, …, X_{ℓ-1}) := t(X₀, …, X_{ℓ-1}) - eq̃(r₀, …, r_{ℓ-1}, X₀, …, X_{ℓ-1})`.
- `𝒫` and `𝒱` both abbreviate `f⁽⁰⁾ := f` and `s₀ := s`, and execute the following loop:

For `i ∈ {0, …, ℓ-1}` do
  1. `𝒫` sends `𝒱` the polynomial
    `hᵢ(X) := ∑_{w ∈ 𝓑_{ℓ-i-1}} h(r'_0, …, r'_{i-1}, X, w₀, …, w_{ℓ-i-2})`
  2. `𝒱` requires `sᵢ ?= hᵢ(0) + hᵢ(1)`
  3. `𝒱` samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`, and sends `𝒫` the challenge `r'ᵢ`
  4. `𝒫` defines `f⁽ⁱ⁺¹⁾: S⁽ⁱ⁺¹⁾ → L` as the function `fold(f⁽ⁱ⁾, r'ᵢ)`.
    4.1. If `i+1 = ℓ` then `𝒫` sends `c := f⁽ⁱ⁾(0, …, 0)` to `𝒱`
    4.2. Else if `ϑ ∣ (i+1)` then `𝒫` submits `(submit, ℓ + 𝓡 - i - 1, f⁽ⁱ⁺¹⁾)` to oracle `ℱᴸ_Vec`

- `𝒱` requires `s_ℓ ?= eq̃(r₀, …, r_{ℓ-1}, r'₀, …, r'_{ℓ-1}) · c`.

### Querying Phase

`𝒱` executes the following querying procedure:

For `γ` repetitions do
  1. `𝒱` samples `v ← 𝓑_{ℓ+𝓡}` randomly
  2. For `i ∈ {0, ϑ, …, ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
    2.1. For each `u ∈ 𝓑_v` do:
      `𝒱` make a query `f⁽ⁱ⁾(u₀, …, u_{v-1}, vᵢ₊ᵥ, …, v_{ℓ+𝓡-1})` to the oracle `ℱᴸ_Vec`
    2.2. If `i > 0` then `𝒱` requires `cᵢ ?= f⁽ⁱ⁾(vᵢ, …, v_{ℓ+𝓡-1})`
    2.3. `𝒱` defines `c_{i+ϑ} := fold(f⁽ⁱ⁾, r'ᵢ, …, r'_{i+ϑ-1})(v_{i+ϑ}, …, v_{ℓ+𝓡-1})`.
  3. `𝒱` requires `c_ℓ ?= c`
-/

open AdditiveNTT Polynomial

noncomputable section Esstentials

universe u
variable {r : ℕ} [NeZero r]
variable {L : Type u} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type u) [Field 𝔽q] [Fintype 𝔽q]
(h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))) (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
variable [Algebra 𝔽q L]

-- Let `β` be a basis of `L` over `𝔽q`, indexed by natural numbers.
variable (β : Fin r → L) (hβ_lin_indep : LinearIndependent 𝔽q β)
variable (ℓ R_rate : ℕ) (h_ℓ_add_R_rate : ℓ + R_rate < r) -- ℓ ∈ {1, ..., r-1}

-- NOTE: For F₂ the quadratic map simplifies as q(X) = c * (X^2 - X) = c * X * (X + 1)
-- The fiber of q(y) = y is {x₀, x₀+1} for some x₀.

/-!
### The Fiber of the Quotient Map `qMap`

The fiber of `qMapᵢ` over a point `y ∈ S⁽ⁱ⁺¹⁾` is the set of all `x ∈ S⁽ⁱ⁾` such that
`qMapᵢ(x) = y`. Your insight provides a highly efficient, algebraic method for constructing
this fiber without solving polynomial equations.

The construction relies on the following key properties:
1.  **Basis Representation**: Any point `x ∈ S⁽ⁱ⁾` has a unique coordinate representation `(cᵢ, ...,
    c_{ℓ+R-1})` in the basis `Bᵢ = {Ŵᵢ(βᵢ), ..., Ŵᵢ(β_{ℓ+R-1})}`.
    So, `x = cᵢ⋅Ŵᵢ(βᵢ) + cᵢ₊₁⋅Ŵᵢ(βᵢ₊₁) + ...`.
2.  **Annihilation Property**: The map `qMapᵢ` annihilates the first basis vector of `Bᵢ`, since
    `qMapᵢ(Ŵᵢ(βᵢ)) = Ŵᵢ₊₁(βᵢ) = 0`. This is because `βᵢ` is a root of `Wᵢ₊₁` and thus of `Ŵᵢ₊₁`.
3.  **Isomorphism Property**: For all other basis vectors (`j > i`), `qMapᵢ` acts as an
    isomorphism, mapping `Ŵᵢ(βⱼ)` to `Ŵᵢ₊₁(βⱼ)`.

#### How `qMapᵢ` Acts on Coordinates
Given a point `x ∈ S⁽ⁱ⁾` with coordinates `(cᵢ, cᵢ₊₁, ..., c_{ℓ+R-1})`, its image `y = qMapᵢ(x)` is:
`y = qMapᵢ(cᵢ⋅Ŵᵢ(βᵢ) + ∑_{j=i+1} cⱼ⋅Ŵᵢ(βⱼ))`
  `= cᵢ⋅qMapᵢ(Ŵᵢ(βᵢ)) + ∑_{j=i+1} cⱼ⋅qMapᵢ(Ŵᵢ(βⱼ))` (by linearity)
  `= 0 + ∑_{j=i+1} cⱼ⋅Ŵᵢ₊₁(βⱼ)`

This means the coordinates of `y` in the basis `Bᵢ₊₁` are simply `(cᵢ₊₁, ..., c_{ℓ+R-1})`.
The first coefficient `cᵢ` is completely discarded.

#### Constructing the Fiber
To find the preimages of `y`, we reverse the process:
1. Find the coordinates of `y` in the basis `Bᵢ₊₁`, let's call them `d = (dᵢ₊₁, ..., d_{ℓ+R-1})`.
2. Any preimage `x` must have coordinates `(cᵢ, cᵢ₊₁, ...)` where `cⱼ = dⱼ` for `j > i`.
3. The first coordinate `cᵢ` is unconstrained by `y`. It can be any element `k ∈ 𝔽q`.

This gives us `q` possible preimages, one for each `k ∈ 𝔽q`, forming the fiber.
-/
noncomputable def qMap_fiber (i : Fin r)
  (y : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate
    h_ℓ_add_R_rate) (⟨i.val + 1, by sorry⟩)) :
  -- The fiber is represented as a function from the free coefficient `k ∈ 𝔽q` to the preimage `xₖ`.
  𝔽q → (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate) i :=
  fun (k : 𝔽q) =>
    -- 1. Get the basis for S⁽ⁱ⁺¹⁾ to find the coordinates of y.
    let basis_y := sDomain_basis 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate
      h_ℓ_add_R_rate ⟨i.val + 1, by sorry⟩ (by sorry)
    -- 2. Represent y as a vector of coefficients in its basis.
    let y_coeffs := basis_y.repr y
        -- 3. The new coefficient vector for the preimage `xₖ` is formed by prepending `k` to y's coefficients.
    let x_coeffs := fun j : Fin (ℓ + R_rate - i.val) =>
      if j.val = 0 then k else y_coeffs ⟨j.val - 1, by sorry⟩
    -- 4. Get the basis for S⁽ⁱ⁾ to construct the preimage point `xₖ`.
    let basis_x := sDomain_basis 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate
      h_ℓ_add_R_rate i (by sorry)
    -- 5. Construct `xₖ` from its basis and coordinate vector.
    -- basis_x.constr (Finsupp.ofSupportFinite x_coeffs (by sorry))
    sorry

-- sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
/-- Definition 4.6: The single-step folding operation.
Given a function `f: S⁽ⁱ⁾ → L` and a challenge `r_chal`,
it produces a new function `f': S⁽ⁱ⁺¹⁾ → L`. -/
noncomputable def fold (i : Fin r) (f : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β
    hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate) i → L) (r_chal : L)
    (y : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate
      h_ℓ_add_R_rate) (⟨i.val + 1, by sorry⟩)) : L :=
  let fiber := (qMap_fiber 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate
    h_ℓ_add_R_rate i) (y:=y)
  let x₀ := fiber 0
  let x₁ := fiber 1
  -- We need to coerce elements from the subspace back to L for evaluation
  let f_x₀ := f ⟨x₀, sorry⟩ -- Proof that x₀ is in S⁽ⁱ⁾ required
  let f_x₁ := f ⟨x₁, sorry⟩ -- Proof that x₁ is in S⁽ⁱ⁾ required
  (1 - r_chal) * (f_x₀ * x₁ - f_x₁ * x₀) - r_chal * (f_x₀ - f_x₁)

/-- Definition 4.8: Iterated Fold -/
noncomputable def iterated_fold (ϑ_folding_factor : ℕ) (i : Fin (ℓ - ϑ_folding_factor + 1))
  (f : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate)
  (i := ⟨i, by omega⟩) → L) (r_challenges : Fin ϑ_folding_factor → L) :
  (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate)
  (⟨i+ϑ_folding_factor, by sorry⟩) → L := by
  -- Use Fin.dfoldl for dependent type folding
  let domain_type := sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ R_rate h_ℓ_add_R_rate
  let fold_func := fold 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate

  -- Define the dependent type function for the fold
  let α (j : Fin (ϑ_folding_factor + 1)) := domain_type (⟨i + j.val, by sorry⟩) → L

  -- Define the folding function
  let fold_step (j : Fin ϑ_folding_factor) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x -- x ∈ S⁽ⁱ⁺¹⁾
    simp only [Fin.val_succ] at x
    simp_rw [←Nat.add_assoc] at x
    have fold_func := fold_func (i:=⟨i + j.val, by sorry⟩) (f_acc) (r_challenges j)
    set i_add_j_castFinr := (⟨i + j, by sorry⟩: Fin r)
    have h_i_add_j: i_add_j_castFinr.val + 1 < r := by sorry
    have h_i_add_j_add_one: (i_add_j_castFinr + 1).val = i_add_j_castFinr.val + 1 :=
      Fin.val_add_one' (a:=i_add_j_castFinr) (h_a_add_1:=h_i_add_j)
    have h_fin_i_add_j_add_one: (i_add_j_castFinr + (1: Fin r))
      = Fin.mk (n:=r) ( i_add_j_castFinr.val + 1) (by omega) := by
        exact Fin.eq_mk_iff_val_eq.mpr h_i_add_j_add_one
    -- simp_rw [h_fin_i_add_j_add_one, i_add_j_castFinr] at fold_func
    exact fold_func x

  -- Apply the dependent fold
  exact Fin.dfoldl (n:=ϑ_folding_factor) (α:=α) (f:=fun i (accF: α ⟨i, by omega⟩) =>
    have fSucc: α ⟨i.succ, by omega⟩ := fold_step i accF
    fSucc
  ) (init:=f)

/- **Lemma 4.9: Matrix Form of Iterated Fold**
  For any `y ∈ S⁽ⁱ⁺ᶿ⁾`, there exists a `2ᶿ × 2ᶿ` invertible matrix `M_y`, depending only on `y`, such
  that the folding operation can be expressed as a matrix-vector product. This separates the
  challenges from the function evaluations:
  `fold(f⁽ⁱ⁾, r₀, ..., r_{ϑ-1})(y) = [⨂_{j=0}^{ϑ-1}(1-rⱼ, rⱼ)] ⋅ M_y ⋅ [f⁽ⁱ⁾(x₀), ..., f⁽ⁱ⁾(x_{2ᶿ-1})]ᵀ`
  where `(x₀, ..., x_{2ᶿ-1})` is the fiber `(q⁽ⁱ⁺ᶿ⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y})`.
-/

/-- Lemma 4.13: Describes how the coefficients of the underlying `intermediateEvaluationPoly`
transform under the `fold` operation. This is crucial for the completeness proof. -/
theorem lemma_fold_coeff_transform
  (i : Fin ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L)
  (r_chal : L) :
  let P_i := intermediateEvaluationPoly 𝔽q β ℓ R_rate (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) (i:=⟨i, by sorry⟩) coeffs
  let f_i := fun (x : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate) (i:=⟨i, by sorry⟩)) => P_i.eval (x.val: L)

  let f_i_plus_1 := (fold 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate) (i:=⟨i, by sorry⟩) f_i r_chal

  let new_coeffs := fun j : Fin (2^(ℓ - i - 1)) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by sorry⟩) + r_chal * (coeffs ⟨j.val * 2 + 1, by sorry⟩)
  let P_i_plus_1 := (intermediateEvaluationPoly 𝔽q β ℓ R_rate (h_ℓ_add_R_rate:=h_ℓ_add_R_rate) (i:=⟨i+1, by sorry⟩)) new_coeffs

  ∀ (y : (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ R_rate h_ℓ_add_R_rate) (i:=⟨i+1, by sorry⟩)),
    f_i_plus_1 y = P_i_plus_1.eval y.val := sorry

end Esstentials

section BinaryBasefoldOracleReduction
/-- The (default) oracle interface for a function `α → β`. -/
instance {α β : Type*} : OracleInterface (α → β) :=
  {
    Query := α
    Response := β
    oracle := id
  }

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT

-- Protocol parameters
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q]
variable (h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))) (h_Fq_card_gt_1 : Fintype.card 𝔽q > 1)
variable [Algebra 𝔽q L]
variable {r : ℕ} [NeZero r]
variable (β : Fin r → L) (hβ_lin_indep : LinearIndependent 𝔽q β)
variable (ℓ 𝓡 ϑ γ_repetitions : ℕ) [NeZero ϑ] [NeZero ℓ]
variable (h_ℓ_add_R_rate : ℓ + 𝓡 < r)
variable {n : ℕ} (i : Fin n)
variable (𝓑 : Fin 2 ↪ L)

section SingleIOPRound

/-- There are ℓ rounds, so there are ℓ + 1 states.
The i'th round receives the state i and outputs state i+1.
For the `i`-th round of the protocol, the input statement contains:
- The original multilinear evaluation claim (r, s)
- The current sumcheck target s_i
- The list of challenges from previous rounds (0 to i-1)
- The list of commitment handles from previous rounds
-/
structure Statement (i : Fin (ℓ + 1)) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  sumcheck_target : L              -- s_i (current sumcheck target)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1})

def toOutCodewordsCount (i : Fin (ℓ + 1)) : ℕ := by
  -- the number of codewords available as oracle at state `i` (at the beginning of round `i`)
  exact i/ϑ + (if i < ℓ then 1 else 0)

#eval toOutCodewordsCount (ℓ:=10) (ϑ:=4) (i:=⟨0, by omega⟩) -- 1
#eval toOutCodewordsCount (ℓ:=10) (ϑ:=4) (i:=⟨4, by omega⟩) -- 2

/-- For the `i`-th round of the protocol, there will be oracle statements corresponding
to all committed codewords. The verifier has oracle access to functions corresponding
to the handles in committed_handles. -/
@[reducible]
def OracleStatement (i : Fin (ℓ + 1)): Fin (toOutCodewordsCount ℓ ϑ (i:=i) + 1) → Type := fun j =>
  match j with
  | ⟨0, _⟩ => L⦃≤ 1⦄[X] -- hᵢ(X)
  | ⟨x, hx⟩ => by
    let submittedCodewordIdx := x - 1
    let sDomainIdx := submittedCodewordIdx * ϑ
    have h_sDomainIdx_lt_ℓ : sDomainIdx < ℓ := by
      unfold sDomainIdx submittedCodewordIdx
      unfold toOutCodewordsCount at hx
      -- hx : x < (↑i / ϑ + if ↑i < ℓ then 1 else 0) + 1
      -- ⊢ (x - 1) * ϑ < ℓ
      if hi: i.val < ℓ then
        simp only [hi, ↓reduceIte] at hx
        -- hx : x < ↑i / ϑ + 1 + 1
        -- We need to show (x - 1) * ϑ < ℓ
        have hx_bound : x ≤ i.val / ϑ + 1 := by omega
        have h_mult : (x - 1) * ϑ ≤ (i.val / ϑ + 1 - 1) * ϑ := by
          apply Nat.mul_le_mul_right
          omega
        have h_simp : (i.val / ϑ + 1 - 1) * ϑ = (i.val / ϑ) * ϑ := by exact rfl
        rw [h_simp] at h_mult
        have h_div_mul : (i.val / ϑ) * ϑ ≤ i.val := Nat.div_mul_le_self i.val ϑ
        have h_i_lt_ℓ : i.val < ℓ := by exact hi
        calc (x - 1) * ϑ
          ≤ (i.val / ϑ) * ϑ := h_mult
          _ ≤ i.val := h_div_mul
          _ < ℓ := h_i_lt_ℓ
      else
        simp only [hi, ↓reduceIte, add_zero] at hx
        have hi_eq : i.val = ℓ := by
          have hi_ge : ℓ ≤ i.val := by omega
          have hi_le : i.val ≤ ℓ := by
            have : i.val < ℓ + 1 := i.isLt
            omega
          omega
        rw [hi_eq] at hx
        -- Now hx : x < ℓ / ϑ + 1
        have hx_bound : x ≤ ℓ / ϑ := by omega
        have h_mult : (x - 1) * ϑ ≤ (ℓ / ϑ) * ϑ := by
          if h : x = 0 then
            simp only [h, zero_tsub, zero_mul, zero_le]
          else
            let x' := x.pred
            have hx: x = x' + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero h)
            simp only [hx, Nat.succ_sub_succ_eq_sub, tsub_zero]
            apply Nat.mul_le_mul_right
            omega
        have h_div_mul : (ℓ / ϑ) * ϑ ≤ ℓ := Nat.div_mul_le_self ℓ ϑ
        -- We need strict inequality, so we use the fact that if ℓ / ϑ * ϑ = ℓ,
        -- then ϑ divides ℓ, but we can show (x-1) * ϑ < ℓ / ϑ * ϑ
        have h_strict : (x - 1) * ϑ < ℓ := by
          cases lt_or_eq_of_le h_div_mul with
          | inl h_lt => -- Case: (ℓ / ϑ) * ϑ < ℓ
            calc (x - 1) * ϑ
              ≤ (ℓ / ϑ) * ϑ := h_mult
              _ < ℓ := h_lt
          | inr h_eq => -- Case: (ℓ / ϑ) * ϑ = ℓ
            -- We need to show (x - 1) * ϑ < (ℓ / ϑ) * ϑ
            if h : x = 0 then
              simp only [h, zero_tsub, zero_mul]
              exact Nat.pos_of_neZero ℓ
            else
              let x' := x.pred
              have hx: x = x' + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero h)
              simp only [hx, Nat.succ_sub_succ_eq_sub, tsub_zero]
              have hltDiv: x' < ℓ / ϑ := by omega
              -- exact Nat.mul_lt_mul_right (by omega) this
              simp only [gt_iff_lt]
              -- ⊢ x' * ϑ < ℓ
              rw [←Nat.mul_lt_mul_right (a:=ϑ) (a0:=by exact Nat.pos_of_neZero ϑ)
                (b:=x') (c:=ℓ/ϑ)] at hltDiv
              apply Nat.lt_of_lt_of_le (m:=ℓ/ϑ * ϑ)
              · exact hltDiv
              · exact Nat.div_mul_le_self ℓ ϑ
        exact h_strict
    exact (sDomain 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 h_ℓ_add_R_rate) ⟨sDomainIdx, by omega⟩ → L

/-- The Binary Basefold protocol has as witness the multilinear polynomial t and
the current codeword f⁽ⁱ⁾. -/
structure Witness (i : Fin (ℓ + 1)) where
  h : L⦃≤ 1⦄[X Fin (ℓ - i)] -- (ℓ - i)-variate multilinear polynomial
  f: L⦃< 2^(ℓ - i)⦄[X] -- the underlying univariate polynomial of
  -- the current codeword f⁽ⁱ⁾: S⁽ⁱ⁾ → L
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input

def inputRelation (i : Fin ℓ) :
    Set ((Statement (L:=L) ℓ i.castSucc × (∀ j, OracleStatement (L:=L) 𝔽q h_Fq_char_prime
      h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.castSucc j))
      × Witness (L:=L) ℓ i.castSucc) :=
  { ⟨⟨stmt, _⟩, wit⟩ |
    have h_sumcheck_current_round :=
      (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.val), wit.h.val.eval x) = stmt.sumcheck_target

    -- i.e. they must be constructed from the original polynomial t(X₀, ..., X_{ℓ-1})
    have h_relation_between_h_and_f := True

    h_sumcheck_current_round ∧ h_relation_between_h_and_f
  }

def outputRelation (i : Fin ℓ) :
    Set ((Statement (L:=L) ℓ (i.succ) × (∀ j, OracleStatement (L:=L) 𝔽q
      h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ j))
      × Witness (L:=L) ℓ (i.succ)) :=
  {⟨⟨stmt, ostmt⟩, wit⟩ |
    -- i.e. they must be constructed from the original polynomial t(X₀, ..., X_{ℓ-1})
    have h_i: L⦃≤ 1⦄[X] := ostmt ⟨0, by
      dsimp [toOutCodewordsCount]
      simp only [lt_add_iff_pos_left, add_pos_iff, Nat.div_pos_iff, zero_lt_one, or_true]
    ⟩
    have r'i := stmt.challenges ⟨i, by exact Nat.lt_add_one ↑i⟩
    have s_i_add_1 := stmt.sumcheck_target
    -- hᵢ(rᵢ') = sᵢ₊₁
    have h_i_eval_eq_next_target := s_i_add_1 = h_i.val.eval r'i

    -- hᵢ(0) + hᵢ(1) = sum_check of round_i (sᵢ)
    have h_next_round_sum_check := ∑ x ∈ (univ.map 𝓑), h_i.val.eval x = s_i_add_1

    let nextWitnessH:  L[X Fin (ℓ - (↑i + 1))] := by
      exact wit.h.val

    have h_sumcheck_next_round :=
      (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - (i.val + 1)), nextWitnessH.eval x) = s_i_add_1

    have h_relation_between_h_and_f := True
    h_i_eval_eq_next_target ∧ h_sumcheck_next_round ∧ h_relation_between_h_and_f
  }

/-- Each round of Binary Basefold consists of 3 messages:
1. P→V: The sumcheck polynomial h_i(X)
2. V→P: The folding/sumcheck challenge r'_i
-/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ![(.P_to_V, L⦃≤ 1⦄[X]), -- P sends hᵢ(X) to V, which is a degree-1 univariate polynomial
    (.V_to_P, L) -- V sends back r'ᵢ as the challenge
  ]

instance : ∀ j, OracleInterface ((pSpec (L:=L)).Message j)
  | ⟨0, h⟩ => by exact OracleInterface.instDefault
  | ⟨1, _⟩ => by exact OracleInterface.instDefault

noncomputable def roundPoly (i : Fin ℓ) (h : ↥L⦃≤ 1⦄[X Fin (ℓ - ↑i.castSucc)]) : L[X] := by
  have h_i_lt_ℓ: ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let h := ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1), curH_cast ⸨X ⦃0⦄, x⸩'(by rfl)
  exact h

/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
  `deg` -/
theorem sumcheck_roundPoly_degreeLE (i : Fin ℓ)
    (h : ↥L⦃≤ 1⦄[X Fin (ℓ - ↑i.castSucc)]):
    roundPoly L 𝔽q ℓ (r:=r) 𝓡 𝓑 i h ∈ L⦃≤ 1⦄[X] := by
  simp_rw [Polynomial.mem_degreeLE]
  unfold roundPoly
  simp only [Fin.coe_castSucc, Fin.cast_refl]
  have h_eq : L[X Fin (ℓ - ↑i.castSucc - 1 + 1)] = L[X Fin (ℓ - ↑i.castSucc)] := by
    congr
    apply Nat.sub_add_cancel
    -- ⊢ 1 ≤ ℓ - ↑i.castSucc
    sorry
  have h_le := Polynomial.degree_sum_le (R:=L)
    (s := Fintype.piFinset fun (i: Fin (ℓ - ↑i - 1)) ↦ Finset.map 𝓑 univ)
    (f := fun (x: Fin (ℓ - ↑i - 1) → L) ↦ Polynomial.map (MvPolynomial.eval (x ∘ id))
      ((finSuccEquivNth L 0) (h_eq.mpr ↑h)))
  apply le_trans (h_le)
  simp only [Finset.sup_le_iff, Fintype.mem_piFinset, mem_map, mem_univ, true_and]
  intro x hx
  refine le_trans (degree_map_le) (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  -- ⊢ degreeOf 0 (h_eq.mpr ↑h) ≤ One.one
  have h_deg_h: degreeOf (R:=L) (σ:=Fin (ℓ - ↑i.castSucc)) (n:=⟨0, by sorry⟩) h ≤ 1 := by
    refine degreeOf_le_iff.mpr ?_
    intro m a
    simp only [Fin.coe_castSucc]
    -- m : Fin (ℓ - ↑i.castSucc) →₀ ℕ
    -- a : m ∈ (↑h).support
    -- ⊢ m ⟨0, ⋯⟩ ≤ 1
    sorry

  have h_deg_h_cast: degreeOf (R:=L) (σ:=Fin (ℓ - ↑i.castSucc - 1 + 1)) (n:=⟨0, by sorry⟩)
    (h_eq.mpr ↑h) ≤ 1 := by sorry

  dsimp only [Fin.coe_castSucc, eq_mpr_eq_cast]
  exact h_deg_h_cast

/-- The prover for the `i`-th round of Binary Basefold. -/
noncomputable def prover (i : Fin ℓ) :
  OracleProver (oSpec:=[]ₒ)
    -- current round
    (StmtIn := Statement (L:=L) ℓ i.castSucc)
    (OStmtIn := OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ
      𝓡 ϑ h_ℓ_add_R_rate i.castSucc)
    (WitIn := Witness (L:=L) ℓ i.castSucc)
    -- next round
    (StmtOut := Statement (L:=L) ℓ i.succ)
    (OStmtOut := OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ)
    (WitOut := Witness (L:=L) ℓ i.succ)
    (pSpec := pSpec (L:=L)) where

  PrvState := fun -- Fin (n+1)
      -- Initial: current  witness x t_eval_point x challenges
    | 0 => Witness (L:=L) ℓ i.castSucc × (Fin ℓ → L) × (Fin i → L)
    -- After sending h_i(X)
    | 1 => Witness (L:=L) ℓ i.castSucc × (Fin ℓ → L) × (Fin i → L) × L⦃≤ 1⦄[X]
    -- After receiving r'_i
    | 2 => Witness (L:=L) ℓ i.castSucc × (Fin ℓ → L) × (Fin i → L) × L⦃≤ 1⦄[X] × L

  -- initialization of prover's state
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (wit, stmt.t_eval_point, stmt.challenges)

  sendMessage
  | ⟨0, h⟩ => fun ⟨wit, t_eval_point, challenges⟩ => do
    let curH: ↥L⦃≤ 1⦄[X Fin (ℓ - ↑i.castSucc)] := wit.h
    let h_i: L⦃≤ 1⦄[X] := by exact ⟨roundPoly L 𝔽q ℓ (r:=r) 𝓡 𝓑 i (h:=curH), by
        exact sumcheck_roundPoly_degreeLE L 𝔽q ℓ (r:=r) 𝓡 𝓑 i curH⟩
    pure ⟨h_i, (wit, t_eval_point, challenges, h_i)⟩
  | ⟨1, _⟩ => by
    contradiction

  -- receiveChallenge (i : pSpec.ChallengeIdx) : self.PrvState (↑i).castSucc
    -- → pSpec.Challenge i → self.PrvState (↑i).succ
  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- i.e. contradiction
  | ⟨1, _⟩ => fun ⟨wit, t_eval_point, challenges, h_i⟩ r_i' =>
    (wit, t_eval_point, challenges, h_i, r_i')

  -- output : PrvState → StmtOut × WitOut
  output := fun finalProverState => by
    simp only [Fin.reduceLast] at finalProverState
    obtain ⟨wit, t_eval_point, challenges, h_i, r_i'⟩ := finalProverState
    let t_eval_point := wit.t_eval_point
    let stmtOut : Statement (L:=L) ℓ i.succ := {
      t_eval_point := t_eval_point,
      sumcheck_target := h_i.val.eval r_i',
      challenges := Fin.snoc challenges r_i'
    }
    let oStmtOut : ∀ j, OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
      β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ j := fun j => sorry
    -- NOTE: how to access the current statement?
    let witOut : Witness (L:=L) ℓ i.succ := {
      h : L⦃≤ 1⦄[X Fin (ℓ - i.succ)]  := by sorry
      t_eval_point := t_eval_point,
      f := by
        let prevF := wit.f
        let newF: ↥L[X]_(2 ^ (ℓ - ↑i.succ)) := by
          -- fold prevF using r_i'
          sorry
        exact newF
    }
    exact ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

/-- The "lazy" verifier for a single round `i` of the Commit Phase. -/
def verifier (i : Fin ℓ) :
  Verifier (oSpec:=[]ₒ)
    (StmtIn := (Statement (L:=L) ℓ i.castSucc) × (∀ j,
      OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
        β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.castSucc j))
    (StmtOut := (Statement (L:=L) ℓ i.succ) × (∀ j,
      OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
        β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ j))
    (pSpec := pSpec (L:=L)) where
  verify := fun ⟨stmt, oStmt⟩ transcript => do
    -- TODO: Fix this
    letI h_i := transcript 0 -- : L⦃≤ 1⦄[X]
    letI ri' := transcript 1 -- : L
    guard (∑ x ∈ (univ.map 𝓑), h_i.val.eval x = stmt.sumcheck_target)
    letI h_i := transcript 0 -- : L⦃≤ 1⦄[X]
    letI ri' := transcript 1 -- : L
    letI stmtOut : Statement (L:=L) ℓ i.succ := {
      t_eval_point := stmt.t_eval_point,
      sumcheck_target := h_i.val.eval ri',
      challenges := Fin.snoc stmt.challenges ri'
    }
    letI oStmtOut : ∀ j, OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
      β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ j := fun j => sorry
    -- pure ⟨stmtOut, oStmtOut⟩
    sorry

/-- The reduction for a single round of the commit phase. -/
noncomputable def reduction (i : Fin ℓ) :
  Reduction (oSpec:=[]ₒ)
    (StmtIn := (Statement (L:=L) ℓ i.castSucc) × (∀ j,
      OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
        β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.castSucc j))
    (WitIn := Witness (L:=L) ℓ i.castSucc)
    (StmtOut := (Statement (L:=L) ℓ i.succ) × (∀ j,
      OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
        β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ j))
    (WitOut := Witness (L:=L) ℓ i.succ)
    (pSpec := pSpec (L:=L)) where
  prover := prover (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 i
  verifier := verifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β
    hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 i

instance {i : Fin (ℓ + 1)} {j : Fin (toOutCodewordsCount ℓ
  ϑ i + 1)} : OracleInterface (OracleStatement L 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i j) := by sorry
instance {i : Fin (ℓ + 1)} {j : Fin (toOutCodewordsCount ℓ
  ϑ i + 1)} : OracleInterface (OracleStatement L 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i j) := by sorry

/-- The oracle verifier for the `i`-th round of Binary Basefold. -/
noncomputable def oracleVerifier (i : Fin ℓ) :
  OracleVerifier
    (oSpec:=[]ₒ)
    (StmtIn := Statement (L:=L) ℓ i.castSucc)
    (OStmtIn := OracleStatement L 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.castSucc)
    -- next round
    (StmtOut := Statement (L:=L) ℓ i.succ)
    (OStmtOut := OracleStatement L 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ)
    (pSpec := pSpec (L:=L)) where

  -- The core verification logic. Takes the input statement `stmtIn` and the transcript, and
  -- performs an oracle computation that outputs a new statement

  verify := fun stmt transcript => do sorry
  embed := sorry
  hEq := sorry

/-- The oracle reduction that is the `i`-th round of Binary Basefold. -/
noncomputable def oracleReduction (i : Fin ℓ) :
  OracleReduction (oSpec:=[]ₒ)
    (StmtIn := Statement (L:=L) ℓ i.castSucc)
    (OStmtIn := OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.castSucc)
    (WitIn := Witness (L:=L) ℓ i.castSucc)
    (StmtOut := Statement (L:=L) ℓ i.succ)
    (OStmtOut := OracleStatement (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1
    β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i.succ)
    (WitOut := Witness (L:=L) ℓ i.succ)
    (pSpec := pSpec (L:=L)) where
  prover := prover (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 i
  verifier := oracleVerifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β
    hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

variable [SelectableType L]

instance : ∀ i, SelectableType (OracleInterface.Response (Challenge (pSpec (L:=L)) i))
  | ⟨1, _⟩ => by
    dsimp [pSpec, OracleInterface.Response];
    -- infer_instance
    -- ⊢ SelectableType L
    sorry

instance : ∀ i, SelectableType ((pSpec (L:=L)).Challenge i)
  | ⟨1, _⟩ => by
    dsimp [pSpec, Challenge];
    -- infer_instance
    -- ⊢ SelectableType L
    sorry

theorem oracleVerifier_eq_verifier (i : Fin ℓ):
    (oracleVerifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate (i:=i)).toVerifier
      = verifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
        ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 i := by
  ext
  simp [OracleVerifier.toVerifier, verifier, OracleInterface.simOracle2]
  sorry

/-- The oracle reduction is equivalent to the non-oracle reduction -/
theorem oracleReduction_eq_reduction (i : Fin ℓ):
    (oracleReduction (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i)).toReduction
      = reduction (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
        ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 i := by
  ext : 1 <;>
  simp [OracleReduction.toReduction, oracleReduction, reduction]
  exact
    oracleVerifier_eq_verifier L 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ
      h_ℓ_add_R_rate 𝓑 i

/-- Perfect completeness for the (non-oracle) reduction -/
theorem reduction_perfectCompleteness (hInit : init.neverFails) (i : Fin ℓ):
  let myReduction := reduction (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
    ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i)
  Reduction.perfectCompleteness
    (pSpec := pSpec (L:=L))
    (relIn := inputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i))
    (relOut := outputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i))
    (reduction:=myReduction)
    (init:=init)
    (impl:=impl) := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  intro ⟨target, oStmt⟩ (wit : Witness (L:=L) ℓ i.castSucc) hValid
  sorry

/-- Perfect completeness for the oracle reduction -/
theorem oracleReduction_perfectCompleteness (hInit : init.neverFails) (i : Fin ℓ):
    let myOracleReduction := oracleReduction (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β
      hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i)
    OracleReduction.perfectCompleteness
      (pSpec := pSpec (L:=L))
      (relIn := inputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ
        h_ℓ_add_R_rate 𝓑 (i:=i))
      (relOut := outputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡
        ϑ h_ℓ_add_R_rate 𝓑 (i:=i))
      (oracleReduction:=myOracleReduction)
      (init:=init)
      (impl:=impl) := by
  unfold OracleReduction.perfectCompleteness
  simp_rw [oracleReduction_eq_reduction]
  exact
    reduction_perfectCompleteness (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ
      𝓡 ϑ h_ℓ_add_R_rate 𝓑 hInit i

open scoped NNReal

/-- Round-by-round knowledge soundness for the verifier -/
theorem verifier_rbrKnowledgeSoundness [Fintype L] (i : Fin ℓ) :
    (verifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ h_ℓ_add_R_rate
      𝓑 i).rbrKnowledgeSoundness init impl
    (inputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ
      h_ℓ_add_R_rate 𝓑 (i:=i))
    (outputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ
    h_ℓ_add_R_rate 𝓑 (i:=i))
    (rbrKnowledgeError:=fun _ => (deg : ℝ≥0) / (Fintype.card L)) := by
  sorry

/-- Round-by-round knowledge soundness for the oracle verifier -/
theorem oracleVerifier_rbrKnowledgeSoundness [Fintype L] (i : Fin ℓ) :
    (oracleVerifier (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep ℓ 𝓡 ϑ
      h_ℓ_add_R_rate (i:=i)).rbrKnowledgeSoundness init impl
    (inputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i))
    (outputRelation (L:=L) 𝔽q h_Fq_char_prime h_Fq_card_gt_1 β hβ_lin_indep
      ℓ 𝓡 ϑ h_ℓ_add_R_rate 𝓑 (i:=i))
    (rbrKnowledgeError:=fun _ => (deg : ℝ≥0) / (Fintype.card L)) := by
  sorry

end SingleIOPRound

section FinalQueryRound

-- TODO: specify the final query round
  -- 1. `𝒫` sends `c := f⁽ⁱ⁾(0, …, 0)` to `𝒱`
  -- 2. `𝒱` executes the query phase

end FinalQueryRound

section MainBinaryBasefold

-- TODO: compose the sumcheck rounds with the final query round into the whole protocol

end MainBinaryBasefold

end BinaryBasefoldOracleReduction

end BinaryBasefold

end Binius
