/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import ArkLib.Data.Probability.Notation
import CompPoly.Data.Fin.BigOperators
import CompPoly.Data.Nat.Bitwise
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

open ProbabilityTheory Filter
open NNReal Finset Function
open scoped BigOperators ProbabilityTheory
open Real

section
variable {α : Type*}

instance [IsEmpty α] : IsEmpty (PMF α) := by
  refine Subtype.isEmpty_of_false ?_
  intro f h
  have : Fintype α := Fintype.ofIsEmpty
  obtain h' := hasSum_fintype f ; simp at h'
  have one_eq_zero := HasSum.unique h h'
  simp_all only [one_ne_zero]

-- @[simp]
-- theorem PMF.eq_pure_iff_ge_one {α : Type*} {p : PMF α} {a : α} : p = pure a ↔ p a ≥ 1 := by
--   constructor <;> intro h
--   · sorry
--   · ext b
--     simp only [pure, PMF.pure_apply]
--     by_cases hb : b = a
--     · simp [hb]; exact le_antisymm (PMF.coe_le_one p a) h
--     · simp [hb]; sorry
end

section ProbabilityTools
/-- Unrolls `Pr_{ let x ← D }[P x]` into a sum of the form
`∑' x, Pr[x] * (if P x then 1 else 0)`. -/
theorem prob_tsum_form_singleton {α : Type} (D : PMF α) (P : α → Prop) [DecidablePred P] :
    Pr_{ let x ← D }[P x] = ∑' x, (D x) * (if P x then 1 else 0) := by
  -- Expand Pr_ using the same approach as Notation.lean
  simp only [Bind.bind, PMF.bind, pure, PMF.pure_apply, eq_iff_iff, mul_ite, mul_one, mul_zero]
  simp only [DFunLike.coe]
  have h: ∀ a: α, (True = P a) = (P a) := fun a => by
    if h_P_a: P a then
      simp only [h_P_a]
    else
      simp only [h_P_a, eq_iff_iff, iff_false, not_true_eq_false]
  simp_rw [h]

theorem prob_tsum_form_split_first {α : Type} (D : PMF α) (D_rest : α → PMF Prop) :
    (do let x ← D; D_rest x) True = ∑' x, (D x) * (D_rest x True) := by
  -- These are definitionally the same!
  exact PMF.bind_apply D D_rest True

open Classical in
/-- Unrolls `Pr_{ let x ← D; let y ← D }[P x y]` into a sum of the form
`∑' (x × y), (if P x y then 1 else 0)`. -/
theorem prob_tsum_form_doubleton {α β : Type}
    (D₁ : PMF α) (D₂ : PMF β)
    (P : α → β → Prop) [∀ x, DecidablePred (P x)] : -- Need decidability for inner P
    Pr_{ let x ← D₁; let y ← D₂ }[P x y]
    =  ∑' xy : α × β, (D₁ xy.1) * (D₂ xy.2) * (if P xy.1 xy.2 then (1 : ENNReal) else 0) := by
  let D_rest := fun (x : α) => (do
    let y ← D₂
    return (P x y)
  )
  conv_lhs =>
    apply prob_tsum_form_split_first (D := D₁) (D_rest := D_rest)
  simp_rw [D_rest]
  simp_rw [prob_tsum_form_singleton]
  conv_lhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ) (i : δ), ...
  rw [←ENNReal.tsum_prod]
  congr 1
  funext xy
  rw [←mul_assoc]

theorem prob_uniform_eq_card_filter_div_card {F : Type} [Fintype F] [Nonempty F]
    (P : F → Prop) [DecidablePred P] :
  Pr_{ let r ←$ᵖ F }[ P r ] =
    ((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  -- Expand Pr_ using the same approach as Notation.lean
  simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply, eq_iff_iff,
    mul_ite, mul_one, mul_zero, ENNReal.coe_natCast]
  simp only [DFunLike.coe, true_iff]
  -- ⊢ (∑' (a : F), if P a then (↑(Fintype.card F))⁻¹ else 0)
    -- = ↑(#(filter P univ)) / ↑(Fintype.card F)
  rw [tsum_eq_sum (α := ENNReal) (β := F) (f := fun a => if P a then (↑(Fintype.card F))⁻¹ else 0)
    (s := Finset.filter P Finset.univ) (hf := fun b => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hb
    simp only [hb, if_false]
  )] -- rewrite the infinite sum as a sum
  -- ⊢ (∑ b with P b, if P b then (↑(Fintype.card F))⁻¹ else 0) = ↑(#(filter P univ)) / ↑q
  rw [Finset.sum_ite] -- simplify the if-then-else inside the sum
  simp only [Finset.sum_const_zero, add_zero] -- remove the second sum of 0s
  rw [Finset.sum_const] -- simplify the left sum of the constants
  -- Rewrite nsmul (scalar multiplication by ℕ) as standard multiplication using Nat.cast
  rw [nsmul_eq_mul'] -- Use nsmul_eq_mul' which handles the coercion to ℝ≥0
  -- ⊢ (↑(Fintype.card F))⁻¹ * ↑(#({x ∈ filter P univ | P x})) = ↑(#(filter P univ)) / ↑q
  rw [mul_comm]
  conv_lhs => rw [←div_eq_mul_inv]
  -- ⊢ ↑(#({x ∈ filter P univ | P x})) / ↑(Fintype.card F) = ↑(#(filter P univ)) / ↑(Fintype.card F)
  have h_card_eq: {x ∈ filter P univ | P x} = filter P univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- ⊢ P x ∧ P x ↔ P x
    rw [and_self_iff]
  rw [h_card_eq]

lemma Fintype.card_fun_fin_one_eq {F : Type} [Fintype F] [Nonempty F] :
  Fintype.card (Fin 1 → F) = Fintype.card F := by
  rw [Fintype.card_fun]
  simp only [Fintype.card_unique, pow_one]

theorem prob_uniform_singleton_finFun_eq {F : Type} [Fintype F] [Nonempty F]
    (P : F → Prop) [DecidablePred P] :
  Pr_{ let r ← $ᵖ (Fin 1 → F) }[
    P (r 0) ] = Pr_{ let r ←$ᵖ F }[ P r ] := by
-- 1. Unfold both sides using the definition of probability for uniform distributions
  rw [prob_uniform_eq_card_filter_div_card (F := F)]
  rw [prob_uniform_eq_card_filter_div_card (F := Fin 1 → F)]
  -- 2. Handle the denominators: Show card(F) = card(Fin 1 → F)
  -- Fintype.card_fun_fin_one proves that `Fintype.card (Fin 1 → F) = Fintype.card F`
  rw [Fintype.card_fun_fin_one_eq]
  -- 3. Handle the numerators: Show the cardinalities of the two filter sets are equal.
  congr 1 -- This tells Lean the denominators match, so just prove the numerators are equal
  -- Define the equivalence `e` that maps `(r : Fin 1 → F)` to `r 0`
  let e : (Fin 1 → F) ≃ F := Equiv.funUnique (Fin 1) F
  -- Define the two sets we are comparing
  let s₁ := Finset.filter (fun (r : Fin 1 → F) => P (r 0)) Finset.univ
  let s₂ := Finset.filter P Finset.univ
  -- Show that s₂ is just the image of s₁ under the map `e`
  have h_map_eq : s₂ = Finset.map e.toEmbedding s₁ := by
    ext x -- ⊢ x ∈ s₂ ↔ x ∈ Finset.map e.toEmbedding s₁
    simp only [mem_filter, mem_univ, true_and, Fin.isValue, mem_map_equiv, s₂, s₁]
    -- ⊢ P x ↔ P (e.symm x 0)
    rfl
  simp only [ENNReal.coe_natCast, Fin.isValue, Nat.cast_inj]
  have h_card_eq : s₂.card = s₁.card := by
    rw [h_map_eq]
    rw [Finset.card_map e.toEmbedding]
  rw [h_card_eq]

theorem prob_split_uniform_sampling_of_prod {γ δ : Type}
    -- Fintype & Nonempty assumptions for all types
    [Fintype γ] [Fintype δ] [Nonempty γ] [Nonempty δ]
    -- The predicate on the original (combined) type
    (P : γ × δ → Prop)
    -- Decidability for the predicates
    [DecidablePred P]
    [DecidablePred (fun xy : γ × δ => P xy)] :
    -- LHS: Probability over the combined space
    Pr_{ let r ← $ᵖ (γ × δ) }[ P r ] =
    -- RHS: Probability over the sequential, split spaces
    Pr_{ let x ← $ᵖ γ; let y ← $ᵖ δ }[ P (x, y) ] := by
  rw [prob_tsum_form_singleton]
  let D_rest := fun (x : γ) => (do
    let y ← $ᵖ δ
    return (P (x, y))
  )
  conv_rhs =>
    apply prob_tsum_form_split_first (D := $ᵖ γ) (D_rest := D_rest)
  simp_rw [D_rest]
  simp_rw [prob_tsum_form_singleton]
  conv_rhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  rw [←ENNReal.tsum_prod]
  congr
  funext xy
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, mul_ite, mul_one,
    mul_zero, Prod.mk.eta]
  by_cases hP : P xy
  · simp only [hP, ↓reduceIte]
    rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
  · simp only [hP, ↓reduceIte]

/--
Proves that a `do` block sampling two independent uniform distributions
is equal to the single uniform distribution over the product type.
-/
theorem do_two_uniform_sampling_eq_uniform_prod {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (do
      let x ← $ᵖ α;
      let y ← $ᵖ β
      pure (x, y)
    ) = $ᵖ (α × β) := by
  apply PMF.ext
  intro xy
  rcases xy with ⟨x, y⟩
  have h_rhs : ($ᵖ (α × β)) (x, y) = (Fintype.card (α × β) : ENNReal)⁻¹ := by
    rw [PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  dsimp only [Bind.bind, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.tsum_mul_left]
  rw [←ENNReal.tsum_prod]
  rw [ENNReal.tsum_mul_left]
  rw [←mul_assoc]
  rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
  conv_rhs =>
    rw [←mul_one (a := ((Fintype.card α : ENNReal) *  (Fintype.card β : ENNReal) : ENNReal)⁻¹)]
  congr 1
  simp only [Prod.mk.eta]
  dsimp only [pure, PMF.pure_apply]
  -- ⊢ ∑' (i : F × (Fin ϑ → F)), (pure i) (x, y) = 1
  rw [tsum_eq_single ((x, y) : α × β)]
  · -- ⊢ (if (x, y) = (x, y) then 1 else 0) = 1
    simp only [ite_true]
  · -- Goal 2: Prove all other terms are 0
    intro i h_ne
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    exact id (Ne.symm h_ne)

/--
**Generic Probability Splitting Lemma (via Equivalence)**

This lemma proves that a single probability statement over a uniform
distribution on a type `α` can be rewritten as a sequential probability
statement over two smaller, independent distributions `γ` and `δ`,
given an equivalence `e : α ≃ γ × δ`.

This is a formal "change of variables" for probabilities, and it's
the generic version of `prob_split_randomness_apply`.
It allows us to "split" one `let` into two.
-/
theorem prob_split_uniform_sampling_of_equiv_prod {α γ δ : Type}
    -- Fintype & Nonempty assumptions for all types
    [Fintype α] [Fintype γ] [Fintype δ]
    [Nonempty α] [Nonempty γ] [Nonempty δ]
    -- The equivalence that splits α into γ × δ
    (e : α ≃ γ × δ)
    -- The predicate on the original (combined) type
    (P : α → Prop)
    -- Decidability for the predicates
    [DecidablePred P]
    [DecidablePred (fun xy : γ × δ => P (e.symm xy))] :

    -- LHS: Probability over the combined space
    Pr_{ let r ← $ᵖ α }[ P r ] =

    -- RHS: Probability over the sequential, split spaces
    Pr_{ let x ← $ᵖ γ; let y ← $ᵖ δ }[ P (e.symm (x, y)) ] := by

  -- 1. Unroll the LHS (a single `let`) using `prStx_unfold_final`
  -- LHS = ∑' r, Pr[r] * (if P r then 1 else 0)
  rw [prob_tsum_form_singleton]
  let D_rest := fun (x : γ) => (do
    let y ← $ᵖ δ
    return (P (e.symm (x, y)))
  )
  conv_rhs =>
    apply prob_tsum_form_split_first (D := $ᵖ γ) (D_rest := D_rest)
  simp_rw [D_rest]

  simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero]
  simp_rw [prob_tsum_form_singleton]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ), (↑(Fintype.card γ))⁻¹ * ∑' (x_1 : δ), ...
  conv_rhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ) (i : δ), ...
  rw [←ENNReal.tsum_prod]
  -- ⊢ (∑' (x : α), ...) = (∑' (p : γ × δ), ...)
  conv_lhs =>
    rw [tsum_eq_sum (α := ENNReal) (β := α) (f :=
      fun x => if P x then (↑(Fintype.card α))⁻¹ else 0) (s := Finset.univ) (hf := fun b => by
      simp only [mem_univ, not_true_eq_false, ite_eq_right_iff, ENNReal.inv_eq_zero,
        IsEmpty.forall_iff]
    )]
  conv_rhs =>
    rw [tsum_eq_sum (α := ENNReal) (β := γ × δ) (f := fun x =>
      (↑(Fintype.card γ))⁻¹ * (($ᵖ δ) x.2 * if P (e.symm x) then 1 else 0)
    ) (s := Finset.univ) (hf := fun b => by
      simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    )]
  -- ⊢ (∑ b : α, .. = ..) = (∑ b : γ × δ, ..)
  have hcard_of_equiv: (Fintype.card α) = (Fintype.card (γ × δ)) := Fintype.card_congr e

  rw [Finset.sum_equiv (s := Finset.univ (α := α)) (t := Finset.univ (α := γ × δ))
    (f := fun x => if P x then (↑(Fintype.card α))⁻¹ else 0)
    (g := fun x => (↑(Fintype.card γ))⁻¹ * (($ᵖ δ) x.2 * if P (e.symm x) then 1 else 0))
    (e := e) (hst := fun i => by
    simp only [mem_univ]
  ) (hfg := fun i => by
    simp only [mem_univ, PMF.uniformOfFintype_apply, Equiv.symm_apply_apply, mul_ite, mul_one,
      mul_zero, forall_const]
    by_cases hP : P i
    · simp only [hP, ↓reduceIte]
      rw [hcard_of_equiv]
      rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
      rw [Fintype.card_prod]; rw [Nat.cast_mul]
    · simp only [hP, ↓reduceIte]
  )]
/-- Rewrites the probability over the large `r` space as a sequential
probability, sampling `r_last` *first*, then `r_init`.
-/
theorem prob_split_last_uniform_sampling_of_finFun {ϑ : ℕ} {F : Type} [Fintype F] [Nonempty F]
    (P : F → (Fin ϑ → F) → Prop)
    [DecidablePred (fun r : Fin (ϑ + 1) → F => P (r (Fin.last ϑ)) (fun i => r i.castSucc))]
    [∀ r_last, DecidablePred (fun r_init => P r_last r_init)] :
    Pr_{ let r ← $ᵖ (Fin (ϑ + 1) → F) }[ P (r (Fin.last ϑ)) (fun i ↦ r i.castSucc) ] =
    Pr_{ let r_last ← $ᵖ F; let r_init ← $ᵖ (Fin ϑ → F) }[ P r_last r_init ] := by
  rw [prob_tsum_form_doubleton]

  let e : (Fin (ϑ + 1) → F) ≃ F × (Fin ϑ → F) := equivFinFunSplitLast
  conv_lhs =>
    rw [prob_split_uniform_sampling_of_equiv_prod (e := e)]
  rw [prob_tsum_form_doubleton]
  congr 1
  funext xy
  congr 1
  have hEquiv_r_last : e.symm (xy.1, xy.2) (Fin.last ϑ) = xy.1 := by
    simp only [equivFinFunSplitLast, Prod.mk.eta, Equiv.coe_fn_symm_mk, Fin.snoc_last, e]
  have hEquiv_r_init : ∀ i: Fin ϑ, e.symm (xy.1, xy.2) i.castSucc = xy.2 i := by
    simp only [equivFinFunSplitLast, Prod.mk.eta, Equiv.coe_fn_symm_mk, Fin.snoc_castSucc,
      implies_true, e]
  simp_rw [hEquiv_r_last, hEquiv_r_init]

/--
Helper lemma for probability marginalization.
`Pr_{ (x, y) ← D₁ × D₂ }[ P x ] = Pr_{ x ← D₁ }[ P x ]`
-/
theorem prob_marginalization_first_of_prod {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (P : α → Prop) [DecidablePred P] :
  Pr_{let r ← $ᵖ (α × β) }[ P r.1 ] = Pr_{ let x ← $ᵖ α }[ P x ] := by
  rw [prob_split_uniform_sampling_of_prod]

  let D_rest := fun (x : α) => (do
    let y ← $ᵖ β
    pure (P (x, y).1)
  )
  conv_lhs =>
    apply prob_tsum_form_split_first (D := $ᵖ α) (D_rest := D_rest)
  simp_rw [prob_tsum_form_singleton]
  congr 1
  funext x
  congr 1
  unfold D_rest
  -- ⊢ (D_rest x) True = if P x then 1 else 0
  simp only [Bind.bind, pure, PMF.bind_const, PMF.pure_apply, eq_iff_iff, true_iff]
/--
**Monotonicity of Probability**

If event `A` (defined by predicate `f`) implies event `B` (defined by
predicate `g`) for all outcomes `r`, then the probability of `A`
is less than or equal to the probability of `B`.
-/
theorem Pr_le_Pr_of_implies {α : Type} (D : PMF α)
    (f g : α → Prop) [DecidablePred f] [DecidablePred g]
    (h_imp : ∀ r, f r → g r) :
    Pr_{ let r ← D }[ f r ] ≤ Pr_{ let r ← D }[ g r ] := by
  -- 1. Unroll both probability statements into their sum forms
  rw [prob_tsum_form_singleton D f]
  rw [prob_tsum_form_singleton D g]
  -- Goal: ⊢ (∑' r, D r * if f r then 1 else 0) ≤ (∑' r, D r * if g r then 1 else 0)
  -- 2. Apply tsum_le_tsum: We need to show term-wise inequality
  apply ENNReal.tsum_le_tsum
  -- 3. Show the term-wise inequality for each r
  intro r
  -- Goal: ⊢ D r * (if f r then 1 else 0) ≤ D r * (if g r then 1 else 0)
  -- Use `mul_le_mul_left'` which requires proving D r ≠ 0 and D r ≠ ∞
  -- Or simpler: use `mul_le_mul_of_nonneg_left` which only requires D r ≥ 0
  apply mul_le_mul_of_nonneg_left
  -- 4. Prove the inequality between the `ite` terms using the implication
  · by_cases hf : f r
    · simp only [hf, ↓reduceIte, h_imp, le_refl]
    · simp only [hf, ↓reduceIte, zero_le]
  -- 5. Prove the factor `D r` is non-negative
  · exact zero_le (D r) -- Probabilities are always non-negative

theorem Pr_multi_let_equiv_single_let {α β : Type}
    (D₁ : PMF α) (D₂ : PMF β) -- Assuming D₂ is independent for simplicity
    (P : α → β → Prop) [∀ x, DecidablePred (P x)] :
    -- LHS: Multi-let probability
    Pr_{ let x ← D₁; let y ← D₂ }[ P x y ]
    =
    -- RHS: Single-let probability over the combined distribution
    let D_combined : PMF (α × β) := do { let x ← D₁; let y ← D₂; pure (x, y) }
    Pr_{ let r ← D_combined }[ P r.1 r.2 ] := by
  dsimp only [Lean.Elab.WF.paramLet] -- Expose LHS do block
  simp only [bind_pure_comp, _root_.map_bind, Functor.map_map]

/--
**Law of Total Probability (Partitioning an Event)**
The probability of an event `f r` occurring can be calculated by
summing the probabilities of two disjoint cases:
1. `f r` occurs AND `g r` occurs.
2. `f r` occurs AND `g r` does NOT occur.
Good to be used with `Pr_multi_let_equiv_single_let`
-/
theorem Pr_add_split_by_complement {α : Type} (D : PMF α)
    (f g : α → Prop) [DecidablePred f] [DecidablePred g]
    -- Need decidability for the combined predicates too
    [DecidablePred (fun r => g r ∧ f r)]
    [DecidablePred (fun r => ¬(g r) ∧ f r)] :
    Pr_{ let r ← D }[ f r ] =
    (D >>= (fun r => pure (g r ∧ f r))) True + Pr_{ let r ← D }[ ¬(g r) ∧ f r ] := by
  -- 1. Unroll all three probability statements into their tsum forms
  rw [prob_tsum_form_singleton D f]
  rw [prob_tsum_form_singleton D (fun r => g r ∧ f r)]
  rw [prob_tsum_form_singleton D (fun r => ¬(g r) ∧ f r)]
  -- 2. Combine the two sums on the RHS using ENNReal.tsum_add
  -- Need to prove summability for both, which is true in ENNReal
  rw [← ENNReal.tsum_add]
  congr 1
  funext r
  rw [←mul_add]
  congr 1
  by_cases hg : g r
  · simp only [hg, true_and, not_true_eq_false, false_and, ↓reduceIte, add_zero]
  · simp only [hg, false_and, ↓reduceIte, not_false_eq_true, true_and, zero_add]

example : -- Pr_split_two_complements
  let f := fun (x, _) => x = true
  let g := fun (_, y) => y = true
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ f (x, y) ] =
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ g (x, y) ∧ f (x, y) ] +
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ ¬(g (x, y)) ∧ f (x, y) ] := by
    let D : PMF (Bool × Bool) := do
      let x ← $ᵖ Bool
      let y ← $ᵖ Bool
      pure (x, y)
    set f := fun ((x, y) : (Bool × Bool)) => x = true
    set g := fun ((x, y) : (Bool × Bool)) => y = true
    simp only
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_add_split_by_complement (D := D) (f := f) (g := g)]

/--
`Pr_{r ← D}[ P_out ∧ P(r) ] = (if P_out then Pr_{r ← D}[ P(r) ] else 0)`
-/
theorem prob_const_and_prop_eq_ite {α : Type} (D : PMF α)
    (P_out : Prop) [Decidable P_out]
    (P : α → Prop) [DecidablePred P] :
    Pr_{ let r ← D }[ P_out ∧ P r ] = if P_out then Pr_{ let r ← D }[ P r ] else 0 := by
  by_cases h_P_out : P_out
  · -- Case 1: P_out is True
    simp only [h_P_out, if_true, true_and]
  · -- Case 2: P_out is False
    simp only [h_P_out, if_false, false_and]
    rw [prob_tsum_form_singleton]
    simp only [if_false, mul_zero, tsum_zero]

/-- Congruence lemma for Probability: If P(x) ↔ Q(x) for all x, then Pr[P] = Pr[Q]. -/
lemma Pr_congr {α : Type} {D : PMF α} {P Q : α → Prop}
    (h : ∀ x, P x ↔ Q x) : Pr_{ let x ← D }[ P x ] = Pr_{ let x ← D }[ Q x ] := by
  congr 2; funext x;
  congr 1; exact propext (h x)

/-- **Schwartz-Zippel Lemma** (Probability Form):
For a non-zero multivariate polynomial `P` of total degree at most `d` over a finite field `L`,
the probability that `P(r)` evaluates to 0 for a uniformly random `r` is at most `d / |L|`. -/
lemma prob_schwartz_zippel_mv_polynomial {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] {n : ℕ}
    (P : MvPolynomial (Fin n) R) (h_nonzero : P ≠ 0) (h_deg : P.totalDegree ≤ n) :
    Pr_{ let r ←$ᵖ (Fin n → R) }[ MvPolynomial.eval r P = 0 ] ≤
      (n : ℝ≥0) / (Fintype.card R : ℝ≥0) := by
  rw [prob_uniform_eq_card_filter_div_card]
  push_cast
  have sz_bound := MvPolynomial.schwartz_zippel_totalDegree (R := R) (n := n)
    (p := P) (hp := h_nonzero) (S := Finset.univ)
  simp only [Fintype.piFinset_univ, card_univ] at sz_bound
  have sz_bound_le_n_div_card_R : ((#{f | (MvPolynomial.eval f) P = 0}) : ℚ≥0)
    / ((Fintype.card R ^ n)) ≤ (n : ℚ≥0) / ((#(Finset.univ : Finset R)) : ℚ≥0) := by
    calc
      _ ≤ (P.totalDegree : ℚ≥0) / ((#(Finset.univ : Finset R)) : ℚ≥0) := sz_bound
      _ ≤ _ := by
        simp only [card_univ]
        apply div_le_of_le_mul₀ (hb := by simp only [zero_le]) (hc := by simp only [zero_le])
        -- ⊢ ↑P.totalDegree ≤ ↑n / ↑(Fintype.card R) * ↑(Fintype.card R)
        rw [div_mul_cancel₀ (h := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
          not_false_eq_true])]
        exact Nat.cast_le.mpr h_deg
  have sz_bound_ENNReal : ((#{f | (MvPolynomial.eval f) P = 0}) : ENNReal)
    / ((Fintype.card R ^ n) : ℕ) ≤ (n : ENNReal) / (Fintype.card R : ENNReal) := by
    simp_rw [ENNReal.coe_Nat_coe_NNRat]
    conv_lhs => rw [ENNReal.coe_div_of_NNRat (hb := by
      simp only [Nat.cast_pow, ne_eq, pow_eq_zero_iff', Nat.cast_eq_zero, Fintype.card_ne_zero,
        false_and, not_false_eq_true])]
    conv_rhs => rw [ENNReal.coe_div_of_NNRat (hb := by simp only [ne_eq, Nat.cast_eq_zero,
      Fintype.card_ne_zero, not_false_eq_true])]
    rw [ENNReal.coe_le_of_NNRat]
    simp only [Nat.cast_pow]
    exact sz_bound_le_n_div_card_R
  simp only [Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Nat.cast_pow, ge_iff_le]
  rw [Nat.cast_pow] at sz_bound_ENNReal
  exact sz_bound_ENNReal

end ProbabilityTools
