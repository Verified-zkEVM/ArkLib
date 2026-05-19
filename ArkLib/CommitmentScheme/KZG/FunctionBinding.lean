/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.Correctness
import ArkLib.CommitmentScheme.HardnessAssumptions
import ArkLib.ToCompPoly.Univariate.Lagrange

/-!
# Function Binding for the KZG Polynomial Commitment Scheme

This file proves function binding for the KZG commitment scheme under the ARSDH assumption. The
proof follows the reduction strategy from [CGKY25], splitting the extraction into the evaluation
binding and interpolation branches used in the paper proof.

## Notation

* `functionBindingGame` is the base function-binding game.
* `functionBindingGameExt` records extra sampled and transcript data used by the reduction.
* `mapFunctionBindingToArsdh` maps extended outputs to ARSDH instances.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

set_option linter.style.longFile 2100

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ} -- the maximal degree of polynomials that can be committed to/opened.

open Commitment

local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

/-- Used to decide which strategy the adversary will take
(breaking ARSDH based on a evaluation binding conflict or breaking ARSDH based on Lagrange
interpolation). Returns the indices of two conflicting evaluations if they exist. -/
def findConflict {L : ℕ} (query : Fin L → ZMod p) (response : Fin L → ZMod p) :
    Option (Fin L × Fin L) :=
  (List.finRange L).findSome? fun i =>
    (List.finRange L).findSome? fun j =>
      if query i == query j && response i != response j then some (i, j) else none

omit [Fact (Nat.Prime p)] [DecidableEq G₁] [Group G₁] in
lemma find_conflict_unsuccessful {L : ℕ} (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hfc : findConflict query response = none) :
    ¬(∃ i : Fin L, ∃ j : Fin L, query i == query j && response i != response j) := by
  unfold findConflict at hfc
  rw [List.findSome?_eq_none_iff] at hfc
  simp only [List.findSome?_eq_none_iff] at hfc
  push Not
  intro i j hcond
  have hfc' := hfc i (List.mem_finRange i) j (List.mem_finRange j)
  simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true, ne_eq] at hfc' hcond
  simp [hcond] at hfc'

omit [Fact (Nat.Prime p)] [DecidableEq G₁] [Group G₁] in
lemma find_conflict_successful {L : ℕ} (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    {i j : Fin L} (hfc : findConflict query response = some (i, j)) :
    query i = query j ∧ response i ≠ response j := by
  unfold findConflict at hfc
  obtain ⟨_, i', _, _, h_inner, _⟩ := List.findSome?_eq_some_iff.mp hfc
  obtain ⟨_, j', _, _, h_cond, _⟩ := List.findSome?_eq_some_iff.mp h_inner
  by_cases hif : (query i' == query j' && response i' != response j') = true
  · rw [if_pos hif] at h_cond
    simp only [Option.some.injEq, Prod.mk.injEq] at h_cond
    obtain ⟨hi, hj⟩ := h_cond
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hif
    subst i
    subst j
    exact hif
  · rw [if_neg hif] at h_cond
    exact absurd h_cond (by simp)

-- case 1: there are two conflicting evaluations (binding failure)

/-- Step 3a (from the paper reduction): choose `S \ {αᵢ}` for the conflict branch.

The paper chooses a size-`D + 1` set `S` containing `αᵢ` with nonzero vanishing polynomial at
`τ`; this function returns the part of `S` away from `αᵢ`. -/
def chooseSConflict (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hn : 1 ≤ n) : Finset (ZMod p) :=
  let arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then
        some x
      else none
    else none
  arr.take n |>.toList.toFinset -- ∪ {αᵢ} to be the S referenced in the paper

omit [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma filter_map_conflict_nodup
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hn : 1 ≤ n) :
    ((Array.range p).filterMap fun i =>
      if h : i < p then
        let x : ZMod p := (⟨i, h⟩ : Fin p)
        if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
        else none
      else none).toList.Nodup := by
  rw [Array.toList_filterMap, Array.toList_range]
  apply List.Nodup.filterMap _ List.nodup_range
  intro a a' b hb hb'
  simp only [Option.mem_def] at hb hb'
  -- Extract a < p from hb (outer dite must take the then-branch)
  have ha : a < p := by
    by_contra h; push Not at h; rw [dif_neg (by omega)] at hb; simp at hb
  have ha' : a' < p := by
    by_contra h; push Not at h; rw [dif_neg (by omega)] at hb'; simp at hb'
  -- Both branches must hit `some x`, giving `b = ↑↑⟨a, ha⟩` and `b = ↑↑⟨a', ha'⟩`.
  simp only [ha, ha', dite_true] at hb hb'
  split at hb <;> simp at hb
  split at hb' <;> simp at hb'
  -- hb : ↑↑⟨a, ha⟩ = b, hb' : ↑↑⟨a', ha'⟩ = b
  have hval := congr_arg ZMod.val (hb.trans hb'.symm)
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hval
  exact hval

omit [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma filter_map_conflict_length (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1) :
    ((Array.range p).filterMap fun i =>
      if h : i < p then
        let x : ZMod p := (⟨i, h⟩ : Fin p)
        if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
        else none
      else none).size ≥ n := by
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  -- Convert Array.size to Finset.card via Nodup
  have hnodup : arr.toList.Nodup := filter_map_conflict_nodup αᵢ srs hn
  rw [show arr.size = arr.toList.toFinset.card from by
    rw [List.toFinset_card_of_nodup hnodup, Array.length_toList]]
  set S := arr.toList.toFinset
  -- Finset.univ (ZMod p) has card p
  have hUnivCard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  -- The complement (univ \ S) contains only x where srs.1[0]^x.val = srs.1[1] ∨ x = αᵢ,
  -- i.e., at most 2 elements (≤ 1 discrete log solution + αᵢ).
  have hCompl : (Finset.univ \ S).card ≤ 2 := by
    -- orderOf srs.1[0] = p (since srs.1[0] ≠ 1 in a group of prime order)
    have hord : orderOf srs.1[0] = p := by
      have hdvd : orderOf srs.1[0] ∣ p := by
        have := orderOf_dvd_natCard (G := G₁) srs.1[0]
        rwa [PrimeOrderWith.hCard] at this
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hgen
      · exact hp'
    -- Injectivity of x ↦ g^x.val for x : ZMod p
    have hinj : ∀ a b : ZMod p,
        srs.1[0] ^ a.val = srs.1[0] ^ b.val → a = b := by
      intro a b heq
      rw [pow_eq_pow_iff_modEq, hord] at heq
      have hval : a.val = b.val := by
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt a),
          Nat.mod_eq_of_lt (ZMod.val_lt b)] at heq
      calc a = ↑a.val := (ZMod.natCast_zmod_val a).symm
        _ = ↑b.val := congrArg Nat.cast hval
        _ = b := ZMod.natCast_zmod_val b
    -- Any x satisfying the condition is in S
    have hmem : ∀ x : ZMod p,
        srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) → x ≠ αᵢ → x ∈ S := by
      intro x hpow hneα
      change x ∈ arr.toList.toFinset
      simp only [List.mem_toFinset, arr, Array.toList_filterMap, Array.toList_range,
        List.mem_filterMap, List.mem_range]
      exact ⟨x.val, ZMod.val_lt x, by
        simp only [ZMod.val_lt x, dite_true, ZMod.natCast_zmod_val]
        exact if_pos ⟨hpow, hneα⟩⟩
    -- The complement ⊆ {x | g^x.val = h} ∪ {αᵢ}
    have hsub : Finset.univ \ S ⊆
        Finset.univ.filter (fun x : ZMod p =>
          srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) ∪ {αᵢ} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_contra h; push Not at h
      exact hx (hmem x h.1 h.2)
    -- The filter set has ≤ 1 element (injectivity of g^·)
    have hfilt : (Finset.univ.filter (fun x : ZMod p =>
        srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hinj a b (ha ▸ hb ▸ rfl)
    calc (Finset.univ \ S).card
        ≤ (Finset.univ.filter (fun x : ZMod p =>
            srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) ∪ {αᵢ}).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun x : ZMod p =>
            srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn))).card +
          ({αᵢ} : Finset _).card := Finset.card_union_le _ _
      _ ≤ 2 := by simp only [Finset.card_singleton]; omega
  -- sdiff identity: (univ \ S).card + S.card = p
  have hSdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  omega

omit [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma choose_s_conflict_size (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hgen : srs.1[0] ≠ 1) :
    (chooseSConflict αᵢ srs hn).card = n := by
  unfold chooseSConflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  have hnodup : arr.toList.Nodup := filter_map_conflict_nodup αᵢ srs hn
  have hsize : arr.size ≥ n := filter_map_conflict_length hp hn αᵢ srs hgen
  have htoList : (arr.take n).toList = arr.toList.take n := by
    simp [Array.take]
  rw [List.toFinset_card_of_nodup]
  · rw [htoList, List.length_take, Array.length_toList]
    omega
  · rw [htoList]
    exact (List.take_sublist n arr.toList).nodup hnodup

omit [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_s_conflict_alpha (hn : 1 ≤ n) (αᵢ : ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) :
    ¬ αᵢ ∈ chooseSConflict αᵢ srs hn := by
  unfold chooseSConflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  simp only [List.mem_toFinset]
  intro hmem
  have htoList : (arr.take n).toList = arr.toList.take n := by simp [Array.take]
  rw [htoList] at hmem
  have hmem := (List.take_sublist n arr.toList).subset hmem
  simp only [arr, Array.toList_filterMap, Array.toList_range, List.mem_filterMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  split at hi
  · split at hi
    · next _ hcond => exact absurd (Option.some.inj hi) hcond.2
    · simp at hi
  · simp at hi

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_s_conflict_size_adjoined (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hgen : srs.1[0] ≠ 1) :
    (chooseSConflict αᵢ srs hn ∪ {αᵢ}).card = n + 1 := by
  simp_all only [ge_iff_le, ne_eq, Finset.union_singleton, choose_s_conflict_alpha,
    not_false_eq_true, Finset.card_insert_of_notMem, choose_s_conflict_size]

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_s_conflict_tau (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) :
    ¬ τ ∈ chooseSConflict αᵢ srs hn := by
  have hsrs_rel : srs.1[0] ^ τ.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [hsrs]; simp [generateSrs, towerOfExponents, Vector.getElem_ofFn]
  unfold chooseSConflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  simp only [List.mem_toFinset]
  intro hmem
  have htoList : (arr.take n).toList = arr.toList.take n := by simp [Array.take]
  rw [htoList] at hmem
  have hmem := (List.take_sublist n arr.toList).subset hmem
  simp only [arr, Array.toList_filterMap, Array.toList_range, List.mem_filterMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  split at hi
  · split at hi
    · next _ hcond =>
      rw [← Option.some.inj hi] at hsrs_rel
      exact absurd hsrs_rel hcond.1
    · simp at hi
  · simp at hi

lemma prod_x_sub_c_to_poly (S : Finset (ZMod p)) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).toPoly =
      ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
  have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
  simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]

lemma prod_x_sub_c_eval_ne_zero {S : Finset (ZMod p)} {τ : ZMod p}
    (hτS : τ ∉ S) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ ≠ 0 := by
  rw [eval_toPoly, prod_x_sub_c_to_poly S, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro s hs
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact fun h => hτS (by simpa [sub_eq_zero.mp h])

lemma prod_x_sub_c_insert_eval {S : Finset (ZMod p)} {α τ : ZMod p}
    (hαS : α ∉ S) :
    (∏ s ∈ S ∪ {α}, (X - C s : CPolynomial (ZMod p))).eval τ =
      (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ * (τ - α) := by
  rw [eval_toPoly, eval_toPoly, prod_x_sub_c_to_poly (S ∪ {α}), prod_x_sub_c_to_poly S,
    Finset.union_singleton, Finset.prod_insert hαS]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    _root_.mul_comm]

omit [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma order_of_eq_prime_of_ne_one (x : G₁) (hx : x ≠ 1) : orderOf x = p := by
  have hdvd := orderOf_dvd_natCard (G := G₁) x
  rw [PrimeOrderWith.hCard] at hdvd
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.1 h1) hx
  · exact hp'

omit [DecidableEq G₁] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma g1_ne_one_of_srs_gen (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1) :
    g₁ ≠ 1 := by
  rw [hsrs] at hgen
  simpa [generateSrs, towerOfExponents] using hgen

omit [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma zmod_eq_zero_of_gpow_eq_one (hord : orderOf g₁ = p) {a : ZMod p}
    (ha : g₁ ^ a.val = 1) : a = 0 := by
  have hdvd := orderOf_dvd_of_pow_eq_one ha
  rw [hord] at hdvd
  apply ZMod.val_injective p
  have hval : a.val = 0 := by
    by_contra h
    exact absurd (ZMod.val_lt a) (not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd))
  simpa using hval

omit [DecidableEq G₁] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- If two ℕ exponents are equal when cast to `ZMod p`, then `g₁` raised to each is the same. -/
lemma gpow_eq_of_nat_cast_eq (hord : orderOf g₁ = p) (a b : ℕ)
    (hab : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) : g₁ ^ a = g₁ ^ b := by
  conv_lhs => rw [← pow_mod_orderOf, hord]
  conv_rhs => rw [← pow_mod_orderOf, hord]
  congr 1
  have := congr_arg ZMod.val hab
  rwa [ZMod.val_natCast, ZMod.val_natCast] at this

omit [DecidableEq G₁] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- Group division of powers equals the power of the `ZMod p` difference. -/
lemma gpow_div_eq (hord : orderOf g₁ = p) (a b : ZMod p) :
    g₁ ^ a.val / g₁ ^ b.val = g₁ ^ (a - b).val := by
  rw [div_eq_iff_eq_mul, ← pow_add]
  exact gpow_eq_of_nat_cast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)

omit [DecidableEq G₁] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- Product of `.val`s as exponent equals `ZMod p` product's `.val` as exponent. -/
lemma gpow_val_mul_eq (hord : orderOf g₁ = p) (a b : ZMod p) :
    g₁ ^ (a.val * b.val) = g₁ ^ (a * b).val :=
  gpow_eq_of_nat_cast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)

omit [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma exists_zmod_power_of_generator (hpG1 : Nat.card G₁ = p) (hg₁ : g₁ ≠ 1)
    (hord : orderOf g₁ = p) (x : G₁) : ∃ a : ZMod p, x = g₁ ^ a.val := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g₁ ^ k = x := mem_powers_of_prime_card hpG1 hg₁
  exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, ← hk, ← pow_mod_orderOf g₁ k, hord]⟩

lemma deg_of_zs {S : Finset (ZMod p)} (hcardS : S.card = n) :
    (∏ s ∈ S, (X - C s)).degree ≤ ↑n := by
  rw [degree_toPoly, prod_x_sub_c_to_poly S]
  apply Polynomial.degree_le_of_natDegree_le
  calc (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree
      ≤ ∑ s ∈ S, (Polynomial.X - Polynomial.C s).natDegree :=
        Polynomial.natDegree_prod_le S _
    _ = S.card := by simp
    _ = n := hcardS

omit [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma h1_ne_one (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1) :
    let S := chooseSConflict αᵢ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    h₁ ≠ 1 := by
    intro S Zₛ h₁
    have cardS : S.card = n := by exact choose_s_conflict_size hp hn αᵢ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_zs cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_c_polynomial hpG1 Zₛ Zₛ_deg]
    have hτS : ¬ τ ∈ S := by
      unfold S
      exact choose_s_conflict_tau hn αᵢ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      exact prod_x_sub_c_eval_ne_zero hτS
    rw [hh₁]
    intro heq
    apply hZₛeval
    exact zmod_eq_zero_of_gpow_eq_one
      (order_of_eq_prime_of_ne_one g₁ (g1_ne_one_of_srs_gen τ srs hsrs hgen)) heq

lemma h1_zs_eq_h2 (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n)
    (α₁ α₂ β₁ β₂ τ : ZMod p) (c pf₁ pf₂ : G₁) (hα : α₁ = α₂)
    (hβ : β₁ ≠ β₂) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1)
  (hpair : pairing g₁ g₂ ≠ 0)
  (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    srs.2 c pf₁ α₁ β₁)
  (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    srs.2 c pf₂ α₂ β₂) :
    let S := chooseSConflict α₁ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 / (β₂ - β₁)).val
    let Zₛᵤₐ := ∏ s ∈ S ∪ {α₁} , (X - C s)
    h₂ = h₁ ^ (1 / Zₛᵤₐ.eval τ).val := by
    intro S Zₛ h₁ h₂ Zₛᵤₐ
    /-prove rhs: h₁ ^ (1 / Zₛᵤₐ.eval τ) = g₁ ^ (1 / (τ - α₁)) -/
    have cardS : S.card = n := by exact choose_s_conflict_size hp hn α₁ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_zs cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_c_polynomial hpG1 Zₛ Zₛ_deg]
    have hα₁S : α₁ ∉ S := choose_s_conflict_alpha hn α₁ srs
    have hτS : ¬ τ ∈ S := choose_s_conflict_tau hn α₁ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      exact prod_x_sub_c_eval_ne_zero hτS
    have hZsua_eval : Zₛᵤₐ.eval τ = Zₛ.eval τ * (τ - α₁) := by
      unfold Zₛᵤₐ Zₛ
      exact prod_x_sub_c_insert_eval hα₁S
    have hrhsfield : Zₛ.eval τ * (1 / Zₛᵤₐ.eval τ) = 1 / (τ - α₁) := by
      rw [hZsua_eval, one_div, one_div, mul_inv_rev,
        show (τ - α₁)⁻¹ * (Zₛ.eval τ)⁻¹ = (Zₛ.eval τ)⁻¹ * (τ - α₁)⁻¹ from
          _root_.mul_comm _ _,
        ← _root_.mul_assoc, mul_inv_cancel₀ hZₛeval, _root_.one_mul]
    have hg₁ : g₁ ≠ 1 := g1_ne_one_of_srs_gen τ srs hsrs hgen
    have hord : orderOf g₁ = p := order_of_eq_prime_of_ne_one g₁ hg₁
    have hrhs : h₁ ^ (1 / Zₛᵤₐ.eval τ).val = g₁ ^ (1 / (τ - α₁)).val := by
      rw [hh₁, ← pow_mul, pow_eq_pow_iff_modEq, hord]
      change (Zₛ.eval τ).val * (1 / Zₛᵤₐ.eval τ).val % p = (1 / (τ - α₁)).val % p
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hcast : (((Zₛ.eval τ).val * (1 / Zₛᵤₐ.eval τ).val : ℕ) : ZMod p)
          = (1 / (τ - α₁) : ZMod p) := by
        push_cast [ZMod.natCast_zmod_val]
        exact hrhsfield
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    /- prove lhs: h₂ = g₁ ^ (1 / (τ - α₁))-/
    obtain ⟨cm, hc⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord c
    obtain ⟨prf₁, hprf₁⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord pf₁
    obtain ⟨prf₂, hprf₂⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord pf₂
    have hfield_verify₁ : cm = prf₁ * (τ - α₁) + β₁ := by
      grind [verify_opening_equation pairing α₁ β₁ τ cm prf₁ c pf₁ srs hsrs hpair
        hc hprf₁ hverify₁]
    have hfield_verify₂ : cm = prf₂ * (τ - α₁) + β₂ := by
      rw [← hα] at hverify₂
      grind [verify_opening_equation pairing α₁ β₂ τ cm prf₂ c pf₂ srs hsrs hpair
        hc hprf₂ hverify₂]
    have hfield_conflict : prf₁ * (τ - α₁) + β₁ = prf₂ * (τ - α₁) + β₂ := by
      simp_all
    have hfield_solution : (prf₁ - prf₂)/(β₂ - β₁) = 1/(τ - α₁) := by
      have hβ_ne : β₂ - β₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
      have hτα : τ - α₁ ≠ 0 := by
        intro h
        apply hβ
        have := hfield_conflict
        simp only [h, MulZeroClass.mul_zero, _root_.zero_add] at this
        exact this
      rw [div_eq_div_iff hβ_ne hτα]
      linear_combination hfield_conflict
    have hlhs : h₂ = g₁ ^ (1 / (τ - α₁)).val := by
      simp_rw [h₂]
      rw [hprf₁, hprf₂]
      rw [gpow_div_eq hord, ← pow_mul, pow_eq_pow_iff_modEq, hord]
      change (prf₁ - prf₂).val * (1 / (β₂ - β₁)).val % p = (1 / (τ - α₁)).val % p
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hcast : (((prf₁ - prf₂).val * (1 / (β₂ - β₁)).val : ℕ) : ZMod p)
          = (1 / (τ - α₁) : ZMod p) := by
        push_cast [ZMod.natCast_zmod_val]
        rw [mul_one_div]
        exact hfield_solution
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    simp_all

-- case 2: there's no conflicting evaluation, but more than D distinct evaluations (degree failure)

/-- Step 4a (from the paper reduction):
    find a subset whose interpolation polynomial has degree `n`. -/
def findA {L : ℕ} (n : ℕ) (query : Fin L → ZMod p) (response : Fin L → ZMod p) :
    Option (Finset (Fin L)) :=
  let candidateslist := (List.finRange L).sublistsLen (n + 1)
  let candidates := candidateslist.map List.toFinset
  candidates.find? fun s => (CLagrange.interpolate s query response).degree = n

lemma find_a_card {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hres : some (A) = findA n query response) :
    A.card = n + 1 := by
  unfold findA at hres
  have hmem := List.mem_of_find?_eq_some hres.symm
  rw [List.mem_map] at hmem
  obtain ⟨l, hl_mem, hl_eq⟩ := hmem
  rw [List.mem_sublistsLen] at hl_mem
  obtain ⟨hl_sub, hl_len⟩ := hl_mem
  rw [← hl_eq, List.toFinset_card_of_nodup ((List.nodup_finRange L).sublist hl_sub), hl_len]

lemma find_a_deg {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p)
    (hres : some (A) = findA n query response) :
    (CLagrange.interpolate A query response).degree = n := by
  unfold findA at hres
  have hpred := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at hpred
  exact hpred

lemma sorted_finset_sort_sublist_fin_range {L : ℕ} (s : Finset (Fin L)) :
    List.Sublist (s.sort (· ≤ ·)) (List.finRange L) :=
  List.sublist_of_subperm_of_sortedLE
    ((Finset.sort_nodup (s := s) (r := (· ≤ ·))).subperm (fun _ _ => List.mem_finRange _))
    (Finset.sortedLT_sort s).sortedLE
    (List.sortedLT_finRange L).sortedLE

lemma finset_mem_sublists_len_map {L : ℕ} (s : Finset (Fin L)) (hn : s.card = n + 1) :
    s ∈ ((List.finRange L).sublistsLen (n + 1)).map List.toFinset := by
  rw [List.mem_map]
  exact ⟨s.sort (· ≤ ·), List.mem_sublistsLen.mpr
    ⟨sorted_finset_sort_sublist_fin_range s,
     by rw [Finset.length_sort]; exact hn⟩,
    Finset.sort_toFinset (s := s) (r := (· ≤ ·))⟩

lemma interp_degree_le_of_card {L : ℕ} (s : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hquery : Function.Injective query) (hn : s.card = n + 1) :
    (CLagrange.interpolate s query response).degree ≤ ↑n := by
  rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate]
  have hle : (Lagrange.interpolate s query response).degree ≤ ↑(s.card - 1) :=
    Lagrange.degree_interpolate_le response hquery.injOn
  simp only [hn, Nat.add_sub_cancel] at hle
  exact hle

lemma find_a_successful {L : ℕ} (n : ℕ) (hL : n < L) (S : Finset (Fin L))
    (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hquery : Function.Injective query)
    (hinterp : (CLagrange.interpolate S query response).degree ≥ n) :
    (findA n query response).isSome := by
  by_contra h_not
  have h_none : findA n query response = none := by
    match hc : findA n query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold findA at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq] at h_none
  have h_deg_lt : ∀ (s : Finset (Fin L)), s.card = n + 1 →
      (CLagrange.interpolate s query response).degree < ↑n := by
    intro s hs
    exact lt_of_le_of_ne (interp_degree_le_of_card s query response hquery hs)
      (h_none s (finset_mem_sublists_len_map s hs))
  -- Core argument: construct a polynomial of degree < n agreeing with all L values
  -- Pick a subset T of size n
  obtain ⟨T, -, hTcard⟩ :=
    Finset.exists_subset_card_eq (n := n) (s := (Finset.univ : Finset (Fin L)))
      (by simp [Finset.card_univ, Fintype.card_fin]; omega)
  -- Let Q_T be the Mathlib interpolation over T
  set Q_T := Lagrange.interpolate T query response with hQ_T_def
  have hQ_T_deg : Q_T.degree < ↑n := by
    rw [← hTcard]
    exact Lagrange.degree_interpolate_lt response (hquery.injOn (s := (T : Set (Fin L))))
  -- Show Q_T agrees with response on all of Fin L
  have hQ_T_eval : ∀ i : Fin L, Q_T.eval (query i) = response i := by
    intro i
    by_cases hiT : i ∈ T
    · exact Lagrange.eval_interpolate_at_node response (hquery.injOn (s := (T : Set (Fin L)))) hiT
    · -- Use the (n+1)-subset T ∪ {i}
      set Si := insert i T with hSi_def
      have hSicard : Si.card = n + 1 := by
        rw [Finset.card_insert_of_notMem hiT, hTcard]
      -- The interpolation over Si also has degree < n (via CPolynomial bridge)
      have hSi_deg_lt : (CLagrange.interpolate Si query response).degree < ↑n :=
        h_deg_lt Si hSicard
      -- Transfer to Polynomial world
      set Q_Si := Lagrange.interpolate Si query response with hQ_Si_def
      have hQ_Si_deg : Q_Si.degree < ↑n := by
        have h := hSi_deg_lt
        rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
        exact h
      -- Q_T and Q_Si agree on T
      have hagree : ∀ j ∈ T, Q_T.eval (query j) = Q_Si.eval (query j) := by
        intro j hjT
        rw [Lagrange.eval_interpolate_at_node response (hquery.injOn (s := (T : Set (Fin L)))) hjT,
            Lagrange.eval_interpolate_at_node response
              (hquery.injOn (s := (Si : Set (Fin L))))
              (Finset.mem_insert_of_mem hjT)]
      -- By uniqueness (both degree < |T| = n, agree on T), Q_T = Q_Si
      have hTn : (↑n : WithBot ℕ) = ↑(T.card) := by
        rw [hTcard]
      have heq : Q_T = Q_Si := by
        rw [hTn] at hQ_T_deg hQ_Si_deg
        exact Polynomial.eq_of_degrees_lt_of_eval_index_eq T
          (hquery.injOn (s := (T : Set (Fin L)))) hQ_T_deg hQ_Si_deg hagree
      -- Hence Q_T.eval(query i) = Q_Si.eval(query i) = response i
      rw [heq]
      exact Lagrange.eval_interpolate_at_node response
        (hquery.injOn (s := (Si : Set (Fin L)))) (Finset.mem_insert_self i T)
  -- Derive n < S.card from hinterp and degree_interpolate_lt
  have hinterp_poly : (Lagrange.interpolate S query response).degree ≥ ↑n := by
    have h := hinterp
    rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
    exact h
  have hScard_gt : n < S.card := by
    have h2 : (Lagrange.interpolate S query response).degree < ↑S.card :=
      Lagrange.degree_interpolate_lt response hquery.injOn
    exact_mod_cast lt_of_le_of_lt hinterp_poly h2
  -- Q_T = interpolation over S, since Q_T has degree < S.card and agrees on S
  have hQ_T_deg_S : Q_T.degree < ↑S.card :=
    lt_trans hQ_T_deg (by exact_mod_cast hScard_gt)
  have hP_eq : Q_T = Lagrange.interpolate S query response :=
    Lagrange.eq_interpolate_of_eval_eq (s := S) response
      hquery.injOn hQ_T_deg_S (fun i _ => hQ_T_eval i)
  -- Contradiction: interp over S has degree ≥ n but Q_T has degree < n
  exact absurd (hP_eq ▸ hQ_T_deg) (not_lt.mpr hinterp_poly)

/-- Step 4b (from the paper reduction): find a subset whose interpolation commitment differs from
the adversary's commitment `c`. -/
def findSPrime {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (c : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) :
    Option (Finset (Fin L)) :=
  let candidateslist := (A.sort (· ≤ ·)).sublistsLen (n + 1)
  let candidates := candidateslist.map List.toFinset
  candidates.find? fun s =>
    commit srs.1 ((CLagrange.interpolate s query response).val.coeff ∘ Fin.val) ≠ c

lemma find_s_prime_existence {L : ℕ} (n : ℕ) (τ c : ZMod p) (A : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hA : (CLagrange.interpolate A query response).degree = n + 1)
    (hquery : Function.Injective query) (hn : 1 ≤ n) :
    ∃ S ⊆ A, S.card = n + 1
      ∧ (CLagrange.interpolate S query response).eval τ ≠ c := by
  by_contra h_all
  push Not at h_all
  -- Bridge h_all to Polynomial world
  have h_poly : ∀ S ⊆ A, S.card = n + 1 →
      (Lagrange.interpolate S query response).eval τ = c := by
    intro S hS hcard
    have h := h_all S hS hcard
    rwa [eval_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
  -- Bridge hA to Polynomial world
  have hA_poly : (Lagrange.interpolate A query response).degree = ↑(n + 1) := by
    rw [← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]; exact_mod_cast hA
  -- Step A: n + 1 < A.card
  have hn_lt : n + 1 < A.card := by
    have h := Lagrange.degree_interpolate_lt response (hquery.injOn (s := (A : Set (Fin L))))
    rw [hA_poly] at h; exact_mod_cast h
  -- Step B: Pick A' ⊆ A with |A'| = n + 2
  obtain ⟨A', hA'_sub, hA'_card⟩ :=
    Finset.exists_subset_card_eq (show n + 2 ≤ A.card by omega)
  -- Step C: interpolate A = interpolate A' (by uniqueness, since deg < |A'| and agrees on A')
  have hA'_eq : Lagrange.interpolate A query response =
      Lagrange.interpolate A' query response :=
    Lagrange.eq_interpolate_of_eval_eq response
      (hquery.injOn (s := (A' : Set (Fin L))))
      (by rw [hA_poly, hA'_card]; exact_mod_cast (show n + 1 < n + 2 by omega))
      (fun i hi => Lagrange.eval_interpolate_at_node response
        (hquery.injOn (s := (A : Set (Fin L)))) (hA'_sub hi))
  -- Degree of interpolate A' equals n + 1
  have hA'_deg : (Lagrange.interpolate A' query response).degree = ↑(n + 1) := by
    rw [← hA'_eq]; exact hA_poly
  -- Step D: Pick two distinct elements i, j ∈ A' (possible since |A'| = n+2 ≥ 2)
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp (show 1 < A'.card by omega)
  -- Erase subset/cardinality facts
  have hej_sub : A'.erase j ⊆ A := (Finset.erase_subset j A').trans hA'_sub
  have hei_sub : A'.erase i ⊆ A := (Finset.erase_subset i A').trans hA'_sub
  have hej_card : (A'.erase j).card = n + 1 := by
    rw [Finset.card_erase_of_mem hj, hA'_card]; omega
  have hei_card : (A'.erase i).card = n + 1 := by
    rw [Finset.card_erase_of_mem hi, hA'_card]; omega
  -- Step E: Show (interpolate A').eval τ = c via decomposition
  --   PA' = P_{A'\j} · basisDivisor(qi,qj) + P_{A'\i} · basisDivisor(qj,qi)
  --   Evaluating at τ and using h_poly gives c · (bd + bd') = c · 1 = c
  have hA'_eval_tau : (Lagrange.interpolate A' query response).eval τ = c := by
    have hdecomp := Lagrange.interpolate_eq_add_interpolate_erase response
      (hquery.injOn (s := (A' : Set (Fin L)))) hi hj hij
    have h1 := congr_arg (Polynomial.eval τ) hdecomp
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at h1
    rw [h_poly (A'.erase j) hej_sub hej_card,
        h_poly (A'.erase i) hei_sub hei_card] at h1
    rw [h1, ← _root_.mul_add, ← Polynomial.eval_add,
        Lagrange.basisDivisor_add_symm (show query i ≠ query j from fun h => hij (hquery h))]
    simp
  -- Step F: Choose k ∈ A' such that τ ∉ (A'.erase k).image query
  obtain ⟨k, hk, hk_fresh⟩ : ∃ k ∈ A', τ ∉ (A'.erase k).image query := by
    by_cases hτ : ∃ k ∈ A', query k = τ
    · obtain ⟨k, hk, hkq⟩ := hτ
      exact ⟨k, hk, by
        simp only [Finset.mem_image]
        rintro ⟨x, hxe, hxq⟩
        exact Finset.ne_of_mem_erase hxe (hquery (hxq.trans hkq.symm))⟩
    · push Not at hτ
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < A'.card by omega)
      exact ⟨k, hk, by
        simp only [Finset.mem_image]
        rintro ⟨x, hxe, hxq⟩
        exact hτ x (Finset.mem_of_mem_erase hxe) hxq⟩
  -- Erase-k facts
  have hek_card : (A'.erase k).card = n + 1 := by
    rw [Finset.card_erase_of_mem hk, hA'_card]; omega
  have hek_sub : A'.erase k ⊆ A := (Finset.erase_subset k A').trans hA'_sub
  -- Degree of interpolate (A'.erase k) < n + 1
  have h_deg_ek : (Lagrange.interpolate (A'.erase k) query response).degree < ↑(n + 1) := by
    rw [← hek_card]
    exact Lagrange.degree_interpolate_lt response (hquery.injOn (s := (A'.erase k : Set (Fin L))))
  -- Step G: The difference polynomial vanishes at n+2 distinct field values, so it is zero
  have hQ_zero : Lagrange.interpolate A' query response -
      Lagrange.interpolate (A'.erase k) query response = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((A'.erase k).image query ∪ {τ})
    · -- degree < |T|
      have hT_card : ((A'.erase k).image query ∪ {τ}).card = n + 2 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hk_fresh),
            Finset.card_image_of_injOn
              (hquery.injOn (s := (A'.erase k : Set (Fin L)))),
            hek_card, Finset.card_singleton]
      rw [hT_card]
      calc (Lagrange.interpolate A' query response -
              Lagrange.interpolate (A'.erase k) query response).degree
          ≤ max (Lagrange.interpolate A' query response).degree
                (Lagrange.interpolate (A'.erase k) query response).degree :=
            Polynomial.degree_sub_le _ _
        _ ≤ ↑(n + 1) := max_le (le_of_eq hA'_deg) (le_of_lt h_deg_ek)
        _ < ↑(n + 2) := by exact_mod_cast (show n + 1 < n + 2 by omega)
    · -- vanishes on T
      intro x hx
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx
      rw [Polynomial.eval_sub, sub_eq_zero]
      rcases hx with ⟨m, hm, rfl⟩ | rfl
      · rw [Lagrange.eval_interpolate_at_node response
              (hquery.injOn (s := (A' : Set (Fin L)))) (Finset.mem_of_mem_erase hm),
            Lagrange.eval_interpolate_at_node response
              (hquery.injOn (s := (A'.erase k : Set (Fin L)))) hm]
      · rw [hA'_eval_tau, h_poly (A'.erase k) hek_sub hek_card]
  -- But they can't be equal (degrees n vs < n)
  have hne : Lagrange.interpolate A' query response ≠
      Lagrange.interpolate (A'.erase k) query response := by
    intro h
    rw [h] at hA'_deg
    exact absurd hA'_deg (ne_of_lt h_deg_ek)
  exact hne (sub_eq_zero.mp hQ_zero)

lemma sorted_finset_sort_sublist_sort {L : ℕ} (S A : Finset (Fin L)) (hSA : S ⊆ A) :
    List.Sublist (S.sort (· ≤ ·)) (A.sort (· ≤ ·)) :=
  List.sublist_of_subperm_of_sortedLE
    ((Finset.sort_nodup (s := S) (r := (· ≤ ·))).subperm
      (fun x hx => by simpa using hSA (by simpa using hx)))
    (Finset.sortedLT_sort S).sortedLE
    (Finset.sortedLT_sort A).sortedLE

lemma finset_subset_mem_sublists_len_map {L : ℕ} (S A : Finset (Fin L))
    (hSA : S ⊆ A) (hn : S.card = n) :
    S ∈ ((A.sort (· ≤ ·)).sublistsLen n).map List.toFinset := by
  rw [List.mem_map]
  exact ⟨S.sort (· ≤ ·), List.mem_sublistsLen.mpr
    ⟨sorted_finset_sort_sublist_sort S A hSA,
     by rw [Finset.length_sort]; exact hn⟩,
    Finset.sort_toFinset (s := S) (r := (· ≤ ·))⟩

omit [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma find_s_prime_successful {L : ℕ} (n : ℕ) (τ : ZMod p) (c : G₁) (A : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1)
    (hA : (CLagrange.interpolate A query response).degree = n + 1)
    (hquery : Function.Injective query) (hn : 1 ≤ n) :
    (findSPrime n A c srs query response).isSome := by
  by_contra h_not
  have h_none : findSPrime n A c srs query response = none := by
    match hc : findSPrime n A c srs query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold findSPrime at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq, not_not] at h_none
  have hg₁ : g₁ ≠ 1 := g1_ne_one_of_srs_gen τ srs hsrs hgen
  have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
  have hord : orderOf g₁ = p := order_of_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨c', hc_eq⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord c
  -- For every candidate S, commit = c means eval τ = c'
  have h_all_eq : ∀ S ⊆ A, S.card = n + 1 →
      (CLagrange.interpolate S query response).eval τ = c' := by
    intro S hSA hScard
    -- S is in the candidate list
    have hS_mem := finset_subset_mem_sublists_len_map S A hSA hScard
    -- The hypothesis says commit = c for S
    have hcommit_eq := h_none S hS_mem
    -- Degree bound for interpolation over S
    have hdeg : (CLagrange.interpolate S query response).degree ≤ ↑n :=
      interp_degree_le_of_card S query response hquery hScard
    -- Rewrite commit using commit_eq_c_polynomial
    have hcommit_rw : commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val)
        = g₁ ^ ((CLagrange.interpolate S query response).eval τ).val := by
      conv_lhs => rw [hsrs, generateSrs]
      exact commit_eq_c_polynomial (g₁ := g₁) hpG1
        (CLagrange.interpolate S query response) hdeg
    -- So g₁ ^ (eval τ ...).val = g₁ ^ c'.val
    rw [hcommit_rw, hc_eq] at hcommit_eq
    -- Injectivity: g₁ ^ a = g₁ ^ b with a, b < orderOf g₁ implies a = b
    have hinj : ((CLagrange.interpolate S query response).eval τ).val = c'.val :=
      pow_injOn_Iio_orderOf
        (show ((CLagrange.interpolate S query response).eval τ).val ∈ Set.Iio (orderOf g₁)
          from by rw [hord]; exact ZMod.val_lt _)
        (show c'.val ∈ Set.Iio (orderOf g₁)
          from by rw [hord]; exact ZMod.val_lt _)
        hcommit_eq
    exact ZMod.val_injective p hinj
  -- But find_s_prime_existence gives an S with eval τ ≠ c'
  obtain ⟨S₀, hS₀_sub, hS₀_card, hS₀_ne⟩ :=
    find_s_prime_existence n τ c' A query response hA hquery hn
  exact hS₀_ne (h_all_eq S₀ hS₀_sub hS₀_card)

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma find_s_prime_card
    {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hres : some (S) = findSPrime n A c srs query response) :
    S.card = n + 1 := by
    unfold findSPrime at hres
    have hS_mem := List.mem_of_find?_eq_some hres.symm
    rw [List.mem_map] at hS_mem
    obtain ⟨l, hl_mem, hl_eq⟩ := hS_mem
    rw [List.mem_sublistsLen] at hl_mem
    obtain ⟨hl_sub, hl_len⟩ := hl_mem
    rw [← hl_eq, List.toFinset_card_of_nodup ((A.sort_nodup (· ≤ ·)).sublist hl_sub), hl_len]

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma find_s_prime_diverges
    {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hres : some (S) = findSPrime n A c srs query response) :
    commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val) ≠ c := by
  unfold findSPrime at hres
  have h := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at h
  exact h

lemma zs_to_poly_eq_nodal {L : ℕ} (S : Finset (Fin L))
    (query : Fin L → ZMod p) (hquery : Function.Injective query) :
    (∏ s ∈ S.image query, (X - C s) : CPolynomial (ZMod p)).toPoly
      = Lagrange.nodal S query := by
  rw [toPoly_prod]
  simp only [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
  rw [Lagrange.nodal_eq]
  exact Finset.prod_image (f := fun s => Polynomial.X - Polynomial.C s)
    (hquery.injOn (s := ↑S))

lemma div_by_monic_zs_to_poly_eq_nodal_erase {L : ℕ}
    (S : Finset (Fin L)) (query : Fin L → ZMod p)
    (hquery : Function.Injective query) (i : Fin L) (hi : i ∈ S) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    (Zₛ.divByMonic (X - C (query i))).toPoly
      = Lagrange.nodal (S.erase i) query := by
  intro Zₛ
  have hq_toPoly : (X - C (query i) : CPolynomial (ZMod p)).toPoly
      = Polynomial.X - Polynomial.C (query i) := by
    rw [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
  have hmonic : (X - C (query i) : CPolynomial (ZMod p)).toPoly.Monic := by
    rw [hq_toPoly]; exact Polynomial.monic_X_sub_C _
  rw [CPolynomial.toPoly_divByMonic _ _ hmonic, zs_to_poly_eq_nodal S query hquery, hq_toPoly,
    Lagrange.nodal_eq_mul_nodal_erase hi]
  exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)

lemma lagrange_zs_conversion {L : ℕ} (τ : ZMod p) (S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hτ : ∀ i ∈ S, (query i) ≠ τ) (hquery : Function.Injective query) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    ((CLagrange.interpolate S query response).eval τ) / (Zₛ.eval τ)
      = ∑ x ∈ S, response x /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)) := by
  intro Zₛ
  -- Derive τ ≠ query i (Mathlib direction)
  have hτ' : ∀ i ∈ S, τ ≠ query i := fun i hi => Ne.symm (hτ i hi)
  -- Convert CPolynomial evals to Polynomial evals
  have hZₛ_toPoly : Zₛ.toPoly = Lagrange.nodal S query := zs_to_poly_eq_nodal S query hquery
  have hZₛ_eval : Zₛ.eval τ = Polynomial.eval τ (Lagrange.nodal S query) := by
    rw [eval_toPoly, hZₛ_toPoly]
  have hinterp_eval : (CLagrange.interpolate S query response).eval τ
      = Polynomial.eval τ (Lagrange.interpolate S query response) := by
    rw [eval_toPoly, CLagrange.cinterpolate_eq_interpolate]
  rw [hinterp_eval, hZₛ_eval]
  -- Apply first barycentric form
  rw [Lagrange.eval_interpolate_not_at_node response hτ']
  -- Cancel nodal(τ)
  have hne : Polynomial.eval τ (Lagrange.nodal S query) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node hτ'
  rw [mul_div_cancel_left₀ _ hne]
  -- Match summands
  apply Finset.sum_congr rfl
  intro i hi
  -- Rewrite nodalWeight using eval of nodal (S.erase i)
  rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv]
  -- Connect divByMonic eval to nodal (S.erase i) eval
  have hdiv_eval : eval (query i) (Zₛ.divByMonic (X - C (query i)))
      = Polynomial.eval (query i) (Lagrange.nodal (S.erase i) query) := by
    rw [eval_toPoly, div_by_monic_zs_to_poly_eq_nodal_erase S query hquery i hi]
  rw [hdiv_eval]
  -- Field algebra: a⁻¹ * b⁻¹ * c = c / (a * b)
  have heval_ne : Polynomial.eval (query i) (Lagrange.nodal (S.erase i) query) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun j hj =>
      fun h => (Finset.ne_of_mem_erase hj) (hquery h.symm))
  have hτqi_ne : τ - query i ≠ 0 := sub_ne_zero.mpr (hτ' i hi)
  field_simp

omit [DecidableEq G₁] in
lemma h1_zs_eq_h2_prime {L : ℕ} (n : ℕ) (τ : ZMod p) (cm : G₁) (S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p) (proofs : Fin L → G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hn : 1 ≤ n)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hτ : ∀ i ∈ S, (query i) ≠ τ)
    (hVerify : ∀ i ∈ S, verifyOpening (pairing := pairing) (g₁ := g₁) (g₂ := g₂)
      srs.2 cm (proofs i) (query i) (response i))
    (hgen : srs.1[0] ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hS : (CLagrange.interpolate S query response).degree ≤ n) (hS_ne : S.Nonempty)
    (hquery : Function.Injective query) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    let c' : G₁ := commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val)
    let h₁ := cm / c'
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ i ∈ S, (proofs i) ^ (d (query i)).val
    h₂ = h₁ ^ (1 / Zₛ.eval τ).val := by
    letI := Classical.decEq G₁
    intro Zₛ c' h₁ d h₂
    unfold h₁ h₂
    -- rewrite the equation to g₁^{*equation*} (expose the field values)
    have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
    have hcommit_rw : c' = g₁ ^ ((CLagrange.interpolate S query response).eval τ).val := by
      unfold c'
      conv_lhs => rw [hsrs, generateSrs]
      exact commit_eq_c_polynomial (g₁ := g₁) hpG1
        (CLagrange.interpolate S query response) hS
    rw [hcommit_rw]
    have hg₁ : g₁ ≠ 1 := g1_ne_one_of_srs_gen τ srs hsrs hgen
    have hord : orderOf g₁ = p := order_of_eq_prime_of_ne_one g₁ hg₁
    obtain ⟨cm', hcm⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord cm
    have hproofs_pow : ∀ i, ∃ prf : ZMod p, proofs i = g₁ ^ prf.val := by
      intro i
      exact exists_zmod_power_of_generator hpG1 hg₁ hord (proofs i)
    choose prf hprf using hproofs_pow
    rw [hcm]
    simp_rw [hprf]
    have hprf_eq : ∀ i ∈ S, prf i = (cm' - response i) / (τ - query i) := by
      intro i hi
      exact verify_opening_prf_equation pairing (query i) (response i) τ cm' (prf i)
        cm (proofs i) srs hsrs hpair (hVerify i hi) hcm (hprf i) (Ne.symm (hτ i hi))
    rw [show ∏ x ∈ S, (g₁ ^ (prf x).val) ^ (d (query x)).val
        = ∏ x ∈ S, (g₁ ^ ((cm' - response x) / (τ - query x)).val) ^ (d (query x)).val from
      Finset.prod_congr rfl (fun i hi => by rw [hprf_eq i hi])]
    -- move prod up to sum
    unfold d
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    have hlhs_rw : g₁ ^ (∑ x ∈ S,
        ((cm' - response x) / (τ - query x)).val *
        (1 / eval (query x) (Zₛ.divByMonic (X - C (query x)))).val)
      = g₁ ^ (∑ x ∈ S,
        (cm' - response x) /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))).val := by
      conv_lhs => rw [← pow_mod_orderOf g₁, hord]
      congr 1
      have hcast : ((∑ x ∈ S,
          ((cm' - response x) / (τ - query x)).val *
          (1 / eval (query x) (Zₛ.divByMonic (X - C (query x)))).val : ℕ) : ZMod p)
        = (∑ x ∈ S,
          (cm' - response x) /
          (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) := by
        push_cast [ZMod.natCast_zmod_val]
        congr 1; ext x
        rw [div_mul_div_comm, _root_.mul_one, mul_comm (τ - query x)]
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    rw [hlhs_rw]
    -- split sum: (cm' - response x) / ... = cm' / ... - response x / ...
    have hsplit : (∑ x ∈ S,
        (cm' - response x) /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      = (∑ x ∈ S,
        cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      - (∑ x ∈ S,
        response x / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) := by
      simp only [sub_div, Finset.sum_sub_distrib]
    rw [hsplit]
    -- Rewrite the response sum using lagrange_zs_conversion
    rw [← lagrange_zs_conversion τ S query response hτ hquery]
    -- Factor cm' from the first sum and simplify to cm' / Zₛ.eval τ
    have hcm_sum : (∑ x ∈ S,
        cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      = cm' / Zₛ.eval τ := by
      have h1 : ∀ x ∈ S,
          cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))
        = cm' * (1 / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) :=
        fun _ _ => by ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
        ← lagrange_zs_conversion τ S query (fun _ => 1) hτ hquery,
        CLagrange.interpolation_of_constants S query (fun _ => 1) 1 (fun _ _ => rfl)
          hquery.injOn hS_ne]
      simp only [eval_toPoly, C_toPoly, Polynomial.eval_C]
      ring
    rw [hcm_sum]
    -- Abbreviate
    set r := (CLagrange.interpolate S query response).eval τ
    set z := Zₛ.eval τ
    -- LHS: cm'/z - r/z = (cm' - r) * (1/z)
    conv_lhs => rw [show cm' / z - r / z = (cm' - r) * (1 / z) from by ring]
    -- RHS: use div_pow (CommGroup) and pow_mul
    rw [div_pow, ← pow_mul, ← pow_mul]
    -- Expand powers over the difference of the scaled exponents.
    rw [gpow_val_mul_eq hord cm' (1 / z), gpow_val_mul_eq hord r (1 / z), gpow_div_eq hord]
    congr 1
    exact congr_arg ZMod.val (by ring : (cm' - r) * (1 / z) = cm' * (1 / z) - r * (1 / z))

-- put all steps together

/-- Steps 3 and 4 of the ARSDH reduction from [CGKY25]. -/
def mapFunctionBindingInstanceToArsdhInstAux {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let (srs, cm, queryOf, responseOf, _accepts, proofs) := val
  if let some (i₁, i₂) := findConflict queryOf responseOf then
    -- step 3
    let S := chooseSConflict (queryOf i₁) srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (proofs i₁ / proofs i₂) ^ (1 / (responseOf i₂ - responseOf i₁)).val
    return (S ∪ {queryOf i₁}, h₁, h₂)
  else if -- additional subcase (not in the paper): find τ in queries
    let some α₁ := (List.finRange L).findSome? fun i =>
      if srs.1[0] ^ (queryOf i).val == srs.1[1]'(Nat.lt_add_of_pos_left hn)
      then some (queryOf i) else none
  then
    -- α₁ = τ
    let S : Finset (ZMod p) := (Finset.range (n + 1)).image ((↑) : ℕ → ZMod p)
    let Zₛ := ∏ s ∈ S, (X - C s)
    return (S, srs.1[0], srs.1[0] ^ (1 / Zₛ.eval α₁).val)
    -- h₂ = h₁ ^ (1 / Zₛ.eval τ).val with h₁:= g₁
  else
    -- step 4
    let A ← findA (n+1) queryOf responseOf
    let S ← findSPrime n A cm srs queryOf responseOf
    let Zₛ := ∏ s ∈ S.image queryOf, (X - C s)
    let c' : G₁ :=
      commit srs.1 ((CLagrange.interpolate S queryOf responseOf).val.coeff ∘ Fin.val)
    let h₁ := cm / c'
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ i ∈ S, (proofs i) ^ (d (queryOf i)).val
    return (S.image queryOf, h₁, h₂)

def mapFunctionBindingInstanceToArsdhInst {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    (Finset (ZMod p) × G₁ × G₁) :=
  -- For instances that break function binding, the auxiliary map should always return `some`.
  Option.getD (mapFunctionBindingInstanceToArsdhInstAux hn val) (∅, 1, 1)

def mapFunctionBindingToArsdh {L : ℕ} (hn : 1 ≤ n)
    (val : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    (ZMod p × Finset (ZMod p) × G₁ × G₁) :=
  (val.1, mapFunctionBindingInstanceToArsdhInst hn val.2)
    -- val.1 = τ, val.2 = (srs, cm, queryOf, responseOf, accepts, proofs)

/-- Abbreviation for a function binding adversary for KZG. -/
abbrev KzgFunctionBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (L : ℕ) (AuxState : Type) :=
  Commitment.FunctionBindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState L
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

include g₁ g₂ pairing in
/-- The reduction breaking ARSDH using a successful function-binding adversary.

The reduction follows the proof of Lemma 9.1, under Definition 9.6, in [CGKY25]. -/
def reduction (L : ℕ) (hn : 1 ≤ n) (AuxState : Type)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.arsdhAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
    letI kzgScheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    -- designed such that ProbEvent_comp can be applied and thus the main task of reasoning
    -- is discharged to the predicate level.
    -- The auxiliary map (steps 3 and 4 of the reduction) is applied to the adversary result
    -- from steps 1 and 2.
    letI so : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
      QueryImpl.addLift
        (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
        (challengeQueryImpl (pSpec := ⟨!v[.P_to_V], !v[G₁]⟩))
    (simulateQ so
          (do
            let (ck, vk) := (srs, srs)
            let claimResult ←
              liftComp (adversary.claim ck) _
            let cm := claimResult.1
            let queryOf := claimResult.2.1
            let responseOf := claimResult.2.2.1
            let stateOf := claimResult.2.2.2
            let reduction := Reduction.mk (adversary.prover ck)
              (kzgScheme.opening (ck, vk)).verifier
            let (resultPairs : Option (Fin L → Bool × G₁)) ← reduction.allOutputs
              (fun ((transcript_data, verifier_accept) :
                (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
                (verifier_accept, transcript_data.1 0))
              (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
                (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                  OracleInterface.Response q))) stateOf
            return resultPairs.map (fun resultOf =>
              let accepts : Fin L → Bool := fun i => (resultOf i).1
              let proofs : Fin L → G₁ := fun i => (resultOf i).2
              mapFunctionBindingInstanceToArsdhInst hn
                (srs, cm, queryOf, responseOf, accepts, proofs))
          ))

/-- ARSDH condition for an adversary "to win" -/
def arsdhCond (D : ℕ) : (ZMod p × Finset (ZMod p) × G₁ × G₁) → Prop :=
  fun (τ, S, (h₁ : G₁), h₂) =>
    let Zₛ : CPolynomial (ZMod p) := ∏ s ∈ S, (X - C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / eval τ Zₛ).val

/-- Function binding condition for an adversary "to win" -/
def functionBindingCond (n L : ℕ) :
    (queryOf : Fin L → OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
      ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool) → Prop :=
  fun ⟨queryOf, responseOf, acceptedOf⟩ =>
    let S : Finset (Fin L) := Finset.univ
    (∀ i ∈ S, acceptedOf i = true)
    ∧ (¬ ∃ (d : Fin (n + 1) → ZMod p),
      ∀ i ∈ S, OracleInterface.answer d (queryOf i) = responseOf i)
    ∧ Function.Injective queryOf

/-- Extended function binding condition (taking more input values, logic unchanged) -/
def functionBindingCondExt (n L : ℕ) :
    (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) →
      Prop :=
  fun ⟨_, _, _, queryOf, responseOf, accepts, _proofs⟩ =>
    functionBindingCond n L ⟨queryOf, responseOf, accepts⟩

/-- Function binding game -/
def functionBindingGame {n L : ℕ} (AuxState : Type)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    (simulateQ (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp)) <|
        (do
          let (ck, vk) ← liftComp scheme.keygen _
          let ⟨cm, queryOf, responseOf, stateOf⟩ ← liftComp (adversary.claim ck) _
          let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
          let (accepts : Option (Fin L → Bool)) ← reduction.allVerdicts
            (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
              (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                OracleInterface.Response q))) stateOf
          pure (accepts.map (fun accepts => (⟨queryOf, responseOf, accepts⟩ :
              (queryOf : Fin L → OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool)))) :
          OracleComp _ _)).run' ∅

/-- Extended function binding game (returning more internal values, logic unchanged) -/
def functionBindingGameExt {n L : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :
    OptionT ProbComp (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    (simulateQ
      (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
      <|
      (do
        let τ ← liftComp ($ᵗ (ZMod p)) _
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
        let ⟨cm, queryOf, responseOf, stateOf⟩ ← liftComp (adversary.claim srs) _
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let (resultPairs : Option (Fin L → Bool × G₁)) ← reduction.allOutputs
          (fun ((transcript_data, verifier_accept) :
            (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
            (verifier_accept, transcript_data.1 0))
          (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))) stateOf
        let accepts : Option (Fin L → Bool) :=
          resultPairs.map (fun resultOf => fun i => (resultOf i).1)
        let proofs : Option (Fin L → G₁) :=
          resultPairs.map (fun resultOf => fun i => (resultOf i).2)
        pure (accepts.bind (fun accepts => proofs.map (fun proofs =>
          (τ, srs, cm, queryOf, ((fun i => responseOf i) : Fin L → ZMod p), accepts,
            proofs)))) :
        OracleComp _ _)).run' ∅

omit [DecidableEq G₁] in
/-- Transition 1: extending output for proofs and commitment preserves the condition -/
lemma function_binding_game_ext_eq_function_binding_game {n L : ℕ} {AuxState : Type}
    [SampleableType G₁]
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[functionBindingCond n L | functionBindingGame AuxState adversary
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Pr[functionBindingCondExt n L |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  -- Define the projection from the extended output tuple to the basic output tuple.
  let proj : (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) →
      ((queryOf : Fin L → OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
        ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool)) :=
    fun x => ⟨x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1⟩
  -- The extended condition factors through the projection.
  have hcond_eq :
      (functionBindingCondExt n L : _ → Prop) = (functionBindingCond n L) ∘ proj := by
    funext x
    rcases x with ⟨_, _, _, _, _, _, _⟩
    rfl
  rw [hcond_eq]
  -- Apply the OptionT bridge lemma with the run-level equality proved inline.
  apply OptionT.probEvent_eq_of_run_map_eq _ _ proj (functionBindingCond n L)
  -- The run-level equality relates the base game to the projected extended game.
  -- Step 1: unfold definitions to expose the computation structure.
  simp only [functionBindingGame, functionBindingGameExt, kzg, OptionT.run, OptionT.mk]
  -- Step 2: push (Option.map proj) <$> through run' and simulateQ on the RHS.
  rw [← StateT.run'_map_comm, ← simulateQ_map]
  -- Step 3: push the map through the bind chain using monad laws.
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, Function.comp]
  -- Step 4: the two sides now share the same bind prefix; match it with congr/funext.
  congr 1; funext τ
  -- Goal: simulateQ impl body₁ τ = simulateQ impl body₂_with_proj τ
  -- Get inside simulateQ to compare the OracleComp bodies.
  apply congr_fun
  apply congr_arg
  -- Goal: body₁ = body₂_with_proj as OracleComp expressions
  -- Match common bind: liftComp ($ᵗ ZMod p)
  congr 1; funext x
  -- Match common bind: adversary.claim (generateSrs n x)
  congr 1; funext x_1
  rw [Reduction.allVerdicts_eq_map_allOutputs_fst (fun result =>
    (result.1.1 0 : G₁))]
  simp only [map_eq_bind_pure_comp, bind_assoc, Option.map_bind]
  congr 1
  funext resultPairs
  cases resultPairs <;> rfl

-- helper lemmas for transition 2

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
lemma function_binding_game_ext_support_srs {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hgame : (τ, srs, cm, queryOf, responseOf, accepts, proofs) ∈
      support (functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)))) :
    srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ := by
  simp only [functionBindingGameExt, kzg] at hgame
  refine OptionT.aux_mem_support_simulateQ_run' _ _ _
    (fun y => y.2.1 = generateSrs (g₁ := g₁) (g₂ := g₂) n y.1) ?_ hgame
  intro x hx ⟨τ', srs', cm', queryOf', responseOf', accepts', proofs'⟩ hxeq
  rw [mem_support_bind_iff] at hx
  obtain ⟨τ_v, _, hx⟩ := hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨cm_v, queryOf_v, responseOf_v, stateOf_v⟩, _, hx⟩ := hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨opts_v, _, hx⟩ := hx
  rw [mem_support_pure_iff] at hx
  subst hx
  cases hres : opts_v with
  | none => simp [hres] at hxeq
  | some resultOf =>
      simp only [Option.bind, Option.map, hres, Option.some.injEq, Prod.mk.injEq]
        at hxeq
      obtain ⟨hτ, hsrs', _⟩ := hxeq
      simp [← hτ, ← hsrs']

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
lemma function_binding_game_ext_support_verify_all {n L : ℕ} {AuxState : Type}
    [SampleableType G₁]
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hgame : (τ, srs, cm, queryOf, responseOf, accepts, proofs) ∈
      support (functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)))) :
    ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
  simp only [functionBindingGameExt, kzg] at hgame
  intro i_idx hai
  let P : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁) → Prop :=
    fun y => y.2.2.2.2.2.1 i_idx = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        y.2.1.2 y.2.2.1 (y.2.2.2.2.2.2 i_idx) (y.2.2.2.1 i_idx)
          (y.2.2.2.2.1 i_idx)
  have hP : P (τ, srs, cm, queryOf, responseOf, accepts, proofs) := by
    refine OptionT.aux_mem_support_simulateQ_run' _ _ _ P ?_ hgame
    intro x hx ⟨τ', srs', cm', queryOf', responseOf', accepts', proofs'⟩ hxeq hai'
    rw [mem_support_bind_iff] at hx
    obtain ⟨τ_v, _, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨cm_v, queryOf_v, responseOf_v, stateOf_v⟩, _, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨opts_v, hopts, hx⟩ := hx
    rw [mem_support_pure_iff] at hx
    subst hx
    cases hres : opts_v with
    | none => simp [hres] at hxeq
    | some resultOf =>
      simp only [Option.bind, Option.map, hres, Option.some.injEq, Prod.mk.injEq] at hxeq
      obtain ⟨h_τ, h_srs, h_cm, h_q, h_r, h_a, h_p⟩ := hxeq
      obtain ⟨result, hresult, hres_eq⟩ :=
        Reduction.support_allOutputs_index
          (fun ((transcript_data, verifier_accept) :
            (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
            (verifier_accept, transcript_data.1 0))
          (fun i => (cm_v, (⟨queryOf_v i, responseOf_v i⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))) stateOf_v
          (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v,
               generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v)).verifier)
          hopts hres i_idx
      obtain ⟨td_data, va⟩ := result
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v,
               generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v).2 stmt.1
              (td ⟨0, by decide⟩) stmt.2.1 stmt.2.2)
          (by intros; rfl)
          (cm_v, ⟨queryOf_v i_idx, responseOf_v i_idx⟩)
          (stateOf_v i_idx)
          hresult rfl
      have hva_eq_v : va = (resultOf i_idx).1 := congrArg Prod.fst hres_eq
      have htd_eq_v : td_data.1 0 = (resultOf i_idx).2 := congrArg Prod.snd hres_eq
      have h_a_i : accepts' i_idx = (resultOf i_idx).1 := by
        have := congrFun h_a i_idx
        simpa using this.symm
      have h_p_i : proofs' i_idx = (resultOf i_idx).2 := by
        have := congrFun h_p i_idx
        simpa using this.symm
      have h_va_acc : va = accepts' i_idx := by rw [hva_eq_v, h_a_i]
      have h_td_prf : td_data.1 0 = proofs' i_idx := by rw [htd_eq_v, ← h_p_i]
      have hva_true : va = true := h_va_acc.trans hai'
      have h_q_i : queryOf' i_idx = queryOf_v i_idx := by
        have := congrFun h_q i_idx
        simpa using this.symm
      have h_r_i : responseOf' i_idx = responseOf_v i_idx := by
        have := congrFun h_r i_idx
        simpa using this.symm
      change KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs'.2 cm' (proofs' i_idx) (queryOf' i_idx) (responseOf' i_idx)
      rw [← h_srs, ← h_cm, ← h_td_prf, h_q_i, h_r_i]
      have heq : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v).2 cm_v
          (td_data.1 ⟨0, by decide⟩) (queryOf_v i_idx) (responseOf_v i_idx)
            = true := hverif.symm.trans hva_true
      exact heq
  exact hP hai

lemma nat_cast_range_card_zmod (hp : p ≥ n + 2) :
    ((Finset.range (n + 1)).image ((↑) : ℕ → ZMod p)).card = n + 1 := by
  have h_inj : Set.InjOn ((↑) : ℕ → ZMod p) ↑(Finset.range (n + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hap : a < p := lt_of_lt_of_le ha (by omega)
    have hbp : b < p := lt_of_lt_of_le hb (by omega)
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt hap, ZMod.val_natCast_of_lt hbp] at hv
  rw [Finset.card_image_of_injOn h_inj, Finset.card_range]

omit hp [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma find_query_with_srs_power_success {L : ℕ} (hn : 1 ≤ n)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (queryOf : Fin L → ZMod p) {α : ZMod p}
    (hfs : List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val
                      = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                  then some (queryOf i) else none)
        (List.finRange L) = some α) :
    srs.1[0] ^ α.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
  obtain ⟨_, i, _, _, hbody, _⟩ := List.findSome?_eq_some_iff.mp hfs
  by_cases hif : srs.1[0] ^ (queryOf i).val = srs.1[1]'(Nat.lt_add_of_pos_left hn)
  · rw [if_pos hif] at hbody
    simp only [Option.some.injEq] at hbody
    rw [← hbody]
    exact hif
  · rw [if_neg hif] at hbody
    exact absurd hbody (by simp)

omit [DecidableEq G₁] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma zmod_eq_of_srs_power_eq {α τ : ZMod p}
    (hn : 1 ≤ n) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hord : orderOf g₁ = p)
    (hpow : srs.1[0] ^ α.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) :
    α = τ := by
  have h_srs0 : srs.1[0] = g₁ := by
    rw [hsrs]
    simp [generateSrs, towerOfExponents]
  have h_srs1 : srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
    rw [hsrs]
    simp [generateSrs, towerOfExponents]
  have hpow' : g₁ ^ α.val = g₁ ^ τ.val := by
    rw [h_srs0, h_srs1] at hpow
    exact hpow
  have hmod : α.val ≡ τ.val [MOD orderOf g₁] := pow_eq_pow_iff_modEq.mp hpow'
  rw [hord] at hmod
  have h_eq : α.val = τ.val := by
    have hm : α.val % p = τ.val % p := hmod
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt α), Nat.mod_eq_of_lt (ZMod.val_lt τ)] at hm
  exact ZMod.val_injective p h_eq

omit hp [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma query_ne_tau_of_find_query_with_srs_power_none {L : ℕ}
    (hn : 1 ≤ n) (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (queryOf : Fin L → ZMod p)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hfs_none : List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val
                      = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                  then some (queryOf i) else none)
        (List.finRange L) = none) :
    ∀ i : Fin L, queryOf i ≠ τ := by
  intro i hqτ
  have hall := List.findSome?_eq_none_iff.mp hfs_none
  have h_at_i := hall i (List.mem_finRange i)
  have h_srs0 : srs.1[0] = g₁ := by
    rw [hsrs]
    simp [generateSrs, towerOfExponents]
  have h_srs1 : srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
    rw [hsrs]
    simp [generateSrs, towerOfExponents]
  have hpow : srs.1[0] ^ (queryOf i).val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [h_srs0, h_srs1, hqτ]
  simp [hpow] at h_at_i

lemma univ_interpolate_degree_ge_of_function_binding_cond {n L : ℕ}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool}
    (hFBcond : functionBindingCond n L ⟨queryOf, responseOf, accepts⟩) :
    (↑(n + 1) : WithBot ℕ) ≤
      (CLagrange.interpolate (Finset.univ : Finset (Fin L)) queryOf responseOf).degree := by
  by_contra hlt
  push Not at hlt
  set Q : Polynomial (ZMod p) :=
    Lagrange.interpolate (Finset.univ : Finset (Fin L)) queryOf responseOf with hQ_def
  have hquery : Function.Injective queryOf := hFBcond.2.2
  have hQdeg_lt : Q.degree < (↑(n + 1) : WithBot ℕ) := by
    have h := hlt
    rw [show
        (CLagrange.interpolate (Finset.univ : Finset (Fin L))
          queryOf responseOf).degree
          = Q.degree from by
          rw [hQ_def, ← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]] at h
    exact h
  have hQ_mem : Q ∈ Polynomial.degreeLT (ZMod p) (n + 1) :=
    Polynomial.mem_degreeLT.mpr hQdeg_lt
  apply hFBcond.2.1
  refine ⟨Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩, ?_⟩
  intro i _
  have hQ_eval : Q.eval (queryOf i) = responseOf i := by
    rw [hQ_def]
    exact Lagrange.eval_interpolate_at_node responseOf
      (hquery.injOn (s := (Finset.univ : Finset (Fin L)))) (Finset.mem_univ i)
  have hQ_sum :
      Q.eval (queryOf i) =
        ∑ k : Fin (n + 1),
          Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ k *
            (queryOf i) ^ (k : ℕ) :=
    Polynomial.eval_eq_sum_degreeLTEquiv hQ_mem (queryOf i)
  set d : Fin (n + 1) → ZMod p :=
    Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ with hd_def
  let P_C : CPolynomial (ZMod p) :=
    ⟨(CompPoly.CPolynomial.Raw.mk (Array.ofFn d)).trim,
      CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩
  change CPolynomial.eval (queryOf i) P_C = responseOf i
  rw [eval_toPoly]
  have hPC_eq : P_C.toPoly = Q := by
    apply Polynomial.ext
    intro k
    rw [← coeff_toPoly]
    change ((CompPoly.CPolynomial.Raw.mk (Array.ofFn d)).trim).coeff k = Q.coeff k
    rw [CompPoly.CPolynomial.Raw.Trim.coeff_eq_coeff]
    change (Array.ofFn d).getD k 0 = Q.coeff k
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    by_cases hk : k < n + 1
    · simp [hk, hd_def, Polynomial.degreeLTEquiv]
    · push Not at hk
      simp only [hk.not_gt, dite_false, Option.getD_none]
      symm
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hQdeg_lt (by exact_mod_cast hk))
  rw [hPC_eq]
  exact hQ_eval

lemma fin_length_gt_of_univ_interpolate_degree_ge {n L : ℕ}
    (queryOf : Fin L → ZMod p) (responseOf : Fin L → ZMod p)
    (hquery : Function.Injective queryOf)
    (huniv_deg : (↑(n + 1) : WithBot ℕ) ≤
      (CLagrange.interpolate (Finset.univ : Finset (Fin L)) queryOf responseOf).degree) :
    n + 1 < L := by
  have h_lt :=
    Lagrange.degree_interpolate_lt responseOf
      (hquery.injOn (s := (Finset.univ : Finset (Fin L))))
  have h_ge : (↑(n + 1) : WithBot ℕ) ≤
      (Lagrange.interpolate (Finset.univ : Finset (Fin L))
        queryOf responseOf).degree := by
    have h := huniv_deg
    rwa [show
        (CLagrange.interpolate (Finset.univ : Finset (Fin L))
          queryOf responseOf).degree
          = (Lagrange.interpolate (Finset.univ : Finset (Fin L))
              queryOf responseOf).degree from by
          rw [← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]] at h
  have h_card_gt :
      (↑(n + 1) : WithBot ℕ) < ((Finset.univ : Finset (Fin L)).card : WithBot ℕ) :=
    lt_of_le_of_lt h_ge h_lt
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_lt] at h_card_gt
  omega

include g₁ g₂ pairing in
lemma function_binding_cond_ext_output_maps_to_arsdh {n L : ℕ} {AuxState : Type}
    [SampleableType G₁]
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hgame : (τ, srs, cm, queryOf, responseOf, accepts, proofs) ∈
      support (functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))))
    (hFBcond : functionBindingCondExt n L (τ, srs, cm, queryOf, responseOf, accepts, proofs)) :
    ((arsdhCond n) ∘ mapFunctionBindingToArsdh hn)
      (τ, srs, cm, queryOf, responseOf, accepts, proofs) := by
  have hsrs : srs = generateSrs n τ (g₂ := g₂) (g₁ := g₁) := by
    exact function_binding_game_ext_support_srs (pairing := pairing) adversary hgame
  have hgen : srs.1[0] ≠ 1 := by
    rw [hsrs]
    simp only [generateSrs, towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn,
      pow_zero, pow_one, ne_eq]
    exact hg₁
  have hverify_all : ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
    exact function_binding_game_ext_support_verify_all (pairing := pairing) adversary hgame
  unfold mapFunctionBindingToArsdh
  unfold mapFunctionBindingInstanceToArsdhInst mapFunctionBindingInstanceToArsdhInstAux
  simp only [one_div, Finset.union_singleton, Option.pure_def, beq_iff_eq, Option.bind_eq_bind,
    Function.comp_apply]
  -- first branch from mapFunctionBindingInstanceToArsdhInstAux
  set fc := findConflict queryOf responseOf with hfc_def
  cases hfc : fc with
  | some c =>
      obtain ⟨i₁, i₂⟩ := c
      -- goal for the first branch
      simp only [arsdhCond, Option.getD_some, ne_eq, one_div]
      constructor
      · rw [← Finset.union_singleton]
        exact choose_s_conflict_size_adjoined hp hn (queryOf i₁) srs hgen
      · constructor
        · exact h1_ne_one (g₁ := g₁) (g₂ := g₂) hp PrimeOrderWith.hCard hn
            (queryOf i₁) τ srs hsrs hgen
        · -- h₂ = h₁ ^ (1 / Zₛᵤₐ.eval τ).val by `h1_zs_eq_h2`.
          have hfc' : findConflict queryOf responseOf = some (i₁, i₂) := hfc_def ▸ hfc
          have hαβ := find_conflict_successful queryOf responseOf hfc'
          obtain ⟨hα, hβ⟩ := hαβ
          have h_acc_all : ∀ i ∈ (Finset.univ : Finset (Fin L)), accepts i = true :=
            hFBcond.1
          have hai₁ : accepts i₁ = true := h_acc_all i₁ (Finset.mem_univ _)
          have hai₂ : accepts i₂ = true := h_acc_all i₂ (Finset.mem_univ _)
          have hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              srs.2 cm (proofs i₁) (queryOf i₁) (responseOf i₁) :=
            hverify_all i₁ hai₁
          have hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              srs.2 cm (proofs i₂) (queryOf i₂) (responseOf i₂) :=
            hverify_all i₂ hai₂
          have key := h1_zs_eq_h2 (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
            hp PrimeOrderWith.hCard hn (queryOf i₁) (queryOf i₂)
            (responseOf i₁) (responseOf i₂) τ cm (proofs i₁) (proofs i₂)
            hα hβ srs hsrs hgen hpair hverify₁ hverify₂
          simpa [Finset.union_singleton, one_div] using key
  | none => -- second branch from mapFunctionBindingInstanceToArsdhInstAux
      set fs := List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val = srs.1[1] then some (queryOf i) else none)
        (List.finRange L) with hfs_def
      cases hfs : fs with
      | some α₁ =>
          simp only [arsdhCond, Option.getD_some, ne_eq, one_div]
          -- branch where `List.findSome? = some α₁`
          -- Extract the precondition: `srs.1[0] ^ α₁.val = srs.1[1]`.
          have hfs' : List.findSome?
              (fun i ↦ if srs.1[0] ^ (queryOf i).val
                            = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                        then some (queryOf i) else none)
              (List.finRange L) = some α₁ := hfs_def.symm.trans hfs
          have hcond : srs.1[0] ^ α₁.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
            exact find_query_with_srs_power_success hn srs queryOf hfs'
          have hord : orderOf g₁ = p := order_of_eq_prime_of_ne_one g₁ hg₁
          have hα_τ : α₁ = τ := by
            exact zmod_eq_of_srs_power_eq (g₁ := g₁) hn srs hsrs hord hcond
          refine ⟨?_, ?_, ?_⟩
          · -- `S.card = n + 1`
            exact nat_cast_range_card_zmod hp
          · -- `srs.1[0] ≠ 1`
            exact hgen
          · -- `h₂ = h₁ ^ (1 / eval τ Zₛ).val`
            rw [hα_τ]
      | none => -- third branch from mapFunctionBindingInstanceToArsdhInstAux
          set fa := findA (n+1) queryOf responseOf with hfa_def
          -- The interpolation has degree ≥ n + 1, since otherwise its first n + 1
          -- coefficients would witness a degree-`n` polynomial fitting all pairs,
          -- contradicting the function-binding hypothesis `hFBcond`.
          have hquery : Function.Injective queryOf := hFBcond.2.2
          have huniv_deg : (↑(n + 1) : WithBot ℕ) ≤
              (CLagrange.interpolate (Finset.univ : Finset (Fin L))
                queryOf responseOf).degree := by
            exact univ_interpolate_degree_ge_of_function_binding_cond hFBcond
          have hL : n + 1 < L := by
            exact fin_length_gt_of_univ_interpolate_degree_ge queryOf responseOf hquery huniv_deg
          cases hfa : fa with
          | some a =>
              set fs' := findSPrime n a cm srs queryOf responseOf with hfs'_def
              cases hfs' : fs' with
              | some a' =>
                  -- third branch actual content (rest are irrelevant corner cases)
                  -- Recover the underlying option equalities from the `set`+`cases` shells.
                  have hresA : findA (n+1) queryOf responseOf = some a :=
                    hfa_def.symm.trans hfa
                  have hresS : findSPrime n a cm srs queryOf responseOf = some a' :=
                    hfs'_def.symm.trans hfs'
                  have hres_a' : some a' = findSPrime n a cm srs queryOf responseOf := hresS.symm
                  -- Reduce the do-block to its `some` value, then unfold `arsdhCond`.
                  simp only [hresS, Option.bind, arsdhCond, Option.getD_some,
                    ne_eq, one_div]
                  refine ⟨?_, ?_, ?_⟩
                  · -- `(a'.image queryOf).card = n + 1`
                    rw [Finset.card_image_of_injective _ hquery]
                    exact find_s_prime_card n cm a a' srs queryOf responseOf hres_a'
                  · -- `cm / c' ≠ 1`, equivalently `cm ≠ c'`, from `find_s_prime_diverges`.
                    intro hdiv
                    have hcm_eq_c' : cm =
                        commit srs.1
                          ((CLagrange.interpolate a' queryOf responseOf).val.coeff ∘ Fin.val) :=
                      div_eq_one.mp hdiv
                    exact (find_s_prime_diverges n cm a a' queryOf responseOf srs hres_a')
                      hcm_eq_c'.symm
                  · -- `h₂ = h₁ ^ (1 / Zₛ.eval τ).val`
                    -- Card and degree bound for `a'` (|a'| = n+1 ⇒ degree ≤ n).
                    have hcard : a'.card = n + 1 :=
                      find_s_prime_card n cm a a' srs queryOf responseOf hres_a'
                    have hdeg :
                        (CLagrange.interpolate a' queryOf responseOf).degree
                          ≤ (n : WithBot ℕ) := by
                      exact interp_degree_le_of_card a' queryOf responseOf hquery hcard
                    have ha'_ne : a'.Nonempty := by
                      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos _
                    -- Queries in `a'` cannot equal τ (else the second branch would have fired).
                    have hτneq : ∀ i ∈ a', queryOf i ≠ τ := by
                      have hfs_none :
                          List.findSome?
                            (fun i ↦ if srs.1[0] ^ (queryOf i).val
                                          = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                                      then some (queryOf i) else none)
                            (List.finRange L) = none := hfs_def.symm.trans hfs
                      intro i _
                      exact query_ne_tau_of_find_query_with_srs_power_none
                        (g₁ := g₁) hn τ srs queryOf hsrs hfs_none i
                    -- Every accepted index passes verification.
                    have hVer : ∀ i ∈ a',
                        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
                          srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
                      intro i _
                      exact hverify_all i (hFBcond.1 i (Finset.mem_univ _))
                    have key := h1_zs_eq_h2_prime (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
                      n τ cm a' queryOf responseOf proofs srs hn hsrs hτneq hVer
                      hgen hpair hdeg ha'_ne hquery
                    simp only [one_div] at key
                    exact key
              | none =>
                  -- `findSPrime` failed: contradicts `find_s_prime_successful`.
                  exfalso
                  have hres_a : some a = findA (n+1) queryOf responseOf := by
                    rw [← hfa_def]; exact hfa.symm
                  have hAdeg :=
                    find_a_deg (n+1) a queryOf responseOf hres_a
                  have hsome :=
                    find_s_prime_successful (g₁ := g₁) n τ cm a queryOf responseOf srs hsrs
                      hgen
                      (by exact_mod_cast hAdeg) hquery hn
                  have hnone :
                      findSPrime n a cm srs queryOf responseOf = none := by
                    rw [← hfs'_def]; exact hfs'
                  rw [hnone] at hsome
                  simp at hsome
          | none =>
              -- `findA` failed: contradicts `find_a_successful` via `huniv_deg`.
              exfalso
              have hsome :=
                find_a_successful (n+1) hL (Finset.univ : Finset (Fin L)) queryOf responseOf
                  hquery huniv_deg
              have hnone : findA (n+1) queryOf responseOf = none := by
                rw [← hfa_def]; exact hfa
              rw [hnone] at hsome
              simp at hsome

include g₁ g₂ pairing in
/-- Transition 2: FB condition implies ARSDH condition after mapping -/
lemma function_binding_cond_le_arsdh_cond {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[functionBindingCondExt n L |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(arsdhCond n) ∘ mapFunctionBindingToArsdh hn |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  apply probEvent_mono
  intro (τ, srs, cm, queryOf, responseOf, accepts, proofs) hgame hFBcond
  exact function_binding_cond_ext_output_maps_to_arsdh (pairing := pairing) hn hp hg₁ hpair
    adversary hgame hFBcond

omit [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event -/
lemma map_instance_drag {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :
    Pr[(arsdhCond n) ∘ mapFunctionBindingToArsdh hn |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[(arsdhCond n) |
      mapFunctionBindingToArsdh hn <$>
        functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

/-- Transition 4: the mapped game equals the ARSDH experiment -/
lemma arsdh_game_eq {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[(arsdhCond n) |
      mapFunctionBindingToArsdh hn <$> functionBindingGameExt (g₁ := g₁) (g₂ := g₂)
        AuxState adversary (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) := by
  let scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.arsdhExperiment]
  unfold arsdhCond
  simp only
  congr 1
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  simpa only [functionBindingGameExt, reduction, kzg, OptionT.mk, pSpec', impl, scheme,
      OptionT.run_map] using
    OptionT.map_mk_run'_simulateQ_bind_eq_of_body
      (impl := impl)
      (impl₀ := randomOracle)
      (oa := OracleComp.liftComp (($ᵗ (ZMod p)) : OracleComp unifSpec (ZMod p)) _)
      (oa₀ := (($ᵗ (ZMod p)) : OracleComp unifSpec (ZMod p)))
      (body₁ := fun τ => do
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
        let claimResult ← liftComp (adversary.claim srs) _
        let cm := claimResult.1
        let queryOf := claimResult.2.1
        let responseOf := claimResult.2.2.1
        let stateOf := claimResult.2.2.2
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let (resultPairs : Option (Fin L → Bool × G₁)) ← reduction.allOutputs
          (fun ((transcript_data, verifier_accept) :
            (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
            (verifier_accept, transcript_data.1 0))
          (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))) stateOf
        let accepts : Option (Fin L → Bool) :=
          resultPairs.map (fun resultOf => fun i => (resultOf i).1)
        let proofs : Option (Fin L → G₁) :=
          resultPairs.map (fun resultOf => fun i => (resultOf i).2)
        pure (accepts.bind (fun accepts => proofs.map (fun proofs =>
          (τ, srs, cm, queryOf, ((fun i => responseOf i) : Fin L → ZMod p), accepts, proofs))))
      )
      (body₂ := fun τ => do
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
        let claimResult ← liftComp (adversary.claim srs) _
        let cm := claimResult.1
        let queryOf := claimResult.2.1
        let responseOf := claimResult.2.2.1
        let stateOf := claimResult.2.2.2
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let (resultPairs : Option (Fin L → Bool × G₁)) ← reduction.allOutputs
          (fun ((transcript_data, verifier_accept) :
            (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
            (verifier_accept, transcript_data.1 0))
          (fun i => (cm, (⟨queryOf i, responseOf i⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))) stateOf
        return resultPairs.map (fun resultOf =>
          mapFunctionBindingInstanceToArsdhInst hn
            (srs, cm, queryOf, responseOf, (fun i => (resultOf i).1), (fun i => (resultOf i).2)))
      )
      (f := mapFunctionBindingToArsdh hn)
      (post := fun τ ((S, h₁, h₂) : Finset (ZMod p) × G₁ × G₁) => (τ, S, h₁, h₂))
      (s := (∅ : unifSpec.QueryCache))
      (hSample := by
        simp only [impl, pSpec', QueryImpl.addLift_def]
        rw [QueryImpl.simulateQ_add_liftComp_left]
        simp)
      (hBody := by
        intro τ
        simp only [simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        congr 1
        funext claimResult
        congr 1
        funext resultPairs
        cases resultPairs <;> rfl
      )

/-- The ARSDH experiment is bounded by the ARSDH error -/
lemma arsdh_error_bound {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (arsdhError : ℝ≥0)
    (hArsdh : Groups.arsdhAssumption (G₁ := G₁) (G₂ := G₂)
      (g₁ := g₁) (g₂ := g₂) n arsdhError)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) n (reduction (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) L hn AuxState adversary)
    ≤ arsdhError := by
  simp_all [Groups.arsdhAssumption]

omit [DecidableEq G₁] in
/-- The KZG scheme satisfies function binding provided ARSDH holds. -/
theorem function_binding {g₁ : G₁} {g₂ : G₂}
    (L : ℕ) (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0)
    [SampleableType G₁] (arsdhError : ℝ≥0)
    (hArsdh : Groups.arsdhAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n arsdhError) :
    Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle)
      (hn := rfl)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) arsdhError := by
  letI := Classical.decEq G₁
  letI scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.functionBinding]
  intro AuxState adversary
  letI game := functionBindingGame AuxState adversary scheme
  letI game_ext := functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[functionBindingCond n L | game]
    _ = Pr[functionBindingCondExt n L | game_ext] :=
      function_binding_game_ext_eq_function_binding_game (pairing := pairing) adversary
    _ ≤ Pr[(arsdhCond n) ∘ mapFunctionBindingToArsdh hn | game_ext] :=
      function_binding_cond_le_arsdh_cond (pairing := pairing) hn hp hg₁ hpair adversary
    _ = Pr[(arsdhCond n) | mapFunctionBindingToArsdh hn <$> game_ext] :=
      map_instance_drag hn adversary scheme
    _ = Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) :=
      arsdh_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn adversary
    _ ≤ arsdhError := arsdh_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn
      arsdhError hArsdh adversary)

end FunctionBinding

end CommitmentScheme

end KZG
