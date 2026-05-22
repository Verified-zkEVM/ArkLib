/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.FunctionBinding.Support

/-!
# Evaluation-Binding Conflict Branch for KZG Function Binding

Branch-specific choices and ARSDH extraction for two accepted openings at the same query with
different responses, following the ARSDH reduction in [CGKY25].

## Notation

* `chooseSConflict` chooses the conflict-branch support away from the repeated query.
* `conflictingEvaluationsArsdhOutput` builds the ARSDH output for this branch.
* `function_binding_conflicting_evaluations_branch_maps_to_arsdh` is the branch proof.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

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

/-- Local oracle interface for evaluating coefficient vectors as computable polynomials. -/
local instance functionBindingEvaluationConflictOracleInterface :
    OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

/-! ### Conflicting Evaluation Branch -/

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
/-- The filtered list used by `chooseSConflict` has no duplicate field elements. -/
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
/-- The conflict-branch candidate list contains at least `n` usable elements. -/
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
/-- `chooseSConflict` returns exactly `n` elements. -/
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
/-- The conflict point is not already included in `chooseSConflict`. -/
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
/-- Adjoining the conflict point to `chooseSConflict` gives a set of size `n + 1`. -/
lemma choose_s_conflict_size_adjoined (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hgen : srs.1[0] ≠ 1) :
    (chooseSConflict αᵢ srs hn ∪ {αᵢ}).card = n + 1 := by
  simp_all only [ge_iff_le, ne_eq, Finset.union_singleton, choose_s_conflict_alpha,
    not_false_eq_true, Finset.card_insert_of_notMem, choose_s_conflict_size]

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- The trapdoor `τ` is not in the conflict-branch support set. -/
lemma choose_s_conflict_tau (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ) :
    ¬ τ ∈ chooseSConflict αᵢ srs hn := by
  have hsrs_rel : srs.1[0] ^ τ.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [hsrs]; simp [Groups.PowerSrs.generate, Groups.PowerSrs.tower, Vector.getElem_ofFn]
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

/-- Evaluating after adjoining `α` multiplies by `τ - α`. -/
lemma prod_x_sub_c_insert_eval {S : Finset (ZMod p)} {α τ : ZMod p}
    (hαS : α ∉ S) :
    (∏ s ∈ S ∪ {α}, (X - C s : CPolynomial (ZMod p))).eval τ =
      (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ * (τ - α) := by
  rw [eval_toPoly, eval_toPoly, prod_x_sub_c_to_poly (S ∪ {α}), prod_x_sub_c_to_poly S,
    Finset.union_singleton, Finset.prod_insert hαS]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    _root_.mul_comm]

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- The conflict-branch adjoined vanishing product is nonzero at `τ`. -/
lemma choose_s_conflict_insert_eval_ne_zero (hn : 1 ≤ n) (α τ : ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ) (hατ : α ≠ τ) :
    (∏ s ∈ insert α (chooseSConflict α srs hn),
      (X - C s : CPolynomial (ZMod p))).eval τ ≠ 0 := by
  have hτS : τ ∉ chooseSConflict α srs hn :=
    choose_s_conflict_tau hn α τ srs hsrs
  have hτS_insert : τ ∉ insert α (chooseSConflict α srs hn) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hατ, hτS⟩
  exact prod_x_sub_c_eval_ne_zero hτS_insert

/-- The vanishing product over an `n`-element set has degree at most `n`. -/
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
/-- The conflict-branch base commitment is nontrivial. -/
lemma h1_ne_one (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
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
      simp_rw [hsrs, Groups.PowerSrs.generate]
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
    have hg₁ : g₁ ≠ 1 :=
      Groups.PowerSrs.generator_ne_one_of_generate (g₁ := g₁) (g₂ := g₂) hsrs hgen
    exact Groups.zmod_eq_zero_of_gpow_eq_one
      (Groups.orderOf_eq_prime_of_ne_one g₁ hg₁) heq

omit [DecidableEq G₁] in
/-- A genuine evaluation conflict cannot occur at the hidden trapdoor point. -/
lemma conflict_query_ne_tau (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n)
    (α₁ α₂ β₁ β₂ τ : ZMod p) (c pf₁ pf₂ : G₁) (hα : α₁ = α₂)
    (hβ : β₁ ≠ β₂) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 c pf₁ α₁ β₁)
    (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 c pf₂ α₂ β₂) :
    α₁ ≠ τ := by
  intro hατ
  have hg₁ : g₁ ≠ 1 :=
    Groups.PowerSrs.generator_ne_one_of_generate (g₁ := g₁) (g₂ := g₂) hsrs hgen
  have hord : orderOf g₁ = p := Groups.orderOf_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨cm, hc⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord c
  obtain ⟨prf₁, hprf₁⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord pf₁
  obtain ⟨prf₂, hprf₂⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord pf₂
  have hfield_verify₁ : cm = prf₁ * (τ - α₁) + β₁ := by
    grind [verify_opening_equation pairing α₁ β₁ τ cm prf₁ c pf₁ srs hsrs hpair
      hc hprf₁ hverify₁]
  have hfield_verify₂ : cm = prf₂ * (τ - α₁) + β₂ := by
    rw [← hα] at hverify₂
    grind [verify_opening_equation pairing α₁ β₂ τ cm prf₂ c pf₂ srs hsrs hpair
      hc hprf₂ hverify₂]
  have hfield_conflict : prf₁ * (τ - α₁) + β₁ = prf₂ * (τ - α₁) + β₂ := by
    simp_all
  apply hβ
  have hzero : τ - α₁ = 0 := by simp [hατ]
  simpa [hzero] using hfield_conflict

/-- The conflict-branch solution satisfies the ARSDH exponent equation. -/
lemma h1_zs_eq_h2 (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n)
    (α₁ α₂ β₁ β₂ τ : ZMod p) (c pf₁ pf₂ : G₁) (hα : α₁ = α₂)
    (hβ : β₁ ≠ β₂) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
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
    -- Prove RHS: `h₁ ^ (1 / Zₛᵤₐ.eval τ) = g₁ ^ (1 / (τ - α₁))`.
    have cardS : S.card = n := by exact choose_s_conflict_size hp hn α₁ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_zs cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, Groups.PowerSrs.generate]
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
    have hg₁ : g₁ ≠ 1 :=
      Groups.PowerSrs.generator_ne_one_of_generate (g₁ := g₁) (g₂ := g₂) hsrs hgen
    have hord : orderOf g₁ = p := Groups.orderOf_eq_prime_of_ne_one g₁ hg₁
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
    -- Prove LHS: `h₂ = g₁ ^ (1 / (τ - α₁))`.
    obtain ⟨cm, hc⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord c
    obtain ⟨prf₁, hprf₁⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord pf₁
    obtain ⟨prf₂, hprf₂⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord pf₂
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
      rw [Groups.gpow_div_eq hord, ← pow_mul, pow_eq_pow_iff_modEq, hord]
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

/-- ARSDH output for the conflicting-evaluations branch of the reduction. -/
def conflictingEvaluationsArsdhOutput {L : ℕ} (hn : 1 ≤ n)
    (tr : FunctionBindingExtTranscript (p := p) n L G₁ G₂) (i₁ i₂ : Fin L) :
    FunctionBindingArsdhOutput (p := p) G₁ :=
  let S := chooseSConflict (tr.queryOf i₁) tr.srs hn
  let Zₛ := ∏ s ∈ S, (X - C s)
  let h₁ := KZG.commit tr.srs.1 (Zₛ.coeff ∘ Fin.val)
  let h₂ : G₁ := (tr.proofs i₁ / tr.proofs i₂) ^
    (1 / (tr.responseOf i₂ - tr.responseOf i₁)).val
  { support := S ∪ {tr.queryOf i₁}, base := h₁, solution := h₂ }

include g₁ g₂ pairing in
/-- The conflicting-evaluations branch maps a function-binding violation to ARSDH. -/
lemma function_binding_conflicting_evaluations_branch_maps_to_arsdh {n L : ℕ}
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hpair : pairing g₁ g₂ ≠ 0)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1)
    (hverify_all : ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i))
    (hFBcond : functionBindingCondExt n L (τ, srs, cm, queryOf, responseOf, accepts, proofs))
    {i₁ i₂ : Fin L} (hfc : findConflict queryOf responseOf = some (i₁, i₂)) :
    Groups.arsdhCondition n
      (τ, (conflictingEvaluationsArsdhOutput (p := p) (G₂ := G₂) hn
        ({ srs := srs, cm := cm, queryOf := queryOf, responseOf := responseOf,
           accepts := accepts, proofs := proofs } :
          FunctionBindingExtTranscript (p := p) n L G₁ G₂) i₁ i₂).toTuple) := by
  simp only [conflictingEvaluationsArsdhOutput, FunctionBindingArsdhOutput.toTuple,
    Groups.arsdhCondition, ne_eq, one_div, Finset.union_singleton]
  have hαβ := find_conflict_successful queryOf responseOf hfc
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
  constructor
  · simpa [Finset.union_singleton] using
      choose_s_conflict_size_adjoined hp hn (queryOf i₁) srs hgen
  · constructor
    · have hα_ne_τ : queryOf i₁ ≠ τ :=
        conflict_query_ne_tau (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          PrimeOrderWith.hCard hn (queryOf i₁) (queryOf i₂)
          (responseOf i₁) (responseOf i₂) τ cm (proofs i₁) (proofs i₂)
          hα hβ srs hsrs hgen hpair hverify₁ hverify₂
      change (∏ s ∈ insert (queryOf i₁) (chooseSConflict (queryOf i₁) srs hn),
        (X - C s : CPolynomial (ZMod p))).eval τ ≠ 0
      exact choose_s_conflict_insert_eval_ne_zero
        (g₁ := g₁) (g₂ := g₂) hn (queryOf i₁) τ srs hsrs hα_ne_τ
    · constructor
      · exact h1_ne_one (g₁ := g₁) (g₂ := g₂) hp PrimeOrderWith.hCard hn
          (queryOf i₁) τ srs hsrs hgen
      · have key := h1_zs_eq_h2 (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          hp PrimeOrderWith.hCard hn (queryOf i₁) (queryOf i₂)
          (responseOf i₁) (responseOf i₂) τ cm (proofs i₁) (proofs i₂)
          hα hβ srs hsrs hgen hpair hverify₁ hverify₂
        simpa [Finset.union_singleton, one_div] using key

end FunctionBinding

end CommitmentScheme

end KZG
