/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.Correctness
import ArkLib.CommitmentScheme.HardnessAssumptions

set_option linter.style.longFile 2400

/-! ## Function binding for the KZG Polynomial Commitment Scheme -/

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ} -- the maximal degree of polynomials that can be commited to/opened.

open Commitment

local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding
/- In this section prove that the KZG is function binding under the ARSDH assumption. The proof is a
reduction to ARSDH following "Proof of Lemma 9.1" from Chiesa, Guan, Knabenhans, and Yu's "On the
Fiat–Shamir Security of Succinct Arguments from Functional Commitments"
(https://eprint.iacr.org/2025/902.pdf).
The paper proof is structured into 5 steps (with substeps), we note each step/substep accordingly in
our definitions.
-/

variable {η : Type} (advSpec : OracleSpec η)

/-- used to decide which strategy the adversary will take
(breaking ARSDH based on a conflict or breaking ARSDH based on lagrange interpolation) -/
def find_conflict (points : List (ZMod p × ZMod p × G₁))
  : Option ((ZMod p × ZMod p × G₁) × (ZMod p × ZMod p × G₁)) :=
  points.findSome? fun (α₁,β₁,pf₁) =>
    points.findSome? fun (α₂,β₂,pf₂) =>
      if α₁ == α₂ && β₁ != β₂ then some ((α₁,β₁, pf₁), (α₂,β₂, pf₂)) else none

omit [Fact (Nat.Prime p)] [DecidableEq G₁] [Fact (0 < p)] [Group G₁] in
lemma find_conflict_unsuccessful (points : List (ZMod p × ZMod p × G₁))
(hfc : find_conflict points = none)
: ¬(∃ a ∈ points, ∃ b ∈ points, a.1 == b.1 && a.2.1 ≠ b.2.1) := by
  unfold find_conflict at hfc
  rw [List.findSome?_eq_none_iff] at hfc
  simp only [List.findSome?_eq_none_iff] at hfc
  push Not
  intro ⟨α₁, β₁, pf₁⟩ ha ⟨α₂, β₂, pf₂⟩ hb hcond
  have hfc' := hfc (α₁, β₁, pf₁) ha (α₂, β₂, pf₂) hb
  simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true, ne_eq, decide_eq_true_eq] at hfc' hcond
  simp [hcond] at hfc'

-- case 1: there's conflicting evaluations (binding failure)

/- step 3 a) Choose S to be a size-(D + 1) subset of 𝔽 such that αᵢ∈ S and [Zₛ(τ)]₁ ≠ [0]₁
Note the reduction works mostly with S \ {αᵢ}, so this function only returns S \ {αᵢ}. -/
def choose_S_conflict (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hn : 1 ≤ n) : Finset (ZMod p) :=
  let arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x else none
    else none
  arr.take n |>.toList.toFinset -- ∪ {αᵢ} to be the S referenced in the paper

omit [Fact (0 < p)] [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma filterMap_conflict_nodup
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
  -- Simplify: both must hit the `some x` branch, giving b = ↑↑⟨a, ha⟩ and b = ↑↑⟨a', ha'⟩
  simp only [ha, ha', dite_true] at hb hb'
  split at hb <;> simp at hb
  split at hb' <;> simp at hb'
  -- hb : ↑↑⟨a, ha⟩ = b, hb' : ↑↑⟨a', ha'⟩ = b
  have hval := congr_arg ZMod.val (hb.trans hb'.symm)
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hval
  exact hval

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma filterMap_conflict_length (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1) :
    ((Array.range p).filterMap fun i =>
      if h : i < p then
        let x : ZMod p := (⟨i, h⟩ : Fin p)
        if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
        else none
      else none).size ≥ n := by
  /- the main insight for this proof is the following:
    1. the array (Array.range p) is distinct and of size p.
    2. the if condition can be false for at most 2 values: one value that does not match the srs
      and one value that is equal to αᵢ
    3. since p ≥ n + 2, we can tolerate removing at most 2 values from the array
      (via the if statement) and still have at least n values remaining (to take).
    -/
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  -- Convert Array.size to Finset.card via Nodup
  have hnodup : arr.toList.Nodup := filterMap_conflict_nodup αᵢ srs hn
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

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_size (hp : p ≥ n + 2) (hn : 1 ≤ n)
  (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1)
  : (choose_S_conflict αᵢ srs hn).card = n := by
  unfold choose_S_conflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  have hnodup : arr.toList.Nodup := filterMap_conflict_nodup αᵢ srs hn
  have hsize : arr.size ≥ n := filterMap_conflict_length hp hn αᵢ srs hgen
  have htoList : (arr.take n).toList = arr.toList.take n := by
    simp [Array.take]
  rw [List.toFinset_card_of_nodup]
  · rw [htoList, List.length_take, Array.length_toList]
    omega
  · rw [htoList]
    exact (List.take_sublist n arr.toList).nodup hnodup

omit [Fact (0 < p)] [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_αᵢ (hn : 1 ≤ n) (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  : ¬ αᵢ ∈ choose_S_conflict αᵢ srs hn := by
  unfold choose_S_conflict
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

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_size_adjoined (hp : p ≥ n + 2) (hn : 1 ≤ n)
  (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1)
  : (choose_S_conflict αᵢ srs hn ∪ {αᵢ}).card = n+1 := by
  simp_all only [ge_iff_le, ne_eq, Finset.union_singleton, choose_S_conflict_αᵢ, not_false_eq_true,
    Finset.card_insert_of_notMem, choose_S_conflict_size]

omit [Fact (0 < p)] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_τ (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
  : ¬ τ ∈ choose_S_conflict αᵢ srs hn := by
  have hsrs_rel : srs.1[0] ^ τ.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [hsrs]; simp [generateSrs, towerOfExponents, Vector.getElem_ofFn]
  unfold choose_S_conflict
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

omit [Fact (0 < p)] in
private lemma prod_X_sub_C_toPoly (S : Finset (ZMod p)) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).toPoly =
      ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
  have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
  simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]

omit [Fact (0 < p)] in
private lemma prod_X_sub_C_eval_ne_zero {S : Finset (ZMod p)} {τ : ZMod p}
    (hτS : τ ∉ S) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ ≠ 0 := by
  rw [eval_toPoly, prod_X_sub_C_toPoly S, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro s hs
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact fun h => hτS (by simpa [sub_eq_zero.mp h])

omit [Fact (0 < p)] in
private lemma prod_X_sub_C_insert_eval {S : Finset (ZMod p)} {α τ : ZMod p}
    (hαS : α ∉ S) :
    (∏ s ∈ S ∪ {α}, (X - C s : CPolynomial (ZMod p))).eval τ =
      (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ * (τ - α) := by
  rw [eval_toPoly, eval_toPoly, prod_X_sub_C_toPoly (S ∪ {α}), prod_X_sub_C_toPoly S,
    Finset.union_singleton, Finset.prod_insert hαS]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    _root_.mul_comm]

omit [DecidableEq G₁] [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
private lemma orderOf_eq_prime_of_ne_one (x : G₁) (hx : x ≠ 1) : orderOf x = p := by
  have hdvd := orderOf_dvd_natCard (G := G₁) x
  rw [PrimeOrderWith.hCard] at hdvd
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.1 h1) hx
  · exact hp'

omit [Fact (0 < p)] [DecidableEq G₁] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
private lemma g₁_ne_one_of_srs_gen (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1) :
    g₁ ≠ 1 := by
  rw [hsrs] at hgen
  simpa [generateSrs, towerOfExponents] using hgen

omit [DecidableEq G₁] [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
private lemma zmod_eq_zero_of_gpow_eq_one (hord : orderOf g₁ = p) {a : ZMod p}
    (ha : g₁ ^ a.val = 1) : a = 0 := by
  have hdvd := orderOf_dvd_of_pow_eq_one ha
  rw [hord] at hdvd
  apply ZMod.val_injective p
  have hval : a.val = 0 := by
    by_contra h
    exact absurd (ZMod.val_lt a) (not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hdvd))
  simpa using hval

omit [DecidableEq G₁] [Fact (0 < p)] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- If two ℕ exponents are equal when cast to `ZMod p`, then `g₁` raised to each is the same. -/
lemma gpow_eq_of_natCast_eq (hord : orderOf g₁ = p) (a b : ℕ)
    (hab : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) : g₁ ^ a = g₁ ^ b := by
  conv_lhs => rw [← pow_mod_orderOf, hord]
  conv_rhs => rw [← pow_mod_orderOf, hord]
  congr 1
  have := congr_arg ZMod.val hab
  rwa [ZMod.val_natCast, ZMod.val_natCast] at this

omit [DecidableEq G₁] [Fact (0 < p)] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- Group division of powers equals the power of the `ZMod p` difference. -/
lemma gpow_div_eq (hord : orderOf g₁ = p) (a b : ZMod p) :
    g₁ ^ a.val / g₁ ^ b.val = g₁ ^ (a - b).val := by
  rw [div_eq_iff_eq_mul, ← pow_add]
  exact gpow_eq_of_natCast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)

omit [DecidableEq G₁] [Fact (0 < p)] [PrimeOrderWith G₁ p]
  [Module (ZMod p) (Additive G₁)] in
/-- Product of `.val`s as exponent equals `ZMod p` product's `.val` as exponent. -/
lemma gpow_val_mul_eq (hord : orderOf g₁ = p) (a b : ZMod p) :
    g₁ ^ (a.val * b.val) = g₁ ^ (a * b).val :=
  gpow_eq_of_natCast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)

omit [DecidableEq G₁] [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
private lemma exists_zmod_power_of_generator (hpG1 : Nat.card G₁ = p) (hg₁ : g₁ ≠ 1)
    (hord : orderOf g₁ = p) (x : G₁) : ∃ a : ZMod p, x = g₁ ^ a.val := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g₁ ^ k = x := mem_powers_of_prime_card hpG1 hg₁
  exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, ← hk, ← pow_mod_orderOf g₁ k, hord]⟩

omit [Fact (0 < p)] in
lemma deg_of_Zₛ {S : Finset (ZMod p)} (hcardS : S.card = n) :
  (∏ s ∈ S, (X - C s)).degree ≤ ↑n := by
  rw [degree_toPoly, prod_X_sub_C_toPoly S]
  apply Polynomial.degree_le_of_natDegree_le
  calc (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree
      ≤ ∑ s ∈ S, (Polynomial.X - Polynomial.C s).natDegree :=
        Polynomial.natDegree_prod_le S _
    _ = S.card := by simp
    _ = n := hcardS


omit [Fact (0 < p)] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma h₁_not_zero (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
  (hgen : srs.1[0] ≠ 1)
  : let S := choose_S_conflict αᵢ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    h₁ ≠ 1 := by
    intro S Zₛ h₁
    have cardS : S.card = n := by exact choose_S_conflict_size hp hn αᵢ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_Zₛ cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_CPolynomial hpG1 Zₛ Zₛ_deg]
    have hτS : ¬ τ ∈ S := by
      unfold S
      exact choose_S_conflict_τ hn αᵢ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      exact prod_X_sub_C_eval_ne_zero hτS
    rw [hh₁]
    intro heq
    apply hZₛeval
    exact zmod_eq_zero_of_gpow_eq_one
      (orderOf_eq_prime_of_ne_one g₁ (g₁_ne_one_of_srs_gen τ srs hsrs hgen)) heq

lemma h₁Zₛ_eq_h₂ (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n) (α₁ α₂ β₁ β₂ τ : ZMod p)
  (c pf₁ pf₂ : G₁) (hα : α₁ = α₂) (hβ : β₁ ≠ β₂) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1)
  (hpair : pairing g₁ g₂ ≠ 0)
  (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing) srs.2 c pf₁ α₁ β₁)
  (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing) srs.2 c pf₂ α₂ β₂) :
    let S := choose_S_conflict α₁ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 / (β₂ - β₁)).val
    let Zₛᵤₐ := ∏ s ∈ S ∪ {α₁} , (X - C s)
    h₂ = h₁ ^ (1 / Zₛᵤₐ.eval τ).val := by
    intro S Zₛ h₁ h₂ Zₛᵤₐ
    /-prove rhs: h₁ ^ (1 / Zₛᵤₐ.eval τ) = g₁ ^ (1 / (τ - α₁)) -/
    have cardS : S.card = n := by exact choose_S_conflict_size hp hn α₁ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_Zₛ cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_CPolynomial hpG1 Zₛ Zₛ_deg]
    have hα₁S : α₁ ∉ S := choose_S_conflict_αᵢ hn α₁ srs
    have hτS : ¬ τ ∈ S := choose_S_conflict_τ hn α₁ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      exact prod_X_sub_C_eval_ne_zero hτS
    have hZsua_eval : Zₛᵤₐ.eval τ = Zₛ.eval τ * (τ - α₁) := by
      unfold Zₛᵤₐ Zₛ
      exact prod_X_sub_C_insert_eval hα₁S
    have hrhsfield : Zₛ.eval τ * (1 / Zₛᵤₐ.eval τ) = 1 / (τ - α₁) := by
      rw [hZsua_eval, one_div, one_div, mul_inv_rev,
        show (τ - α₁)⁻¹ * (Zₛ.eval τ)⁻¹ = (Zₛ.eval τ)⁻¹ * (τ - α₁)⁻¹ from _root_.mul_comm _ _,
        ← _root_.mul_assoc, mul_inv_cancel₀ hZₛeval, _root_.one_mul]
    have hg₁ : g₁ ≠ 1 := g₁_ne_one_of_srs_gen τ srs hsrs hgen
    have hord : orderOf g₁ = p := orderOf_eq_prime_of_ne_one g₁ hg₁
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
      grind [verifyOpening_equation pairing α₁ β₁ τ cm prf₁ c pf₁ srs hsrs hpair hverify₁ hc hprf₁]
    have hfield_verify₂ : cm = prf₂ * (τ - α₁) + β₂ := by
      rw [← hα] at hverify₂
      grind [verifyOpening_equation pairing α₁ β₂ τ cm prf₂ c pf₂ srs hsrs hpair hverify₂ hc hprf₂]
    have hfield_conflict : prf₁ * (τ - α₁) + β₁ = prf₂ * (τ - α₁) + β₂ := by simp_all
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

/-- step 4a) find A ⊆ {αᵢ,βᵢ,pfᵢ}, i ∈ [L], such that Lagrange(A).degree = n -/
def find_A {L : ℕ} (n : ℕ) (query : Fin L → ZMod p) (response : Fin L → ZMod p)
  : Option (Finset (Fin L)) :=
    let candidateslist := (List.finRange L).sublistsLen (n+1)
    let candidates := candidateslist.map List.toFinset
    candidates.find? fun s => (CLagrange.interpolate s query response).degree = n

omit [Fact (0 < p)] in
lemma find_A_card {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p) (hres : some (A) = find_A n query response)
  : A.card = n+1 := by
  unfold find_A at hres
  have hmem := List.mem_of_find?_eq_some hres.symm
  rw [List.mem_map] at hmem
  obtain ⟨l, hl_mem, hl_eq⟩ := hmem
  rw [List.mem_sublistsLen] at hl_mem
  obtain ⟨hl_sub, hl_len⟩ := hl_mem
  rw [← hl_eq, List.toFinset_card_of_nodup ((List.nodup_finRange L).sublist hl_sub), hl_len]

omit [Fact (0 < p)] in
lemma find_A_deg {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p)
  (hres : some (A) = find_A n query response)
  : (CLagrange.interpolate A query response).degree = n := by
  unfold find_A at hres
  have hpred := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at hpred
  exact hpred

private lemma sorted_finset_sort_sublist_finRange {L : ℕ} (s : Finset (Fin L)) :
    List.Sublist (s.sort (· ≤ ·)) (List.finRange L) :=
  List.sublist_of_subperm_of_sortedLE
    ((Finset.sort_nodup (s := s) (r := (· ≤ ·))).subperm (fun _ _ => List.mem_finRange _))
    (Finset.sortedLT_sort s).sortedLE
    (List.sortedLT_finRange L).sortedLE

private lemma finset_mem_sublistsLen_map {L : ℕ} (s : Finset (Fin L)) (hn : s.card = n + 1) :
    s ∈ ((List.finRange L).sublistsLen (n + 1)).map List.toFinset := by
  rw [List.mem_map]
  exact ⟨s.sort (· ≤ ·), List.mem_sublistsLen.mpr
    ⟨sorted_finset_sort_sublist_finRange s,
     by rw [Finset.length_sort]; exact hn⟩,
    Finset.sort_toFinset (s := s) (r := (· ≤ ·))⟩

omit [Fact (0 < p)] in
private lemma interp_degree_le_of_card {L : ℕ} (s : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hquery : Function.Injective query) (hn : s.card = n + 1) :
    (CLagrange.interpolate s query response).degree ≤ ↑n := by
  rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate]
  have hle : (Lagrange.interpolate s query response).degree ≤ ↑(s.card - 1) :=
    Lagrange.degree_interpolate_le response hquery.injOn
  simp only [hn, Nat.add_sub_cancel] at hle
  exact hle

omit [Fact (0 < p)] in
lemma find_A_successful {L : ℕ} (n : ℕ) (hL : n < L) (S : Finset (Fin L)) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p) (hquery : Function.Injective query)
  (hinterp : (CLagrange.interpolate S query response).degree ≥ n)
  : (find_A n query response).isSome := by
  by_contra h_not
  have h_none : find_A n query response = none := by
    match hc : find_A n query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold find_A at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq] at h_none
  have h_deg_lt : ∀ (s : Finset (Fin L)), s.card = n + 1 →
      (CLagrange.interpolate s query response).degree < ↑n := by
    intro s hs
    exact lt_of_le_of_ne (interp_degree_le_of_card s query response hquery hs)
      (h_none s (finset_mem_sublistsLen_map s hs))
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

/-- step 4b) Assume A has size n+1, check all n-sized subsets of A until you find a
subset whose interpolation commitment differs from the adversaries commitment c. -/
def find_S' {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (c : G₁)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p)
  : Option (Finset (Fin L)) :=
    let candidateslist := (A.sort (· ≤ ·)).sublistsLen (n+1)
    let candidates := candidateslist.map List.toFinset
    candidates.find? fun s =>
      commit srs.1 ((CLagrange.interpolate s query response).val.coeff ∘ Fin.val) ≠ c

omit [Fact (0 < p)] in
lemma find_S'_existence {L : ℕ} (n : ℕ) (τ c : ZMod p) (A : Finset (Fin L))
  (query : Fin L → ZMod p) (response : Fin L → ZMod p)
  (hA : (CLagrange.interpolate A query response).degree = n + 1)
  (hquery : Function.Injective query)
  (hn : 1 ≤ n)
  : ∃ S ⊆ A, S.card = n + 1
  ∧ (CLagrange.interpolate S query response).eval τ ≠ c
  := by
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
  obtain ⟨A', hA'_sub, hA'_card⟩ := Finset.exists_subset_card_eq (show n + 2 ≤ A.card by omega)
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

private lemma sorted_finset_sort_sublist_sort {L : ℕ} (S A : Finset (Fin L)) (hSA : S ⊆ A) :
    List.Sublist (S.sort (· ≤ ·)) (A.sort (· ≤ ·)) :=
  List.sublist_of_subperm_of_sortedLE
    ((Finset.sort_nodup (s := S) (r := (· ≤ ·))).subperm
      (fun x hx => by simpa using hSA (by simpa using hx)))
    (Finset.sortedLT_sort S).sortedLE
    (Finset.sortedLT_sort A).sortedLE

private lemma finset_subset_mem_sublistsLen_map {L : ℕ} (S A : Finset (Fin L))
    (hSA : S ⊆ A) (hn : S.card = n) :
    S ∈ ((A.sort (· ≤ ·)).sublistsLen n).map List.toFinset := by
  rw [List.mem_map]
  exact ⟨S.sort (· ≤ ·), List.mem_sublistsLen.mpr
    ⟨sorted_finset_sort_sublist_sort S A hSA,
     by rw [Finset.length_sort]; exact hn⟩,
    Finset.sort_toFinset (s := S) (r := (· ≤ ·))⟩

omit [Fact (0 < p)] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma find_S'_successful {L : ℕ} (n : ℕ) (τ : ZMod p) (c : G₁) (A : Finset (Fin L))
  (query : Fin L → ZMod p) (response : Fin L → ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1)
  (hA : (CLagrange.interpolate A query response).degree = n + 1)
  (hquery : Function.Injective query) (hn : 1 ≤ n)
  : (find_S' n A c srs query response).isSome := by
  by_contra h_not
  have h_none : find_S' n A c srs query response = none := by
    match hc : find_S' n A c srs query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold find_S' at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq, not_not] at h_none
  have hg₁ : g₁ ≠ 1 := g₁_ne_one_of_srs_gen τ srs hsrs hgen
  have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
  have hord : orderOf g₁ = p := orderOf_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨c', hc_eq⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord c
  -- For every candidate S, commit = c means eval τ = c'
  have h_all_eq : ∀ S ⊆ A, S.card = n + 1 →
      (CLagrange.interpolate S query response).eval τ = c' := by
    intro S hSA hScard
    -- S is in the candidate list
    have hS_mem := finset_subset_mem_sublistsLen_map S A hSA hScard
    -- The hypothesis says commit = c for S
    have hcommit_eq := h_none S hS_mem
    -- Degree bound for interpolation over S
    have hdeg : (CLagrange.interpolate S query response).degree ≤ ↑n :=
      interp_degree_le_of_card S query response hquery hScard
    -- Rewrite commit using commit_eq_CPolynomial
    have hcommit_rw : commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val)
        = g₁ ^ ((CLagrange.interpolate S query response).eval τ).val := by
      conv_lhs => rw [hsrs, generateSrs]
      exact commit_eq_CPolynomial (g₁ := g₁) hpG1
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
  -- But find_S'_existence gives an S with eval τ ≠ c'
  obtain ⟨S₀, hS₀_sub, hS₀_card, hS₀_ne⟩ := find_S'_existence n τ c' A query response hA hquery hn
  exact hS₀_ne (h_all_eq S₀ hS₀_sub hS₀_card)

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma find_S'_card
  {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p) (hres : some (S) = find_S' n A c srs query response)
  : S.card = n + 1 := by
    unfold find_S' at hres
    have hS_mem := List.mem_of_find?_eq_some hres.symm
    rw [List.mem_map] at hS_mem
    obtain ⟨l, hl_mem, hl_eq⟩ := hS_mem
    rw [List.mem_sublistsLen] at hl_mem
    obtain ⟨hl_sub, hl_len⟩ := hl_mem
    rw [← hl_eq, List.toFinset_card_of_nodup ((A.sort_nodup (· ≤ ·)).sublist hl_sub), hl_len]

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma find_S'_diverges
  {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
  (query : Fin L → ZMod p) (response : Fin L → ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hres : some (S) = find_S' n A c srs query response)
  : commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val) ≠ c := by
  unfold find_S' at hres
  have h := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at h
  exact h

-- TODO should be in CompPoly?
omit [Fact (0 < p)] in
lemma interpolation_of_constants {L : ℕ} (S : Finset (Fin L))
  (query : Fin L → ZMod p) (response : Fin L → ZMod p)
  (c : ZMod p) (hresp : ∀ i ∈ S, response i = c)
  (hquery : Function.Injective query) (hS : S.Nonempty) :
CLagrange.interpolate S query response = (C c) := by
  suffices h : (CLagrange.interpolate S query response).toPoly = (C c).toPoly from
    ringEquiv.injective h
  rw [CLagrange.cinterpolate_eq_interpolate, C_toPoly]
  symm
  exact Lagrange.eq_interpolate_of_eval_eq response hquery.injOn
    (lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Finset.card_pos.mpr hS))
    (fun i hi => by simp [hresp i hi])

omit [Fact (0 < p)] in
private lemma Zₛ_toPoly_eq_nodal {L : ℕ} (S : Finset (Fin L))
    (query : Fin L → ZMod p) (hquery : Function.Injective query) :
    (∏ s ∈ S.image query, (X - C s) : CPolynomial (ZMod p)).toPoly
      = Lagrange.nodal S query := by
  rw [toPoly_prod]
  simp only [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
  rw [Lagrange.nodal_eq]
  exact Finset.prod_image (f := fun s => Polynomial.X - Polynomial.C s)
    (hquery.injOn (s := ↑S))

omit [Fact (0 < p)] in
private lemma divByMonic_Zₛ_toPoly_eq_nodal_erase {L : ℕ}
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
  rw [CPolynomial.toPoly_divByMonic _ _ hmonic, Zₛ_toPoly_eq_nodal S query hquery, hq_toPoly,
    Lagrange.nodal_eq_mul_nodal_erase hi]
  exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)

omit [Fact (0 < p)] in
lemma lagrange_Zₛ_conversion {L : ℕ} (τ : ZMod p) (S : Finset (Fin L)) (query : Fin L → ZMod p)
  (response : Fin L → ZMod p) (hτ : ∀ i ∈ S, (query i) ≠ τ) (hquery : Function.Injective query)
  : let Zₛ := ∏ s ∈ S.image query, (X - C s)
  ((CLagrange.interpolate S query response).eval τ) / (Zₛ.eval τ)
  = ∑ x ∈ S, response x / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)) := by
  intro Zₛ
  -- Derive τ ≠ query i (Mathlib direction)
  have hτ' : ∀ i ∈ S, τ ≠ query i := fun i hi => Ne.symm (hτ i hi)
  -- Convert CPolynomial evals to Polynomial evals
  have hZₛ_toPoly : Zₛ.toPoly = Lagrange.nodal S query := Zₛ_toPoly_eq_nodal S query hquery
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
    rw [eval_toPoly, divByMonic_Zₛ_toPoly_eq_nodal_erase S query hquery i hi]
  rw [hdiv_eval]
  -- Field algebra: a⁻¹ * b⁻¹ * c = c / (a * b)
  have heval_ne : Polynomial.eval (query i) (Lagrange.nodal (S.erase i) query) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun j hj =>
      fun h => (Finset.ne_of_mem_erase hj) (hquery h.symm))
  have hτqi_ne : τ - query i ≠ 0 := sub_ne_zero.mpr (hτ' i hi)
  field_simp

omit [DecidableEq G₁] in
lemma h₁Zₛ_eq_h₂' {L : ℕ} (n : ℕ) (τ : ZMod p) (cm : G₁) (S : Finset (Fin L))
  (query : Fin L → ZMod p) (response : Fin L → ZMod p) (proofs : Fin L → G₁)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hn : 1 ≤ n)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hτ : ∀ i ∈ S, (query i) ≠ τ)
  (hVerify : ∀ i ∈ S, verifyOpening (pairing := pairing) (g₁ := g₁) (g₂ := g₂) srs.2 cm (proofs i)
    (query i) (response i))
  (hgen : srs.1[0] ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
  (hS : (CLagrange.interpolate S query response).degree ≤ n) (hS_ne : S.Nonempty)
  (hquery : Function.Injective query)
  : let Zₛ := ∏ s ∈ S.image query, (X - C s)
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
      exact commit_eq_CPolynomial (g₁ := g₁) hpG1
        (CLagrange.interpolate S query response) hS
    rw [hcommit_rw]
    have hg₁ : g₁ ≠ 1 := g₁_ne_one_of_srs_gen τ srs hsrs hgen
    have hord : orderOf g₁ = p := orderOf_eq_prime_of_ne_one g₁ hg₁
    obtain ⟨cm', hcm⟩ := exists_zmod_power_of_generator hpG1 hg₁ hord cm
    have hproofs_pow : ∀ i, ∃ prf : ZMod p, proofs i = g₁ ^ prf.val := by
      intro i
      exact exists_zmod_power_of_generator hpG1 hg₁ hord (proofs i)
    choose prf hprf using hproofs_pow
    rw [hcm]
    simp_rw [hprf]
    have hprf_eq : ∀ i ∈ S, prf i = (cm' - response i) / (τ - query i) := by
      intro i hi
      exact verifyOpening_prf_equation pairing (query i) (response i) τ cm' (prf i)
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
    -- Rewrite the response sum using lagrange_Zₛ_conversion
    rw [← lagrange_Zₛ_conversion τ S query response hτ hquery]
    -- Factor cm' from the first sum and simplify to cm' / Zₛ.eval τ
    have hcm_sum : (∑ x ∈ S,
        cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      = cm' / Zₛ.eval τ := by
      have h1 : ∀ x ∈ S, cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))
        = cm' * (1 / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) :=
        fun _ _ => by ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
        ← lagrange_Zₛ_conversion τ S query (fun _ => 1) hτ hquery,
        interpolation_of_constants S query (fun _ => 1) 1 (fun _ _ => rfl) hquery hS_ne]
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
    -- Now: g₁ ^ ((cm' - r) * (1/z)).val = g₁ ^ (cm'.val * (1/z).val) / g₁ ^ (r.val * (1/z).val)
    rw [gpow_val_mul_eq hord cm' (1 / z), gpow_val_mul_eq hord r (1 / z), gpow_div_eq hord]
    congr 1
    exact congr_arg ZMod.val (by ring : (cm' - r) * (1 / z) = cm' * (1 / z) - r * (1 / z))

-- put all steps together

/-- These are steps 3 and 4 of the reduction listed in the paper (Proof of Lemma 9.1
in https://eprint.iacr.org/2025/902.pdf) -/
def map_FB_instance_to_ARSDH_inst' {L : ℕ} (hn : 1 ≤ n)
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁))
  : Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let (srs, cm, queryOf, responseOf, _accepts, proofs) := val
  let points := List.ofFn (fun (i : Fin L) => (queryOf i, responseOf i, proofs i))
  -- TODO update find conflicts to use index maps instead of points lists
  if let some ((α₁,β₁,pf₁),(α₂,β₂,pf₂)) := find_conflict points then
    -- step 3
    let S := choose_S_conflict α₁ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 / (β₂ - β₁)).val
    return (S ∪ {α₁}, h₁, h₂)
  else if -- Additional Subcase: find τ in queries
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
    let A ← find_A (n+1) queryOf responseOf
    let S ← find_S' n A cm srs queryOf responseOf
    let Zₛ := ∏ s ∈ S.image queryOf, (X - C s)
    let c' : G₁ :=
      commit srs.1 ((CLagrange.interpolate S queryOf responseOf).val.coeff ∘ Fin.val)
    let h₁ := cm / c'
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ i ∈ S, (proofs i) ^ (d (queryOf i)).val
    return (S.image queryOf, h₁, h₂)

def map_FB_instance_to_ARSDH_inst {L : ℕ} (hn : 1 ≤ n)
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁))
  : (Finset (ZMod p) × G₁ × G₁)
  -- for instances that break function binding map_FB_instance_to_ARSDH_inst' should always
  -- be 'Some'
  := Option.getD (map_FB_instance_to_ARSDH_inst' hn val) (∅, 1, 1)

def map_FB_to_ARSDH {L : ℕ} (hn : 1 ≤ n)
  (val : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁))
  : (ZMod p × Finset (ZMod p) × G₁ × G₁)
  := (val.1, map_FB_instance_to_ARSDH_inst hn val.2)
    -- val.1 = τ, val.2 = (srs, cm, queryOf, responseOf, accepts, proofs)

/-- Abbreviation for a function binding adversary for KZG. -/
abbrev KZGFunctionBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (L : ℕ) (AuxState : Type) :=
  Commitment.FunctionBindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState L
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

include g₁ g₂ pairing in
/-- The reduction breaking ARSDH using a (successful) Function Binding Adversary.
The redution follows the proof of lemma 9.1 (under Def. 9.6) in https://eprint.iacr.org/2025/902.pdf -/
def reduction (L : ℕ) (hn : 1 ≤ n) (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDHAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
    letI kzgScheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    -- designed such that ProbEvent_comp can be applied and thus the main task of reasoning
    -- is discharged to the predicate level.
    -- map_FB_instance_to_ARSDH_inst' (Step 3 and 4 of the reduction) is applied to the result
    -- of the adversary (step 1 and 2 of the reduction)
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
              map_FB_instance_to_ARSDH_inst hn
                (srs, cm, queryOf, responseOf, accepts, proofs))
          ))

/-- ARSDH condition for an adversary "to win" -/
def ARSDH_cond (D : ℕ) : (ZMod p × Finset (ZMod p) × G₁ × G₁) → Prop :=
  fun (τ, S, (h₁ : G₁), h₂) =>
    let Zₛ : CPolynomial (ZMod p) := ∏ s ∈ S, (X - C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / eval τ Zₛ).val

/-- Function binding condition for an adversary "to win" -/
def FB_cond (n L : ℕ) :
    (queryOf : Fin L → OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
      ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool) → Prop :=
  fun ⟨queryOf, responseOf, acceptedOf⟩ =>
    let S : Finset (Fin L) := Finset.univ
    (∀ i ∈ S, acceptedOf i = true)
    ∧ (¬ ∃ (d : Fin (n + 1) → ZMod p), ∀ i ∈ S, OracleInterface.answer d (queryOf i) = responseOf i)
    ∧ Function.Injective queryOf

/-- Extended function binding condition (taking more input values, logic unchanged) -/
def FB_cond_ext (n L : ℕ) : (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
  (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) → Prop :=
  fun ⟨_, _, _, queryOf, responseOf, accepts, _proofs⟩ =>
    FB_cond n L ⟨queryOf, responseOf, accepts⟩

/-- Function binding game -/
def FB_game {n L : ℕ} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
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
                ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool))))
        : OracleComp _ _)).run' ∅

/-- Extended function binding game (returning more internal values, logic unchanged) -/
def FB_game_ext {n L : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
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
          (τ, srs, cm, queryOf, ((fun i => responseOf i) : Fin L → ZMod p), accepts, proofs))))
      : OracleComp _ _)).run' ∅

omit [DecidableEq G₁] [Fact (0 < p)] in
/-- Transition 1: extending output for proofs and commitment preserves the condition -/
lemma FB_game_ext_eq_FB_game {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[FB_cond n L | FB_game AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Pr[FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  -- Define the projection from the extended output tuple to the basic output tuple.
  let proj : (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) →
      ((queryOf : Fin L → OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
        ((i : Fin L) → OracleInterface.Response (queryOf i)) × (Fin L → Bool)) :=
    fun x => ⟨x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1⟩
  -- The extended condition factors through the projection: `FB_cond_ext = FB_cond ∘ proj`.
  have hcond_eq : (FB_cond_ext n L : _ → Prop) = (FB_cond n L) ∘ proj := by
    funext x
    rcases x with ⟨_, _, _, _, _, _, _⟩
    rfl
  rw [hcond_eq]
  -- Apply the OptionT bridge lemma with the run-level equality proved inline.
  apply OptionT.probEvent_eq_of_run_map_eq _ _ proj (FB_cond n L)
  -- The run-level equality: FB_game.run = Option.map proj <$> FB_game_ext.run
  -- Step 1: unfold definitions to expose the computation structure.
  simp only [FB_game, FB_game_ext, KZG, OptionT.run, OptionT.mk]
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

include g₁ g₂ pairing in
/-- Transition 2: FB condition implies ARSDH condition after mapping -/
lemma FB_cond_le_ARSDH_cond {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn |
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  apply probEvent_mono
  simp only [FB_game_ext, KZG]
  intro (τ, srs, cm, queryOf, responseOf, accepts, proofs) hgame hFBcond
  have hsrs : srs = generateSrs n τ (g₂ := g₂) (g₁ := g₁) := by
    refine OptionT.aux_mem_support_simulateQ_run' _ _ _
      (fun y => y.2.1 = generateSrs (g₁ := g₁) (g₂ := g₂) n y.1) ?_ hgame
    -- Walk through the `do`-block's binds in the underlying OracleComp.
    intro x hx ⟨τ', srs', cm', queryOf', responseOf', accepts', proofs'⟩ hxeq
    rw [mem_support_bind_iff] at hx
    obtain ⟨τ_v, _, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨cm_v, queryOf_v, responseOf_v, stateOf_v⟩, _, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨opts_v, _, hx⟩ := hx
    rw [mem_support_pure_iff] at hx
    -- `hx` now equates `x` with the syntactic `pure (... (τ_v, generateSrs n τ_v, ...))`
    subst hx
    -- Case-analyze the resulting `Option.bind` / `Option.map` to obtain the equality
    cases hres : opts_v with
    | none => simp [hres] at hxeq
    | some resultOf =>
        simp only [Option.bind, Option.map, hres, Option.some.injEq, Prod.mk.injEq]
          at hxeq
        obtain ⟨hτ, hsrs', _⟩ := hxeq
        simp [← hτ, ← hsrs']
  have hgen : srs.1[0] ≠ 1 := by
    rw [hsrs]
    simp only [generateSrs, towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn,
      pow_zero, pow_one, ne_eq]
    exact hg₁
  -- For every index `i`, if `accepts i = true` then the KZG verification holds.
  have hverify_all : ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
    intro i_idx hai
    -- Define the predicate to be propagated through the OptionT/simulateQ wrapper.
    let P : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
        (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁) → Prop :=
      fun y => y.2.2.2.2.2.1 i_idx = true →
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          y.2.1.2 y.2.2.1 (y.2.2.2.2.2.2 i_idx) (y.2.2.2.1 i_idx) (y.2.2.2.2.1 i_idx)
    have hP : P (τ, srs, cm, queryOf, responseOf, accepts, proofs) := by
      refine OptionT.aux_mem_support_simulateQ_run' _ _ _ P ?_ hgame
      -- Walk the do-block in the underlying `OracleComp`.
      intro x hx ⟨τ', srs', cm', queryOf', responseOf', accepts', proofs'⟩ hxeq hai'
      rw [mem_support_bind_iff] at hx
      obtain ⟨τ_v, _, hx⟩ := hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨⟨cm_v, queryOf_v, responseOf_v, stateOf_v⟩, _, hx⟩ := hx
      rw [mem_support_bind_iff] at hx
      obtain ⟨opts_v, hopts, hx⟩ := hx
      rw [mem_support_pure_iff] at hx
      subst hx
      -- Case analyze the resulting `Option.bind`/`Option.map`.
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
              ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
                (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v,
                 generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v)).verifier)
            hopts hres i_idx
        obtain ⟨td_data, va⟩ := result
        -- `hres_eq : (va, td_data.1 0) = resultOf i_idx`
        -- Apply the generic Reduction.run pure-verifier helper.
        have hverif :=
          Reduction.support_run_pure_verifier
            (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v))
              ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
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
        -- `hverif : va = verifyOpening (generateSrs...).2 cm_v (td_data.1 ⟨0,_⟩) ...`
        -- From `hres_eq` extract: va = resultOf i_idx.1 and td_data.1 0 = resultOf i_idx.2.
        have hva_eq_v : va = (resultOf i_idx).1 := by
          have h := congrArg Prod.fst hres_eq
          exact h
        have htd_eq_v : td_data.1 0 = (resultOf i_idx).2 := by
          have h := congrArg Prod.snd hres_eq
          exact h
        -- Component equalities from `hxeq`: accepts'/proofs' come from resultOf.
        have h_a_i : accepts' i_idx = (resultOf i_idx).1 := by
          have := congrFun h_a i_idx
          simpa using this.symm
        have h_p_i : proofs' i_idx = (resultOf i_idx).2 := by
          have := congrFun h_p i_idx
          simpa using this.symm
        -- Combine to get accepts' i_idx = va and proofs' i_idx = td_data.1 0.
        have h_va_acc : va = accepts' i_idx := by rw [hva_eq_v, h_a_i]
        have h_td_prf : td_data.1 0 = proofs' i_idx := by rw [htd_eq_v, ← h_p_i]
        have hva_true : va = true := h_va_acc.trans hai'
        -- queryOf'/responseOf' are also tied to queryOf_v/responseOf_v.
        have h_q_i : queryOf' i_idx = queryOf_v i_idx := by
          have := congrFun h_q i_idx
          simpa using this.symm
        have h_r_i : responseOf' i_idx = responseOf_v i_idx := by
          have := congrFun h_r i_idx
          simpa using this.symm
        -- The goal: verifyOpening srs'.2 cm' (proofs' i_idx) (queryOf' i_idx)
        --                                    (responseOf' i_idx) = true
        change KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          srs'.2 cm' (proofs' i_idx) (queryOf' i_idx) (responseOf' i_idx)
        rw [← h_srs, ← h_cm, ← h_td_prf, h_q_i, h_r_i]
        -- Goal: verifyOpening (generateSrs n τ_v).2 cm_v (td_data.1 0)
        --                     (queryOf_v i_idx) (responseOf_v i_idx)
        -- From `hverif` and `hva_true`:
        have heq : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
            (generateSrs (g₁ := g₁) (g₂ := g₂) n τ_v).2 cm_v
            (td_data.1 ⟨0, by decide⟩) (queryOf_v i_idx) (responseOf_v i_idx)
              = true := hverif.symm.trans hva_true
        -- `td_data.1 ⟨0, by decide⟩` is definitionally `td_data.1 0` for `Fin 1`.
        exact heq
    exact hP hai
  unfold map_FB_to_ARSDH
  unfold map_FB_instance_to_ARSDH_inst map_FB_instance_to_ARSDH_inst'
  simp only [one_div, Finset.union_singleton, Option.pure_def, beq_iff_eq, Option.bind_eq_bind,
    Function.comp_apply]
  -- first branch from map_FB_instance_to_ARSDH_inst'
  set fc := find_conflict (List.ofFn fun i ↦ (queryOf i, responseOf i, proofs i)) with hfc_def
  cases hfc : fc with
  | some c =>
      obtain ⟨⟨α₁, β₁, pf₁⟩, α₂, β₂, pf₂⟩ := c
      -- goal for the first branch
      simp only [ARSDH_cond, Option.getD_some, ne_eq, one_div]
      constructor
      · rw [← Finset.union_singleton]
        exact choose_S_conflict_size_adjoined hp hn α₁ srs hgen
      · constructor
        · exact h₁_not_zero (g₁ := g₁) (g₂ := g₂) hp PrimeOrderWith.hCard hn α₁ τ srs hsrs hgen
        · -- h₂ = h₁ ^ (1 / Zₛᵤₐ.eval τ).val by `h₁Zₛ_eq_h₂`.
          -- Extract `α₁ = α₂` and `β₁ ≠ β₂` from the success of `find_conflict`.
          have hfc' : find_conflict (List.ofFn fun i ↦ (queryOf i, responseOf i, proofs i))
              = some ((α₁, β₁, pf₁), (α₂, β₂, pf₂)) := hfc_def ▸ hfc
          have hαβ : α₁ = α₂ ∧ β₁ ≠ β₂ := by
            unfold find_conflict at hfc'
            obtain ⟨_, ⟨a₁', b₁', p₁'⟩, _, _, h_inner, _⟩ :=
              List.findSome?_eq_some_iff.mp hfc'
            simp only at h_inner
            obtain ⟨_, ⟨a₂', b₂', p₂'⟩, _, _, h_cond, _⟩ :=
              List.findSome?_eq_some_iff.mp h_inner
            simp only at h_cond
            by_cases hif : (a₁' == a₂' && b₁' != b₂') = true
            · rw [if_pos hif] at h_cond
              simp only [Option.some.injEq, Prod.mk.injEq] at h_cond
              simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hif
              grind
            · rw [if_neg hif] at h_cond
              exact absurd h_cond (by simp)
          obtain ⟨hα, hβ⟩ := hαβ
          -- `hverify_all` is provided by the outer scope: every accepting index passes
          -- KZG verification.
          -- Find indices `i₁`, `i₂` in `List.ofFn` corresponding to the conflict pairs.
          have h_in₁ : (α₁, β₁, pf₁) ∈
              List.ofFn (fun i ↦ (queryOf i, responseOf i, proofs i)) := by
            obtain ⟨pre₁, ⟨a₁', b₁', p₁'⟩, suf₁, hdec₁, h_inner, _⟩ :=
              List.findSome?_eq_some_iff.mp hfc'
            simp only at h_inner
            obtain ⟨_, ⟨a₂', b₂', p₂'⟩, _, _, h_cond, _⟩ :=
              List.findSome?_eq_some_iff.mp h_inner
            simp only at h_cond
            by_cases hif : (a₁' == a₂' && b₁' != b₂') = true
            · rw [if_pos hif] at h_cond
              simp only [Option.some.injEq, Prod.mk.injEq] at h_cond
              obtain ⟨⟨ha, hb, hp⟩, _⟩ := h_cond
              rw [← ha, ← hb, ← hp, hdec₁]
              simp
            · rw [if_neg hif] at h_cond
              exact absurd h_cond (by simp)
          have h_in₂ : (α₂, β₂, pf₂) ∈
              List.ofFn (fun i ↦ (queryOf i, responseOf i, proofs i)) := by
            obtain ⟨_, ⟨a₁', b₁', p₁'⟩, _, _, h_inner, _⟩ :=
              List.findSome?_eq_some_iff.mp hfc'
            simp only at h_inner
            obtain ⟨pre₂, ⟨a₂', b₂', p₂'⟩, suf₂, hdec₂, h_cond, _⟩ :=
              List.findSome?_eq_some_iff.mp h_inner
            simp only at h_cond
            by_cases hif : (a₁' == a₂' && b₁' != b₂') = true
            · rw [if_pos hif] at h_cond
              simp only [Option.some.injEq, Prod.mk.injEq] at h_cond
              obtain ⟨_, ⟨ha, hb, hp⟩⟩ := h_cond
              rw [← ha, ← hb, ← hp, hdec₂]
              simp
            · rw [if_neg hif] at h_cond
              exact absurd h_cond (by simp)
          obtain ⟨i₁, hi₁⟩ := List.mem_ofFn.mp h_in₁
          obtain ⟨i₂, hi₂⟩ := List.mem_ofFn.mp h_in₂
          have h_acc_all : ∀ i ∈ (Finset.univ : Finset (Fin L)), accepts i = true :=
            hFBcond.1
          have hai₁ : accepts i₁ = true := h_acc_all i₁ (Finset.mem_univ _)
          have hai₂ : accepts i₂ = true := h_acc_all i₂ (Finset.mem_univ _)
          have hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              srs.2 cm pf₁ α₁ β₁ := by
            have h := hverify_all i₁ hai₁
            -- hi₁ : (queryOf i₁, responseOf i₁, proofs i₁) = (α₁, β₁, pf₁)
            simp only [Prod.mk.injEq] at hi₁
            obtain ⟨hq, hr, hp⟩ := hi₁
            rw [← hq, ← hr, ← hp]
            exact h
          have hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              srs.2 cm pf₂ α₂ β₂ := by
            have h := hverify_all i₂ hai₂
            simp only [Prod.mk.injEq] at hi₂
            obtain ⟨hq, hr, hp⟩ := hi₂
            rw [← hq, ← hr, ← hp]
            exact h
          have key := h₁Zₛ_eq_h₂ (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
            hp PrimeOrderWith.hCard hn α₁ α₂ β₁ β₂ τ cm pf₁ pf₂
            hα hβ srs hsrs hgen hpair hverify₁ hverify₂
          simpa [Finset.union_singleton, one_div] using key
  | none => -- second branch from map_FB_instance_to_ARSDH_inst'
      set fs := List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val = srs.1[1] then some (queryOf i) else none)
        (List.finRange L) with hfs_def
      cases hfs : fs with
      | some α₁ =>
          simp only [ARSDH_cond, Option.getD_some, ne_eq, one_div]
          -- branch where `List.findSome? = some α₁`
          -- Extract the precondition: `srs.1[0] ^ α₁.val = srs.1[1]`.
          have hfs' : List.findSome?
              (fun i ↦ if srs.1[0] ^ (queryOf i).val
                            = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                        then some (queryOf i) else none)
              (List.finRange L) = some α₁ := hfs_def.symm.trans hfs
          have hcond : srs.1[0] ^ α₁.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
            obtain ⟨_, i, _, _, hbody, _⟩ := List.findSome?_eq_some_iff.mp hfs'
            by_cases hif : srs.1[0] ^ (queryOf i).val
                              = srs.1[1]'(Nat.lt_add_of_pos_left hn)
            · rw [if_pos hif] at hbody
              simp only [Option.some.injEq] at hbody
              rw [← hbody]; exact hif
            · rw [if_neg hif] at hbody
              exact absurd hbody (by simp)
          have hord : orderOf g₁ = p := orderOf_eq_prime_of_ne_one g₁ hg₁
          -- Identify `srs.1[0] = g₁` and `srs.1[1] = g₁ ^ τ.val`.
          have h_srs0 : srs.1[0] = g₁ := by
            rw [hsrs]; simp [generateSrs, towerOfExponents]
          have h_srs1 : srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
            rw [hsrs]; simp [generateSrs, towerOfExponents]
          have hpow : g₁ ^ α₁.val = g₁ ^ τ.val := by
            have h := hcond
            rw [h_srs0, h_srs1] at h
            exact h
          -- Conclude `α₁ = τ`.
          have hα_τ : α₁ = τ := by
            have hmod : α₁.val ≡ τ.val [MOD orderOf g₁] :=
              pow_eq_pow_iff_modEq.mp hpow
            rw [hord] at hmod
            have hα_lt : α₁.val < p := ZMod.val_lt α₁
            have hτ_lt : τ.val < p := ZMod.val_lt τ
            have h_eq : α₁.val = τ.val := by
              have hm : α₁.val % p = τ.val % p := hmod
              rwa [Nat.mod_eq_of_lt hα_lt, Nat.mod_eq_of_lt hτ_lt] at hm
            exact ZMod.val_injective p h_eq
          refine ⟨?_, ?_, ?_⟩
          · -- `S.card = n + 1`
            have h_inj : Set.InjOn ((↑) : ℕ → ZMod p) ↑(Finset.range (n + 1)) := by
              intro a ha b hb hab
              simp only [Finset.coe_range, Set.mem_Iio] at ha hb
              have hap : a < p := lt_of_lt_of_le ha (by omega)
              have hbp : b < p := lt_of_lt_of_le hb (by omega)
              have hv := congrArg ZMod.val hab
              rwa [ZMod.val_natCast_of_lt hap, ZMod.val_natCast_of_lt hbp] at hv
            rw [Finset.card_image_of_injOn h_inj, Finset.card_range]
          · -- `srs.1[0] ≠ 1`
            exact hgen
          · -- `h₂ = h₁ ^ (1 / eval τ Zₛ).val`
            rw [hα_τ]
      | none => -- third branch from map_FB_instance_to_ARSDH_inst'
          set fa := find_A (n+1) queryOf responseOf with hfa_def
          -- The interpolation has degree ≥ n + 1, since otherwise its first n + 1
          -- coefficients would witness a degree-`n` polynomial fitting all pairs,
          -- contradicting the function-binding hypothesis `hFBcond`.
          have hquery : Function.Injective queryOf := hFBcond.2.2
          have huniv_deg : (↑(n + 1) : WithBot ℕ) ≤
              (CLagrange.interpolate (Finset.univ : Finset (Fin L))
                queryOf responseOf).degree := by
            by_contra hlt
            push Not at hlt
            -- Bridge to Mathlib polynomial.
            set Q : Polynomial (ZMod p) :=
              Lagrange.interpolate (Finset.univ : Finset (Fin L)) queryOf responseOf with hQ_def
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
            -- The coefficient vector witness.
            apply hFBcond.2.1
            refine ⟨Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩, ?_⟩
            intro i _
            -- Show: `OracleInterface.answer d (queryOf i) = responseOf i`.
            -- Using the local instance, the answer at `z` is `∑ k, d k * z ^ k.val`.
            have hQ_eval : Q.eval (queryOf i) = responseOf i := by
              rw [hQ_def]
              exact Lagrange.eval_interpolate_at_node responseOf
                (hquery.injOn (s := (Finset.univ : Finset (Fin L)))) (Finset.mem_univ i)
            -- Reduce the answer to a `Fin (n+1)` sum and identify with `Q.eval`.
            have hQ_sum :
                Q.eval (queryOf i) =
                  ∑ k : Fin (n + 1),
                    Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ k *
                      (queryOf i) ^ (k : ℕ) :=
              Polynomial.eval_eq_sum_degreeLTEquiv hQ_mem (queryOf i)
            -- The OracleInterface answer reduces (definitionally) to evaluating the
            -- canonical CPolynomial built from the coefficient vector.
            set d : Fin (n + 1) → ZMod p :=
              Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ with hd_def
            let P_C : CPolynomial (ZMod p) :=
              ⟨(CompPoly.CPolynomial.Raw.mk (Array.ofFn d)).trim,
                CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩
            change CPolynomial.eval (queryOf i) P_C = responseOf i
            -- Bridge CPolynomial.eval to Polynomial.eval, then identify polynomials by coeffs.
            rw [eval_toPoly]
            have hPC_eq : P_C.toPoly = Q := by
              apply Polynomial.ext
              intro k
              rw [← coeff_toPoly]
              -- The CPolynomial built from `Array.ofFn d` has coefficients `d k` for `k < n + 1`
              -- and zero elsewhere.
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
          -- From `huniv_deg` we also get `n + 1 < L`.
          have hL : n + 1 < L := by
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
          cases hfa : fa with
          | some a =>
              set fs' := find_S' n a cm srs queryOf responseOf with hfs'_def
              cases hfs' : fs' with
              | some a' =>
                  -- third branch actual content (rest are irrelevant corner cases)
                  -- Recover the underlying option equalities from the `set`+`cases` shells.
                  have hresA : find_A (n+1) queryOf responseOf = some a :=
                    hfa_def.symm.trans hfa
                  have hresS : find_S' n a cm srs queryOf responseOf = some a' :=
                    hfs'_def.symm.trans hfs'
                  have hres_a' : some a' = find_S' n a cm srs queryOf responseOf := hresS.symm
                  -- Reduce the do-block to its `some` value, then unfold `ARSDH_cond`.
                  simp only [hresS, Option.bind, ARSDH_cond, Option.getD_some,
                    ne_eq, one_div]
                  refine ⟨?_, ?_, ?_⟩
                  · -- `(a'.image queryOf).card = n + 1`
                    rw [Finset.card_image_of_injective _ hquery]
                    exact find_S'_card n cm a a' srs queryOf responseOf hres_a'
                  · -- `cm / c' ≠ 1`, equivalently `cm ≠ c'`, from `find_S'_diverges`.
                    intro hdiv
                    have hcm_eq_c' : cm =
                        commit srs.1
                          ((CLagrange.interpolate a' queryOf responseOf).val.coeff ∘ Fin.val) :=
                      div_eq_one.mp hdiv
                    exact (find_S'_diverges n cm a a' queryOf responseOf srs hres_a')
                      hcm_eq_c'.symm
                  · -- `h₂ = h₁ ^ (1 / Zₛ.eval τ).val`
                    -- Card and degree bound for `a'` (|a'| = n+1 ⇒ degree ≤ n).
                    have hcard : a'.card = n + 1 :=
                      find_S'_card n cm a a' srs queryOf responseOf hres_a'
                    have hdeg :
                        (CLagrange.interpolate a' queryOf responseOf).degree
                          ≤ (n : WithBot ℕ) := by
                      have h_lt :
                          (Lagrange.interpolate a' queryOf responseOf).degree
                            < ((n + 1 : ℕ) : WithBot ℕ) := by
                        have := Lagrange.degree_interpolate_lt responseOf
                          (hquery.injOn (s := a'))
                        rw [hcard] at this
                        exact_mod_cast this
                      have h_eq :
                          (CLagrange.interpolate a' queryOf responseOf).degree
                            = (Lagrange.interpolate a' queryOf responseOf).degree := by
                        rw [← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]
                      rw [h_eq]
                      rcases hd :
                          (Lagrange.interpolate a' queryOf responseOf).degree with _ | k
                      · exact bot_le
                      · rw [hd] at h_lt
                        have hk : k < n + 1 := WithBot.coe_lt_coe.mp h_lt
                        exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp hk)
                    have ha'_ne : a'.Nonempty := by
                      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos _
                    -- `srs.1[0] = g₁`, `srs.1[1] = g₁ ^ τ.val`.
                    have h_srs0 : srs.1[0] = g₁ := by
                      rw [hsrs]; simp [generateSrs, towerOfExponents]
                    have h_srs1 :
                        srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
                      rw [hsrs]; simp [generateSrs, towerOfExponents]
                    -- Queries in `a'` cannot equal τ (else the second branch would have fired).
                    have hτneq : ∀ i ∈ a', queryOf i ≠ τ := by
                      intro i _ hqτ
                      have hfs_none :
                          List.findSome?
                            (fun i ↦ if srs.1[0] ^ (queryOf i).val
                                          = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                                      then some (queryOf i) else none)
                            (List.finRange L) = none := hfs_def.symm.trans hfs
                      have hall := List.findSome?_eq_none_iff.mp hfs_none
                      have h_at_i := hall i (List.mem_finRange i)
                      have hpow : srs.1[0] ^ (queryOf i).val
                          = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
                        rw [h_srs0, h_srs1, hqτ]
                      simp [hpow] at h_at_i
                    -- Every accepted index passes verification.
                    have hVer : ∀ i ∈ a',
                        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
                          srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
                      intro i _
                      exact hverify_all i (hFBcond.1 i (Finset.mem_univ _))
                    have key := h₁Zₛ_eq_h₂' (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
                      n τ cm a' queryOf responseOf proofs srs hn hsrs hτneq hVer
                      hgen hpair hdeg ha'_ne hquery
                    simp only [one_div] at key
                    exact key
              | none =>
                  -- `find_S'` failed: contradicts `find_S'_successful`.
                  exfalso
                  have hres_a : some a = find_A (n+1) queryOf responseOf := by
                    rw [← hfa_def]; exact hfa.symm
                  have hAdeg :=
                    find_A_deg (n+1) a queryOf responseOf hres_a
                  have hsome :=
                    find_S'_successful (g₁ := g₁) n τ cm a queryOf responseOf srs hsrs hgen
                      (by exact_mod_cast hAdeg) hquery hn
                  have hnone :
                      find_S' n a cm srs queryOf responseOf = none := by
                    rw [← hfs'_def]; exact hfs'
                  rw [hnone] at hsome
                  simp at hsome
          | none =>
              -- `find_A` failed: contradicts `find_A_successful` via `huniv_deg`.
              exfalso
              have hsome :=
                find_A_successful (n+1) hL (Finset.univ : Finset (Fin L)) queryOf responseOf
                  hquery huniv_deg
              have hnone : find_A (n+1) queryOf responseOf = none := by
                rw [← hfa_def]; exact hfa
              rw [hnone] at hsome
              simp at hsome

omit [Fact (0 < p)] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event -/
lemma map_instance_drag {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :
    Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn |
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[(ARSDH_cond n) |
      map_FB_to_ARSDH hn <$> FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

omit [Fact (0 < p)] in
/-- Transition 4: the mapped game equals the ARSDH experiment -/
lemma ARSDH_game_eq {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[(ARSDH_cond n) | map_FB_to_ARSDH hn <$> FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) := by
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.ARSDH_Experiment]
  unfold ARSDH_cond
  simp only
  congr 1
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  simpa only [FB_game_ext, reduction, KZG, OptionT.mk, pSpec', impl, scheme,
      OptionT.run_map] using
    OptionT.simulateQ_liftComp_bind_map_eq_of_body
      (impl := impl)
      (impl₀ := randomOracle)
      (sample := (($ᵗ (ZMod p)) : OracleComp unifSpec (ZMod p)))
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
          map_FB_instance_to_ARSDH_inst hn
            (srs, cm, queryOf, responseOf, (fun i => (resultOf i).1), (fun i => (resultOf i).2)))
      )
      (f := map_FB_to_ARSDH hn)
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

omit [Fact (0 < p)] in
/-- The ARSDH experiment is bounded by the ARSDH error -/
lemma ARSDH_error_bound {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂)
      (g₁ := g₁) (g₂ := g₂) n ARSDHerror)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n (reduction (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) L hn AuxState adversary)
    ≤ ARSDHerror := by
  simp_all [Groups.ARSDHAssumption]

omit [DecidableEq G₁] in
/- the KZG satisfies function binding as defined in `CommitmentScheme` provided ARSDH holds. -/
theorem functionBinding {g₁ : G₁} {g₂ : G₂}
    (L : ℕ) (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (AuxState : Type) [SampleableType G₁] (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n ARSDHerror) :
    Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle)
      (hn := rfl) (hpSpec := { prover_first' := by simp }) AuxState
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) ARSDHerror := by
  letI := Classical.decEq G₁
  letI scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.functionBinding]
  intro adversary
  letI game := FB_game AuxState adversary scheme
  letI game_ext := FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[FB_cond n L | game]
    _ = Pr[FB_cond_ext n L | game_ext] :=
      FB_game_ext_eq_FB_game (pairing := pairing) adversary
    _ ≤ Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn | game_ext] :=
      FB_cond_le_ARSDH_cond (pairing := pairing) hn hp hg₁ hpair adversary
    _ = Pr[(ARSDH_cond n) | map_FB_to_ARSDH hn <$> game_ext] :=
      map_instance_drag hn adversary scheme
    _ = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) :=
      ARSDH_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn adversary
    _ ≤ ARSDHerror := ARSDH_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn ARSDHerror
      hARSDH adversary)

end FunctionBinding

end CommitmentScheme

end KZG
