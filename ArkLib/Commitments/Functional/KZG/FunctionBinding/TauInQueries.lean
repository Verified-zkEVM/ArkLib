/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.Commitments.Functional.KZG.FunctionBinding.Support

/-!
# Tau-in-Queries Branch for KZG Function Binding

Branch-specific search and ARSDH extraction for the case where a query reveals the trapdoor,
following the ARSDH reduction in [CGKY25].

## Notation

* `chooseSMiddle` chooses a support set avoiding the discovered trapdoor query.
* `queryEqTauArsdhOutput` builds the ARSDH output for this branch.
* `function_binding_query_eq_tau_branch_maps_to_arsdh` is the branch proof.

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
local instance functionBindingTauInQueriesOracleInterface :
    OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

omit hp [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- If the SRS-power search returns `α`, then `α` satisfies the searched equation. -/
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
/-- Equality with the second SRS power identifies a field element as the trapdoor. -/
lemma zmod_eq_of_srs_power_eq {α τ : ZMod p}
    (hn : 1 ≤ n) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hord : orderOf g₁ = p)
    (hpow : srs.1[0] ^ α.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) :
    α = τ := by
  have h_srs0 : srs.1[0] = g₁ := by
    rw [hsrs]
    simp [Groups.PowerSrs.generate, Groups.PowerSrs.tower]
  have h_srs1 : srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
    rw [hsrs]
    simp [Groups.PowerSrs.generate, Groups.PowerSrs.tower]
  have hpow' : g₁ ^ α.val = g₁ ^ τ.val := by
    rw [h_srs0, h_srs1] at hpow
    exact hpow
  have hmod : α.val ≡ τ.val [MOD orderOf g₁] := pow_eq_pow_iff_modEq.mp hpow'
  rw [hord] at hmod
  have h_eq : α.val = τ.val := by
    have hm : α.val % p = τ.val % p := hmod
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt α), Nat.mod_eq_of_lt (ZMod.val_lt τ)] at hm
  exact ZMod.val_injective p h_eq

/-! ### Query Equal to Trapdoor Branch -/

/- We introduce one middle case to handle the case where the discovered value `τ` is part of the
queries. This explicit step converts the probabilistic step 4 from the paper into a deterministic
step. -/

/-- choose a size-`n + 1` set that avoids the discovered value `α`(= `τ`).

If `α` lies among the first `n + 2` representatives, remove it from that set. Otherwise the
first `n + 1` representatives already avoid `α`. -/
def chooseSMiddle (n : ℕ) (α : ZMod p) : Finset (ZMod p) :=
  let base : Finset (ZMod p) := (Finset.range (n + 2)).image ((↑) : ℕ → ZMod p)
  if α ∈ base then base.erase α else (Finset.range (n + 1)).image ((↑) : ℕ → ZMod p)

/-- Casting the first `k ≤ p` natural numbers into `ZMod p` is injective. -/
lemma nat_cast_range_card_zmod_of_le {k : ℕ} (hk : k ≤ p) :
    ((Finset.range k).image ((↑) : ℕ → ZMod p)).card = k := by
  have h_inj : Set.InjOn ((↑) : ℕ → ZMod p) ↑(Finset.range k) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hap : a < p := lt_of_lt_of_le ha hk
    have hbp : b < p := lt_of_lt_of_le hb hk
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt hap, ZMod.val_natCast_of_lt hbp] at hv
  rw [Finset.card_image_of_injOn h_inj, Finset.card_range]

/-- The first `n + 1` natural representatives have cardinality `n + 1` in `ZMod p`. -/
lemma nat_cast_range_card_zmod (hp : p ≥ n + 2) :
    ((Finset.range (n + 1)).image ((↑) : ℕ → ZMod p)).card = n + 1 := by
  exact nat_cast_range_card_zmod_of_le (k := n + 1) (by omega)

/-- `chooseSMiddle` returns a support set of size `n + 1`. -/
lemma choose_s_middle_card (hp : p ≥ n + 2) (α : ZMod p) :
    (chooseSMiddle n α).card = n + 1 := by
  unfold chooseSMiddle
  set base : Finset (ZMod p) := (Finset.range (n + 2)).image ((↑) : ℕ → ZMod p)
    with hbase_def
  by_cases hα : α ∈ base
  · rw [if_pos hα, Finset.card_erase_of_mem hα]
    have hbase : base.card = n + 2 := by
      rw [hbase_def]
      exact nat_cast_range_card_zmod_of_le (k := n + 2) hp
    omega
  · rw [if_neg hα]
    exact nat_cast_range_card_zmod hp

/-- The avoided point is not in the set returned by `chooseSMiddle`. -/
lemma choose_s_middle_not_mem (α : ZMod p) :
    α ∉ chooseSMiddle n α := by
  unfold chooseSMiddle
  set base : Finset (ZMod p) := (Finset.range (n + 2)).image ((↑) : ℕ → ZMod p)
  by_cases hα : α ∈ base
  · simp [hα]
  · rw [if_neg hα]
    intro hmem
    apply hα
    simp only [base, Finset.mem_image, Finset.mem_range] at hmem ⊢
    obtain ⟨i, hi, rfl⟩ := hmem
    exact ⟨i, by omega, rfl⟩

/-- The middle-branch vanishing product does not vanish at the avoided point. -/
lemma choose_s_middle_eval_ne_zero (α : ZMod p) :
    (∏ s ∈ chooseSMiddle n α, (X - C s : CPolynomial (ZMod p))).eval α ≠ 0 := by
  exact prod_x_sub_c_eval_ne_zero (choose_s_middle_not_mem α)

/-- ARSDH output for the branch that discovers a query equal to `τ`. -/
def queryEqTauArsdhOutput (n : ℕ) (α : ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) :
    FunctionBindingArsdhOutput (p := p) G₁ :=
  let S : Finset (ZMod p) := chooseSMiddle n α
  let Zₛ := ∏ s ∈ S, (X - C s)
  { support := S, base := srs.1[0], solution := srs.1[0] ^ (1 / Zₛ.eval α).val }

omit [DecidableEq G₁] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- The branch that finds a query equal to `τ` maps to ARSDH. -/
lemma function_binding_query_eq_tau_branch_maps_to_arsdh {n : ℕ}
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1)
    {τ α : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2}
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1)
    (hpow : srs.1[0] ^ α.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) :
    Groups.arsdhCondition n (τ, (queryEqTauArsdhOutput (p := p) n α srs).toTuple) := by
  simp only [queryEqTauArsdhOutput, FunctionBindingArsdhOutput.toTuple,
    Groups.arsdhCondition, ne_eq, one_div]
  have hord : orderOf g₁ = p := Groups.orderOf_eq_prime_of_ne_one g₁ hg₁
  have hα_τ : α = τ :=
    zmod_eq_of_srs_power_eq (g₁ := g₁) hn srs hsrs hord hpow
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact choose_s_middle_card hp α
  · rw [← hα_τ]
    exact choose_s_middle_eval_ne_zero α
  · exact hgen
  · rw [hα_τ]

end FunctionBinding

end CommitmentScheme

end KZG
