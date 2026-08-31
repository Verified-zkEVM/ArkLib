/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.Commitments.Functional.KZG.Correctness
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions
import ArkLib.ToCompPoly.Univariate.Lagrange

/-!
# Shared Function-Binding Support for KZG

Definitions and facts used by more than one branch of the KZG function-binding reduction.

## Notation

* `findConflict` searches for two equal queries with different claimed responses.
* `FunctionBindingExtTranscript` records the transcript data shared by branch maps.
* `FunctionBindingArsdhOutput` packages one branch's ARSDH output.

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
local instance functionBindingSupportOracleInterface :
    OracleInterface (Fin (n + 1) → ZMod p) where
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
/-- If `findConflict` returns `none`, no pair of indices has equal query and unequal response. -/
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
/-- If `findConflict` returns a pair, that pair has equal queries and distinct responses. -/
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

omit [Fact (Nat.Prime p)] [DecidableEq G₁] [Group G₁] in
/-- With no conflict, equal queries force equal responses. -/
lemma response_eq_of_find_conflict_none {L : ℕ} (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hfc : findConflict query response = none)
    {i j : Fin L} (hquery : query i = query j) :
    response i = response j := by
  by_contra hresp
  exact (find_conflict_unsuccessful query response hfc) ⟨i, j, by simp [hquery, hresp]⟩

/-- Convert a computable vanishing product into the corresponding mathlib polynomial product. -/
lemma prod_x_sub_c_to_poly (S : Finset (ZMod p)) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).toPoly =
      ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
  have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
  simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]

/-- A vanishing product evaluates nonzero away from its support. -/
lemma prod_x_sub_c_eval_ne_zero {S : Finset (ZMod p)} {τ : ZMod p}
    (hτS : τ ∉ S) :
    (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).eval τ ≠ 0 := by
  rw [eval_toPoly, prod_x_sub_c_to_poly S, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro s hs
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact fun h => hτS (by simpa [sub_eq_zero.mp h])

/-! ### Reduction Output Assembly -/

/-- Transcript data kept by the extended function-binding game, excluding the sampled secret. -/
structure FunctionBindingExtTranscript (n L : ℕ) (G₁ G₂ : Type) where
  srs : Vector G₁ (n + 1) × Vector G₂ 2
  cm : G₁
  queryOf : Fin L → ZMod p
  responseOf : Fin L → ZMod p
  accepts : Fin L → Bool
  proofs : Fin L → G₁

namespace FunctionBindingExtTranscript

/-- Turn the legacy nested tuple transcript into the named record used by the reduction map. -/
def ofTuple {L : ℕ}
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    FunctionBindingExtTranscript (p := p) n L G₁ G₂ where
  srs := val.1
  cm := val.2.1
  queryOf := val.2.2.1
  responseOf := val.2.2.2.1
  accepts := val.2.2.2.2.1
  proofs := val.2.2.2.2.2

end FunctionBindingExtTranscript

/-- The ARSDH instance produced by one branch of the function-binding reduction. -/
structure FunctionBindingArsdhOutput (G₁ : Type) where
  support : Finset (ZMod p)
  base : G₁
  solution : G₁

namespace FunctionBindingArsdhOutput

/-- Return to the tuple shape expected by `Groups.arsdhCondition`. -/
def toTuple (out : FunctionBindingArsdhOutput (p := p) G₁) :
    Finset (ZMod p) × G₁ × G₁ :=
  (out.support, out.base, out.solution)

end FunctionBindingArsdhOutput

/-- Extended function binding condition (taking more input values, logic unchanged) -/
def functionBindingCondExt (n L : ℕ) :
    (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) →
      Prop :=
  fun ⟨_, _, _, queryOf, responseOf, accepts, _proofs⟩ =>
    Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p)
      ⟨queryOf, responseOf, accepts⟩

end FunctionBinding

end CommitmentScheme

end KZG
