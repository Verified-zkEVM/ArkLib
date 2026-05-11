/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.FunctionBinding

/-! ## Evaluation binding for the KZG Polynomial Commitment Scheme -/

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

section Binding
/- In this section prove that the KZG is evakuation binding under the t-SDH assumption. The proof is a
reduction to t-SDH following (TODO KZG citation etc. here)
-/

variable {η : Type} (advSpec : OracleSpec η) [hp : Fact (Nat.Prime p)]

/- the KZG satisfies evaluation binding as defined in `CommitmentScheme` provided t-SDH holds. -/
theorem Binding {g₁ : G₁} {g₂ : G₂} (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (tSDHerror : ℝ≥0)
    (htSDH : Groups.tSDHAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n tSDHerror) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) tSDHerror := by
  letI scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.binding]
  intro adversary
  sorry /-
  letI game := FB_game adversary scheme
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
  -/

-- TODO put VCV-io lemmas in the right place.

end Binding

end CommitmentScheme

end KZG
