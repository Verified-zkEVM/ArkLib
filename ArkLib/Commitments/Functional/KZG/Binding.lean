/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.Commitments.Functional.KZG.Correctness
import ArkLib.Commitments.Functional.KZG.Algebra
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions
import ArkLib.ToVCVio.EvalDist.Defs.Support

/-!
# Evaluation Binding for the KZG Polynomial Commitment Scheme

This file proves evaluation binding for the KZG commitment scheme by reducing a successful
two-opening adversary to the `t`-SDH experiment. The proof separates the algebraic extraction
from the probabilistic game transformations.

## Notation

* `bindingGame` is the base evaluation-binding game.
* `bindingGameExt` records the sampled secret and proof elements used by the reduction.
* `mapBindingToTsdh` maps extended binding outputs to `t`-SDH instances.

## References

This proof follows the extended version of the KZG paper, which has all the security proofs.

* [Kate, A., Zaverucha, G. M., and Goldberg, I., *Polynomial Commitments*][KZG10TR]
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
local instance bindingOracleInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section Binding

/-- Output of the evaluation-binding game. -/
abbrev BindingOutput (n : ℕ) :=
  (query : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
    OracleInterface.Response query × OracleInterface.Response query × Bool × Bool

/-- Extended evaluation-binding output carrying the data needed by the reduction. -/
abbrev BindingExtOutput (n : ℕ) (G₁ G₂ : Type) :=
  ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    ZMod p × ZMod p × ZMod p × Bool × Bool × G₁ × G₁

/-- Abbreviation for a binding adversary for KZG. -/
abbrev KzgBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (AuxState : Type) :=
  Commitment.BindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

/-- Extended evaluation binding condition, carrying values needed by the reduction. -/
def bindingCondExt : BindingExtOutput (p := p) n G₁ G₂ → Prop :=
  fun ⟨_, _, _, query, resp₁, resp₂, accept₁, accept₂, _, _⟩ =>
    Commitment.bindingCondition (Data := Fin (n + 1) → ZMod p)
      (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BindingOutput (p := p) n)

/-- Extended evaluation binding game, returning the two proof elements in addition to verdicts. -/
def bindingGameExt {n : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) : OptionT ProbComp (BindingExtOutput (p := p) n G₁ G₂) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    let τ ← Groups.sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
    (simulateQ
      (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
      <|
      (do
        let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let result₁ ← (reduction.run
          (cm, (⟨query, resp₁⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₁).run
        let result₂ ← (reduction.run
          (cm, (⟨query, resp₂⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₂).run
        let accept₁ := result₁.map (fun result => result.2) |>.getD false
        let accept₂ := result₂.map (fun result => result.2) |>.getD false
        let proof₁ : G₁ := result₁.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        let proof₂ : G₁ := result₂.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        pure (some (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁,
          proof₂)) :
          OracleComp _ _)).run' ∅

/-- The instance-level map used by the t-SDH reduction. -/
def mapBindingInstanceToTsdh
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      ZMod p × ZMod p × ZMod p × Bool × Bool × G₁ × G₁) : ZMod p × G₁ :=
  let (_, _, query, resp₁, resp₂, _, _, proof₁, proof₂) := val
  (-query, (proof₁ / proof₂) ^ (1 / (resp₂ - resp₁)).val)

/-- Map an extended binding-game output to a t-SDH instance. -/
def mapBindingToTsdh
    (val : BindingExtOutput (p := p) n G₁ G₂) : ZMod p × ZMod p × G₁ :=
  (val.1, mapBindingInstanceToTsdh (p := p) (n := n) val.2)

omit [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] [Group G₂]
  [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
/-- If two accepted openings at the same query give different responses, the t-SDH denominator
`τ + (-query)` cannot vanish. This is the small algebraic contradiction used to avoid a separate
`query = τ` branch in the binding reduction. -/
lemma t_sdh_denominator_ne_zero_of_opening_equations
    (τ query resp₁ resp₂ cm prf₁ prf₂ : ZMod p) (hresp : resp₁ ≠ resp₂)
    (hverifyEq₁ : cm - resp₁ = prf₁ * (τ - query))
    (hverifyEq₂ : cm - resp₂ = prf₂ * (τ - query)) :
    τ + -query ≠ 0 := by
  intro hzero
  have hτq : τ - query = 0 := by
    simpa [sub_eq_add_neg] using hzero
  have hcm₁ : cm = resp₁ := by
    simp only [hτq, MulZeroClass.mul_zero] at hverifyEq₁
    exact sub_eq_zero.mp hverifyEq₁
  have hcm₂ : cm = resp₂ := by
    simp only [hτq, MulZeroClass.mul_zero] at hverifyEq₂
    exact sub_eq_zero.mp hverifyEq₂
  exact hresp (hcm₁.symm.trans hcm₂)

omit [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- A nontrivial element of a prime-order group has order `p`. -/
lemma binding_order_of_eq_prime_of_ne_one (x : G₁) (hx : x ≠ 1) : orderOf x = p := by
  have hdvd := orderOf_dvd_natCard (G := G₁) x
  rw [PrimeOrderWith.hCard] at hdvd
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.1 h1) hx
  · exact hp'

omit [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Every element of a prime-order group is a `ZMod p` power of a nontrivial generator. -/
lemma binding_exists_zmod_power_of_generator (hpG1 : Nat.card G₁ = p) (hg₁ : g₁ ≠ 1)
    (hord : orderOf g₁ = p) (x : G₁) : ∃ a : ZMod p, x = g₁ ^ a.val := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g₁ ^ k = x := mem_powers_of_prime_card hpG1 hg₁
  exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, ← hk, ← pow_mod_orderOf g₁ k, hord]⟩

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- The algebraic core of evaluation binding:
two valid KZG openings of the same commitment at the same point, but to different values, yield a
t-SDH solution with challenge `c = -query`.

This lemma is intentionally isolated from the probabilistic (game-based) binding game.
The proof of `binding_cond_le_t_sdh_cond` only needs to extract `hsrs` and the
two `verifyOpening` facts from the extended game, then apply this lemma. -/
lemma t_sdh_cond_of_two_valid_openings
    (τ query resp₁ resp₂ : ZMod p) (cm proof₁ proof₂ : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hresp : resp₁ ≠ resp₂) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₁ query resp₁)
    (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₂ query resp₂) :
    Groups.tSdhCondition (p := p) (g₁ := g₁)
      (τ, -query, (proof₁ / proof₂) ^ (1 / (resp₂ - resp₁)).val) := by
  have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
  have hord : orderOf g₁ = p := binding_order_of_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨cm', hcm⟩ := binding_exists_zmod_power_of_generator hpG1 hg₁ hord cm
  obtain ⟨prf₁, hprf₁⟩ :=
    binding_exists_zmod_power_of_generator hpG1 hg₁ hord proof₁
  obtain ⟨prf₂, hprf₂⟩ :=
    binding_exists_zmod_power_of_generator hpG1 hg₁ hord proof₂
  have hEq₁ : cm' - resp₁ = prf₁ * (τ - query) :=
    verify_opening_equation pairing query resp₁ τ cm' prf₁ cm proof₁ srs hsrs hpair hcm
      hprf₁ hverify₁
  have hEq₂ : cm' - resp₂ = prf₂ * (τ - query) :=
    verify_opening_equation pairing query resp₂ τ cm' prf₂ cm proof₂ srs hsrs hpair hcm
      hprf₂ hverify₂
  have hdenom : τ + -query ≠ 0 :=
    t_sdh_denominator_ne_zero_of_opening_equations τ query resp₁ resp₂ cm' prf₁ prf₂
      hresp hEq₁ hEq₂
  refine ⟨hdenom, ?_⟩
  have hfield_conflict : prf₁ * (τ - query) + resp₁ = prf₂ * (τ - query) + resp₂ := by
    linear_combination hEq₂ - hEq₁
  have hfield_solution : (prf₁ - prf₂) / (resp₂ - resp₁) = 1 / (τ - query) := by
    have hresp_ne : resp₂ - resp₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hresp)
    have hτq_ne : τ - query ≠ 0 := by simpa [sub_eq_add_neg] using hdenom
    rw [div_eq_div_iff hresp_ne hτq_ne]
    linear_combination hfield_conflict
  rw [hprf₁, hprf₂, Groups.gpow_div_eq hord, ← pow_mul, pow_eq_pow_iff_modEq, hord]
  change (prf₁ - prf₂).val * (1 / (resp₂ - resp₁)).val % p =
    (1 / (τ + -query)).val % p
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
  have hcast : (((prf₁ - prf₂).val * (1 / (resp₂ - resp₁)).val : ℕ) : ZMod p)
      = (1 / (τ + -query) : ZMod p) := by
    push_cast [ZMod.natCast_zmod_val]
    rw [mul_one_div, hfield_solution]
    ring
  have := congr_arg ZMod.val hcast
  rwa [ZMod.val_natCast] at this

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Adapter from the algebraic lemma to the concrete mapping used by the binding reduction. -/
lemma map_binding_to_t_sdh_of_two_valid_openings
    (τ query resp₁ resp₂ : ZMod p) (cm proof₁ proof₂ : G₁) (accept₁ accept₂ : Bool)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hresp : resp₁ ≠ resp₂) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₁ query resp₁)
    (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₂ query resp₂) :
    Groups.tSdhCondition (p := p) (g₁ := g₁)
      (mapBindingToTsdh (p := p) (n := n)
        (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂)) := by
  simpa [mapBindingToTsdh, mapBindingInstanceToTsdh] using
    t_sdh_cond_of_two_valid_openings (p := p) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      τ query resp₁ resp₂ cm proof₁ proof₂ srs hsrs hresp hg₁ hpair hverify₁ hverify₂

include g₁ g₂ pairing in
/-- The reduction breaking t-SDH using a successful evaluation-binding adversary. -/
def bindingReduction (AuxState : Type)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Groups.tSdhAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs =>
    letI kzgScheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    letI so : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
      QueryImpl.addLift
        (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
        (challengeQueryImpl (pSpec := ⟨!v[.P_to_V], !v[G₁]⟩))
    (simulateQ so
      (do
        let (ck, vk) := (srs, srs)
        let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim ck) _
        let reduction := Reduction.mk (adversary.prover ck) (kzgScheme.opening (ck, vk)).verifier
        let result₁ ← (reduction.run
          (cm, (⟨query, resp₁⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₁).run
        let result₂ ← (reduction.run
          (cm, (⟨query, resp₂⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₂).run
        let accept₁ := result₁.map (fun result => result.2) |>.getD false
        let accept₂ := result₂.map (fun result => result.2) |>.getD false
        let proof₁ : G₁ := result₁.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        let proof₂ : G₁ := result₂.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        return some (mapBindingInstanceToTsdh (p := p) (n := n)
          (srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))
      ))

/-- Relate two option-valued monadic computations before and after adding extended output. -/
lemma bind_two_option_project_get_d
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ δ ε ζ : Type} (mx : m (Option α)) (my : m (Option β))
    (fa : α → γ) (fb : β → δ) (da : γ) (db : δ)
    (mkBase : γ → δ → ε) (mkExt : Option α → Option β → ζ) (proj : ζ → ε)
    (hproj : ∀ x y, proj (mkExt x y) =
      mkBase ((Option.map fa x).getD da) ((Option.map fb y).getD db)) :
    (do
      let x ← Option.map fa <$> mx
      let y ← Option.map fb <$> my
      pure (some (mkBase (x.getD da) (y.getD db)))) =
    mx >>= fun x =>
      my >>= fun y =>
        pure (some (mkExt x y)) >>= pure ∘ Option.map proj := by
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    Option.map_some]
  congr 1
  funext x
  congr 1
  funext y
  simp [hproj]

/-- If `Option.map f x` defaults to `true`, then `x` contains a value satisfying `f`. -/
lemma exists_of_option_map_get_d_true {α : Type} (f : α → Bool) (x : Option α)
    (h : (Option.map f x).getD false = true) : ∃ a, x = some a ∧ f a = true := by
  cases x with
  | none => simp at h
  | some a =>
      exact ⟨a, rfl, by simpa using h⟩

omit [DecidableEq G₁] in
/-- Transition 1: extending the binding game output preserves the event. -/
lemma binding_game_ext_eq_binding_game {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[Commitment.bindingCondition (Data := Fin (n + 1) → ZMod p) |
      Commitment.bindingGame (init := pure ∅) (impl := randomOracle) (AuxState := AuxState)
        (scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))
        (adversary := adversary)]
    = Pr[bindingCondExt (p := p) (n := n) | bindingGameExt (g₁ := g₁) (g₂ := g₂)
      AuxState adversary (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  let proj : BindingExtOutput (p := p) n G₁ G₂ → BindingOutput (p := p) n :=
    fun ⟨_, _, _, query, resp₁, resp₂, accept₁, accept₂, _, _⟩ =>
      ⟨query, resp₁, resp₂, accept₁, accept₂⟩
  have hcond_eq :
      (bindingCondExt (p := p) (n := n) : _ → Prop) =
        (Commitment.bindingCondition (Data := Fin (n + 1) → ZMod p)) ∘ proj := by
    funext x
    rcases x with ⟨_, _, _, _, _, _, _, _, _, _⟩
    rfl
  rw [hcond_eq]
  apply OptionT.probEvent_eq_of_run_map_eq _ _ proj
    (Commitment.bindingCondition (Data := Fin (n + 1) → ZMod p))
  simp only [Commitment.bindingGame, bindingGameExt, kzg, OptionT.run, OptionT.mk]
  rw [pure_bind]
  have hsample :
      (simulateQ randomOracle (Groups.sampleNonzeroZMod (p := p))).run' ∅ =
        Groups.sampleNonzeroZMod (p := p) :=
    Groups.simulateQ_randomOracle_sampleNonzeroZMod (p := p)
  have hkeygen :
      (simulateQ randomOracle (do
        let a ← Groups.sampleNonzeroZMod (p := p)
        pure (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a,
          Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a))).run' ∅
        =
      (fun a => (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a,
        Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a))
          <$> Groups.sampleNonzeroZMod (p := p) := by
    calc
      (simulateQ randomOracle (do
        let a ← Groups.sampleNonzeroZMod (p := p)
        pure (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a,
          Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a))).run' ∅
          = (fun a => (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a,
              Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a))
              <$> (simulateQ randomOracle (Groups.sampleNonzeroZMod (p := p))).run' ∅ := by
            rw [← StateT.run'_map_comm, ← simulateQ_map]
            rfl
      _ = (fun a => (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a,
              Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n a))
              <$> Groups.sampleNonzeroZMod (p := p) := by
            rw [hsample]
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  let sample : ProbComp (ZMod p) := Groups.sampleNonzeroZMod (p := p)
  let bodyBase : ZMod p → OracleComp _ (Option (BindingOutput (p := p) n)) := fun τ => do
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
    let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
    let reduction := Reduction.mk (adversary.prover srs)
      ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
        (srs, srs)).verifier
    let accept₁ := (← (reduction.verdict
      (cm, (⟨query, resp₁⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
          OracleInterface.Response q)) st₁).run).getD false
    let accept₂ := (← (reduction.verdict
      (cm, (⟨query, resp₂⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
          OracleInterface.Response q)) st₂).run).getD false
    pure (some (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BindingOutput (p := p) n))
  let bodyExt : ZMod p → OracleComp _ (Option (BindingExtOutput (p := p) n G₁ G₂)) :=
    fun τ => do
      let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
      let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
      let reduction := Reduction.mk (adversary.prover srs)
        ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (srs, srs)).verifier
      let result₁ ← (reduction.run
        (cm, (⟨query, resp₁⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
        st₁).run
      let result₂ ← (reduction.run
        (cm, (⟨query, resp₂⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
        st₂).run
      let accept₁ := result₁.map (fun result => result.2) |>.getD false
      let accept₂ := result₂.map (fun result => result.2) |>.getD false
      let proof₁ : G₁ := result₁.map (fun result => result.1.1 0) |>.getD (1 : G₁)
      let proof₂ : G₁ := result₂.map (fun result => result.1.1 0) |>.getD (1 : G₁)
      pure (some (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))
  rw [hkeygen]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  change (OptionT.mk (do
    let τ ← sample
    (simulateQ impl (bodyBase τ)).run' (∅ : unifSpec.QueryCache))).run =
      (OptionT.mk (do
        let τ ← sample
        let r ← (simulateQ impl (bodyExt τ)).run' (∅ : unifSpec.QueryCache)
        pure (Option.map (proj) r))).run
  simpa only [id_map] using
    congrArg OptionT.run
      (OptionT.map_mk_bind_eq_of_body
        (sample := sample)
        (body₁ := fun τ => (simulateQ impl (bodyBase τ)).run' (∅ : unifSpec.QueryCache))
        (body₂ := fun τ => (simulateQ impl (bodyExt τ)).run' (∅ : unifSpec.QueryCache))
        (f := id) (post := fun _ => proj)
        (hBody := by
          intro τ
          rw [← StateT.run'_map_comm (Option.map id),
            ← StateT.run'_map_comm (Option.map proj)]
          apply congrArg (fun mx : StateT unifSpec.QueryCache ProbComp
            (Option (BindingOutput (p := p) n)) => mx.run' ∅)
          dsimp only [bodyBase, bodyExt]
          rw [← simulateQ_map, ← simulateQ_map]
          apply congrArg (simulateQ impl)
          simp only [map_eq_bind_pure_comp, bind_assoc]
          congr 1
          funext claim
          rcases claim with ⟨cm, query, resp₁, resp₂, st₁, st₂⟩
          rw [Reduction.verdict_run_eq_map_run, Reduction.verdict_run_eq_map_run]
          exact bind_two_option_project_get_d
            (mx := ((Reduction.mk
              (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
              ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
                (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
                  Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier).run
              (cm, (⟨query, resp₁⟩ :
                (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                  OracleInterface.Response q)) st₁).run)
            (my := ((Reduction.mk
              (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
              ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
                (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
                  Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier).run
              (cm, (⟨query, resp₂⟩ :
                (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                  OracleInterface.Response q)) st₂).run)
            (fa := fun result : (FullTranscript pSpec' × Bool × Unit) × Bool => result.2)
            (fb := fun result : (FullTranscript pSpec' × Bool × Unit) × Bool => result.2)
            (da := false) (db := false)
            (mkBase := fun accept₁ accept₂ =>
              (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BindingOutput (p := p) n))
            (mkExt := fun result₁ result₂ =>
              (τ, Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ, cm, query,
                resp₁, resp₂,
                (Option.map (fun result => result.2) result₁).getD false,
                (Option.map (fun result => result.2) result₂).getD false,
                (Option.map (fun result => result.1.1 0) result₁).getD (1 : G₁),
                (Option.map (fun result => result.1.1 0) result₂).getD (1 : G₁)))
            (proj := proj) (by intro result₁ result₂; rfl)))

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Transition 2: a successful extended binding run maps to a successful t-SDH instance. -/
lemma binding_cond_le_t_sdh_cond {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[bindingCondExt (p := p) (n := n) | bindingGameExt (g₁ := g₁) (g₂ := g₂)
      AuxState adversary (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(Groups.tSdhCondition (p := p) (g₁ := g₁)) ∘ mapBindingToTsdh (p := p)
        (n := n) |
      bindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  let Claim : Type :=
    G₁ × (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
      OracleInterface.Response q × OracleInterface.Response q × AuxState × AuxState
  letI : ∀ i, OracleInterface (pSpec'.Challenge i) := ProtocolSpec.challengeOracleInterface
  let RunResult : Type := (FullTranscript pSpec' × Bool × Unit) × Bool
  let spec' := unifSpec + [pSpec'.Challenge]ₒ
  let sample : ProbComp (ZMod p) := Groups.sampleNonzeroZMod (p := p)
  let body : ZMod p → OracleComp spec' Claim := fun τ =>
    liftComp (adversary.claim (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)) spec'
  let run₁ : ZMod p → Claim → OracleComp spec' (Option RunResult) := fun τ claim =>
    (Reduction.run
      (claim.1, (⟨claim.2.1, claim.2.2.1⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
      claim.2.2.2.2.1
      (Reduction.mk
        (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
        ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
           Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier)).run
  let run₂ : ZMod p → Claim → OracleComp spec' (Option RunResult) := fun τ claim =>
    (Reduction.run
      (claim.1, (⟨claim.2.1, claim.2.2.2.1⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
      claim.2.2.2.2.2
      (Reduction.mk (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
        ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
           Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier)).run
  let pack : ZMod p → Claim → Option RunResult → Option RunResult →
      BindingExtOutput (p := p) n G₁ G₂ := fun τ claim result₁ result₂ =>
    (τ, Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ, claim.1, claim.2.1,
      claim.2.2.1,
      claim.2.2.2.1, (Option.map (fun result => result.2) result₁).getD false,
      (Option.map (fun result => result.2) result₂).getD false,
      (Option.map (fun result => result.1.1 0) result₁).getD (1 : G₁),
      (Option.map (fun result => result.1.1 0) result₂).getD (1 : G₁))
  let gameComp : ZMod p → OracleComp spec' (Option (BindingExtOutput (p := p) n G₁ G₂)) :=
    fun τ => do
      let claim ← body τ
      let result₁ ← run₁ τ claim
      let result₂ ← run₂ τ claim
      pure (some (pack τ claim result₁ result₂))
  let P : BindingExtOutput (p := p) n G₁ G₂ → Prop := bindingCondExt (p := p) (n := n)
  let Q : BindingExtOutput (p := p) n G₁ G₂ → Prop :=
    (Groups.tSdhCondition (p := p) (g₁ := g₁)) ∘ mapBindingToTsdh (p := p) (n := n)
  have hmono :
      Pr[P | OptionT.mk (do
        let τ ← sample
        (simulateQ impl (gameComp τ)).run' (∅ : unifSpec.QueryCache))]
      ≤ Pr[Q | OptionT.mk (do
        let τ ← sample
        (simulateQ impl (gameComp τ)).run' (∅ : unifSpec.QueryCache))] := by
    apply probEvent_mono
    intro y hy hP
    obtain ⟨τ, _, hy⟩ := OptionT.mem_support_bind_mk _ _ hy
    refine OptionT.aux_mem_support_simulateQ_run' impl (gameComp τ)
      (∅ : unifSpec.QueryCache) (fun y => P y → Q y) ?_ hy hP
    intro x hx y' hxy hP'
    rw [hxy] at hx
    dsimp only [gameComp] at hx
    obtain ⟨claim, _, hx⟩ :=
      support_bind_exists (x := body τ)
        (f := fun claim => do
          let result₁ ← run₁ τ claim
          let result₂ ← run₂ τ claim
          pure (some (pack τ claim result₁ result₂))) hx
    obtain ⟨result₁, hresult₁, hx⟩ :=
      support_bind_exists (x := run₁ τ claim)
        (f := fun result₁ => do
          let result₂ ← run₂ τ claim
          pure (some (pack τ claim result₁ result₂))) hx
    obtain ⟨result₂, hresult₂, hx⟩ :=
      support_bind_exists (x := run₂ τ claim)
        (f := fun result₂ => pure (some (pack τ claim result₁ result₂))) hx
    have hy' : y' = pack τ claim result₁ result₂ := by
      have : some y' = some (pack τ claim result₁ result₂) := by
        simpa [mem_support_pure_iff] using hx
      exact Option.some.inj this
    subst y'
    clear hxy hx hy
    rcases claim with ⟨cm, query, resp₁, resp₂, st₁, st₂⟩
    dsimp [P, pack, bindingCondExt, Commitment.bindingCondition] at hP'
    rcases hP' with ⟨hresp, haccept₁, haccept₂⟩
    obtain ⟨out₁, hrun₁, haccept₁⟩ :=
      exists_of_option_map_get_d_true (fun result : RunResult => result.2) result₁
        haccept₁
    obtain ⟨out₂, hrun₂, haccept₂⟩ :=
      exists_of_option_map_get_d_true (fun result : RunResult => result.2) result₂
        haccept₂
    dsimp [run₁] at hresult₁
    dsimp [run₂] at hresult₂
    have hverify₁ :
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ).2 cm
          ((Option.map (fun result : RunResult => result.1.1 0) result₁).getD (1 : G₁))
          query resp₁ := by
      rw [hrun₁] at hresult₁
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk
            (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
               Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ).2 stmt.1
              (td ⟨0, by decide⟩) stmt.2.1 stmt.2.2)
          (by intros; rfl)
          (cm, (⟨query, resp₁⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))
          st₁ hresult₁ rfl
      have hproof :
          (Option.map (fun result : RunResult => result.1.1 0) result₁).getD (1 : G₁) =
            out₁.1.1 0 := by simp [hrun₁]
      rw [hproof]
      exact hverif.symm.trans haccept₁
    have hverify₂ :
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ).2 cm
          ((Option.map (fun result : RunResult => result.1.1 0) result₂).getD (1 : G₁))
          query resp₂ := by
      rw [hrun₂] at hresult₂
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk
            (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ,
               Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ).2 stmt.1
              (td ⟨0, by decide⟩) stmt.2.1 stmt.2.2)
          (by intros; rfl)
          (cm, (⟨query, resp₂⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))
          st₂ hresult₂ rfl
      have hproof :
          (Option.map (fun result : RunResult => result.1.1 0) result₂).getD (1 : G₁) =
            out₂.1.1 0 := by simp [hrun₂]
      rw [hproof]
      exact hverif.symm.trans haccept₂
    exact map_binding_to_t_sdh_of_two_valid_openings (p := p) (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) τ query resp₁ resp₂ cm
      ((Option.map (fun result : RunResult => result.1.1 0) result₁).getD (1 : G₁))
      ((Option.map (fun result : RunResult => result.1.1 0) result₂).getD (1 : G₁))
      ((Option.map (fun result : RunResult => result.2) result₁).getD false)
      ((Option.map (fun result : RunResult => result.2) result₂).getD false)
      (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ) rfl hresp hg₁ hpair
      hverify₁ hverify₂
  simpa only [bindingGameExt, kzg, OptionT.mk, pSpec', impl, sample, body, run₁, run₂,
      pack, gameComp, P, Q] using hmono

omit [DecidableEq G₁] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event. -/
lemma map_binding_instance_drag {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :
    Pr[(Groups.tSdhCondition (p := p) (g₁ := g₁)) ∘ mapBindingToTsdh (p := p)
        (n := n) |
      bindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[Groups.tSdhCondition (p := p) (g₁ := g₁) |
      mapBindingToTsdh (p := p) (n := n) <$> bindingGameExt (g₁ := g₁) (g₂ := g₂)
        AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Transition 4: the mapped extended binding game is the t-SDH experiment. -/
lemma t_sdh_game_eq {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[Groups.tSdhCondition (p := p) (g₁ := g₁) |
      mapBindingToTsdh (p := p) (n := n) <$> bindingGameExt (g₁ := g₁) (g₂ := g₂)
        AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) AuxState
        adversary) := by
  let scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.tSdhExperiment]
  congr 1
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  simpa only [bindingGameExt, bindingReduction, kzg, OptionT.mk, pSpec', impl, scheme,
      OptionT.run_map] using
    OptionT.map_mk_bind_eq_of_body
      (sample := (Groups.sampleNonzeroZMod (p := p) : ProbComp (ZMod p)))
      (body₁ := fun τ => (simulateQ impl (do
        let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
        let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let result₁ ← (reduction.run
          (cm, (⟨query, resp₁⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₁).run
        let result₂ ← (reduction.run
          (cm, (⟨query, resp₂⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₂).run
        let accept₁ := result₁.map (fun result => result.2) |>.getD false
        let accept₂ := result₂.map (fun result => result.2) |>.getD false
        let proof₁ : G₁ := result₁.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        let proof₂ : G₁ := result₂.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        pure (some (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁,
          proof₂)))).run' (∅ : unifSpec.QueryCache))
      (body₂ := fun τ => (simulateQ impl (do
        let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
        let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
        let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
        let result₁ ← (reduction.run
          (cm, (⟨query, resp₁⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₁).run
        let result₂ ← (reduction.run
          (cm, (⟨query, resp₂⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
          st₂).run
        let accept₁ := result₁.map (fun result => result.2) |>.getD false
        let accept₂ := result₂.map (fun result => result.2) |>.getD false
        let proof₁ : G₁ := result₁.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        let proof₂ : G₁ := result₂.map (fun result => result.1.1 0) |>.getD (1 : G₁)
        pure (some (mapBindingInstanceToTsdh (p := p) (n := n)
          (srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))))).run'
            (∅ : unifSpec.QueryCache))
      (f := mapBindingToTsdh (p := p) (n := n))
      (post := fun τ ((c, h) : ZMod p × G₁) => (τ, c, h))
      (hBody := by
        intro τ
        dsimp only
        refine StateT.map_run'_eq_of_map_eq _ _ _ _ (∅ : unifSpec.QueryCache) ?_
        simp only [simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        congr 1)

omit [DecidableEq G₁] in
/-- The t-SDH experiment is bounded by the t-SDH error. -/
lemma t_sdh_error_bound {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (tSdhError : ℝ≥0)
    (htSdh : Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂)
      (g₁ := g₁) (g₂ := g₂) n tSdhError)
    (adversary : KzgBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) AuxState adversary)
    ≤ tSdhError := by
  exact htSdh (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) AuxState
    adversary)

omit [DecidableEq G₁] in
/-- The KZG scheme satisfies evaluation binding provided `t`-SDH holds. -/
theorem binding {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (tSdhError : ℝ≥0)
    (htSdh : Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁)
      (g₂ := g₂) n tSdhError) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) tSdhError := by
  letI scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.binding]
  intro AuxState adversary
  letI game := Commitment.bindingGame (init := pure ∅) (impl := randomOracle)
    (AuxState := AuxState) (scheme := scheme) (adversary := adversary)
  letI game_ext := bindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[Commitment.bindingCondition (Data := Fin (n + 1) → ZMod p) | game]
    _ = Pr[bindingCondExt (p := p) (n := n) | game_ext] :=
      binding_game_ext_eq_binding_game (pairing := pairing) adversary
    _ ≤ Pr[(Groups.tSdhCondition (p := p) (g₁ := g₁)) ∘ mapBindingToTsdh (p := p)
        (n := n) | game_ext] :=
      binding_cond_le_t_sdh_cond (pairing := pairing) hg₁ hpair adversary
    _ = Pr[Groups.tSdhCondition (p := p) (g₁ := g₁) |
        mapBindingToTsdh (p := p) (n := n) <$> game_ext] :=
      map_binding_instance_drag adversary scheme
    _ = Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) AuxState adversary) :=
      t_sdh_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) adversary
    _ ≤ tSdhError := t_sdh_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      tSdhError htSdh adversary)

end Binding

end CommitmentScheme

end KZG
