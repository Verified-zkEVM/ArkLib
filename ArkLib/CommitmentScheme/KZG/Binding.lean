/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.FunctionBinding
import ArkLib.ToVCVio.EvalDist.Defs.Support

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

abbrev BOutput (n : ℕ) :=
  (query : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
    OracleInterface.Response query × OracleInterface.Response query × Bool × Bool

abbrev BExtOutput (n : ℕ) (G₁ G₂ : Type) :=
  ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    ZMod p × ZMod p × ZMod p × Bool × Bool × G₁ × G₁

/-- Abbreviation for a binding adversary for KZG. -/
abbrev KZGBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (AuxState : Type) :=
  Commitment.BindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

/-- t-SDH condition for an adversary to win. -/
def tSDH_cond : (ZMod p × ZMod p × G₁) → Prop :=
  fun (τ, c, h) => τ + c ≠ 0 ∧ h = g₁ ^ (1 / (τ + c)).val

/-- Evaluation binding condition for an adversary to win. -/
def B_cond : BOutput (p := p) n → Prop :=
  fun ⟨_, resp₁, resp₂, accept₁, accept₂⟩ =>
    resp₁ ≠ resp₂ ∧ accept₁ ∧ accept₂

/-- Extended evaluation binding condition, carrying values needed by the reduction. -/
def B_cond_ext : BExtOutput (p := p) n G₁ G₂ → Prop :=
  fun ⟨_, _, _, query, resp₁, resp₂, accept₁, accept₂, _, _⟩ =>
    B_cond (p := p) (n := n)
      (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BOutput (p := p) n)

/-- Evaluation binding game. -/
def B_game {n : ℕ} (AuxState : Type)
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) : OptionT ProbComp (BOutput (p := p) n) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    (simulateQ (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp)) <|
        (do
          let (ck, vk) ← liftComp scheme.keygen _
          let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim ck) _
          let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
          let accept₁ := (← (reduction.verdict
            (cm, (⟨query, resp₁⟩ :
              (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                OracleInterface.Response q)) st₁).run).getD false
          let accept₂ := (← (reduction.verdict
            (cm, (⟨query, resp₂⟩ :
              (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                OracleInterface.Response q)) st₂).run).getD false
          pure (some (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BOutput (p := p) n))
        : OracleComp _ _)).run' ∅

/-- Extended evaluation binding game, returning the two proof elements in addition to verdicts. -/
def B_game_ext {n : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) : OptionT ProbComp (BExtOutput (p := p) n G₁ G₂) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    (simulateQ
      (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
      <|
      (do
        let τ ← liftComp ($ᵗ (ZMod p)) _
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
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
        pure (some (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))
      : OracleComp _ _)).run' ∅

/-- The instance-level map used by the t-SDH reduction. -/
def map_B_instance_to_tSDH
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      ZMod p × ZMod p × ZMod p × Bool × Bool × G₁ × G₁) : ZMod p × G₁ :=
  let (_, _, query, resp₁, resp₂, _, _, proof₁, proof₂) := val
  (-query, (proof₁ / proof₂) ^ (1 / (resp₂ - resp₁)).val)

/-- Map an extended binding-game output to a t-SDH instance.

This is the main algebraic extraction step and is intentionally left as a skeleton for now. -/
def map_B_to_tSDH
    (val : BExtOutput (p := p) n G₁ G₂) : ZMod p × ZMod p × G₁ :=
  (val.1, map_B_instance_to_tSDH (p := p) (n := n) val.2)

set_option linter.unusedSectionVars false in
omit [Fact (0 < p)] [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] [Group G₂]
  [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
/-- If two accepted openings at the same query give different responses, the t-SDH denominator
`τ + (-query)` cannot vanish. This is the small algebraic contradiction used to avoid a separate
`query = τ` branch in the binding reduction. -/
lemma tSDH_denominator_ne_zero_of_opening_equations
    (τ query resp₁ resp₂ cm prf₁ prf₂ : ZMod p) (hresp : resp₁ ≠ resp₂)
    (hverifyEq₁ : cm - resp₁ = prf₁ * (τ - query))
    (hverifyEq₂ : cm - resp₂ = prf₂ * (τ - query)) :
    τ + -query ≠ 0 := by
  intro hzero
  have hτq : τ - query = 0 := by
    simpa [sub_eq_add_neg] using hzero
  have hcm₁ : cm = resp₁ := by
    simp [hτq] at hverifyEq₁
    exact sub_eq_zero.mp hverifyEq₁
  have hcm₂ : cm = resp₂ := by
    simp [hτq] at hverifyEq₂
    exact sub_eq_zero.mp hverifyEq₂
  exact hresp (hcm₁.symm.trans hcm₂)

omit [Fact (0 < p)] [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma binding_orderOf_eq_prime_of_ne_one (x : G₁) (hx : x ≠ 1) : orderOf x = p := by
  have hdvd := orderOf_dvd_natCard (G := G₁) x
  rw [PrimeOrderWith.hCard] at hdvd
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
  · exact absurd (orderOf_eq_one_iff.1 h1) hx
  · exact hp'

omit [Fact (0 < p)] [DecidableEq G₁] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma binding_exists_zmod_power_of_generator (hpG1 : Nat.card G₁ = p) (hg₁ : g₁ ≠ 1)
    (hord : orderOf g₁ = p) (x : G₁) : ∃ a : ZMod p, x = g₁ ^ a.val := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g₁ ^ k = x := mem_powers_of_prime_card hpG1 hg₁
  exact ⟨(k : ZMod p), by rw [ZMod.val_natCast, ← hk, ← pow_mod_orderOf g₁ k, hord]⟩

include g₁ g₂ pairing in
/-- The algebraic core of evaluation binding:
two valid KZG openings of the same commitment at the same point, but to different values, yield a
t-SDH solution with challenge `c = -query`.

This lemma is intentionally isolated from the probabilistic binding game. The future proof of
`B_cond_le_tSDH_cond` should only need to extract `hsrs` and the two `verifyOpening` facts from the
extended game, then apply this lemma. -/
lemma tSDH_cond_of_two_valid_openings
    (τ query resp₁ resp₂ : ZMod p) (cm proof₁ proof₂ : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hresp : resp₁ ≠ resp₂) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₁ query resp₁)
    (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₂ query resp₂) :
    tSDH_cond (p := p) (g₁ := g₁)
      (τ, -query, (proof₁ / proof₂) ^ (1 / (resp₂ - resp₁)).val) := by
  have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
  have hord : orderOf g₁ = p := binding_orderOf_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨cm', hcm⟩ := binding_exists_zmod_power_of_generator hpG1 hg₁ hord cm
  obtain ⟨prf₁, hprf₁⟩ :=
    binding_exists_zmod_power_of_generator hpG1 hg₁ hord proof₁
  obtain ⟨prf₂, hprf₂⟩ :=
    binding_exists_zmod_power_of_generator hpG1 hg₁ hord proof₂
  have hEq₁ : cm' - resp₁ = prf₁ * (τ - query) :=
    verifyOpening_equation pairing query resp₁ τ cm' prf₁ cm proof₁ srs hsrs hpair hverify₁
      hcm hprf₁
  have hEq₂ : cm' - resp₂ = prf₂ * (τ - query) :=
    verifyOpening_equation pairing query resp₂ τ cm' prf₂ cm proof₂ srs hsrs hpair hverify₂
      hcm hprf₂
  have hdenom : τ + -query ≠ 0 :=
    tSDH_denominator_ne_zero_of_opening_equations τ query resp₁ resp₂ cm' prf₁ prf₂
      hresp hEq₁ hEq₂
  refine ⟨hdenom, ?_⟩
  have hfield_conflict : prf₁ * (τ - query) + resp₁ = prf₂ * (τ - query) + resp₂ := by
    linear_combination hEq₂ - hEq₁
  have hfield_solution : (prf₁ - prf₂) / (resp₂ - resp₁) = 1 / (τ - query) := by
    have hresp_ne : resp₂ - resp₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hresp)
    have hτq_ne : τ - query ≠ 0 := by simpa [sub_eq_add_neg] using hdenom
    rw [div_eq_div_iff hresp_ne hτq_ne]
    linear_combination hfield_conflict
  rw [hprf₁, hprf₂, gpow_div_eq hord, ← pow_mul, pow_eq_pow_iff_modEq, hord]
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

include g₁ g₂ pairing in
/-- Adapter from the algebraic lemma to the concrete mapping used by the binding reduction. -/
lemma map_B_to_tSDH_of_two_valid_openings
    (τ query resp₁ resp₂ : ZMod p) (cm proof₁ proof₂ : G₁) (accept₁ accept₂ : Bool)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
    (hresp : resp₁ ≠ resp₂) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₁ query resp₁)
    (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      srs.2 cm proof₂ query resp₂) :
    tSDH_cond (p := p) (g₁ := g₁)
      (map_B_to_tSDH (p := p) (n := n)
        (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂)) := by
  simpa [map_B_to_tSDH, map_B_instance_to_tSDH] using
    tSDH_cond_of_two_valid_openings (p := p) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      τ query resp₁ resp₂ cm proof₁ proof₂ srs hsrs hresp hg₁ hpair hverify₁ hverify₂

include g₁ g₂ pairing in
/-- The reduction breaking t-SDH using a successful evaluation-binding adversary. -/
def bindingReduction (_hn : 1 ≤ n) (AuxState : Type)
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Groups.tSDHAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs =>
    letI kzgScheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
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
        return some (map_B_instance_to_tSDH (p := p) (n := n)
          (srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))
      ))

lemma Reduction.verdict_run_eq_map_run
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (reduction.verdict stmt wit).run =
      Option.map (fun result : (FullTranscript pSpec × StmtOut × WitOut) × StmtOut =>
        result.2) <$> (reduction.run stmt wit).run := by
  simp [Reduction.verdict, OptionT.run_map]

lemma bind_two_option_project_getD
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

lemma exists_of_option_map_getD_true {α : Type} (f : α → Bool) (x : Option α)
    (h : (Option.map f x).getD false = true) : ∃ a, x = some a ∧ f a = true := by
  cases x with
  | none => simp at h
  | some a =>
      exact ⟨a, rfl, by simpa using h⟩

omit [Fact (0 < p)] [DecidableEq G₁] in
/-- Transition 1: extending the binding game output preserves the event. -/
lemma B_game_ext_eq_B_game {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[B_cond (p := p) (n := n) | B_game AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Pr[B_cond_ext (p := p) (n := n) | B_game_ext (g₁ := g₁) (g₂ := g₂)
      AuxState adversary (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  let proj : BExtOutput (p := p) n G₁ G₂ → BOutput (p := p) n :=
    fun x => ⟨x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
      x.2.2.2.2.2.2.2.1⟩
  have hcond_eq : (B_cond_ext (p := p) (n := n) : _ → Prop) =
      (B_cond (p := p) (n := n)) ∘ proj := by
    funext x
    rcases x with ⟨_, _, _, _, _, _, _, _, _, _⟩
    rfl
  rw [hcond_eq]
  apply OptionT.probEvent_eq_of_run_map_eq _ _ proj (B_cond (p := p) (n := n))
  simp only [B_game, B_game_ext, KZG, OptionT.run, OptionT.mk]
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  let sample : OracleComp unifSpec (ZMod p) := $ᵗ (ZMod p)
  let Srs : Type := Vector G₁ (n + 1) × Vector G₂ 2
  let mk : ZMod p → Srs × Srs := fun τ =>
    let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
    (srs, srs)
  let bodyKey : Srs × Srs → OracleComp _ (Option (BOutput (p := p) n)) := fun key => do
      let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim key.1) _
      let reduction := Reduction.mk (adversary.prover key.1)
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening key).verifier
      let accept₁ := (← (reduction.verdict
        (cm, (⟨query, resp₁⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
            OracleInterface.Response q)) st₁).run).getD false
      let accept₂ := (← (reduction.verdict
        (cm, (⟨query, resp₂⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
            OracleInterface.Response q)) st₂).run).getD false
      pure (some (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BOutput (p := p) n))
  let bodyBase : ZMod p → OracleComp _ (Option (BOutput (p := p) n)) := fun τ => bodyKey (mk τ)
  let bodyExt : ZMod p → OracleComp _ (Option (BExtOutput (p := p) n G₁ G₂)) := fun τ => do
      let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
      let ⟨cm, query, resp₁, resp₂, st₁, st₂⟩ ← liftComp (adversary.claim srs) _
      let reduction := Reduction.mk (adversary.prover srs)
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening (srs, srs)).verifier
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
  trans (simulateQ impl (do
      let τ ← OracleComp.liftComp sample _
      bodyBase τ)).run' (∅ : unifSpec.QueryCache)
  · apply congrArg (fun oa => (simulateQ impl oa).run' (∅ : unifSpec.QueryCache))
    calc
      (do
        let k ← OracleComp.liftComp (do let τ ← sample; pure (mk τ)) _
        bodyKey k)
        = (do
          let k ← mk <$> OracleComp.liftComp sample _
          bodyKey k) := by rw [OracleComp.liftComp_bind_pure]
      _ = (do
        let τ ← OracleComp.liftComp sample _
        bodyKey (mk τ)) := OracleComp.bind_liftComp_map sample mk bodyKey
  · refine StateT.run'_simulateQ_bind_map_eq_of_body
      (impl := impl) (oa := OracleComp.liftComp sample _) (body₁ := bodyBase)
      (body₂ := bodyExt) (f := Option.map proj) (s := (∅ : unifSpec.QueryCache)) ?_
    intro τ
    dsimp only [bodyBase, bodyKey, bodyExt, mk]
    rw [← simulateQ_map]
    apply congrArg (simulateQ impl)
    simp only [map_eq_bind_pure_comp, bind_assoc]
    congr 1
    funext claim
    rcases claim with ⟨cm, query, resp₁, resp₂, st₁, st₂⟩
    rw [Reduction.verdict_run_eq_map_run, Reduction.verdict_run_eq_map_run]
    exact bind_two_option_project_getD
      (mx := ((Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
            generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier).run
        (cm, (⟨query, resp₁⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
            OracleInterface.Response q)) st₁).run)
      (my := ((Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
            generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier).run
        (cm, (⟨query, resp₂⟩ :
          (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
            OracleInterface.Response q)) st₂).run)
      (fa := fun result : (FullTranscript pSpec' × Bool × Unit) × Bool => result.2)
      (fb := fun result : (FullTranscript pSpec' × Bool × Unit) × Bool => result.2)
      (da := false) (db := false)
      (mkBase := fun accept₁ accept₂ =>
        (⟨query, resp₁, resp₂, accept₁, accept₂⟩ : BOutput (p := p) n))
      (mkExt := fun result₁ result₂ =>
        (τ, generateSrs (g₁ := g₁) (g₂ := g₂) n τ, cm, query, resp₁, resp₂,
          (Option.map (fun result => result.2) result₁).getD false,
          (Option.map (fun result => result.2) result₂).getD false,
          (Option.map (fun result => result.1.1 0) result₁).getD (1 : G₁),
          (Option.map (fun result => result.1.1 0) result₂).getD (1 : G₁)))
      (proj := proj) (by intro result₁ result₂; rfl)

include g₁ g₂ pairing in
/-- Transition 2: a successful extended binding run maps to a successful t-SDH instance. -/
lemma B_cond_le_tSDH_cond {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (_hn : 1 ≤ n) (_hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[B_cond_ext (p := p) (n := n) | B_game_ext (g₁ := g₁) (g₂ := g₂)
      AuxState adversary (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(tSDH_cond (p := p) (g₁ := g₁)) ∘ map_B_to_tSDH (p := p) (n := n) |
      B_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
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
  let sample : OracleComp unifSpec (ZMod p) := $ᵗ (ZMod p)
  let body : ZMod p → OracleComp spec' Claim := fun τ =>
    liftComp (adversary.claim (generateSrs (g₁ := g₁) (g₂ := g₂) n τ)) spec'
  let run₁ : ZMod p → Claim → OracleComp spec' (Option RunResult) := fun τ claim =>
    (Reduction.run
      (claim.1, (⟨claim.2.1, claim.2.2.1⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
      claim.2.2.2.2.1
      (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
           generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier)).run
  let run₂ : ZMod p → Claim → OracleComp spec' (Option RunResult) := fun τ claim =>
    (Reduction.run
      (claim.1, (⟨claim.2.1, claim.2.2.2.1⟩ :
        (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) × OracleInterface.Response q))
      claim.2.2.2.2.2
      (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
        ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
           generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier)).run
  let pack : ZMod p → Claim → Option RunResult → Option RunResult →
      BExtOutput (p := p) n G₁ G₂ := fun τ claim result₁ result₂ =>
    (τ, generateSrs (g₁ := g₁) (g₂ := g₂) n τ, claim.1, claim.2.1, claim.2.2.1,
      claim.2.2.2.1, (Option.map (fun result => result.2) result₁).getD false,
      (Option.map (fun result => result.2) result₂).getD false,
      (Option.map (fun result => result.1.1 0) result₁).getD (1 : G₁),
      (Option.map (fun result => result.1.1 0) result₂).getD (1 : G₁))
  let P : BExtOutput (p := p) n G₁ G₂ → Prop := B_cond_ext (p := p) (n := n)
  let Q : BExtOutput (p := p) n G₁ G₂ → Prop :=
    (tSDH_cond (p := p) (g₁ := g₁)) ∘ map_B_to_tSDH (p := p) (n := n)
  let gameComp : OracleComp spec' (Option (BExtOutput (p := p) n G₁ G₂)) := do
    let τ ← OracleComp.liftComp sample spec'
    let claim ← body τ
    let result₁ ← run₁ τ claim
    let result₂ ← run₂ τ claim
    pure (some (pack τ claim result₁ result₂))
  have hmono :
      Pr[P | OptionT.mk ((simulateQ impl gameComp).run' (∅ : unifSpec.QueryCache))]
      ≤ Pr[Q | OptionT.mk ((simulateQ impl gameComp).run' (∅ : unifSpec.QueryCache))] := by
    apply probEvent_mono
    intro y hy hP
    refine OptionT.aux_mem_support_simulateQ_run' impl gameComp
      (∅ : unifSpec.QueryCache) (fun y => P y → Q y) ?_ hy hP
    intro x hx y' hxy hP'
    rw [hxy] at hx
    dsimp only [gameComp] at hx
    obtain ⟨τ, _, hx⟩ :=
      support_bind_exists (x := OracleComp.liftComp sample spec')
        (f := fun τ => do
          let claim ← body τ
          let result₁ ← run₁ τ claim
          let result₂ ← run₂ τ claim
          pure (some (pack τ claim result₁ result₂))) hx
    obtain ⟨claim, hclaim, hx⟩ :=
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
      have := eq_of_mem_support_pure hx
      simpa using Option.some.inj this
    subst y'
    clear hxy hx hy
    rcases claim with ⟨cm, query, resp₁, resp₂, st₁, st₂⟩
    dsimp [P, pack, B_cond_ext, B_cond] at hP'
    rcases hP' with ⟨hresp, haccept₁, haccept₂⟩
    obtain ⟨out₁, hrun₁, haccept₁⟩ :=
      exists_of_option_map_getD_true (fun result : RunResult => result.2) result₁
        haccept₁
    obtain ⟨out₂, hrun₂, haccept₂⟩ :=
      exists_of_option_map_getD_true (fun result : RunResult => result.2) result₂
        haccept₂
    dsimp [run₁] at hresult₁
    dsimp [run₂] at hresult₂
    have hverify₁ :
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ).2 cm
          ((Option.map (fun result : RunResult => result.1.1 0) result₁).getD (1 : G₁))
          query resp₁ := by
      rw [hrun₁] at hresult₁
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
            ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
               generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ).2 stmt.1
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
          (generateSrs (g₁ := g₁) (g₂ := g₂) n τ).2 cm
          ((Option.map (fun result : RunResult => result.1.1 0) result₂).getD (1 : G₁))
          query resp₂ := by
      rw [hrun₂] at hresult₂
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk (adversary.prover (generateSrs (g₁ := g₁) (g₂ := g₂) n τ))
            ((KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ,
               generateSrs (g₁ := g₁) (g₂ := g₂) n τ)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (generateSrs (g₁ := g₁) (g₂ := g₂) n τ).2 stmt.1
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
    exact map_B_to_tSDH_of_two_valid_openings (p := p) (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) τ query resp₁ resp₂ cm
      ((Option.map (fun result : RunResult => result.1.1 0) result₁).getD (1 : G₁))
      ((Option.map (fun result : RunResult => result.1.1 0) result₂).getD (1 : G₁))
      ((Option.map (fun result : RunResult => result.2) result₁).getD false)
      ((Option.map (fun result : RunResult => result.2) result₂).getD false)
      (generateSrs (g₁ := g₁) (g₂ := g₂) n τ) rfl hresp hg₁ hpair
      hverify₁ hverify₂
  simpa only [B_game_ext, KZG, OptionT.mk, pSpec', impl, spec', sample, body, run₁, run₂,
      pack, gameComp, P, Q] using hmono

omit [Fact (0 < p)] [DecidableEq G₁] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event. -/
lemma map_B_instance_drag {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) G₁ Unit
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2)
      ⟨!v[.P_to_V], !v[G₁]⟩) :
    Pr[(tSDH_cond (p := p) (g₁ := g₁)) ∘ map_B_to_tSDH (p := p) (n := n) |
      B_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[tSDH_cond (p := p) (g₁ := g₁) |
      map_B_to_tSDH (p := p) (n := n) <$> B_game_ext (g₁ := g₁) (g₂ := g₂)
        AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

omit [Fact (0 < p)] [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Transition 4: the mapped extended binding game is the t-SDH experiment. -/
lemma tSDH_game_eq {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Pr[tSDH_cond (p := p) (g₁ := g₁) |
      map_B_to_tSDH (p := p) (n := n) <$> B_game_ext (g₁ := g₁) (g₂ := g₂)
        AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.tSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn AuxState adversary) := by
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.tSDH_Experiment]
  congr 1
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  simpa only [B_game_ext, bindingReduction, KZG, OptionT.mk, pSpec', impl, scheme,
      OptionT.run_map] using
    OptionT.map_mk_run'_simulateQ_bind_eq_of_body
      (impl := impl)
      (impl₀ := randomOracle)
      (oa := OracleComp.liftComp (($ᵗ (ZMod p)) : OracleComp unifSpec (ZMod p)) _)
      (oa₀ := (($ᵗ (ZMod p)) : OracleComp unifSpec (ZMod p)))
      (body₁ := fun τ => do
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
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
        pure (some (τ, srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂)))
      (body₂ := fun τ => do
        let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n τ
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
        pure (some (map_B_instance_to_tSDH (p := p) (n := n)
          (srs, cm, query, resp₁, resp₂, accept₁, accept₂, proof₁, proof₂))))
      (f := map_B_to_tSDH (p := p) (n := n))
      (post := fun τ ((c, h) : ZMod p × G₁) => (τ, c, h))
      (s := (∅ : unifSpec.QueryCache))
      (hSample := by
        simp only [impl, pSpec', QueryImpl.addLift_def]
        rw [QueryImpl.simulateQ_add_liftComp_left]
        simp)
      (hBody := by
        intro τ
        simp only [simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        congr 1)

omit [Fact (0 < p)] [DecidableEq G₁] in
/-- The t-SDH experiment is bounded by the t-SDH error. -/
lemma tSDH_error_bound {n : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (tSDHerror : ℝ≥0)
    (htSDH : Groups.tSDHAssumption (p := p) (G₁ := G₁) (G₂ := G₂)
      (g₁ := g₁) (g₂ := g₂) n tSDHerror)
    (adversary : KZGBindingAdversary p G₁ G₂ n unifSpec AuxState) :
    Groups.tSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn AuxState adversary)
    ≤ tSDHerror := by
  exact htSDH (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn AuxState adversary)

/- the KZG satisfies evaluation binding as defined in `CommitmentScheme` provided t-SDH holds. -/
theorem Binding {g₁ : G₁} {g₂ : G₂} (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1)
    (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (tSDHerror : ℝ≥0)
    (htSDH : Groups.tSDHAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n tSDHerror) :
    Commitment.binding (init := pure ∅) (impl := randomOracle)
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) tSDHerror := by
  letI scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.binding]
  intro AuxState adversary
  letI game := B_game AuxState adversary scheme
  letI game_ext := B_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[B_cond (p := p) (n := n) | game]
    _ = Pr[B_cond_ext (p := p) (n := n) | game_ext] :=
      B_game_ext_eq_B_game (pairing := pairing) adversary
    _ ≤ Pr[(tSDH_cond (p := p) (g₁ := g₁)) ∘ map_B_to_tSDH (p := p) (n := n) |
        game_ext] :=
      B_cond_le_tSDH_cond (pairing := pairing) hn hp hg₁ hpair adversary
    _ = Pr[tSDH_cond (p := p) (g₁ := g₁) | map_B_to_tSDH (p := p) (n := n) <$> game_ext] :=
      map_B_instance_drag adversary scheme
    _ = Groups.tSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (bindingReduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn AuxState adversary) :=
      tSDH_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn adversary
    _ ≤ tSDHerror := tSDH_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn
      tSDHerror htSDH adversary)

end Binding

end CommitmentScheme

end KZG
