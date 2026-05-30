/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.CommitmentScheme.KZG.FunctionBinding.EvaluationBindingConflict
import ArkLib.CommitmentScheme.KZG.FunctionBinding.TauInQueries
import ArkLib.CommitmentScheme.KZG.FunctionBinding.DegreeConflict

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
local instance functionBindingOracleInterface : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

/-- Steps 3 and 4 of the ARSDH reduction from [CGKY25]. -/
def mapFunctionBindingInstanceToArsdhInstAux {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let tr := FunctionBindingExtTranscript.ofTuple (p := p) val
  if let some (i₁, i₂) := findConflict tr.queryOf tr.responseOf then
    -- step 3
    return (conflictingEvaluationsArsdhOutput hn tr i₁ i₂).toTuple
  else if -- additional subcase (not in the paper): find τ in queries
    let some α₁ := (List.finRange L).findSome? fun i =>
      if tr.srs.1[0] ^ (tr.queryOf i).val == tr.srs.1[1]'(Nat.lt_add_of_pos_left hn)
      then some (tr.queryOf i) else none
  then
    -- α₁ = τ
    return (queryEqTauArsdhOutput n α₁ tr.srs).toTuple
    -- h₂ = h₁ ^ (1 / Zₛ.eval τ).val with h₁:= g₁
  else
      -- step 4
    let R := queryReps tr.queryOf
    let A ← findA R (n + 1) tr.queryOf tr.responseOf
    let S ← findS n A tr.cm tr.srs tr.queryOf tr.responseOf
    return (interpolationArsdhOutput S tr).toTuple

/-- Totalized version of `mapFunctionBindingInstanceToArsdhInstAux`, defaulting outside the
event. -/
def mapFunctionBindingInstanceToArsdhInst {L : ℕ} (hn : 1 ≤ n)
    (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
      (Fin L → ZMod p) × (Fin L → ZMod p) × (Fin L → Bool) × (Fin L → G₁)) :
    (Finset (ZMod p) × G₁ × G₁) :=
  -- For instances that break function binding, the auxiliary map should always return `some`.
  Option.getD (mapFunctionBindingInstanceToArsdhInstAux hn val) (∅, 1, 1)

/-- Map an extended function-binding output, including `τ`, into an ARSDH game output. -/
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
    -- The setup trapdoor is private key-generation randomness: the adversary receives only the
    -- public powers-of-τ SRS, while `τ` remains outside the oracle-visible state.
    let τ ← Groups.sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
    (simulateQ
      (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
      <|
      (do
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
    Pr[Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p) |
      Commitment.functionBindingGame (init := pure ∅) (impl := randomOracle) (hn := rfl)
        (AuxState := AuxState)
        (scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))
        (adversary := adversary)]
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
      (functionBindingCondExt n L : _ → Prop) =
        (Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p)) ∘ proj := by
    funext x
    rcases x with ⟨_, _, _, _, _, _, _⟩
    rfl
  rw [hcond_eq]
  -- Apply the OptionT bridge lemma with the run-level equality proved inline.
  apply OptionT.probEvent_eq_of_run_map_eq _ _ proj
    (Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p))
  simp only [Commitment.functionBindingGame, functionBindingGameExt, kzg, OptionT.run,
    OptionT.mk]
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
  rw [hkeygen]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  congr 1
  funext τ
  rw [← map_eq_bind_pure_comp, ← StateT.run'_map_comm, ← simulateQ_map]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  congr 1
  funext x
  apply congr_fun
  apply congr_arg
  congr 1
  funext x_1
  rw [Reduction.allVerdicts_eq_map_allOutputs_fst (fun result =>
    (result.1.1 0 : G₁))]
  simp only [map_eq_bind_pure_comp, bind_assoc, Option.map_bind]
  congr 1
  funext resultPairs
  cases resultPairs <;> rfl

-- helper lemmas for transition 2

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Extract the sampled SRS equation from a supported extended function-binding game output. -/
lemma function_binding_game_ext_support_srs {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hgame : (τ, srs, cm, queryOf, responseOf, accepts, proofs) ∈
      support (functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)))) :
    srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ := by
  simp only [functionBindingGameExt, kzg] at hgame
  obtain ⟨τ', _, hgame⟩ := OptionT.mem_support_bind_mk _ _ hgame
  refine OptionT.aux_mem_support_simulateQ_run' _ _ _
    (fun y => y.2.1 = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n y.1) ?_ hgame
  intro x hx y hxy
  rw [hxy] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨⟨cm', queryOf', responseOf', stateOf'⟩, _, hx⟩ := hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨resultPairs, _, hx⟩ := hx
  have hx' : some y =
      ((Option.map (fun resultOf i => (resultOf i).1) resultPairs).bind fun accepts =>
        Option.map
          (fun proofs =>
            (τ', Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ', cm', queryOf',
              (fun i => responseOf' i), accepts, proofs))
          (Option.map (fun resultOf i => (resultOf i).2) resultPairs)) := by
    simpa [mem_support_pure_iff] using hx
  cases hres : resultPairs with
  | none => simp [hres] at hx'
  | some resultOf =>
      simp only [hres, Option.map_some, Option.bind_some] at hx'
      have hy := Option.some.inj hx'
      rw [hy]

omit [DecidableEq G₁] in
include g₁ g₂ pairing in
/-- Accepted outputs in the extended function-binding game correspond to successful KZG checks. -/
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
    obtain ⟨τ_v, _, hgame⟩ := OptionT.mem_support_bind_mk _ _ hgame
    refine OptionT.aux_mem_support_simulateQ_run' _ _ _ P ?_ hgame
    intro x hx ⟨τ', srs', cm', queryOf', responseOf', accepts', proofs'⟩ hxeq hai'
    rw [hxeq] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨claim_v, _, hx⟩ := hx
    let cm_v := claim_v.1
    let queryOf_v := claim_v.2.fst
    let responseOf_v := claim_v.2.2.1
    let stateOf_v := claim_v.2.2.2
    rw [mem_support_bind_iff] at hx
    obtain ⟨opts_v, hopts, hx⟩ := hx
    have hx' : some (τ', srs', cm', queryOf', responseOf', accepts', proofs') =
        ((Option.map (fun resultOf i => (resultOf i).1) opts_v).bind fun accepts =>
          Option.map
            (fun proofs =>
              (τ_v, Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v, cm_v, queryOf_v,
                (fun i => responseOf_v i), accepts, proofs))
            (Option.map (fun resultOf i => (resultOf i).2) opts_v)) := by
      simpa [mem_support_pure_iff] using hx
    cases hres : opts_v with
    | none => simp [hres] at hx'
    | some resultOf =>
      simp only [hres, Option.map_some, Option.bind_some] at hx'
      have hy := Option.some.inj hx'
      have h_srs : srs' = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v := by
        simpa using congrArg (fun y => y.2.1) hy
      have h_cm : cm' = cm_v := by
        simpa using congrArg (fun y => y.2.2.1) hy
      have h_q : queryOf' = queryOf_v := by
        simpa using congrArg (fun y => y.2.2.2.1) hy
      have h_r : responseOf' = fun i => responseOf_v i := by
        simpa using congrArg (fun y => y.2.2.2.2.1) hy
      have h_a : accepts' = fun i => (resultOf i).1 := by
        simpa using congrArg (fun y => y.2.2.2.2.2.1) hy
      have h_p : proofs' = fun i => (resultOf i).2 := by
        simpa using congrArg (fun y => y.2.2.2.2.2.2) hy
      obtain ⟨result, hresult, hres_eq⟩ :=
        Reduction.support_allOutputs_index
          (fun ((transcript_data, verifier_accept) :
            (FullTranscript ⟨!v[.P_to_V], !v[G₁]⟩ × Bool × Unit) × Bool) =>
            (verifier_accept, transcript_data.1 0))
          (fun i => (cm_v, (⟨queryOf_v i, responseOf_v i⟩ :
            (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q))) stateOf_v
          (Reduction.mk
            (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v,
               Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v)).verifier)
          hopts hres i_idx
      obtain ⟨td_data, va⟩ := result
      have hverif :=
        Reduction.support_run_pure_verifier
          (Reduction.mk
            (adversary.prover (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v))
            ((kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)).opening
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v,
               Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v)).verifier)
          (fun stmt td =>
            KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
              (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v).2 stmt.1
              (td ⟨0, by decide⟩) stmt.2.1 stmt.2.2)
          (by intros; rfl)
          (cm_v, ⟨queryOf_v i_idx, responseOf_v i_idx⟩)
          (stateOf_v i_idx)
          hresult rfl
      have hva_eq_v : va = (resultOf i_idx).1 := congrArg Prod.fst hres_eq
      have htd_eq_v : td_data.1 0 = (resultOf i_idx).2 := congrArg Prod.snd hres_eq
      have h_a_i : accepts' i_idx = (resultOf i_idx).1 := by
        have := congrFun h_a i_idx
        simpa using this
      have h_p_i : proofs' i_idx = (resultOf i_idx).2 := by
        have := congrFun h_p i_idx
        simpa using this
      have h_va_acc : va = accepts' i_idx := by rw [hva_eq_v, ← h_a_i]
      have h_td_prf : td_data.1 0 = proofs' i_idx := by rw [htd_eq_v, ← h_p_i]
      have hva_true : va = true := h_va_acc.trans hai'
      have h_q_i : queryOf' i_idx = queryOf_v i_idx := by
        have := congrFun h_q i_idx
        simpa using this
      have h_r_i : responseOf' i_idx = responseOf_v i_idx := by
        have := congrFun h_r i_idx
        simpa using this
      change KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs'.2 cm' (proofs' i_idx) (queryOf' i_idx) (responseOf' i_idx)
      rw [h_srs, h_cm, ← h_td_prf, h_q_i, h_r_i]
      have heq : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          (Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ_v).2 cm_v
          (td_data.1 ⟨0, by decide⟩) (queryOf_v i_idx) (responseOf_v i_idx)
            = true := hverif.symm.trans hva_true
      exact heq
  exact hP hai

include g₁ g₂ pairing in
/-- A supported extended function-binding violation maps to an ARSDH-winning output. -/
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
    ((Groups.arsdhCondition n) ∘ mapFunctionBindingToArsdh hn)
      (τ, srs, cm, queryOf, responseOf, accepts, proofs) := by
  have hsrs : srs = Groups.PowerSrs.generate n τ (g₂ := g₂) (g₁ := g₁) := by
    exact function_binding_game_ext_support_srs (pairing := pairing) adversary hgame
  have hgen : srs.1[0] ≠ 1 := by
    rw [hsrs]
    simp only [Groups.PowerSrs.generate, Groups.PowerSrs.tower, Nat.reduceAdd, Vector.getElem_ofFn,
      pow_zero, pow_one, ne_eq]
    exact hg₁
  have hverify_all : ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
    exact function_binding_game_ext_support_verify_all (pairing := pairing) adversary hgame
  unfold mapFunctionBindingToArsdh
  unfold mapFunctionBindingInstanceToArsdhInst mapFunctionBindingInstanceToArsdhInstAux
  simp only [FunctionBindingExtTranscript.ofTuple, Option.pure_def, beq_iff_eq,
    Option.bind_eq_bind, Function.comp_apply]
  cases hfc : findConflict queryOf responseOf with
  | some c =>
      obtain ⟨i₁, i₂⟩ := c
      simp only [Option.getD_some]
      exact function_binding_conflicting_evaluations_branch_maps_to_arsdh
        (pairing := pairing) hn hp hpair hsrs hgen hverify_all hFBcond hfc
  | none =>
      cases hfs : List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val = srs.1[1] then some (queryOf i) else none)
        (List.finRange L) with
      | some α₁ =>
          simp only [Option.getD_some]
          have hcond : srs.1[0] ^ α₁.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
            exact find_query_with_srs_power_success hn srs queryOf hfs
          exact function_binding_query_eq_tau_branch_maps_to_arsdh
            (g₁ := g₁) (g₂ := g₂) hn hp hg₁ hsrs hgen hcond
      | none =>
          -- The interpolation has degree ≥ n + 1, since otherwise its first n + 1
          -- coefficients would witness a degree-`n` polynomial fitting all pairs,
          -- contradicting the function-binding hypothesis `hFBcond`.
          let R := queryReps queryOf
          have hRinj : Set.InjOn queryOf ↑R := queryReps_injOn queryOf
          have hRnoData : ¬ ∃ d : Fin (n + 1) → ZMod p,
              ∀ i ∈ R, (CPolynomial.ofFn d).eval (queryOf i) = responseOf i := by
            exact no_data_queryReps_of_function_binding_cond hFBcond hfc
          have hRdeg : (↑(n + 1) : WithBot ℕ) ≤
              (CLagrange.interpolate R queryOf responseOf).degree := by
            exact interpolate_degree_ge_of_no_data R hRinj hRnoData
          have hRcard : n + 1 < R.card := by
            exact finset_card_gt_of_interpolate_degree_ge R queryOf responseOf hRinj hRdeg
          cases hfa : findA R (n + 1) queryOf responseOf with
          | some a =>
              have hres_a : some a = findA R (n + 1) queryOf responseOf := hfa.symm
              have hAsub : a ⊆ R := find_a_subset R a (n + 1) queryOf responseOf hres_a
              have hAinj : Set.InjOn queryOf ↑a := hRinj.mono hAsub
              cases hfs' : findS n a cm srs queryOf responseOf with
              | some a' =>
                  have hres_s : some a' = findS n a cm srs queryOf responseOf := hfs'.symm
                  have hSsub : a' ⊆ a :=
                    find_s_subset n cm a a' srs queryOf responseOf hres_s
                  have hSinj : Set.InjOn queryOf ↑a' := hAinj.mono hSsub
                  simp only [hfs', Option.bind, Option.getD_some]
                  exact function_binding_interpolation_branch_maps_to_arsdh
                    (pairing := pairing) hn hpair hsrs hgen hverify_all hFBcond hSinj hfs' hfs
              | none =>
                  -- `findS` failed: contradicts `find_s_successful`.
                  exfalso
                  have hAdeg :=
                    find_a_deg R a (n + 1) queryOf responseOf hres_a
                  have hsome :=
                    find_s_successful (g₁ := g₁) n τ cm a queryOf responseOf srs hsrs
                      hgen
                      (by exact_mod_cast hAdeg) hAinj hn
                  rw [hfs'] at hsome
                  simp at hsome
          | none =>
              -- `findA` failed: contradicts `find_a_successful` via `hRdeg`.
              exfalso
              have hsome :=
                find_a_successful R (n + 1) queryOf responseOf hRcard hRinj hRdeg
              rw [hfa] at hsome
              simp at hsome

include g₁ g₂ pairing in
/-- Transition 2: FB condition implies ARSDH condition after mapping -/
lemma function_binding_cond_le_arsdh_cond {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[functionBindingCondExt n L |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(Groups.arsdhCondition n) ∘ mapFunctionBindingToArsdh hn |
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
    Pr[(Groups.arsdhCondition n) ∘ mapFunctionBindingToArsdh hn |
      functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[(Groups.arsdhCondition n) |
      mapFunctionBindingToArsdh hn <$>
        functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

/-- Transition 4: the mapped game equals the ARSDH experiment -/
lemma arsdh_game_eq {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KzgFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
  Pr[(Groups.arsdhCondition n) |
      mapFunctionBindingToArsdh hn <$> functionBindingGameExt (g₁ := g₁) (g₂ := g₂)
        AuxState adversary (kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) := by
  let scheme := kzg (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.arsdhExperiment, Groups.arsdhGame]
  unfold Groups.arsdhCondition
  simp only
  congr 1
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  let impl : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
    QueryImpl.addLift
      (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (challengeQueryImpl (pSpec := pSpec'))
  simpa only [functionBindingGameExt, reduction, kzg, OptionT.mk, pSpec', impl, scheme,
      OptionT.run_map] using
    OptionT.map_mk_bind_eq_of_body
      (sample := (Groups.sampleNonzeroZMod (p := p) : ProbComp (ZMod p)))
      (body₁ := fun τ => (simulateQ impl (do
        let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
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
      )).run' (∅ : unifSpec.QueryCache))
      (body₂ := fun τ => (simulateQ impl (do
        let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ
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
      )).run' (∅ : unifSpec.QueryCache))
      (f := mapFunctionBindingToArsdh hn)
      (post := fun τ ((S, h₁, h₂) : Finset (ZMod p) × G₁ × G₁) => (τ, S, h₁, h₂))
      (hBody := by
        intro τ
        dsimp only
        refine StateT.map_run'_eq_of_map_eq _ _ _ _ (∅ : unifSpec.QueryCache) ?_
        simp only [simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
        congr 1
        funext claimResult
        congr 1
        funext resultPairs
        cases resultPairs <;> rfl)

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
  letI game := Commitment.functionBindingGame (init := pure ∅) (impl := randomOracle) (hn := rfl)
    (AuxState := AuxState) (scheme := scheme) (adversary := adversary)
  letI game_ext := functionBindingGameExt (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p) | game]
    _ = Pr[functionBindingCondExt n L | game_ext] :=
      function_binding_game_ext_eq_function_binding_game (pairing := pairing) adversary
    _ ≤ Pr[(Groups.arsdhCondition n) ∘ mapFunctionBindingToArsdh hn | game_ext] :=
      function_binding_cond_le_arsdh_cond (pairing := pairing) hn hp hg₁ hpair adversary
    _ = Pr[(Groups.arsdhCondition n) | mapFunctionBindingToArsdh hn <$> game_ext] :=
      map_instance_drag hn adversary scheme
    _ = Groups.arsdhExperiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) :=
      arsdh_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn adversary
    _ ≤ arsdhError := arsdh_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn
      arsdhError hArsdh adversary)


end FunctionBinding

end CommitmentScheme

end KZG
