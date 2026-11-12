/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.OracleReduction.Security.Adaptive

/-!
# Adaptive interactive soundness separation

The verifier accepts exactly when its statement matches a one-bit public oracle. Every fixed
false statement is accepted with probability one half, while a chooser that queries the oracle
can select an accepting statement with certainty.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace AdaptiveSoundnessTest

abbrev coinSpec : OracleSpec Unit := Unit →ₒ Bool
def bitInit : ProbComp Bool := $ᵗ Bool
def bitImpl : QueryImpl coinSpec (StateT Bool ProbComp) := fun _ => get
def coin : OracleComp coinSpec Bool := query (spec := coinSpec) ()

def bitVerifier : Verifier coinSpec Bool Bool (!p[]) where
  verify x _ := (fun h => decide (x = h)) <$>
    (OptionT.lift coin : OptionT (OracleComp coinSpec) Bool)

def bitChooser : OracleComp coinSpec (Bool × Unit) := (fun b => (b, ())) <$> coin

def adaptiveBitProver : AdaptiveProver coinSpec Bool Bool Bool (!p[]) where
  Aux := Bool
  choose := (fun b => (b, b)) <$> coin
  prover := Prover.id

def oneQueryContinuation : Prover coinSpec Bool Unit Bool Unit (!p[]) where
  PrvState := fun _ => Bool
  input := fun (stmt, _) => stmt
  sendMessage := fun i => Fin.elim0 i
  receiveChallenge := fun i => Fin.elim0 i
  output stmt := do
    let _ ← coin
    pure (stmt, ())

def twoQueryAdversary : AdaptiveProver coinSpec Bool Bool Unit (!p[]) where
  Aux := Unit
  choose := (fun bit => (bit, ())) <$> coin
  prover := oneQueryContinuation

def adaptiveBadEvent (out : Option (Bool × Bool)) : Prop :=
  nargSoundFailEvent (∅ : Set Bool) {true} out

def adaptiveExperiment : ProbComp (Option (Bool × Bool)) :=
  bitVerifier.adaptiveSoundnessExp bitInit bitImpl adaptiveBitProver

abbrev oneMessage : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[Bool]⟩

def nargInput : OracleComp coinSpec (Bool × Bool) := (fun bit => (bit, bit)) <$> coin

def deterministicImpl : QueryImpl (coinSpec + [oneMessage.Challenge]ₒ' challengeOracleInterface) Id
  | .inl _ => pure false
  | .inr q => isEmptyElim q.1

run_cmd do
  let result := simulateQ deterministicImpl (AdaptiveProver.ofNARG (Out := Bool) nargInput).run
  let msg : Bool := result.2.1 ⟨0, by decide⟩
  unless result.1 == false && msg == false && result.2.2 == () do
    throwError "adaptive prover run lost the chosen statement or NARG message"

-- A fixed statement can match the sampled oracle bit with probability at most one half.
theorem nonadaptive_bound :
    bitVerifier.soundness bitInit bitImpl (∅ : Set Bool) {true} (1 / 2) := by
  intro WitIn WitOut witIn prover x _hx
  let pImpl : QueryImpl _ (StateT Bool ProbComp) :=
    bitImpl.addLift (challengeQueryImpl (pSpec := (!p[] : ProtocolSpec 0)))
  have hInv : ∀ b : Bool, QueryImpl.PreservesInv
      (bitImpl + QueryImpl.liftTarget (StateT Bool ProbComp)
        (challengeQueryImpl (pSpec := (!p[] : ProtocolSpec 0)))) (· = b) := by
    intro b q
    rcases q with _ | ⟨i, _⟩
    · intro σ₀ hσ z hz
      simp_all [bitImpl]
    · exact i.1.elim0
  have key : ∀ {T : Type} (Y : Bool → ProbComp (T × Bool)),
      (∀ a, ∀ p ∈ support (Y a), p.2 = a) →
      Pr{let a ← (liftM ($ᵗ Bool : ProbComp Bool) : OptionT ProbComp Bool)
         let z ← (OptionT.mk ((fun p => some (p.1, decide (x = p.2))) <$> Y a) :
            OptionT ProbComp (T × Bool))}[z.2 = true] * 2 ≤ 1 := by
    intro T Y hY
    have hmk3 : ∀ a, ((fun z => z.2 = true) <$> (OptionT.mk
        ((fun p => some (p.1, decide (x = p.2))) <$> Y a) : OptionT ProbComp (T × Bool))) =
        OptionT.lift ((fun p => x = p.2) <$> Y a) := by
      intro a
      apply OptionT.ext
      simp [OptionT.run_lift]
    have hlift : ∀ {α β : Type} (m : ProbComp α) (Z : α → ProbComp β),
        ((liftM m : OptionT ProbComp α) >>= fun a => OptionT.lift (Z a)) =
          OptionT.lift (m >>= Z) := by
      intro α β m Z
      apply OptionT.ext
      simp [OptionT.run_bind, OptionT.run_lift, Option.elimM]
    have hpl : ∀ W : ProbComp Prop, prEvent (OptionT.lift W) = prEvent W := by
      intro W
      simpa only [id_map'] using OptionT.prEvent_lift W (fun p => p)
    simp only [hmk3, hlift, hpl]
    have hb := prEvent_bind_le_prEvent_of_forall_eq_zero (m := ProbComp) ($ᵗ Bool)
      (fun a => (fun p => x = p.2) <$> Y a) (fun a => x = a) (fun y => y) (by
        intro a ha
        simp only [id_map']
        exact prEvent_eq_zero_of_forall_mem_support (Y a) (fun p => x = p.2)
          (fun p hp h => ha (h.trans (hY a p hp))))
    simp only [id_map'] at hb
    calc
      _ * 2 ≤ Pr{let a ← ($ᵗ Bool : ProbComp Bool)}[x = a] * 2 := by gcongr
      _ ≤ 1 := by
        simp only [SampleableType.prEvent_uniformSample, Fintype.univ_bool,
          Fintype.card_bool, Nat.cast_ofNat]
        have hc : (Finset.filter (Eq x) ({true, false} : Finset Bool)).card = 1 := by
          cases x <;> decide
        rw [hc, Nat.cast_one, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  have h := key (fun a => (simulateQ pImpl (prover.run x witIn)).run a)
    (fun a p hp => simulateQ_run_preservesInv _ _ (hInv a) _ a rfl p hp)
  simpa [pImpl, bitVerifier, bitImpl, bitInit, coin, Reduction.run_run_eq_bind,
    Verifier.run, OptionT.run_map, OptionT.run_lift,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.addLift_def, liftComp_eq_liftM,
    StateT.run_map, StateT.run_bind] using h

-- The chooser queries the same table and selects its bit, so it always wins.
theorem adaptive_attack :
    Pr{let out ← adaptiveExperiment}[adaptiveBadEvent out] = 1 := by
  simp [adaptiveExperiment, adaptiveBadEvent, Verifier.adaptiveSoundnessExp,
    AdaptiveGame.run, AdaptiveProver.run,
    bitInit, bitImpl, bitVerifier, adaptiveBitProver, coin, Prover.id, Prover.run,
    Verifier.run, OptionT.run_map, OptionT.run_lift, QueryImpl.addLift_def,
    liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left, nargSoundFailEvent]

private theorem twoQueryAdversary_bound_iff (budget : ℕ) :
    twoQueryAdversary.IsQueryBound (fun _ => True) budget ↔ 2 ≤ budget := by
  let spec := coinSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ
  change IsQueryBoundP (spec := spec)
    (do
      let bit ← liftM (spec.query (.inl ()))
      let _ ← liftM (spec.query (.inl ()))
      pure (bit, (default : (!p[] : ProtocolSpec 0).FullTranscript), ()))
    (publicQuerySelector (fun _ => True)) budget ↔ _
  simp only [isQueryBoundP_query_bind_iff, publicQuerySelector, not_true_eq_false,
    false_or, isQueryBoundP_pure, implies_true, and_true]
  change (0 < budget ∧ ∀ _ : Bool, 0 < budget - 1) ↔ 2 ≤ budget
  simp only [forall_const]
  omega

-- The budget includes one chooser query and one continuation query; neither phase can be omitted.
example : twoQueryAdversary.IsQueryBound (fun _ => True) 2 := by
  simp [twoQueryAdversary_bound_iff]

example : ¬ twoQueryAdversary.IsQueryBound (fun _ => True) 1 := by
  simp [twoQueryAdversary_bound_iff]

-- The usual fixed-statement error bound also holds for all constant adaptive choosers.
theorem constant_chooser_bound :
    bitVerifier.adaptiveSoundness bitInit bitImpl (∅ : Set Bool) {true}
      (fun _ A => ∃ (Aux : Type) (stmt : Bool) (aux : Aux)
        (P : Prover coinSpec Bool Aux Bool _ (!p[])),
        A = AdaptiveProver.fixed stmt aux P) (1 / 2) := by
  have h := (bitVerifier.soundness_iff_adaptiveSoundness_fixed bitInit bitImpl
    (∅ : Set Bool) {true} (1 / 2)).mp nonadaptive_bound
  simpa using h

end AdaptiveSoundnessTest
