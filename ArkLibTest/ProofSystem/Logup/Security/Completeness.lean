/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLibTest.ProofSystem.Logup.Prover.State
import ArkLib.Interaction.Oracle.LoggedExecution
import Lean.Compiler.IR

/-! # Actual honest strategy, formal original-prefix correspondence and pole completeness -/

open Interaction.Oracle OracleComp OracleSpec CompPoly MvPolynomial
open Logup.Interaction Logup.Prover Logup.Prover.Honest
open scoped BigOperators ENNReal ProbabilityTheory
namespace LogupHonestTest
namespace Cubic

abbrev F := LogupStateTest.F
abbrev combined := protocol F 1 2 1
abbrev ambientSpec : OracleSpec (Fin 5) := Fin 5 →ₒ F

def event (i : Fin 5) : OracleComp ambientSpec F := liftM (ambientSpec.query i)
def jointDraw : OracleComp ambientSpec ((Fin 1 → F) × (Fin 2 → F)) := do
  let z ← event 1
  let a ← event 2
  let b ← event 3
  return (fun _ => z, ![a, b])

def logger (alpha : F) : QueryImpl ambientSpec (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![alpha, 3, 4, 6, 5] i

abbrev Result := LoggedResult combined.tree combined.oracles (LogupStateTest.access)
  (fun _ => Unit) (fun _ => Bool)

def run : OracleComp ambientSpec Result :=
  executeStrategiesLogged ambientSpec combined.tree combined.roles combined.oracles
    LogupStateTest.access LogupStateTest.impl
    (honestWith (RingHom.id F) LogupStateTest.cfg LogupStateTest.data ambientSpec
      (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le))
    (verifier (RingHom.id F) 1 2 1 LogupStateTest.cfg ambientSpec (event 0) jointDraw (event 4)
      LogupStateTest.access LogupStateTest.view)

def pathData (path : combined.tree.ExecutionPath) :
    CPolynomial.Raw F × Vector (CMlPolynomialEval F 1) 2 := by
  rcases path with ⟨alpha, helper, joint, message, choice, stop⟩
  exact (message.val.val, helper)

def summarize (result : Result × List Nat) :
    Bool × CPolynomial.Raw F × Vector (CMlPolynomialEval F 1) 2 × Nat × List Nat :=
  (result.1.verifierOut, (pathData result.1.path).1, (pathData result.1.path).2,
    result.1.sourceLog.length, result.2)

def summary (alpha : F) := summarize ((simulateQ (logger alpha) run).run [])

open Lean Elab Command
run_cmd do
  unless summary 2 == (true, #[0, 2, 10, 5], #v[#v[9, 1], #v[-9, -1]], 9, [0, 1, 2, 3, 4]) do
    throwError "actual honest native cubic execution failed"
  unless summary 0 == (false, #[13, 10, 4, 7], #v[#v[0, -1], #v[0, 1]], 2, [0, 1, 2, 3]) do
    throwError "actual honest pole did not abort before the native challenge"
  for name in #[``nativeWith, ``pureBuilder, ``honestWith, ``run, ``summary] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing actual honest ordinary-strategy IR: {name}"

end Cubic

abbrev F := LogupStateTest.F

theorem balanced : ∀ key : F,
    ((Finset.univ : Finset (Fin 1 → Fin 2)).product (Finset.univ : Finset (Fin 2))).sumFiber
      (fun p => (LogupStateTest.data (0, p.2)).get (finFunctionFinEquiv p.1))
      (fun p => (LogupStateTest.data (1, p.2)).get (finFunctionFinEquiv p.1)) key = 0 := by decide

theorem offPole_two : ∀ i u, (2 : F) - (LogupStateTest.data (0, i)).get u ≠ 0 := by decide

theorem mappedSupport : valueSupport (RingHom.id F) LogupStateTest.data = {0, 1} := by decide

theorem mappedSupport_card : (valueSupport (RingHom.id F) LogupStateTest.data).card = 2 := by
  rw [mappedSupport]
  decide

def uniformCubic : ProbComp Bool := uniformExecute (RingHom.id F) 1 2 1 LogupStateTest.cfg
  LogupStateTest.access LogupStateTest.view LogupStateTest.impl
  (honestWith (RingHom.id F) LogupStateTest.cfg LogupStateTest.data unifSpec
    (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le))

theorem actual_uniform_failure :
    Pr{let accepted ← uniformCubic}[accepted = false] ≤ (2 : ℝ≥0∞) / 17 := by
  unfold uniformCubic
  have h := uniformExecute_honestWith_failure_le (RingHom.id F) LogupStateTest.cfg
    LogupStateTest.data (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le)
    (pureBuilder_correct _ _) balanced LogupStateTest.access LogupStateTest.view
    LogupStateTest.impl LogupStateTest.realizes
  simpa only [mappedSupport_card, ZMod.card, Nat.cast_ofNat] using h

theorem actual_uniform_success :
    (15 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniformCubic}[accepted = true] := by
  unfold uniformCubic
  have h := uniformExecute_honestWith_success_ge (RingHom.id F) LogupStateTest.cfg
    LogupStateTest.data (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le)
    (pureBuilder_correct _ _) balanced LogupStateTest.access LogupStateTest.view
    LogupStateTest.impl LogupStateTest.realizes
  have harith : (15 : ℝ≥0∞) / 17 = 1 - 2 / 17 := by
    have hself : (17 : ℝ≥0∞) / 17 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    rw [← hself, ← ENNReal.sub_div (by intros; norm_num)]
    congr 1
    exact_mod_cast (show (15 : Nat) = 17 - 2 by rfl)
  rw [harith]
  simpa only [mappedSupport_card, ZMod.card, Nat.cast_ofNat] using h

theorem actual_uniform_total : Pr{let _ ← uniformCubic}[True] = 1 :=
  uniformExecute_honestWith_total (RingHom.id F) LogupStateTest.cfg LogupStateTest.data
    (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le)
    LogupStateTest.access LogupStateTest.view LogupStateTest.impl

theorem actual_supported_offPole
    (joint : OracleComp Cubic.ambientSpec ((Fin 1 → F) × (Fin 2 → F)))
    (round : OracleComp Cubic.ambientSpec F) :
    ∀ accepted ∈ support
      (execute (RingHom.id F) 1 2 1 LogupStateTest.cfg Cubic.ambientSpec (pure 2) joint round
        LogupStateTest.access LogupStateTest.view LogupStateTest.impl
        (honestWith (RingHom.id F) LogupStateTest.cfg LogupStateTest.data Cubic.ambientSpec
          (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le))),
      accepted = true := by
  have hoff : ∀ alpha ∈ support (pure (2 : F) : OracleComp Cubic.ambientSpec F),
      ∀ i u, alpha - (LogupStateTest.data (0, i)).get u ≠ 0 := by
    intro alpha halpha
    have heq : alpha = 2 := by simpa only [support_pure, Set.mem_singleton_iff] using halpha
    subst alpha
    exact offPole_two
  exact execute_honestWith_support_completeness (RingHom.id F) LogupStateTest.cfg
    LogupStateTest.data (pureBuilder LogupStateTest.cfg.groups LogupStateTest.cfg.length_group_le)
    (pureBuilder_correct (E := F) _ _) balanced Cubic.ambientSpec (pure 2) hoff joint round
    LogupStateTest.access LogupStateTest.view LogupStateTest.impl LogupStateTest.realizes


namespace TwoRound

def cfg : Config 2 2 1 := (Config.create? 2 2 1).get (by decide)
def data (i : Fin 2 × Fin 2) : CMlPolynomialEval F 2 :=
  if i.1 = 0 then #v[0, 1, 2, 3] else if i.2 = 0 then #v[1, 1, 1, 1] else #v[-1, -1, -1, -1]
abbrev access := (inputFamily (RingHom.id F) 2 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 2 2).behaviorOfRealizations data
def view := VirtualOracle.id (inputFamily (RingHom.id F) 2 2)
abbrev ambient : OracleSpec Unit := Unit →ₒ F
def round : OracleComp ambient F := liftM (ambient.query ())
def logger : QueryImpl ambient (StateM Nat) := fun _ => do
  let count ← get
  set (count + 1)
  return if count = 0 then 5 else 9

def state : Logup.Prover.State F 2 2 2 :=
  State.start (State.prepare (RingHom.id F) 5 cfg data) (![3, 7]) (![4, 6])
def first := pureBuilder cfg.groups cfg.length_group_le 1 state
def second := pureBuilder cfg.groups cfg.length_group_le 0 (State.fold state 5)
def originalFinal : F := simulateQ
  (Access.extendImpl access (helperInterface (E := F) 2 2) impl state.helper)
  (queryQ (RingHom.id F) 2 2 2 cfg.groups 5 (![3, 7]) (![4, 6]) access view (![5, 9]))

def run (alpha : F) : OracleComp ambient Bool := execute (RingHom.id F) 2 2 1 cfg ambient
  (pure alpha) (pure ((![3, 7] : Fin 2 → F), (![4, 6] : Fin 2 → F))) round access view impl
  (honestWith (RingHom.id F) cfg data ambient (pureBuilder cfg.groups cfg.length_group_le))
def summary (alpha : F) : Bool × Nat := (simulateQ logger (run alpha)).run 0
end TwoRound

namespace ZeroRound

def cfg : Config 0 2 1 := (Config.create? 0 2 1).get (by decide)
def data (i : Fin 2 × Fin 2) : CMlPolynomialEval F 0 :=
  if i.1 = 0 then #v[0] else if i.2 = 0 then #v[1] else #v[-1]
abbrev access := (inputFamily (RingHom.id F) 0 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (inputFamily (RingHom.id F) 0 2).behaviorOfRealizations data
def view := VirtualOracle.id (inputFamily (RingHom.id F) 0 2)
def run (alpha : F) : OracleComp TwoRound.ambient Bool := execute (RingHom.id F) 0 2 1 cfg
  TwoRound.ambient (pure alpha) (pure (Fin.elim0, (![4, 6] : Fin 2 → F))) TwoRound.round
  access view impl
  (honestWith (RingHom.id F) cfg data TwoRound.ambient
    (pureBuilder cfg.groups cfg.length_group_le))
def summary (alpha : F) : Bool × Nat := (simulateQ TwoRound.logger (run alpha)).run 0
end ZeroRound

open Lean Elab Command
run_cmd do
  let folded := State.fold TwoRound.state 5
  unless folded.denominator[0][0] == 0 && folded.helper[0][0] == 3 do
    throwError "folded helper was recomputed by dividing at a new zero denominator"
  unless TwoRound.first.val.val == #[0, 8, 6, 3] && TwoRound.second.val.val == #[13, 13, 10, 6] do
    throwError "actual original-prefix two-round coefficient arrays changed"
  unless TwoRound.first.val.evalHorner 5 == 4 &&
      TwoRound.second.val.evalHorner 0 + TwoRound.second.val.evalHorner 1 == 4 &&
      TwoRound.second.val.evalHorner 9 == 10 && TwoRound.originalFinal == 10 do
    throwError "folded messages no longer authenticate the nonzero retained original Q(5, 9)"
  unless TwoRound.summary 5 == (true, 2) && TwoRound.summary 0 == (false, 0) do
    throwError "whole two-round honest/pole execution or public abort changed"
  unless ZeroRound.summary 2 == (true, 0) && ZeroRound.summary 0 == (false, 0) do
    throwError "zero-round honest final authentication or pole boundary changed"
  for name in #[``nativeWith, ``pureBuilder, ``honestWith, ``valueSupport, ``uniformCubic,
      ``Cubic.run, ``TwoRound.run, ``TwoRound.first, ``TwoRound.second,
      ``ZeroRound.run] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing ordinary honest caller IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``pureBuilder_correct, ``honest_initial_relation,
      ``native_start_prepare_support_completeness, ``execute_honestWith_eq_binds,
      ``execute_honestWith_support_completeness, ``mem_valueSupport,
      ``offPole_iff_not_mem_valueSupport, ``card_valueSupport_le,
      ``uniformExecute_honestWith_failure_le, ``uniformExecute_honestWith_success_ge,
      ``uniformExecute_honestWith_total, ``balanced, ``offPole_two,
      ``mappedSupport, ``mappedSupport_card,
      ``actual_uniform_failure, ``actual_uniform_success, ``actual_uniform_total,
      ``actual_supported_offPole] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "honest completeness proof has unexpected axioms: {name}"
  logInfo "honest cubic, n2 prefix, n0 authentication, poles and uniform bounds passed"

end LogupHonestTest
