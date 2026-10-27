/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Completeness
import ArkLib.Interaction.Oracle.LoggedExecution
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime
import Lean.Compiler.IR

/-! # Actual histogram-before-alpha scalar prover and declared-table pole completeness -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Honest
open scoped BigOperators ENNReal ProbabilityTheory
open Lean Elab Command
namespace LogupScalarHonestTest
namespace Small
abbrev F := ZMod 17
instance : Fact (Nat.Prime 17) := ⟨by decide⟩
def f : F →+* F := RingHom.id F
def cfg : Config F 1 1 2 1 := (Config.create? F 1 1 2 1 17).get (by decide)
def data : Data F 1 1 2 := Sum.elim (fun _ => #v[5, 7])
  (fun p => if p = 0 then #v[3, 3] else #v[5, 7])
def indices : Vector (Fin 4) 2 := #v[2, 3]
theorem valid : ValidIndices data indices := by unfold ValidIndices; decide
theorem invalid : checkIndices data #v[0, 1] = false := by decide
abbrev access := (valuesFamily f 1 1 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 1 1 2).behaviorOfRealizations data
def view := VirtualOracle.id (valuesFamily f 1 1 2)
theorem realizes : view.eval impl = (valuesFamily f 1 1 2).behaviorOfRealizations data :=
  VirtualOracle.eval_id impl

def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le

theorem support_eq : tableSupport f data = {3, 5, 7} := by decide
theorem support_card : (tableSupport f data).card = 3 := by rw [support_eq]; decide
theorem offPole_two : (2 : F) ∉ tableSupport f data := by decide

def uniform : ProbComp Bool := uniformExecute f 1 1 2 1 cfg access view impl
  (proverWith f cfg data indices unifSpec build)

theorem failure : Pr{let accepted ← uniform}[accepted = false] ≤ (3 : ℝ≥0∞) / 17 := by
  unfold uniform
  have h := uniformExecute_proverWith_failure_le f cfg data indices valid build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) access view impl realizes
  simpa only [support_card, ZMod.card, Nat.cast_ofNat] using h

theorem success : (14 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniform}[accepted = true] := by
  unfold uniform
  have h := uniformExecute_proverWith_success_ge f cfg data indices valid build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) access view impl realizes
  have harith : (14 : ℝ≥0∞) / 17 = 1 - 3 / 17 := by
    have hself : (17 : ℝ≥0∞) / 17 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    rw [← hself, ← ENNReal.sub_div (by intros; norm_num)]
    congr 1
    exact_mod_cast (show (14 : Nat) = 17 - 3 by rfl)
  rw [harith]
  simpa only [support_card, ZMod.card, Nat.cast_ofNat] using h

theorem total : Pr{let _ ← uniform}[True] = 1 :=
  uniformExecute_proverWith_total f cfg data indices build access view impl

abbrev combined := protocol f 1 1 2 1
abbrev ambient : OracleSpec (Fin 6) := Fin 6 →ₒ F
def event (i : Fin 6) : OracleComp ambient F := liftM (ambient.query i)
def joint : OracleComp ambient ((Fin 1 → F) × (Fin 3 → F)) := do
  let z ← event 1
  let a ← event 2
  let b ← event 3
  let c ← event 4
  return (fun _ => z, ![a, b, c])
def logger (alpha : F) : QueryImpl ambient (StateM (List Nat)) := fun i => do
  modify (· ++ [i.val])
  return ![alpha, 3, 4, 9, 6, 5] i
abbrev Result := LoggedResult combined.tree combined.oracles access (fun _ => Unit) (fun _ => Bool)
def run (witness : Vector (Fin 4) 2) : OracleComp ambient Result := executeStrategiesLogged
  ambient combined.tree combined.roles combined.oracles access impl
  (proverWith f cfg data witness ambient build)
  (verifier f 1 1 2 1 cfg ambient (event 0) joint (event 5) access view)
def pathData (path : combined.tree.ExecutionPath) :
    Vector (CMlPolynomialEval F 1) 2 × CPolynomial.Raw F := by
  rcases path with ⟨mu, alpha, helper, joint, message, choice, stop⟩
  exact (mu, message.val.val)
def summarize (result : Result × List Nat) :
    Bool × (Vector (CMlPolynomialEval F 1) 2 × CPolynomial.Raw F) × Nat × List Nat :=
  (result.1.verifierOut, pathData result.1.path, result.1.sourceLog.length, result.2)
def summary (alpha : F) (witness : Vector (Fin 4) 2 := indices) :
    Bool × (Vector (CMlPolynomialEval F 1) 2 × CPolynomial.Raw F) × Nat × List Nat :=
  summarize ((simulateQ (logger alpha) (run witness)).run [])

theorem supported
    (jointDraw : OracleComp ambient ((Fin 1 → F) × (Fin 3 → F)))
    (roundDraw : OracleComp ambient F) :
    ∀ accepted ∈ support (execute f 1 1 2 1 cfg ambient (pure 2) jointDraw roundDraw
      access view impl (proverWith f cfg data indices ambient build)), accepted = true := by
  have hoff : ∀ alpha ∈ support (pure (2 : F) : OracleComp ambient F),
      alpha ∉ tableSupport f data := by
    intro alpha halpha
    have heq : alpha = 2 := by simpa only [support_pure, Set.mem_singleton_iff] using halpha
    subst alpha
    exact offPole_two
  exact execute_proverWith_support_completeness f cfg data indices valid ambient build
    (Logup.Prover.Honest.pureBuilder_correct (E := F) _ _) (pure 2) hoff jointDraw roundDraw
    access view impl realizes
end Small

namespace TwoRound
abbrev F := ZMod 257
instance : Fact (Nat.Prime 257) := ⟨by norm_num⟩
def f : F →+* F := RingHom.id F
def cfg : Config F 2 2 1 1 := (Config.create? F 2 2 1 1 257).get (by decide)
def data : Data F 2 2 1 := fun _ => #v[0, 1, 2, 3]
def indices : Vector (Fin 4) 8 := #v[0, 1, 2, 3, 0, 1, 2, 3]
theorem valid : ValidIndices data indices := by unfold ValidIndices; decide
def mu : Vector (CMlPolynomialEval F 2) 1 := multiplicities indices
abbrev access := (valuesFamily f 2 2 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 2 2 1).behaviorOfRealizations data
def view := VirtualOracle.id (valuesFamily f 2 2 1)
abbrev ambient : OracleSpec Unit := Unit →ₒ F
def round : OracleComp ambient F := liftM (ambient.query ())
def logger : QueryImpl ambient (StateM Nat) := fun _ => do
  let count ← get
  set (count + 1)
  return if count = 0 then 5 else 9
def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le
def state := Logup.Prover.State.start
  (Logup.Prover.State.prepare f 5 cfg.weighted (weightedData data mu)) (![3, 7]) (![4, 9, 6])
def first := build 1 state
def second := build 0 (Logup.Prover.State.fold state 5)
def originalFinal : F := simulateQ
  (Access.extendImpl (Access.extend access (multiplicityInterface f 2 1))
    (Logup.Interaction.helperInterface (E := F) 2 3)
    (Access.extendImpl access (multiplicityInterface f 2 1) impl mu) state.helper)
  (Logup.Interaction.queryQ f 2 3 3 cfg.weighted.groups 5 (![3, 7]) (![4, 9, 6])
    (Access.extend access (multiplicityInterface f 2 1))
    (weightedView f 2 2 1 access view) (![5, 9]))
def run : OracleComp ambient Bool := execute f 2 2 1 1 cfg ambient (pure 5)
  (pure ((![3, 7] : Fin 2 → F), (![4, 9, 6] : Fin 3 → F))) round access view impl
  (proverWith f cfg data indices ambient build)
def summary : Bool × Nat := (simulateQ logger run).run 0
end TwoRound

namespace ZeroRound
abbrev F := LogupScalarHonestTest.Small.F
def f : F →+* F := RingHom.id F
def cfg : Config F 0 1 2 1 := (Config.create? F 0 1 2 1 17).get (by decide)
def data : Data F 0 1 2 := Sum.elim (fun _ => #v[7])
  (fun p => if p = 0 then #v[5] else #v[7])
def indices : Vector (Fin 2) 1 := #v[1]
theorem valid : ValidIndices data indices := by unfold ValidIndices; decide
abbrev access := (valuesFamily f 0 1 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 0 1 2).behaviorOfRealizations data
def view := VirtualOracle.id (valuesFamily f 0 1 2)
abbrev ambient : OracleSpec Unit := Unit →ₒ F
def round : OracleComp ambient F := liftM (ambient.query ())
def logger : QueryImpl ambient (StateM Nat) := fun _ => do
  modify (· + 1)
  return 3
def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le
def run (alpha : F) : OracleComp ambient Bool := execute f 0 1 2 1 cfg ambient (pure alpha)
  (pure (Fin.elim0, (![4, 9, 6] : Fin 3 → F))) round access view impl
  (proverWith f cfg data indices ambient build)
def summary (alpha : F) : Bool × Nat := (simulateQ logger (run alpha)).run 0
end ZeroRound

namespace NoQueries
abbrev F := LogupScalarHonestTest.Small.F
def f : F →+* F := RingHom.id F
def cfg : Config F 1 0 1 1 := (Config.create? F 1 0 1 1 17).get (by decide)
def data : Data F 1 0 1 := Sum.elim Fin.elim0 (fun _ => #v[0, 1])
def indices : Vector (Fin 2) 0 := #v[]
theorem valid : ValidIndices data indices := fun i => Fin.elim0 i
abbrev access := (valuesFamily f 1 0 1).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id := (valuesFamily f 1 0 1).behaviorOfRealizations data
def view := VirtualOracle.id (valuesFamily f 1 0 1)
def build := Logup.Prover.Honest.pureBuilder (E := F) cfg.weighted.groups
  cfg.weighted.length_group_le
def run (alpha : F) : OracleComp ZeroRound.ambient Bool := execute f 1 0 1 1 cfg
  ZeroRound.ambient (pure alpha) (pure ((fun _ => 2), (fun _ => 4))) ZeroRound.round
  access view impl (proverWith f cfg data indices ZeroRound.ambient build)
def summary (alpha : F) : Bool × Nat := (simulateQ ZeroRound.logger (run alpha)).run 0
end NoQueries

run_cmd do
  unless Small.summary 2 ==
      (true, (#v[#v[0, 0], #v[1, 1]], #[0, 9, 11, 14]), 11, [0, 1, 2, 3, 4, 5]) do
    throwError "actual second-piece indexed scalar cubic or source/effect routing changed"
  unless Small.summary 3 ==
      (true, (#v[#v[0, 0], #v[1, 1]], #[0, 2, 10, 5]), 11, [0, 1, 2, 3, 4, 5]) do
    throwError "unused zero-weight table pole was scanned/retried or changed honest helpers"
  unless Small.summary 5 ==
      (false, (#v[#v[0, 0], #v[1, 1]], #[13, 10, 4, 7]), 2, [0, 1, 2, 3, 4]) do
    throwError "active pole failed to abort before native challenge"
  unless !(Small.summary 2 #v[0, 1]).1 do
    throwError "invalid indexed witness did not reach actual verifier rejection"
  unless TwoRound.mu == #v[#v[2, 2, 2, 2]] &&
      TwoRound.first.val.val == #[0, 221, 126, 167] &&
      TwoRound.second.val.val == #[138, 185, 160, 94] && TwoRound.originalFinal == 21 &&
      TwoRound.second.val.evalHorner 9 == 21 && TwoRound.summary == (true, 2) do
    throwError "F257 duplicate indexed histogram or original two-round terminal Q changed"
  unless ZeroRound.summary 2 == (true, 0) && ZeroRound.summary 7 == (false, 0) &&
      ZeroRound.summary 5 == (true, 0) do
    throwError "scalar zero-round terminal authentication or active/unused pole behavior changed"
  for alpha in List.finRange 17 do
    unless NoQueries.summary (alpha.val : NoQueries.F) == (true, 1) do
      throwError "empty query histogram failed, scanned or retried at a pole"
  for name in #[``proverWith, ``tableSupport, ``Small.uniform, ``Small.run, ``Small.summary,
      ``TwoRound.run, ``TwoRound.first, ``TwoRound.second, ``ZeroRound.run, ``NoQueries.run] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing ordinary scalar honest executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``mem_tableSupport, ``card_tableSupport_le,
      ``valueSupport_weighted_eq_tableSupport, ``execute_proverWith_eq,
      ``uniformExecute_proverWith_eq, ``uniformExecute_proverWith_failure_le,
      ``uniformExecute_proverWith_success_ge, ``uniformExecute_proverWith_total,
      ``execute_proverWith_support_completeness, ``uniformExecute_proverWith_failure_le_rows,
      ``uniformExecute_proverWith_success_ge_rows, ``Small.valid, ``Small.invalid,
      ``Small.realizes, ``Small.support_eq, ``Small.support_card, ``Small.offPole_two,
      ``Small.failure, ``Small.success, ``Small.total, ``Small.supported,
      ``TwoRound.valid, ``ZeroRound.valid, ``NoQueries.valid] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "scalar honest proof uses unexpected axioms: {name}"
  logInfo "histogram-before-alpha, table-only pole loss and actual scalar n0/n1/n2 execution passed"
end LogupScalarHonestTest
