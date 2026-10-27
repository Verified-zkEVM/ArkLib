/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Prover
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Completeness
import Lean.Compiler.IR

/-! # The actual cached tuple default, lossless completeness and its selected-program ledger -/

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Lookup Logup.Lookup.Tuple
open scoped ENNReal ProbabilityTheory
namespace LogupTupleDefaultTest

namespace Small
open LogupTupleHonestTest.Small

def run (witness : Vector (Fin 6) 2) : OracleComp ambient Result := executeStrategiesLogged
  ambient combined.tree combined.roles combined.oracles access impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared witness ambient)
  (Tuple.verifier f 1 1 3 2 1 cfg ambient (event 0) (event 1) joint (event 3) access view)

def summary (beta alpha : F) (witness : Vector (Fin 6) 2 := indices) :=
  summarize ((simulateQ (logger beta alpha) (run witness)).run [])

def uniform : ProbComp Bool := Tuple.uniformExecute f 1 1 3 2 1 cfg access view impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices unifSpec)

theorem uniform_eq : uniform = LogupTupleHonestTest.Small.uniform := by
  unfold uniform LogupTupleHonestTest.Small.uniform
  rw [Logup.Lookup.Tuple.Honest.prover_eq_proverWith]
  rfl

theorem failure : Pr{let accepted ← uniform}[accepted = false] ≤ (6 : ℝ≥0∞) / 17 := by
  rw [uniform_eq]
  exact LogupTupleHonestTest.Small.failure

theorem success : (11 : ℝ≥0∞) / 17 ≤ Pr{let accepted ← uniform}[accepted = true] := by
  rw [uniform_eq]
  exact LogupTupleHonestTest.Small.success

theorem total : Pr{let _ ← uniform}[True] = 1 := by
  rw [uniform_eq]
  exact LogupTupleHonestTest.Small.total

def handler (beta alpha : F) : QueryImpl ambient Id := fun i => ![beta, alpha, 2, 5] i
def fixedJoint : (Fin 1 → F) × (Fin 4 → F) := ((fun _ => 2), ![4, 9, 6, 3])

def observed (beta alpha : F) (choice : Option F) :=
  Logup.Lookup.Tuple.Honest.Accounting.observeProver ambient (handler beta alpha) f
    (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices ambient)
    beta alpha fixedJoint #v[choice]

def profiled (beta alpha : F) (choice : Option F) :=
  Logup.Lookup.Tuple.Honest.Accounting.observeProver ambient (handler beta alpha) f
    (Logup.Lookup.Tuple.Honest.Accounting.profiledProver f cfg prepared indices ambient)
    beta alpha fixedJoint #v[choice]

def recorded (beta alpha : F) (choice : Option F) :=
  Logup.Lookup.Tuple.Honest.Accounting.observeProver ambient (handler beta alpha) f
    (Logup.Lookup.Tuple.Honest.Accounting.recordedProver f cfg prepared indices ambient)
    beta alpha fixedJoint #v[choice]

def label : Logup.Prover.Honest.Accounting.Call F F 4 4 → Nat
  | .prepare _ _ _ _ _ => 0
  | .start _ _ _ _ => 1
  | .message _ _ _ => 2
  | .fold _ _ _ => 3

end Small

namespace TwoRound
open LogupTupleHonestTest.Small

def cfg : Config F 2 1 3 1 := (Config.create? F 2 1 3 1 17).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 2) 4 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩, ⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 1]⟩, ⟨0, #v[0, 0]⟩, ⟨0, #v[0, 1]⟩, ⟨0, #v[0, 0]⟩],
    Vector.replicate 4 ⟨1, #v[0]⟩, Vector.replicate 4 ⟨1, #v[0]⟩]
def prepared : PreparedProvider schema layout 2 1 :=
  PreparedProvider.prepare schema layout keys (by decide)
def indices : Vector (Fin 12) 4 := #v[0, 4, 2, 5]
theorem valid : ValidIndices prepared.keyData indices := by unfold ValidIndices; decide

abbrev empty : OracleSpec Empty := fun i => nomatch i
def handler : QueryImpl empty Id := fun i => nomatch i
def joint : (Fin 2 → F) × (Fin 4 → F) := (![2, 7], ![4, 9, 6, 3])
def recorded (choices : Vector (Option F) 2) :=
  Logup.Lookup.Tuple.Honest.Accounting.observeProver empty handler f
    (Logup.Lookup.Tuple.Honest.Accounting.recordedProver f cfg prepared indices empty)
    1 5 joint choices
def profiled (choices : Vector (Option F) 2) :=
  Logup.Lookup.Tuple.Honest.Accounting.observeProver empty handler f
    (Logup.Lookup.Tuple.Honest.Accounting.profiledProver f cfg prepared indices empty)
    1 5 joint choices

abbrev access := (coefficientFamily f 2 1 3 2).spec.toPFunctor
def impl : QueryImpl (ofPFunctor access) Id :=
  (coefficientFamily f 2 1 3 2).behaviorOfRealizations
    (fun sj => prepared.coefficientTable sj.1 sj.2)
def endpoint : Bool := simulateQ handler (Tuple.execute f 2 1 3 2 1 cfg empty
  (pure 1) (pure 5) (pure joint) (pure 5) access
  (VirtualOracle.id (coefficientFamily f 2 1 3 2)) impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices empty))
end TwoRound

namespace ZeroRound
open LogupTupleHonestTest.ZeroRound

def run : OracleComp ambient Bool := Tuple.execute f 0 1 2 0 1 cfg ambient
  (LogupTupleHonestTest.Small.event 0) (LogupTupleHonestTest.Small.event 1) joint
  (LogupTupleHonestTest.Small.event 3) access view impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared indices ambient)

def summary (beta alpha : F) : Bool × List Nat :=
  (simulateQ (LogupTupleHonestTest.Small.logger beta alpha) run).run []
end ZeroRound

namespace Extension
open LogupTupleHonestTest.Extension

def run : OracleComp ambient Bool := Tuple.execute f 1 1 3 2 1 cfg ambient
  (pure KoalaBear.ext6Gen) (pure 2)
  (pure ((fun _ => KoalaBear.ext6Gen), ![KoalaBear.ext6Gen, 1, KoalaBear.ext6Gen ^ 2, 3]))
  round access view impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared LogupTupleHonestTest.Small.indices ambient)

def summary : Bool × Nat := (simulateQ logger run).run 0

def uniform : ProbComp Bool := Tuple.uniformExecute f 1 1 3 2 1 cfg access view impl
  (Logup.Lookup.Tuple.Honest.prover f cfg prepared LogupTupleHonestTest.Small.indices unifSpec)

theorem total : Pr{let _ ← uniform}[True] = 1 := by
  unfold uniform
  rw [Logup.Lookup.Tuple.Honest.prover_eq_proverWith]
  exact Logup.Lookup.Tuple.Honest.uniformExecute_proverWith_total
    f cfg prepared LogupTupleHonestTest.Small.indices build access view impl
end Extension

#eval (show IO _ from do
  for beta in [0, 1] do
    for witness in [LogupTupleHonestTest.Small.indices, #v[0, 3]] do
      unless Small.summary beta 5 witness == LogupTupleHonestTest.Small.summary beta 5 witness do
        throw (IO.userError "actual cached default changed a colliding-beta source/native trace")
    unless (Small.summary beta 5).1 do
      throw (IO.userError "true lookup with beta collision was rejected")
  unless Small.summary 1 2 == LogupTupleHonestTest.Small.summary 1 2 &&
      (Small.summary 1 2).1 do
    throw (IO.userError "unused in-piece pole changed actual cached default")
  unless Small.summary 0 0 == LogupTupleHonestTest.Small.summary 0 0 &&
      !(Small.summary 0 0).1 do
    throw (IO.userError "active pole lost the actual native rejection path")
  for beta in [0, 1] do
    for choice in [none, some 5] do
      let ordinary := Small.observed beta 5 choice
      let measured := Small.profiled beta 5 choice
      let calls := Small.recorded beta 5 choice
      unless ordinary.1 == measured.1 && ordinary.1 == calls.1 &&
          ordinary.2.1 == measured.2.1 && ordinary.2.1 == calls.2.1 &&
          (ordinary.2.2.1.map fun q => q.val.val) ==
            (measured.2.2.1.map fun q => q.val.val) &&
          (ordinary.2.2.1.map fun q => q.val.val) ==
            (calls.2.2.1.map fun q => q.val.val) do
        throw (IO.userError "control observations changed actual mu/helpers/messages")
      unless calls.2.2.2.map Small.label == [0, 1, 2] do
        throw (IO.userError "one-round actual control performed an unused final private fold")
      let weighted := Logup.Prover.Honest.Accounting.charges calls.2.2.2
      for kind in #[ArithmeticCostKind.add, .sub, .mul, .inv, .eq,
          .coefficientRead, .nodeRead, .valueRead, .metadata] do
        unless measured.2.2.2 kind == compressionCost 1 1 3 2 kind + weighted kind do
          throw (IO.userError "actual profile omitted compression or a selected weighted call")
      match calls.2.2.2.head? with
      | some (.prepare n _ _ _ data) =>
        if hn : n = 1 then
          let data : Fin 2 × Fin 4 → CMlPolynomialEval LogupTupleHonestTest.Small.F 1 := hn ▸ data
          for kind in List.finRange 2 do
            for slot in List.finRange 4 do
              let mu := multiplicities (B := LogupTupleHonestTest.Small.F)
                (n := 1) (P := 3) LogupTupleHonestTest.Small.indices
              unless data (kind, slot) == LogupTupleHonestTest.Small.prepared.weightedData
                  LogupTupleHonestTest.Small.f beta mu (kind, slot) do
                throw (IO.userError "recorded preparation did not receive the actual beta cache")
        else throw (IO.userError "recorded preparation changed its actual row dimension")
      | _ => throw (IO.userError "actual weighted preparation call missing")
  unless TwoRound.endpoint do
    throw (IO.userError "two-round actual cached default/source endpoint rejected a true witness")
  for choices in [#v[none, none], #v[some 5, none], #v[some 5, some 5]] do
    let measured := TwoRound.profiled choices
    let calls := TwoRound.recorded choices
    let expected := if choices[0].isSome then [0, 1, 2, 3, 2] else [0, 1, 2]
    unless calls.2.2.2.map Small.label == expected do
      throw (IO.userError "two-round control folded after abort/final round or skipped a fold")
    if choices[0].isSome then
      match calls.2.2.1.getLast? with
      | some q =>
        unless Sumcheck.Impl.Representation.evaluate LogupTupleHonestTest.Small.F 3 q 5 == 12 do
          throw (IO.userError "two-round non-Boolean terminal value changed")
      | none => throw (IO.userError "two-round final coefficient message missing")
    let weighted := Logup.Prover.Honest.Accounting.charges calls.2.2.2
    for kind in #[ArithmeticCostKind.add, .sub, .mul, .inv, .eq,
        .coefficientRead, .nodeRead, .valueRead, .metadata] do
      unless measured.2.2.2 kind == compressionCost 2 1 3 2 kind + weighted kind do
        throw (IO.userError "initial compression annotation was lost across a real private fold")
  for beta in List.finRange 17 do
    let b : LogupTupleHonestTest.ZeroRound.F := beta.val
    for alpha in [0, 1, 5] do
      unless ZeroRound.summary b alpha ==
          LogupTupleHonestTest.ZeroRound.summary b alpha do
        throw (IO.userError "n0/W0/tag0 cached default altered active/unused pole behavior")
  unless Extension.summary == LogupTupleHonestTest.Extension.summary &&
      Extension.summary == (true, 1) do
    throw (IO.userError "actual base-to-Ext6 default/source/native endpoint changed")
  pure (Small.summary 1 5, Extension.summary))

open Lean Elab Command in
run_cmd do
  for name in #[``Logup.Lookup.Tuple.Honest.prover,
      ``Logup.Lookup.Tuple.Honest.Accounting.profiledProver,
      ``Logup.Lookup.Tuple.Honest.Accounting.recordedProver,
      ``Logup.Lookup.Tuple.Honest.Accounting.observeProver,
      ``Small.run, ``Small.uniform, ``Small.observed, ``Small.profiled, ``Small.recorded,
      ``TwoRound.endpoint, ``TwoRound.recorded, ``TwoRound.profiled,
      ``ZeroRound.run, ``Extension.run, ``Extension.uniform] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Logup.Prover.Honest.Accounting.proverWith_erases_unit,
      ``Logup.Lookup.Tuple.Honest.prover_eq_sender_beta_cache,
      ``Logup.Lookup.Tuple.Honest.prover_eq_proverWith,
      ``Logup.Lookup.Tuple.Honest.Accounting.profiledProver_erases,
      ``Logup.Lookup.Tuple.Honest.Accounting.recordedProver_erases,
      ``Logup.Lookup.Tuple.Honest.Accounting.observe_profiledProver_eq_compression_add_charges,
      ``Small.uniform_eq, ``Small.failure, ``Small.success, ``Small.total, ``TwoRound.valid,
      ``Extension.total] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"
end LogupTupleDefaultTest
