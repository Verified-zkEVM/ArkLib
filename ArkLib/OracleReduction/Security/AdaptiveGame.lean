/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Shared adaptive security games

An experiment runs an adversarial computation, passes its output to the verifier phase, and
interprets both in a single oracle state. The knowledge game adds a final extraction phase with
its own interface and handler. Protocol-specific adapters decide what information reaches that
phase and which adversaries are admissible.
-/

@[expose] public section

open OracleComp
open scoped ProbabilityTheory

namespace AdaptiveGame

variable {ι κ σ A V O W : Type} {spec : OracleSpec ι} {extractorSpec : OracleSpec κ}

/-- Execute the two phases, retaining the data needed to read the result or extract a witness. -/
def execute (adversary : OracleComp spec A) (verify : A → OracleComp spec V) :
    OracleComp spec (A × V) := do
  let a ← adversary
  let v ← verify a
  return (a, v)

/-- Initialize the shared oracle once and read the outcome of the execution. -/
def run (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (adversary : OracleComp spec A) (verify : A → OracleComp spec V)
    (readout : A → V → O) : ProbComp O := do
  (simulateQ impl (do
    let a ← adversary
    let v ← verify a
    return readout a v)).run' (← init)

/-- An optional verifier result can be read through an optional oracle computation. -/
theorem run_eq_runOption (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (adversary : OracleComp spec A) (verify : A → OptionT (OracleComp spec) V)
    (readout : A → V → O) :
    run init impl adversary (fun a => (verify a).run) (fun a out => out.map (readout a)) = (do
      (simulateQ impl (do
        let a ← liftM adversary
        let v ← verify a
        return readout a v : OptionT (OracleComp spec) O).run).run' (← init)) := by
  unfold run
  congr 1
  funext st
  congr 1
  congr 1
  simp only [OptionT.run_bind, OptionT.run_monadLift,
    Option.elimM, bind_map_left, Option.elim_some, OptionT.run_pure]
  congr 1
  funext a
  congr 1
  funext out
  cases out <;> rfl

/-- Run the extractor in the final shared state with explicitly supplied oracle permissions.
Retain failure as an optional witness in the outcome. -/
def runWithExtractor (init : ProbComp σ) (impl : QueryImpl spec (StateT σ ProbComp))
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (adversary : OracleComp spec A) (verify : A → OracleComp spec V)
    (extract : A → V → OptionT (OracleComp extractorSpec) W)
    (readout : A → V → Option W → O) : ProbComp O := do
  (do
    let (a, v) ← simulateQ impl (execute adversary verify)
    let wit ← simulateQ extractorImpl (extract a v).run
    return readout a v wit : StateT σ ProbComp O).run' (← init)

/-- Bound a failure event for each admissible adversary. Admissibility does not truncate runs. -/
def Bounded {Adv : Type*} (admissible : Adv → Prop) (experiment : Adv → ProbComp O)
    (bad : O → Prop) (error : ENNReal) : Prop :=
  ∀ a, admissible a → Pr{let out ← experiment a}[bad out] ≤ error

end AdaptiveGame
