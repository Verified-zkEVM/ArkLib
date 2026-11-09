/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.Completeness

/-!
# Soundness

For every admissible false input and every adversary in the model, acceptance of an output in
the output language has bounded probability. Rejected runs and missing probability mass are
both excluded from this event, without identifying them in the observation distribution.
For a general model the bound uses the measure's outer extension; the classical wrapper
uses discrete observations, so every event is measurable.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM OracleComp Oracle
open scoped ENNReal

/-- Soundness against all adversaries in a model, within the input admissibility promise. -/
def soundness {S Obs T : Type*} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : StatementProblem T)
    (verdict : Obs → Option T) (ε : ℝ≥0∞) : Prop :=
  ∀ stmt, input.admissible () stmt → ¬ input.language () stmt →
    ∀ adv : M.Adv stmt,
      M.outcome stmt adv {obs | ∃ t, verdict obs = some t ∧ output.language () t} ≤ ε

/-- Classical soundness uses the full class of focal strategies, including private continuations. -/
abbrev Verifier.soundness {ι σ S T : Type} {ambient : OracleSpec ι}
    {s : Protocol}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : StatementProblem T) (ε : ℝ≥0∞) : Prop :=
  ∀ Out : PathAlong plainSig s → Type,
  letI : MeasurableSpace (Observation plainSig s Out T) := ⊤
  Core.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => obs.2.2) ε

/-- Classical oracle soundness uses the full class of focal strategies over the oracle protocol,
with the input oracle data supplied to the run. -/
abbrev OracleVerifier.soundness {ι I J σ S T : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol} {A : I → Type} {B : J → Type}
    {inputs : OracleFamily I A} {outputs : OracleFamily J B}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : StatementProblem (T × (∀ j, B j)))
    (ε : ℝ≥0∞) : Prop :=
  ∀ Out : PathAlong oracleSig s → Type,
  letI : MeasurableSpace (Observation oracleSig s Out (T × (∀ j, B j))) := ⊤
  Core.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => obs.2.2) ε

end Interaction.Core
