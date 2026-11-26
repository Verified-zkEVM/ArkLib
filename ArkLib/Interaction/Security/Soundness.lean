/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Security.Completeness

/-!
# Soundness

For every admissible false input and every adversary in the model, acceptance of an output in
the output language has bounded probability. Rejected runs and missing probability mass are
both excluded from this event, without identifying them in the outcome distribution.
For a general model the bound uses the measure's outer extension; the classical wrapper
uses discrete outcomes, so every event is measurable.
-/

@[expose] public section

universe v v'

namespace Interaction
open PFunctor FreeM OracleComp Oracle
open scoped ENNReal

/-- Soundness against all adversaries in a model, within the input admissibility promise.

The verdict's claim type may depend on a public context read from the outcome, such as the
shape path of the run; the output language is judged at that context.
-/
def soundness {S Obs Ctx : Type} {T : ClaimFamily.{0, 0} Ctx} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : Problem.{0, 0, 0} T)
    (context : Obs → Ctx) (verdict : (obs : Obs) → Option (T.Claim (context obs)))
    (ε : ℝ≥0∞) : Prop :=
  ∀ stmt, input.admissible () stmt → ¬ input.language () stmt →
    ∀ adv : M.Adv stmt,
      M.outcome stmt adv
        {obs | ∃ t, verdict obs = some t ∧ output.language (context obs) t} ≤ ε

/-- Soundness of a plain run interpreted in an arbitrary distribution monad.
Ambient failure contributes no mass to the accepting event. -/
def Verifier.soundnessUsing {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T)
    (run : {α : Type} → OracleComp (ambient + challengeSpec plainSig s) α → m α)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  ∀ (Out : Transcript plainSig s → Type) stmt,
    input.admissible () stmt → ¬ input.language () stmt →
    ∀ p : Prover plainSig ambient s Out,
      Pr{let obs ← run (V.run stmt p)}[
        ∃ t, obs.2.2 = some t ∧ output.language (Transcript.path obs.1) t] ≤ ε

/-- Interpret the whole run with a query handler. -/
abbrev Verifier.soundnessWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T)
    (handler : QueryImpl (ambient + challengeSpec plainSig s) m)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  V.soundnessUsing (simulateQ handler) input output ε

/-- A plain decision has positive probability of accepting an output in the language. -/
def Verifier.validAcceptanceUsing {m : Type → Type v} {n : Type → Type v'}
    [Monad m] [Monad n] [EvalDistSemantics n]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (impl : QueryImpl ambient m)
    (run : {α : Type} → m α → n α) (langOut : (p : Path s) → T p → Prop)
    (stmt : S) (tr : Transcript plainSig s) : Prop :=
  0 < Pr{let v ← run (simulateQ impl
      (V.decide stmt tr.path (toPlainView s tr)).run)}[
        ∃ t, v = some t ∧ langOut tr.path t]

/-- Interpret the decision without an additional execution map. -/
def Verifier.validAcceptanceWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (impl : QueryImpl ambient m)
    (langOut : (p : Path s) → T p → Prop)
    (stmt : S) (tr : Transcript plainSig s) : Prop :=
  V.validAcceptanceUsing impl (fun x => x) langOut stmt tr

/-- Soundness of an oracle run interpreted in an arbitrary distribution monad, with the output
oracle data read from the verifier's output map. The input is any oracle bundle, as in
`OracleVerifier.run`; an oracle family enters through its coercion to a bundle. -/
def OracleVerifier.soundnessUsing {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs)
    (run : {α : Type} → OracleComp (ambient + challengeSpec oracleSig s) α → m α)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (Out : Transcript oracleSig s → Type) stmt,
    input.admissible () stmt → ¬ input.language () stmt →
    ∀ p : Prover oracleSig ambient s Out,
      Pr{let obs ← run (V.run stmt.1 stmt.2 p)}[
        ∃ t, obs.2.2 = some t ∧ output.language (Transcript.path obs.1) t] ≤ ε

/-- Interpret the whole run with a query handler. -/
abbrev OracleVerifier.soundnessWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (ε : ℝ≥0∞) : Prop :=
  V.soundnessUsing (simulateQ handler) input output ε

/-- An oracle decision has positive probability of accepting an output in the language,
using the input data and the transcript's oracle messages to answer bundle queries. -/
def OracleVerifier.validAcceptanceUsing {m : Type → Type v} {n : Type → Type v'}
    [Monad m] [Monad n] [EvalDistSemantics n]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs) (impl : QueryImpl ambient m)
    (run : {α : Type} → m α → n α)
    (langOut : (p : Path s) → OracleVerifier.Output T outputs p → Prop)
    (stmt : S × inputs.Data)
    (tr : Transcript oracleSig s) : Prop :=
  let p := tr.path
  let view := toView s tr
  let pathData := (stmt.2, oracleMessages s tr)
  let handler : QueryImpl (ambient + (pathBundle inputs s p).spec) m :=
    QueryImpl.addLift impl
      ((pathBundle inputs s p).answer pathData)
  0 < Pr{let v ← run (simulateQ handler (V.decide stmt.1 p view).run)}[
    ∃ t, v = some t ∧ langOut p (t, (V.outputMap stmt.1 p view).f pathData)]

/-- Interpret the decision without an additional execution map. -/
def OracleVerifier.validAcceptanceWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : OracleProtocol.{0, 0}}
    {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs) (impl : QueryImpl ambient m)
    (langOut : (p : Path s) → OracleVerifier.Output T outputs p → Prop)
    (stmt : S × inputs.Data)
    (tr : Transcript oracleSig s) : Prop :=
  V.validAcceptanceUsing impl (fun x => x) langOut stmt tr

/-- Classical soundness uses the full class of focal strategies, including private continuations.
The output language is indexed by the shape path of the run. -/
abbrev Verifier.soundness {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  ∀ Out : Transcript plainSig s → Type,
  letI : MeasurableSpace (Outcome plainSig s Out T) := ⊤
  Interaction.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => Transcript.path obs.1) (fun obs => obs.2.2) ε

/-- Classical soundness specializes the whole-computation experiment interface. -/
theorem Verifier.soundness_iff_soundnessUsing {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) :
    V.soundness init impl challenges input output ε ↔
      V.soundnessUsing (experiment init impl challenges) input output ε := by
  unfold Verifier.soundness Verifier.soundnessUsing Interaction.soundness
  apply forall_congr'
  intro Out
  let : MeasurableSpace (Outcome plainSig s Out T) := ⊤
  apply forall_congr'
  intro stmt
  apply forall_congr'
  intro hadm
  apply forall_congr'
  intro hfalse
  apply forall_congr'
  intro p
  rw [prEvent_eq_evalDist_of_discrete]
  rfl

/-- Classical oracle soundness uses the full class of focal strategies over the oracle protocol,
with the input oracle data supplied to the run. -/
abbrev OracleVerifier.soundness {ι σ : Type} {S : Type} {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs))
    (ε : ℝ≥0∞) : Prop :=
  ∀ Out : Transcript oracleSig s → Type,
  letI : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs)) := ⊤
  Interaction.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => Transcript.path obs.1) (fun obs => obs.2.2) ε

/-- Classical soundness specializes the whole-computation experiment interface. -/
theorem OracleVerifier.soundness_iff_soundnessUsing {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι}
    {s : OracleProtocol.{0, 0}} {T : Path s → Type} {inputs : OracleBundle}
    {outputs : Path s → OracleBundle}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T outputs)) (ε : ℝ≥0∞) :
    V.soundness init impl challenges input output ε ↔
      V.soundnessUsing (experiment init impl challenges) input output ε := by
  unfold OracleVerifier.soundness OracleVerifier.soundnessUsing Interaction.soundness
  apply forall_congr'
  intro Out
  let : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T outputs)) := ⊤
  apply forall_congr'
  intro stmt
  apply forall_congr'
  intro hadm
  apply forall_congr'
  intro hfalse
  apply forall_congr'
  intro p
  rw [prEvent_eq_evalDist_of_discrete]
  rfl

end Interaction
