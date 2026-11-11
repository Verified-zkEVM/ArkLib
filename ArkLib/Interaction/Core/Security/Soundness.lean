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

universe v uS uI wI wJ

namespace Interaction.Core
open PFunctor FreeM OracleComp Oracle
open scoped ENNReal

/-- Soundness against all adversaries in a model, within the input admissibility promise.

The verdict's claim type may depend on a public context read from the observation, such as the
shape path of the run; the output language is judged at that context.
-/
def soundness {S Obs Ctx : Type*} {T : ClaimFamily Ctx} [MeasurableSpace Obs]
    (M : AdversaryModel S Obs) (input : StatementProblem S) (output : Problem T)
    (context : Obs → Ctx) (verdict : (obs : Obs) → Option (T.Claim (context obs)))
    (ε : ℝ≥0∞) : Prop :=
  ∀ stmt, input.admissible () stmt → ¬ input.language () stmt →
    ∀ adv : M.Adv stmt,
      M.outcome stmt adv
        {obs | ∃ t, verdict obs = some t ∧ output.language (context obs) t} ≤ ε

/-- Soundness of a plain run interpreted in an arbitrary distribution monad.
Ambient failure contributes no mass to the accepting event. -/
abbrev Verifier.soundnessWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T)
    (handler : QueryImpl (ambient + challengeSpec plainSig s) m)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  ∀ (Out : PathAlong plainSig s → Type) stmt,
    input.admissible () stmt → ¬ input.language () stmt →
    ∀ p : Prover plainSig ambient s Out,
      Pr{let obs ← simulateQ handler (V.run stmt p)}[
        ∃ t, obs.2.2 = some t ∧ output.language (projectPathAlong _ s obs.1) t] ≤ ε

/-- A plain decision has positive probability of accepting an output in the language. -/
def Verifier.validAcceptanceWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {S : Type uS} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (impl : QueryImpl ambient m) (langOut : (p : Path s) → T p → Prop)
    (stmt : S) (tr : PathAlong plainSig s) : Prop :=
  0 < Pr{let v ← (simulateQ impl
      (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run)}[
        ∃ t, v = some t ∧ langOut (projectPathAlong plainSig s tr) t]

/-- Soundness of an oracle run interpreted in an arbitrary distribution monad, with the output
oracle data read from the verifier's output map. -/
abbrev OracleVerifier.soundnessWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs)
    (handler : QueryImpl (ambient + challengeSpec oracleSig s) m)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (Out : PathAlong oracleSig s → Type) stmt,
    input.admissible () stmt → ¬ input.language () stmt →
    ∀ p : Prover oracleSig ambient s Out,
      Pr{let obs ← simulateQ handler (V.run stmt.1 stmt.2 p)}[
        ∃ t, obs.2.2 = some t ∧ output.language (projectPathAlong _ s obs.1) t] ≤ ε

/-- An oracle decision has positive probability of accepting an output in the language,
using the input data and the full transcript payloads to answer resource queries. -/
def OracleVerifier.validAcceptanceWith {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι} {s : OracleProtocol}
    {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (impl : QueryImpl ambient m)
    (langOut : (p : Path s) → OracleVerifier.Output T B p → Prop) (stmt : S × (∀ i, A i))
    (tr : PathAlong oracleSig s) : Prop :=
  let p := projectPathAlong oracleSig s tr
  let view := toView s tr
  let resources := (stmt.2, payloads s tr)
  let handler : QueryImpl (ambient + (pathResources inputs s p).spec) m :=
    QueryImpl.addLift impl
      ((pathResources inputs s p).answer resources)
  0 < Pr{let v ← simulateQ handler (V.decide stmt.1 p view).run}[
    ∃ t, v = some t ∧ langOut p (t, (V.outputMap stmt.1 p view).f resources)]

/-- Classical soundness uses the full class of focal strategies, including private continuations.
The output language is indexed by the shape path of the run. The input statement may lie in any
universe. -/
abbrev Verifier.soundness {ι σ : Type} {S : Type uS} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  ∀ Out : PathAlong plainSig s → Type,
  letI : MeasurableSpace (Observation plainSig s Out T) := ⊤
  Core.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => projectPathAlong plainSig s obs.1) (fun obs => obs.2.2) ε

/-- Classical oracle soundness uses the full class of focal strategies over the oracle protocol,
with the input oracle data supplied to the run. -/
abbrev OracleVerifier.soundness {ι σ : Type} {I : Type uI} {S : Type uS} {ambient : OracleSpec ι}
    {s : OracleProtocol} {T : Path s → Type} {A : I → Type} {J : Path s → Type}
    {B : (p : Path s) → J p → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, wJ} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (ε : ℝ≥0∞) : Prop :=
  ∀ Out : PathAlong oracleSig s → Type,
  letI : MeasurableSpace (Observation oracleSig s Out (OracleVerifier.Output T B)) := ⊤
  Core.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => projectPathAlong oracleSig s obs.1) (fun obs => obs.2.2) ε

end Interaction.Core
