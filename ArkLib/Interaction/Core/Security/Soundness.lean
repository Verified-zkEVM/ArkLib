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

/-- Classical soundness uses the full class of focal strategies, including private continuations.
The output language is indexed by the shape path of the run. -/
abbrev Verifier.soundness {ι σ S : Type} {ambient : OracleSpec ι}
    {s : Protocol} {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T) (ε : ℝ≥0∞) : Prop :=
  ∀ Out : PathAlong plainSig s → Type,
  letI : MeasurableSpace (Observation plainSig s Out T) := ⊤
  Core.soundness (V.classicalModel (Out := Out) init impl challenges) input output
    (fun obs => projectPathAlong plainSig s obs.1) (fun obs => obs.2.2) ε

end Interaction.Core
