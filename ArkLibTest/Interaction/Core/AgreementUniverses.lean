/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Security.Agreement
import ArkLib.Interaction.Core.Legacy.OracleKnowledge

/-! # Agreement clients with unequal input and query universes

Statements, input indices, input queries and output queries occupy `Type 2`, `Type 1`,
`Type 3` and `Type 4`, respectively. Only observations, responses and output indices are small.
-/

open PFunctor FreeM Interaction.Core Interaction.Core.OracleVerifier Interaction.Oracle OracleComp

namespace Interaction.Core.AgreementUniversesTests

variable {ι J T : Type} {S : Type 2} {I : Type 1}
  {ambient : OracleSpec ι} {s s' : OracleProtocol} {A : I → Type} {B : J → Type}
  {inputs : OracleFamily.{1, 0, 3} I A} {outputs : OracleFamily.{0, 0, 4} J B}
  {V V' : OracleVerifier ambient s S (fun _ => T) inputs (fun _ => outputs)}

example (h : Agrees V V') (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := h.run_eq stmt data p

example {σ : Type} (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : PathProblem s (fun _ => T × (∀ j, B j)))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ENNReal) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε :=
  h.rbrSoundness_iff impl input output draw ε

example {σ Win : Type} {W : PathAlong oracleSig s → Type}
    (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (adm : S × (∀ i, A i) → Prop) (relIn : (S × (∀ i, A i)) → Win → Prop)
    (relOut : (tr : PathAlong oracleSig s) → (T × (∀ j, B j)) → W tr → Prop)
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ENNReal) :
    V.rbrKnowledgeSoundness.{2, 0, 1} impl adm relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness.{2, 0, 1} impl adm relIn relOut draw ε :=
  h.rbrKnowledgeSoundness_iff impl adm relIn relOut draw ε

-- These applications specialize the Cast APIs before any tree equality is supplied.
#check OracleVerifier.soundness_cast (S := S) (inputs := inputs) (outputs := outputs)
#check OracleVerifier.rbrKnowledgeSoundness_cast (S := S) (inputs := inputs) (outputs := outputs)
#check Legacy.completeness_cast (S := S) (inputs := inputs) (outputs := outputs)
#check Legacy.knowledgeSoundness_cast (S := S) (inputs := inputs) (outputs := outputs)

end Interaction.Core.AgreementUniversesTests
