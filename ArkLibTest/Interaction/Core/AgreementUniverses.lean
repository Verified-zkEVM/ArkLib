/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Security.Agreement
import ArkLib.Interaction.Core.Legacy.OracleKnowledge

/-! # Agreement clients with unequal input and query universes

Statements, input indices, input queries and output queries occupy `Type 2`, `Type 1`,
`Type 3` and `Type 4`, respectively; oracle-node queries occupy `Type 5`. Output families depend
on the shape path. Knowledge witnesses depend on the statement and transcript, in `Type 6` and
`Type 7`. The last section also checks the general move, ambient and output-index universes.
-/

open PFunctor FreeM Interaction.Core Interaction.Core.OracleVerifier Interaction.Oracle OracleComp

namespace Interaction.Core.AgreementUniversesTests

variable {ι : Type} {S : Type 2} {I : Type 1}
  {ambient : OracleSpec ι} {s s' : OracleProtocol.{0, 5}} {A : I → Type}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleFamily.{1, 0, 3} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, 4} (J p) (B p)}
  {V V' : OracleVerifier ambient s S T inputs outputs}

example (h : Agrees V V') (stmt : S) (data : ∀ i, A i)
    {Out : PathAlong oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := h.run_eq stmt data p

example {σ : Type} (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ENNReal) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε :=
  h.rbrSoundness_iff impl input output draw ε

example {σ : Type} {Win : (S × (∀ i, A i)) → Type 6}
    {W : (S × (∀ i, A i)) → PathAlong oracleSig s → Type 7}
    (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (adm : S × (∀ i, A i) → Prop) (relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop)
    (relOut : (stmt : S × (∀ i, A i)) → (tr : PathAlong oracleSig s) →
      OracleVerifier.Output T B (projectPathAlong oracleSig s tr) → W stmt tr → Prop)
    (draw : PrefixDraw oracleSig ProbComp s) (ε : PrefixError oracleSig s) :
    V.rbrKnowledgeSoundness.{2, 6, 1, 7} impl adm relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness.{2, 6, 1, 7} impl adm relIn relOut draw ε :=
  h.rbrKnowledgeSoundness_iff impl adm relIn relOut draw ε

-- These applications specialize the Cast APIs before any tree equality is supplied.
#check OracleVerifier.soundness_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)

section KnowledgeCast
variable {Win : (S × (∀ i, A i)) → Type 6}
  {W : (S × (∀ i, A i)) → PathAlong oracleSig s → Type 7}

#check OracleVerifier.rbrKnowledgeSoundness_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs) (Win := Win) (W := W)
end KnowledgeCast
section LegacyOutputs
variable {J T : Type} {B : J → Type} {outputs : OracleFamily.{0, 0, 4} J B}

-- These legacy relation adapters retain the original large output-query specialization.
#check Legacy.completeness_cast (S := S) (inputs := inputs) (outputs := outputs)
#check Legacy.knowledgeSoundness_cast (S := S) (inputs := inputs) (outputs := outputs)
end LegacyOutputs

section General

variable {ι : Type 2} {S : Type 3} {s s' : OracleProtocol.{1, 4}}
  {ambient : OracleSpec.{2, 1} ι} {T : Path s → Type 1} {J : Path s → Type 5}
  {B : (p : Path s) → J p → Type 1} {inputs : Resources.{1, 6, 7}}
  {outputs : (p : Path s) → OracleFamily.{5, 1, 8} (J p) (B p)}
  {V V' : OracleVerifier ambient s S T inputs outputs}

-- Agreement and decision/output transport retain independent ambient and output-index universes.
example
    (hd : ∀ (stmt : S) (tr : PathAlong oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : inputs.Data) (tr : PathAlong oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, payloads s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, payloads s tr)) :
    Agrees V V' := Agrees.of_decide_eq hd ho

#check OracleVerifier.outputMap_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)
#check OracleVerifier.simulateQ_decide_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)

-- Ordinary runs keep general moves and independent input data, node queries and output queries.
example {ι : Type 1} {ambient : OracleSpec ι} {J : Path s → Type 1}
    {B : (p : Path s) → J p → Type 1}
    {outputs : (p : Path s) → OracleFamily.{1, 1, 8} (J p) (B p)}
    {V V' : OracleVerifier ambient s S T inputs outputs}
    (h : Agrees V V') (stmt : S) (data : inputs.Data)
    {Out : PathAlong oracleSig s → Type 1} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := h.run_eq stmt data p

end General

end Interaction.Core.AgreementUniversesTests
