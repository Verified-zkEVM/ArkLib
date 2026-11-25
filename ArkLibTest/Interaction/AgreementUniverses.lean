/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Agreement
import ArkLib.Interaction.Legacy.OracleKnowledge

/-! # Agreement clients

Agreement transports runs and security statements between verifiers with the same decisions and
outputs. Output families depend on the shape path, and knowledge witnesses depend on the statement
and transcript. The security definitions take their data in `Type`, so every argument here does.
-/

open PFunctor FreeM Interaction Interaction.OracleVerifier Interaction.Oracle OracleComp

namespace Interaction.AgreementUniversesTests

variable {ι : Type} {S : Type} {I : Type}
  {ambient : OracleSpec ι} {s s' : OracleProtocol.{0, 0}} {A : I → Type}
  {T : Path s → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
  {inputs : OracleFamily.{0, 0, 0} I A}
  {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
  {V V' : OracleVerifier ambient s S T inputs outputs}

example (h : Agrees V V') (stmt : S) (data : ∀ i, A i)
    {Out : Transcript oracleSig s → Type} (p : Prover oracleSig ambient s Out) :
    V.run stmt data p = V'.run stmt data p := h.run_eq stmt data p

example {σ : Type} (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i)))
    (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ENNReal) :
    V.rbrSoundness impl input output draw ε ↔ V'.rbrSoundness impl input output draw ε :=
  h.rbrSoundness_iff impl input output draw ε

example {σ : Type} {Win : (S × (∀ i, A i)) → Type}
    {W : (S × (∀ i, A i)) → Transcript oracleSig s → Type}
    (h : Agrees V V') (impl : QueryImpl ambient (StateT σ ProbComp))
    (adm : S × (∀ i, A i) → Prop) (relIn : (stmt : S × (∀ i, A i)) → Win stmt → Prop)
    (relOut : (stmt : S × (∀ i, A i)) → (tr : Transcript oracleSig s) →
      OracleVerifier.Output T B tr.path → W stmt tr → Prop)
    (draw : PrefixDraw viewSig ProbComp s) (ε : PrefixError oracleSig s) :
    V.rbrKnowledgeSoundness impl adm relIn relOut draw ε ↔
      V'.rbrKnowledgeSoundness impl adm relIn relOut draw ε :=
  h.rbrKnowledgeSoundness_iff impl adm relIn relOut draw ε

-- These applications specialize the Cast APIs before any tree equality is supplied.
#check OracleVerifier.soundness_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)

section KnowledgeCast
variable {Win : (S × (∀ i, A i)) → Type}
  {W : (S × (∀ i, A i)) → Transcript oracleSig s → Type}

#check OracleVerifier.rbrKnowledgeSoundness_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs) (Win := Win) (W := W)
end KnowledgeCast
section LegacyOutputs
variable {J T : Type} {B : J → Type} {outputs : OracleFamily.{0, 0, 0} J B}

-- These legacy relation adapters transport completeness and knowledge soundness along a tree
-- equality.
#check Legacy.completeness_cast (S := S) (inputs := inputs) (outputs := outputs)
#check Legacy.knowledgeSoundness_cast (S := S) (inputs := inputs) (outputs := outputs)
end LegacyOutputs

section Bundles

variable {inputs : OracleBundle} {V V' : OracleVerifier ambient s S T inputs outputs}

-- Agreement follows from equal decisions and outputs on every transcript.
example
    (hd : ∀ (stmt : S) (tr : Transcript oracleSig s),
      V.decide stmt _ (toView s tr) = V'.decide stmt _ (toView s tr))
    (ho : ∀ (stmt : S) (data : inputs.Data) (tr : Transcript oracleSig s),
      (V.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr) =
        (V'.outputMap stmt _ (toView s tr)).f (data, oracleMessages s tr)) :
    Agrees V V' := Agrees.of_decide_eq hd ho

#check OracleVerifier.outputMap_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)
#check OracleVerifier.simulateQ_decide_cast (S := S) (T := T) (ambient := ambient)
  (inputs := inputs) (outputs := outputs)

end Bundles

end Interaction.AgreementUniversesTests
