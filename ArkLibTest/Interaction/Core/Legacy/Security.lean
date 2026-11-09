/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.Security
import ArkLibTest.Interaction.Core.Legacy.Execution

/-! Acceptance examples for the security transfers: completeness and soundness of an embedded
legacy reduction, and an adversarial interaction-layer prover passed through the soundness
transfer. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec MeasureTheory
open scoped NNReal

namespace Interaction.Core.Legacy.SecurityTests
open Interaction.Core.Legacy.ExecutionTests

/-! ### Completeness -/

example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (relIn : Set (Nat × Nat)) (relOut : Set (Nat × Nat)) (ε : ℝ≥0) :
    (embedReduction counterReduction).completeness init impl
        (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (relProblem relIn)
        (relProblem relOut) (fun _ o => o.1) (fun obs _ _ => obs.2.1.2) (fun _ w => w) ε ↔
      counterReduction.completeness init impl relIn relOut ε :=
  completeness_iff init impl counterReduction relIn relOut ε

/-! ### An adversarial interaction-layer prover -/

/-- A cheating prover written directly in the interaction layer: it sends `42`, answers the
challenge `true` with `7`, and claims an unrelated output `true`. It is not the embedding of any
honest legacy prover. -/
def cheat : Core.Prover plainSig []ₒ (protocol twoWay) (fun _ => Bool) :=
  pure ⟨(42 : Nat), pure fun (b : Bool) => pure ⟨(bif b then 7 else 0 : Nat), pure true⟩⟩

/-- The legacy prover translated from the cheating prover, with fixed output statement `0`. -/
def cheatLegacy : _root_.Prover []ₒ Nat PUnit Nat PUnit twoWay :=
  translate (mapOut _ (fun _ _ => ⟨⟩) cheat) 0

/-- Embedding the translation gives back the cheating prover with its outputs replaced. -/
example (stmt : Nat) :
    embedProver cheatLegacy stmt ⟨⟩ =
      mapOut _ (fun _ _ => ((0, ⟨⟩) : Nat × PUnit))
        (mapOut _ (fun _ _ => (⟨⟩ : PUnit)) cheat) :=
  embedProver_translate _ 0 stmt

def cheatOutputs (r : LegacyResult twoWay Nat PUnit) : Option (Nat × Nat × Nat) :=
  r.map fun x => (show Nat from x.1.1 0, show Nat from x.1.1 2, x.2)

/-- The translated cheating prover sends the same messages in the legacy layer: the verifier
accepts with challenge `true` and outputs `2 + 7`. -/
example : cheatOutputs (simulateQ (legacyAnswers true)
    ((⟨cheatLegacy, lastIfTrue⟩ : _root_.Reduction []ₒ Nat PUnit Nat PUnit twoWay).run 2
      ⟨⟩).run) = some (42, 7, 9) := by
  decide

/-- With challenge `false`, the verifier rejects. -/
example : cheatOutputs (simulateQ (legacyAnswers false)
    ((⟨cheatLegacy, lastIfTrue⟩ : _root_.Reduction []ₒ Nat PUnit Nat PUnit twoWay).run 2
      ⟨⟩).run) = none := by
  decide

/-- Legacy soundness of `lastIfTrue` bounds the acceptance probability of the cheating
interaction-layer prover, through the soundness transfer. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (langIn langOut : Set Nat) (ε : ℝ≥0) (h : lastIfTrue.soundness init impl langIn langOut ε)
    (stmt : Nat) (hstmt : stmt ∉ langIn) :
    letI : MeasurableSpace (Observation plainSig (protocol twoWay) (fun _ => Bool) Nat) := ⊤
    𝒟[experiment init impl (plainChallengeImpl ProtocolSpec.challengeQueryImpl)
        ((embedVerifier lastIfTrue).run stmt cheat)]
      {obs | ∃ t, obs.2.2 = some t ∧ (langProblem langOut).language () t} ≤ ε :=
  (soundness_iff init impl lastIfTrue langIn langOut ε).mpr h (fun _ => Bool) stmt trivial
    (fun hl => hstmt ((langProblem_language langIn stmt).mp hl)) cheat

/-- Interaction-layer soundness of the embedded verifier bounds a cheating legacy prover. -/
example [∀ i, SampleableType (twoWay.Challenge i)] (init : ProbComp Unit)
    (impl : QueryImpl []ₒ (StateT Unit ProbComp))
    (langIn langOut : Set Nat) (ε : ℝ≥0)
    (h : (embedVerifier lastIfTrue).soundness init impl
      (plainChallengeImpl ProtocolSpec.challengeQueryImpl) (langProblem langIn)
      (langProblem langOut) ε) :
    lastIfTrue.soundness init impl langIn langOut ε :=
  (soundness_iff init impl lastIfTrue langIn langOut ε).mp h

end Interaction.Core.Legacy.SecurityTests
