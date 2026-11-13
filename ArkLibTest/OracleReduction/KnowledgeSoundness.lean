/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.UnboundedExtraction

/-! Compile-time checks for proof-system relations with non-Boolean witnesses, and for the
equivalence of unbounded knowledge soundness with relation soundness. -/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (relation : Set (Nat × Nat)) (verifier : Verifier oSpec Nat Bool pSpec)

-- Proof-system witnesses need not be Boolean.
example : Prop := Proof.knowledgeSoundness init impl relation verifier 0

example : Prop := Proof.rbrKnowledgeSoundness init impl relation verifier (fun _ => 0)

-- A noncomputable classical selector is a straightline extractor: the type bounds no cost.
noncomputable example : Extractor.Straightline oSpec Nat Nat Bool pSpec :=
  Extractor.Straightline.choose relation

-- Knowledge soundness with an unconstrained extractor is relation soundness.
example (relOut : Set (Bool × Unit)) (ε : NNReal) :
    verifier.knowledgeSoundness init impl relation relOut ε ↔
      verifier.relationSoundness init impl relation relOut ε :=
  Verifier.knowledgeSoundness_iff_relationSoundness init impl

-- The equivalence applies to concrete verifiers: the identity verifier is relation sound.
example (rel : Set (Nat × Nat)) :
    (Verifier.id : Verifier oSpec Nat Nat _).relationSoundness init impl rel rel 0 :=
  (Verifier.knowledgeSoundness_iff_relationSoundness init impl).mp
    (Verifier.id_knowledgeSoundness init impl)
