/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-! Compile-time checks for proof-system relations with non-Boolean witnesses. -/

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (relation : Set (Nat × Nat)) (verifier : Verifier oSpec Nat Bool pSpec)

-- Proof-system witnesses need not be Boolean.
example : Prop := Proof.knowledgeSoundness init impl relation verifier 0

example : Prop := Proof.rbrKnowledgeSoundness init impl relation verifier (fun _ => 0)
