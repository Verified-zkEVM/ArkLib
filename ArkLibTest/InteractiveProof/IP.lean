/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
import ArkLib.InteractiveProof.IP

/-! Regression tests for the public-coin state-restoration adapters. -/

open OracleComp OracleSpec ProtocolSpec

-- Adding the dummy witness changes neither the move count nor the private-coin convention.
example {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : IP.SRProver Statement pSpec (Salt := Salt)) (t : ℕ) :
    P.toReduction.IsQueryBoundP
      (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t ↔
    P.IsQueryBoundP
      (publicQuerySelector (Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t := by
  simp [IP.SRProver.toReduction]
