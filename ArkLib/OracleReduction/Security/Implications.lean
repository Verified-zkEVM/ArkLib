/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt

/-!
# Implications between security notions

This file collects the implications between the various security notions.

For now, we only state the theorems. It's likely that we will split this file into multiple files in
a single `Implication` folder in the future, each file for the proof of a single implication.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SelectableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `roundByRoundSoundness` implies `soundness`
- `roundByRoundKnowledgeSoundness` implies `roundByRoundSoundness`
- `roundByRoundKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness init impl relIn relOut verifier knowledgeError →
        soundness init impl relIn.language relOut.language verifier knowledgeError := by
  simp [knowledgeSoundness, soundness, Set.language]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   sorry
  -- · simp only [Set.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ℝ≥0.coe_lt_one_iff, hLt]

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  unfold rbrSoundness
  unfold rbrKnowledgeSoundness at h
  obtain ⟨WitMid, extractor, kSF, h⟩ := h
  refine ⟨kSF.toStateFunction, ?_⟩
  intro stmtIn hRelIn WitIn' WitOut' witIn' prover chalIdx
  simp_all
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        knowledgeSoundness init impl relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

-- /-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
-- protocol with arbitrary added non-empty salts. -/
-- theorem rbrSoundness_implies_srSoundness_addSalt
--     {init : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType}
--     {impl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp)}
--     (langIn : Set StmtIn) (langOut : Set StmtOut)
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
--         Verifier.StateRestoration.soundness init impl langIn langOut (verifier.addSalt Salt)
--           (∑ i, (rbrSoundnessError i)) := by sorry

-- /-- Round-by-round knowledge soundness for a protocol implies state-restoration
-- knowledge soundness for the same protocol with arbitrary added non-empty salts. -/
-- theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
--     {init : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType}
--     {impl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp)}
--     (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
--         Verifier.StateRestoration.knowledgeSoundness init impl relIn relOut
--           (verifier.addSalt Salt) (∑ i, rbrKnowledgeError i) := by sorry

/-- State-restoration soundness for a protocol with added salts implies state-restoration
soundness for the original protocol (with improved parameters?)
-/
theorem srSoundness_addSalt_implies_srSoundness_original
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn (pSpec.addSalt Salt)).FunctionType)
    (srImpl : QueryImpl oSpec
      (StateT (srChallengeOracle StmtIn (pSpec.addSalt Salt)).FunctionType ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut
        (verifier.addSalt Salt) srSoundnessError →
        Verifier.StateRestoration.soundness sorry sorry langIn langOut
          verifier srSoundnessError := by sorry

/-- State-restoration knowledge soundness for a protocol with added salts implies state-restoration
knowledge soundness for the original protocol with improved parameters. -/
theorem srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn (pSpec.addSalt Salt)).FunctionType)
    (srImpl : QueryImpl oSpec
      (StateT (srChallengeOracle StmtIn (pSpec.addSalt Salt)).FunctionType ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        (verifier.addSalt Salt) srKnowledgeError →
        Verifier.StateRestoration.knowledgeSoundness sorry sorry relIn relOut
          verifier srKnowledgeError := by sorry

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        soundness init impl langIn langOut verifier srSoundnessError := by
  sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        verifier srKnowledgeError →
      knowledgeSoundness init impl relIn relOut verifier srKnowledgeError := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier
