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
  --     zero_add, ENNReal.coe_lt_one_iff, hLt]

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

/-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
protocol with arbitrary added non-empty salts.

This theorem shows that the addition of salts does not weaken the security guarantee when moving
from round-by-round to state-restoration security. -/
theorem rbrSoundness_implies_srSoundness_addSalt
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Inhabited (Salt i)] [∀ i, Fintype (Salt i)]
    [∀ i, Nonempty (Salt i)] :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        let saltedPSpec := pSpec.addSalt Salt
        ∃ (saltedVerifier : Verifier oSpec StmtIn StmtOut saltedPSpec)
          (srInit : ProbComp (srChallengeOracle StmtIn saltedPSpec).FunctionType)
          (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn saltedPSpec).FunctionType ProbComp))
          (srSoundnessError : ENNReal),
        Verifier.StateRestoration.soundness srInit srImpl langIn langOut saltedVerifier srSoundnessError ∧
        srSoundnessError ≤ ∑ i, (rbrSoundnessError i : ENNReal) := by sorry

/-- Round-by-round knowledge soundness for a protocol implies state-restoration knowledge soundness
for the same protocol with arbitrary added non-empty salts. -/
theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Inhabited (Salt i)] [∀ i, Fintype (Salt i)]
    [∀ i, Nonempty (Salt i)] :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        let saltedPSpec := pSpec.addSalt Salt
        ∃ (saltedVerifier : Verifier oSpec StmtIn StmtOut saltedPSpec)
          (srInit : ProbComp (srChallengeOracle StmtIn saltedPSpec).FunctionType)
          (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn saltedPSpec).FunctionType ProbComp))
          (srKnowledgeError : ENNReal),
        Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut saltedVerifier srKnowledgeError ∧
        srKnowledgeError ≤ ∑ i, (rbrKnowledgeError i : ENNReal) := by sorry

/-- State-restoration soundness for a protocol with added salts implies state-restoration soundness
for the original protocol with improved parameters.

This shows that adding salts is a sound transformation - the security of the original protocol
is preserved (and potentially improved) when salts are removed. -/
theorem srSoundness_addSalt_implies_srSoundness_original
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Inhabited (Salt i)] [∀ i, Fintype (Salt i)]
    [∀ i, Nonempty (Salt i)]
    (saltedPSpec := pSpec.addSalt Salt)
    (saltedVerifier : Verifier oSpec StmtIn StmtOut saltedPSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn saltedPSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn saltedPSpec).FunctionType ProbComp))
    (srSoundnessError : ENNReal) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut saltedVerifier srSoundnessError →
        ∃ (originalVerifier : Verifier oSpec StmtIn StmtOut pSpec)
          (originalSrInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
          (originalSrImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
          (originalSrSoundnessError : ENNReal),
        Verifier.StateRestoration.soundness originalSrInit originalSrImpl langIn langOut originalVerifier originalSrSoundnessError ∧
        originalSrSoundnessError ≤ srSoundnessError / (∏ i, Fintype.card (Salt i) : ENNReal) := by sorry

/-- State-restoration knowledge soundness for a protocol with added salts implies state-restoration
knowledge soundness for the original protocol with improved parameters. -/
theorem srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (Salt : pSpec.MessageIdx → Type) [∀ i, Inhabited (Salt i)] [∀ i, Fintype (Salt i)]
    [∀ i, Nonempty (Salt i)]
    (saltedPSpec := pSpec.addSalt Salt)
    (saltedVerifier : Verifier oSpec StmtIn StmtOut saltedPSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn saltedPSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn saltedPSpec).FunctionType ProbComp))
    (srKnowledgeError : ENNReal) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut saltedVerifier srKnowledgeError →
        ∃ (originalVerifier : Verifier oSpec StmtIn StmtOut pSpec)
          (originalSrInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
          (originalSrImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
          (originalSrKnowledgeError : ENNReal),
        Verifier.StateRestoration.knowledgeSoundness originalSrInit originalSrImpl relIn relOut originalVerifier originalSrKnowledgeError ∧
        originalSrKnowledgeError ≤ srKnowledgeError / (∏ i, Fintype.card (Salt i) : ENNReal) := by sorry

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
    (srSoundnessError : ENNReal) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        ∃ (basicInit : ProbComp σ) (basicImpl : QueryImpl oSpec (StateT σ ProbComp)),
        soundness basicInit basicImpl langIn langOut verifier (srSoundnessError.toNNReal) := by sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (srChallengeOracle StmtIn pSpec).FunctionType)
    (srImpl : QueryImpl oSpec (StateT (srChallengeOracle StmtIn pSpec).FunctionType ProbComp))
    (srKnowledgeError : ENNReal) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut verifier srKnowledgeError →
        ∃ (basicInit : ProbComp σ) (basicImpl : QueryImpl oSpec (StateT σ ProbComp)),
        knowledgeSoundness basicInit basicImpl relIn relOut verifier (srKnowledgeError.toNNReal) := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier
