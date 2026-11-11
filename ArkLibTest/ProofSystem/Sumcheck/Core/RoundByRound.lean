/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.LegacySoundness
import ArkLibTest.ProofSystem.Sumcheck.Core.Soundness
import ArkLib.ProofSystem.Sumcheck.Core.RoundByRound
import ArkLib.ProofSystem.Sumcheck.Core.Knowledge
import ArkLib.ProofSystem.Sumcheck.Core.LegacyCompleteness

/-!
# Round-by-round and knowledge soundness of Sumcheck in the interaction layer

Consumers of the transferred security theorems: the round-by-round soundness of the verifier
bounds every prover's success on a false claim by `n * deg / |F|`; the knowledge soundness and the
completeness of the embedded legacy prover hold at concrete parameters.
-/

namespace Sumcheck.Core.RoundByRoundTest

open Polynomial PFunctor Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec ProtocolSpec MeasureTheory Interaction.Core.Legacy
  Sumcheck.Core.SoundnessTest
open scoped ENNReal NNReal

noncomputable section

section Universal

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n deg : ℕ)
  {d : ℕ} (D : Fin d ↪ F) {ι : Type} (amb : OracleSpec ι)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl amb (StateT σ ProbComp))

-- Migration row: Sumcheck Interaction/RoundByRound #1.

/-- The verifier is round-by-round sound with error `deg / |F|` at every challenge. -/
example : (verifier F deg n D amb).rbrSoundness impl
    (langProblem (Spec.relationRound F n deg D 0).language)
    (langProblem (Spec.relationRound F n deg D (Fin.last n)).language)
    (@challengeQueryImpl _ oracleSig (protocol F deg n) (challengeSampleable F deg n))
    (fun _ => (((deg : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞)) :=
  verifier_rbrSoundness F deg n D amb init impl

/-- Every prover, with any output, makes a false claim reach the final language with probability
at most `n * deg / |F|`. -/
theorem false_claim_bound {Out : FreeM.PathAlong oracleSig (protocol F deg n) → Type}
    (P : Prover oracleSig amb (protocol F deg n) Out)
    (stmt : Spec.StatementRound F n 0) (oStmt : ∀ i, Spec.OracleStatement F n deg i)
    (hfalse : (stmt, oStmt) ∉ (Spec.relationRound F n deg D 0).language) :
    letI : MeasurableSpace (Observation oracleSig (protocol F deg n) Out
      (fun _ => Spec.StatementRound F n (Fin.last n) × (∀ i, Spec.OracleStatement F n deg i))) := ⊤
    𝒟[experiment init impl (@challengeQueryImpl _ oracleSig (protocol F deg n)
      (challengeSampleable F deg n))
        ((verifier F deg n D amb).run stmt oStmt P)] (accepted D) ≤
      (n : ℝ≥0∞) * deg / Fintype.card F := by
  let : MeasurableSpace (Observation oracleSig (protocol F deg n) Out
      (fun _ => Spec.StatementRound F n (Fin.last n) × (∀ i, Spec.OracleStatement F n deg i))) := ⊤
  have h := legacyVerifier_soundness_rounds F deg n D amb init impl Out (stmt, oStmt) trivial
    (by simpa only [langProblem_language] using hfalse) P
  rw [soundnessEvent_eq] at h
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.coe_div (by simp), mul_div_assoc]
  simp

end Universal

/-! ## Knowledge soundness and legacy completeness at concrete parameters -/

section Concrete

open Sumcheck.Core.CompletenessTest Sumcheck.Core.SingleRoundTest

/-- Five is prime. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))

/-- Two rounds of degree one over `ZMod 5` are knowledge sound with error `2/5`. -/
example :
    letI : MeasurableSpace (Observation oracleSig (protocol F 1 2)
      (fun _ => (Spec.StatementRound F 2 (Fin.last 2) × (∀ i, Spec.OracleStatement F 2 1 i)) ×
        Unit) (fun _ => Spec.StatementRound F 2 (Fin.last 2) × (∀ i, Spec.OracleStatement F 2 1
          i))) := ⊤
    letI : MeasurableSpace Unit := ⊤
    knowledgeSoundness ((verifier F 1 2 D₂ ambient).classicalModel init impl
        (@challengeQueryImpl _ oracleSig (protocol F 1 2) (challengeSampleable F 1 2)))
      (relProblem (Spec.relationRound F 2 1 D₂ 0))
      (relProblem (Spec.relationRound F 2 1 D₂ (Fin.last 2)))
      (knowledgeJudgementOn (protocol F 1 2) (Spec.relationRound F 2 1 D₂ (Fin.last 2)))
      ((verifier F 1 2 D₂ ambient).classicalStraightline (fun _ => Unit) init impl
        (@challengeQueryImpl _ oracleSig (protocol F 1 2) (challengeSampleable F 1 2))
        (fun _ (o : (Spec.StatementRound F 2 (Fin.last 2) ×
          (∀ i, Spec.OracleStatement F 2 1 i)) × Unit) => o.2))
      (2 / 5) := by
  have h := verifier_knowledgeSoundness F 1 2 D₂ ambient init impl
  rw [Finset.sum_const, Finset.card_univ, card_challengeIdx, ZMod.card] at h
  convert h using 1
  norm_num [ENNReal.coe_div]

/-- The embedded legacy prover is perfectly complete for three rounds of degree two. -/
example :
    letI : MeasurableSpace (Observation oracleSig (protocol F 2 3)
      (fun _ => (Spec.StatementRound F 3 (Fin.last 3) × (∀ i, Spec.OracleStatement F 3 2 i)) ×
        Unit) (fun _ => Spec.StatementRound F 3 (Fin.last 3) × (∀ i, Spec.OracleStatement F 3 2
          i))) := ⊤
    completeness ((verifier F 2 3 D₂ ambient).classicalModel init impl
        (@challengeQueryImpl _ oracleSig (protocol F 2 3) (challengeSampleable F 2 3)))
      (relProblem (Spec.relationRound F 3 2 D₂ 0))
      (relProblem (Spec.relationRound F 3 2 D₂ (Fin.last 3)))
      (knowledgeJudgementOn (protocol F 2 3) (Spec.relationRound F 3 2 D₂ (Fin.last 3)))
      (legacyProver F 2 3 D₂ ambient) 0 :=
  legacyProver_perfectCompleteness F 2 3 D₂ ambient init impl

end Concrete

end

end Sumcheck.Core.RoundByRoundTest

-- Migration row: Sumcheck Interaction/RoundByRound #1 (audit).
run_cmd do
  for decl in [``Sumcheck.Core.RoundByRoundTest.false_claim_bound,
      ``Sumcheck.Core.verifier_rbrSoundness, ``Sumcheck.Core.verifier_rbrKnowledgeSoundness,
      ``Sumcheck.Core.verifier_knowledgeSoundness,
      ``Sumcheck.Core.legacyProver_perfectCompleteness] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
