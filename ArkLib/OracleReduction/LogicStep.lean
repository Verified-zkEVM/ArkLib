/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# Oracle-aware reduction logic

A reduction step may query its input and message oracles while checking an honest transcript.
`OracleAwareLogicStep` records that check, its accepted output and the honest prover data.
The common `LogicStep` structure permits either a proposition-valued deterministic check or an
oracle computation, and uses the verifier's output-oracle representation and materialization.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

/-- A reduction step's check, output-oracle representation and honest execution data.
The parameter `Check` determines whether checks are propositions or oracle computations. -/
structure LogicStep
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn : Type)
    {ιᵢ ιₒ : Type} (OracleIn : ιᵢ → Type) (OracleOut : ιₒ → Type)
    (StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) (Check : Type)
    [inputInterfaces : ∀ i, OracleInterface (OracleIn i)]
    [messageInterfaces : ∀ i, OracleInterface (pSpec.Message i)] where
  /-- The completeness input relation. -/
  completeness_relIn : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  /-- The completeness output relation. -/
  completeness_relOut : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop
  /-- The check on the input statement and complete transcript. -/
  verifierCheck : StmtIn → FullTranscript pSpec → Check
  /-- The accepted output statement. -/
  verifierOut : StmtIn → FullTranscript pSpec → StmtOut
  /-- The public interfaces of the accepted output oracles. -/
  outputInterfaces : ∀ i, OracleInterface (OracleOut i)
  /-- Output oracle selection with its representation and interface coherence. -/
  outputOracle :
    OracleOutputEmbedding OracleIn pSpec.Message OracleOut (Oₛₒ := outputInterfaces) ⊕
      OracleOutputSimulation oSpec OracleIn OracleOut pSpec (Oₛₒ := outputInterfaces)
  /-- The honest transcript at each fixed challenge family. -/
  honestProverTranscript : StmtIn → WitIn → (∀ i, OracleIn i) →
    pSpec.Challenges → FullTranscript pSpec
  /-- The honest prover output at the supplied transcript. -/
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- A reduction logic step whose check is an oracle computation. -/
abbrev OracleAwareLogicStep
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn : Type)
    {ιᵢ ιₒ : Type} (OracleIn : ιᵢ → Type) (OracleOut : ιₒ → Type)
    (StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (OracleIn i)] [∀ i, OracleInterface (pSpec.Message i)] :=
  LogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec
    (OptionT (OracleComp (oSpec + ([OracleIn]ₒ + [pSpec.Message]ₒ))) StmtOut)

/-- A reduction logic step whose check is a deterministic proposition. -/
abbrev DeterministicLogicStep
    {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn : Type)
    {ιᵢ ιₒ : Type} (OracleIn : ιᵢ → Type) (OracleOut : ιₒ → Type)
    (StmtOut WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface (OracleIn i)] [∀ i, OracleInterface (pSpec.Message i)] :=
  LogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec Prop

namespace LogicStep

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut Check : Type}
  {ιᵢ ιₒ : Type} {OracleIn : ιᵢ → Type} {OracleOut : ιₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OracleIn i)] [∀ i, OracleInterface (pSpec.Message i)]

/-- Materialize the output oracles from their embedded or simulated representation. -/
def materializeOutput
    (step : LogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec Check)
    (oracles : ∀ i, OracleIn i) (tr : FullTranscript pSpec) : ∀ i, OracleOut i :=
  OracleVerifier.materializeOutputOracle (Oₛₒ := step.outputInterfaces)
    step.outputOracle tr.challenges oracles tr.messages

/-- At every fixed challenge family, the honest transcript passes the deterministic check;
its output satisfies the relation and agrees with the verifier's statement and oracles. -/
def IsStronglyComplete
    (step : DeterministicLogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) :
    Prop :=
  ∀ stmt wit oracles chals, step.completeness_relIn ((stmt, oracles), wit) →
    let tr := step.honestProverTranscript stmt wit oracles chals
    step.verifierCheck stmt tr ∧
    let out := step.verifierOut stmt tr
    let outOracles := step.materializeOutput oracles tr
    let ((prvOut, prvOracles), prvWit) := step.proverOut stmt wit oracles tr
    step.completeness_relOut ((out, outOracles), prvWit) ∧
      prvOut = out ∧ prvOracles = outOracles

end LogicStep

/-- Every supported honest check avoids rejection; the honest prover agrees with the
accepted output and the resulting relation holds. This support-level predicate alone does not
assert total probability mass. A probability-one transfer must additionally establish
losslessness, or prove that the simulated check equals a pure accepted value. -/
def OracleAwareLogicStep.IsStronglyCompleteUnderSimulation
    {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {ιᵢ ιₒ : Type} {OracleIn : ιᵢ → Type} {OracleOut : ιₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, OracleInterface (OracleIn i)] [∀ i, OracleInterface (pSpec.Message i)]
    (step : OracleAwareLogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) :
    Prop :=
  ∀ (stmt : StmtIn) (wit : WitIn) (oracles : ∀ i, OracleIn i) (chals : pSpec.Challenges),
    step.completeness_relIn ((stmt, oracles), wit) →
    let tr := step.honestProverTranscript stmt wit oracles chals
    let sim := OracleInterface.simOracle2 oSpec oracles tr.messages
    none ∉ support (simulateQ sim (step.verifierCheck stmt tr)) ∧
    let out := step.verifierOut stmt tr
    let outOracles := OracleVerifier.materializeOutputOracle (oSpec := oSpec)
      (Oₛₒ := step.outputInterfaces)
      step.outputOracle tr.challenges oracles tr.messages
    let ((prvOut, prvOracles), prvWit) := step.proverOut stmt wit oracles tr
    step.completeness_relOut ((out, outOracles), prvWit) ∧
      prvOut = out ∧ prvOracles = outOracles

end OracleReduction

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- A guarded reduction is perfectly complete when every supported honest prover execution
passes its check, satisfies the output relation and agrees with the verifier's verdict. -/
theorem perfectCompleteness_of_guarded_prover_support
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (G : R.verifier.GuardedForm)
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (h : ∀ stmt wit, (stmt, wit) ∈ relIn →
      ∀ q ∈ support (R.prover.run stmt wit),
        G.check stmt q.1 = true ∧ (G.out stmt q.1, q.2.2) ∈ relOut ∧
          q.2.1 = G.out stmt q.1) :
    R.perfectCompleteness init impl relIn relOut := by
  apply perfectCompleteness_of_run_support
  intro stmt wit hIn x hx
  rw [run_eq_of_guarded_verifier R G] at hx
  obtain ⟨q, hq, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  obtain ⟨hcheck, hrel, hout⟩ := h stmt wit hIn q hq
  simp only [hcheck, ↓reduceIte, mem_support_pure_iff] at hx
  exact ⟨_, hx, hrel, hout⟩

end Reduction

namespace OracleReduction.LogicStep

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {ιᵢ ιₒ : Type} {OracleIn : ιᵢ → Type} {OracleOut : ιₒ → Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (OracleIn i)] [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, OracleInterface (OracleOut i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Strong deterministic logic implies perfect completeness when supported prover runs are
honest transcripts and the guarded verifier implements the logic's check and output. -/
theorem perfectCompleteness_of_isStronglyComplete
    (step : DeterministicLogicStep oSpec StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec)
    [∀ s tr, Decidable (step.verifierCheck s tr)]
    (R : OracleReduction oSpec StmtIn OracleIn WitIn StmtOut OracleOut WitOut pSpec)
    (G : R.verifier.toVerifier.GuardedForm)
    (hcomplete : step.IsStronglyComplete)
    (hprover : ∀ stmt wit oracles q,
      q ∈ support (R.prover.run (stmt, oracles) wit) → ∃ chals,
        q = (step.honestProverTranscript stmt wit oracles chals,
          step.proverOut stmt wit oracles (step.honestProverTranscript stmt wit oracles chals)))
    (hcheck : ∀ stmt oracles tr,
      G.check (stmt, oracles) tr = decide (step.verifierCheck stmt tr))
    (hout : ∀ stmt oracles tr,
      G.out (stmt, oracles) tr = (step.verifierOut stmt tr, step.materializeOutput oracles tr)) :
    R.perfectCompleteness init impl {x | step.completeness_relIn x}
      {x | step.completeness_relOut x} := by
  apply Reduction.perfectCompleteness_of_guarded_prover_support R.toReduction G
  intro ⟨stmt, oracles⟩ wit hIn q hq
  obtain ⟨chals, rfl⟩ := hprover stmt wit oracles q hq
  obtain ⟨hc, hr, hs, ho⟩ := hcomplete stmt wit oracles chals hIn
  rw [hcheck, decide_eq_true hc, hout]
  exact ⟨rfl, hr, Prod.ext hs ho⟩

end OracleReduction.LogicStep
