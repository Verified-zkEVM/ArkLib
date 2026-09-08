/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Packing.PackedCommitment
import ArkLib.OracleReduction.Composition.Sequential.Append.Knowledge
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness

/-!
# Downstream opening of the same packed commitment

An opening argument starts at the commitment's evaluation relation over C. Its output
types and relation are arbitrary. Assembly uses oracle-reduction append and its exact
extractor and guarded knowledge states. Worst-case security permits an effectful opening verifier;
the separate completeness theorem states the guarded-verifier and shared-state requirements of
the state-aware completeness composition interface.

The ambient oracle is explicit. Concrete packing prefixes use the empty ambient oracle;
the generic assembly also supports other ambient oracles when its supplied front does.
-/

noncomputable section

namespace RingSwitching.Packing

open OracleSpec OracleComp ProtocolSpec MvPolynomial
open scoped NNReal

/-- An opening reduction from a challenge-algebra evaluation on the same commitment. -/
structure PackedOpening {P : Type} [CommRing P] {m : ℕ} (pc : PackedCommitment P m)
    (C : Type) [CommRing C] [Algebra P C] {ι : Type} (oSpec : OracleSpec ι)
    {n : ℕ} (pSpec : ProtocolSpec n) [∀ i, OracleInterface (pSpec.Message i)] where
  /-- The opening's output statement type. -/
  StmtOut : Type
  /-- Indices of output oracle statements. -/
  ιOut : Type
  /-- Output oracle statement types. -/
  OStmtOut : ιOut → Type
  /-- Output oracle interfaces. -/
  Oᵢ : ∀ i, OracleInterface (OStmtOut i)
  /-- The opening's output witness type. -/
  WitOut : Type
  /-- The opening's claimed output relation. -/
  relOut : Set ((StmtOut × (∀ i, OStmtOut i)) × WitOut)
  /-- The opening reduction with a packed polynomial as its input witness. -/
  reduction : OracleReduction oSpec ((Fin m → C) × C) pc.OStmt P⦃≤ 1⦄[X Fin m]
    StmtOut OStmtOut WitOut pSpec

attribute [instance] PackedOpening.Oᵢ

namespace PackedOpening

variable {P C : Type} [CommRing P] [CommRing C] [Algebra P C] {m : ℕ}
  {pc : PackedCommitment P m} {ι : Type} {oSpec : OracleSpec ι}
  {n k : ℕ} {pSpec : ProtocolSpec n} {prefixSpec : ProtocolSpec k}
  [∀ i, OracleInterface (pSpec.Message i)]
  [∀ i, OracleInterface (prefixSpec.Message i)]
  (opening : PackedOpening pc C oSpec pSpec)
  {StmtIn WitIn : Type} {ιIn : Type} {OStmtIn : ιIn → Type}
  [∀ i, OracleInterface (OStmtIn i)]
  (front : OracleReduction oSpec StmtIn OStmtIn WitIn
    ((Fin m → C) × C) pc.OStmt P⦃≤ 1⦄[X Fin m] prefixSpec)

/-- Append the opening reduction at the packed-evaluation relation. -/
def assemble : OracleReduction oSpec StmtIn OStmtIn WitIn
    opening.StmtOut opening.OStmtOut opening.WitOut (prefixSpec ++ₚ pSpec) :=
  front.append opening.reduction

/-- Materializing the assembled oracle verifier gives ordinary verifier append. -/
theorem assemble_toVerifier : (opening.assemble front).verifier.toVerifier =
    front.verifier.toVerifier.append opening.reduction.verifier.toVerifier :=
  OracleVerifier.append_toVerifier _ _

/-- A passing front runs the opening verifier; rejection prevents the opening verifier's effects. -/
theorem verifier_run (G : front.verifier.toVerifier.GuardedForm)
    (stmt : StmtIn × (∀ i, OStmtIn i)) (tr : (prefixSpec ++ₚ pSpec).FullTranscript) :
    (opening.assemble front).verifier.toVerifier.run stmt tr =
      if G.check stmt tr.fst then
        opening.reduction.verifier.toVerifier.run (G.out stmt tr.fst) tr.snd else failure := by
  rw [assemble_toVerifier, Verifier.KnowledgeAppend.run_guarded G]

variable {W₁ : Fin (k + 1) → Type} {W₂ : Fin (n + 1) → Type}
  (G : front.verifier.toVerifier.GuardedForm)
  (E₁ : Extractor.RoundByRound oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
    P⦃≤ 1⦄[X Fin m] prefixSpec W₁)
  (E₂ : Extractor.RoundByRound oSpec (((Fin m → C) × C) × (∀ i, pc.OStmt i))
    P⦃≤ 1⦄[X Fin m] opening.WitOut pSpec W₂)

/-- The append extractor through the packed-polynomial witness at the evaluation boundary. -/
def extractor : Extractor.RoundByRound oSpec (StmtIn × (∀ i, OStmtIn i)) WitIn
    opening.WitOut (prefixSpec ++ₚ pSpec) (Verifier.KnowledgeAppend.Witness W₁ W₂) :=
  E₁.append E₂ G.out

variable [∀ i, SampleableType (prefixSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (source : Set ((StmtIn × (∀ i, OStmtIn i)) × WitIn))
  (K₁ : front.verifier.toVerifier.KnowledgeStateFunction init impl source pc.evalRel E₁)
  (K₂ : opening.reduction.verifier.toVerifier.KnowledgeStateFunction init impl
    pc.evalRel opening.relOut E₂)

/-- Guarded append's exact knowledge state, with the evaluation relation fixed at the seam. -/
def knowledgeStateFunction :
    (opening.assemble front).verifier.toVerifier.KnowledgeStateFunction init impl source
      opening.relOut (opening.extractor front G E₁ E₂) := by
  let K := Verifier.KnowledgeStateFunction.appendGuarded G K₁ K₂
  exact {
    toFun := K.toFun
    toFun_empty := K.toFun_empty
    toFun_next := K.toFun_next
    toFun_full := fun stmt tr w h => K.toFun_full stmt tr w (by
      simpa only [Verifier.run, assemble_toVerifier] using h) }

/-- Worst-case knowledge soundness from the front and opening contracts at `pc.evalRel`. -/
theorem rbrKnowledgeSoundnessWorstCaseWith
    {ε₁ : prefixSpec.ChallengeIdx → ℝ≥0} {ε₂ : pSpec.ChallengeIdx → ℝ≥0}
    (h₁ : front.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      source pc.evalRel W₁ E₁ K₁ ε₁)
    (h₂ : opening.reduction.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      pc.evalRel opening.relOut W₂ E₂ K₂ ε₂) :
    (opening.assemble front).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      source opening.relOut (Verifier.KnowledgeAppend.Witness W₁ W₂)
      (opening.extractor front G E₁ E₂)
      (opening.knowledgeStateFunction front G E₁ E₂ init impl source K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundnessWorstCaseWith_of_guarded_first G K₁ K₂ h₁ h₂

/-- The assembled extractor and knowledge state satisfy the prover-averaged contract. -/
theorem rbrKnowledgeSoundnessWith
    {ε₁ : prefixSpec.ChallengeIdx → ℝ≥0} {ε₂ : pSpec.ChallengeIdx → ℝ≥0}
    (h₁ : front.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      source pc.evalRel W₁ E₁ K₁ ε₁)
    (h₂ : opening.reduction.verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      pc.evalRel opening.relOut W₂ E₂ K₂ ε₂) :
    (opening.assemble front).verifier.toVerifier.rbrKnowledgeSoundnessWith init impl
      source opening.relOut (Verifier.KnowledgeAppend.Witness W₁ W₂)
      (opening.extractor front G E₁ E₂)
      (opening.knowledgeStateFunction front G E₁ E₂ init impl source K₁ K₂)
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith init impl
    (opening.rbrKnowledgeSoundnessWorstCaseWith front G E₁ E₂ init impl source K₁ K₂ h₁ h₂)

/--
Perfect completeness under guarded downstream verification, completeness from every seam
state, and compatible sampling at the seam.
-/
theorem perfectCompleteness (frontGuard : front.verifier.toVerifier.GuardedForm)
    (G₂ : opening.reduction.verifier.toVerifier.GuardedForm)
    (hSeam : ∀ hn : 0 < n,
      front.prover.OutputIsPure ∨ pSpec.dir ⟨0, hn⟩ = .P_to_V)
    (h₁ : front.perfectCompleteness init impl source pc.evalRel)
    (h₂ : ∀ s, opening.reduction.perfectCompleteness (pure s) impl pc.evalRel opening.relOut) :
    (opening.assemble front).perfectCompleteness init impl source opening.relOut :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    front opening.reduction frontGuard G₂ hSeam h₁ h₂

end PackedOpening

end RingSwitching.Packing

end
