/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Opening
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.FullFamilyOpening
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.ScalarOpening
import ArkLibTest.ProofSystem.RingSwitching.Packing.ScalarFamily

/-!
# Same-commitment downstream opening assembly

The concrete polynomial-oracle fixture actually queries its input oracle and checks the claimed
evaluation. It closes to the always-true decision relation, with no remaining polynomial witness.
The production scalar and full-family prefixes are instantiated at this opening boundary.
This fixture is not a FRI opening proof.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Opening

open MvPolynomial OracleSpec OracleComp ProtocolSpec ProbabilityTheory
open scoped NNReal

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩


abbrev F := ZMod 5
abbrev pc := ScalarFamily.pc
abbrev Stmt := (Fin 1 → F) × F
abbrev Poly := F⦃≤ 1⦄[X Fin 1]
local instance : ∀ i, OracleInterface (pc.OStmt i) := pc.Oᵢ

abbrev relOut : Set ((Unit × (∀ i, pc.OStmt i)) × Unit) := Set.univ

def prover : OracleProver []ₒ Stmt pc.OStmt Poly Unit pc.OStmt Unit !p[] where
  PrvState _ := (Stmt × (∀ i, pc.OStmt i)) × Poly
  input := id
  sendMessage i := nomatch i
  receiveChallenge i := nomatch i
  output st := pure (((), st.1.2), ())

open scoped Classical in
def verifier : OracleVerifier []ₒ Stmt pc.OStmt Unit pc.OStmt !p[] where
  verify stmt _ := do
    let p : Poly ← query (spec := [pc.OStmt]ₒ) ⟨(), ()⟩
    if stmt.2 = aeval stmt.1 p.val then return () else failure
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun _ _ h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro i; rfl }

def opening : PackedOpening pc.toPackedCommitment F []ₒ !p[] where
  StmtOut := Unit
  ιOut := pc.ιC
  OStmtOut := pc.OStmt
  Oᵢ := pc.Oᵢ
  WitOut := Unit
  relOut := relOut
  reduction := by
    letI : ∀ i, OracleInterface (pc.OStmt i) := pc.Oᵢ
    exact ⟨prover, verifier⟩

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The checked opening reads the actual packed polynomial from this same input oracle. -/
theorem verifier_verify (stmt : Stmt) (ost : ∀ i, pc.OStmt i) (tr : FullTranscript !p[]) :
    verifier.toVerifier.verify (stmt, ost) tr =
      if stmt.2 = aeval stmt.1 (ost ()).val then pure ((), ost) else failure := by
  apply OptionT.ext
  have hout : verifier.materializeOutput tr.challenges ost tr.messages = ost := by
    funext i
    rfl
  simp only [OracleVerifier.toVerifier, OptionT.run_mk]
  rw [hout]
  change (Option.map fun out => (out, ost)) <$>
    simulateQ (OracleInterface.simOracle2 []ₒ ost tr.messages)
      ((liftM (([pc.OStmt]ₒ).query ⟨(), ()⟩) :
        OracleComp ([]ₒ + ([pc.OStmt]ₒ + [(!p[]).Message]ₒ)) Poly) >>= fun p =>
        (if stmt.2 = aeval stmt.1 p.val then pure () else failure :
          OptionT (OracleComp ([]ₒ + ([pc.OStmt]ₒ + [(!p[]).Message]ₒ))) Unit).run) = _
  have hquery : simulateQ (OracleInterface.simOracle2 []ₒ ost tr.messages)
      (liftM (([pc.OStmt]ₒ).query ⟨(), ()⟩) :
        OracleComp ([]ₒ + ([pc.OStmt]ₒ + [(!p[]).Message]ₒ)) Poly) = pure (ost ()) := by
    exact QueryImpl.simulateQ_addLift_add_liftM_left (target := OracleComp []ₒ)
      (QueryImpl.id []ₒ) (OracleInterface.simOracle0 pc.OStmt ost)
      (OracleInterface.simOracle0 (!p[]).Message tr.messages) (([pc.OStmt]ₒ).query ⟨(), ()⟩)
  rw [simulateQ_bind, hquery, pure_bind]
  split <;> simp_all [OptionT.run_pure, OptionT.run_failure]

open scoped Classical in
def guardedForm : verifier.toVerifier.GuardedForm where
  check stmt _ := decide (stmt.1.2 = aeval stmt.1.1 (stmt.2 ()).val)
  out stmt _ := ((), stmt.2)
  verify_eq stmt tr := by rw [verifier_verify]; simp only [decide_eq_true_eq]

/-- The zero-round prover sends no messages and retains the actual input oracle. -/
theorem prover_run (stmt : Stmt) (ost : ∀ i, pc.OStmt i) (p : Poly) :
    prover.run (stmt, ost) p = pure (default, ((), ost), ()) := by
  rfl

/-- The output unit witness is extracted back to the polynomial really held in the oracle. -/
def extractor : Extractor.RoundByRound []ₒ (Stmt × (∀ i, pc.OStmt i)) Poly Unit !p[]
    (fun _ => Poly) where
  eqIn := rfl
  extractMid i := nomatch i
  extractOut stmt _ _ := stmt.2 ()

/-- Positive probability of actual acceptance supplies the exact input evaluation equation. -/
theorem positive_check {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (stmt : Stmt) (ost : ∀ i, pc.OStmt i)
    (tr : FullTranscript !p[])
    (h : Pr[ fun out => (out, ()) ∈ relOut |
      OptionT.mk do (simulateQ impl (verifier.toVerifier.run (stmt, ost) tr)).run' (← init)] > 0) :
    stmt.2 = aeval stmt.1 (ost ()).val := by
  classical
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨out, hout, _⟩ := h
  rw [OptionT.mem_support_iff] at hout
  simp only [Verifier.run, verifier_verify] at hout
  by_contra hc
  rw [if_neg hc] at hout
  change some out ∈ support (init >>= fun _ => pure none) at hout
  simp at hout

def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    verifier.toVerifier.KnowledgeStateFunction init impl pc.evalRel relOut extractor where
  toFun _ stmt _ p := (stmt, p) ∈ pc.evalRel
  toFun_empty _ _ := Iff.rfl
  toFun_next i := nomatch i
  toFun_full stmt tr _ h := ⟨positive_check init impl stmt.1 stmt.2 tr h, rfl⟩

/-- The exact downstream WC premise closes this nontrivial evaluation relation without error. -/
theorem worstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl pc.evalRel relOut
      (fun _ => Poly) extractor (knowledgeStateFunction init impl) (fun _ => 0) := by
  intro _ i
  nomatch i

/-- Completeness is valid from every initial distribution of the shared oracle state. -/
theorem complete {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    opening.reduction.perfectCompleteness init impl pc.evalRel relOut := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt p hIn x hx
  rw [Reduction.run_eq_of_guarded_verifier _ guardedForm] at hx
  change x ∈ support (prover.run stmt p >>= _) at hx
  rw [prover_run, pure_bind] at hx
  have hc : stmt.1.2 = aeval stmt.1.1 (stmt.2 ()).val := hIn.2 ▸ hIn.1
  simp only [guardedForm, hc, decide_true, ↓reduceIte] at hx
  have hx := OracleComp.eq_of_mem_support_pure _ hx
  subst x
  exact ⟨_, rfl, Set.mem_univ _, rfl⟩

/-- The checked opening accepts X at two and preserves this actual oracle. -/
theorem checked_accept : verifier.toVerifier.run
    ((fun _ => 2, 2), pc.commit ScalarFamily.source) default =
      pure ((), pc.commit ScalarFamily.source) := by
  rw [Verifier.run, verifier_verify]
  apply if_pos
  simp [pc, ScalarFamily.pc, ExactPackedCommitment.polynomialOracle, ScalarFamily.source]

/-- A false evaluation of the very same polynomial is rejected by the actual opening. -/
theorem checked_reject : verifier.toVerifier.run
    ((fun _ => 2, 3), pc.commit ScalarFamily.source) default = failure := by
  rw [Verifier.run, verifier_verify]
  apply if_neg
  change (3 : F) ≠ aeval (fun _ : Fin 1 => (2 : F)) (X 0)
  simpa only [aeval_X] using (by decide : (3 : F) ≠ 2)

abbrev scalarFront := ScalarOpening.reduction ScalarFamily.data 1 ScalarFamily.layout
  ScalarFamily.bat pc
abbrev scalarGuard := ScalarOpening.guardedForm ScalarFamily.data 1 ScalarFamily.layout
  ScalarFamily.bat pc
abbrev scalarSource := Packing.ScalarFamily.relIn ScalarFamily.data 1 ScalarFamily.layout pc
abbrev scalarExtractor := opening.extractor scalarFront scalarGuard
  (ScalarOpening.extractor ScalarFamily.data 1 ScalarFamily.layout ScalarFamily.bat pc) extractor

abbrev familyFront := FullFamilyOpening.reduction ScalarFamily.data 1 ScalarFamily.bat pc
abbrev familyGuard := FullFamilyOpening.guardedForm ScalarFamily.data 1 ScalarFamily.bat pc
abbrev familySource := FullFamily.relIn ScalarFamily.data 1 pc
abbrev familyExtractor := opening.extractor familyFront familyGuard
  (FullFamilyOpening.extractor ScalarFamily.data 1 ScalarFamily.bat pc) extractor

local instance : ∀ i, OracleInterface
    ((ScalarOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat ++ₚ !p[]).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := ScalarOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat) (pSpec₂ := !p[])
local instance : ∀ i, SampleableType
    ((ScalarOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := ScalarOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat) (pSpec₂ := !p[])
local instance : ∀ i, OracleInterface
    ((FullFamilyOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat ++ₚ !p[]).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := FullFamilyOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat) (pSpec₂ := !p[])
local instance : ∀ i, SampleableType
    ((FullFamilyOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat ++ₚ !p[]).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := FullFamilyOpening.pSpec ScalarFamily.data 1 ScalarFamily.bat) (pSpec₂ := !p[])

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

def scalarState := opening.knowledgeStateFunction scalarFront scalarGuard
  (ScalarOpening.extractor ScalarFamily.data 1 ScalarFamily.layout ScalarFamily.bat pc)
  extractor init impl scalarSource
  (ScalarOpening.knowledgeStateFunction ScalarFamily.data 1 ScalarFamily.layout
    ScalarFamily.bat pc init impl) (knowledgeStateFunction init impl)

/-- Actual original-scalar pipeline followed by the checked opening, with exact E and K. -/
theorem scalar_worstCase :
    (opening.assemble scalarFront).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl scalarSource relOut
      (Verifier.KnowledgeAppend.Witness (m := 6) (n := 0)
        (ScalarOpening.Witness ScalarFamily.data 1 ScalarFamily.layout) (fun _ => Poly))
      scalarExtractor (scalarState init impl)
      (Sum.elim (ScalarOpening.rbrError ScalarFamily.data 1 ScalarFamily.bat) (fun _ => 0) ∘
        ChallengeIdx.sumEquiv.symm) :=
  opening.rbrKnowledgeSoundnessWorstCaseWith scalarFront scalarGuard _ extractor
    init impl scalarSource _ (knowledgeStateFunction init impl)
    (ScalarOpening.rbrKnowledgeSoundnessWorstCaseWith ScalarFamily.data 1 ScalarFamily.layout
      ScalarFamily.bat pc pc.commitsTo_functional Function.injective_id init impl)
    (worstCase init impl)

def familyState := opening.knowledgeStateFunction familyFront familyGuard
  (FullFamilyOpening.extractor ScalarFamily.data 1 ScalarFamily.bat pc)
  extractor init impl familySource
  (FullFamilyOpening.knowledgeStateFunction ScalarFamily.data 1 ScalarFamily.bat pc init impl)
  (knowledgeStateFunction init impl)

/-- The public full-family pipeline uses the same actual closing oracle and WC premise. -/
theorem family_worstCase :
    (opening.assemble familyFront).verifier.toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl familySource relOut
      (Verifier.KnowledgeAppend.Witness (m := 5) (n := 0)
        (FullFamilyOpening.Witness ScalarFamily.data 1)
        (fun _ => Poly)) familyExtractor (familyState init impl)
      (Sum.elim (FullFamilyOpening.rbrError ScalarFamily.data 1 ScalarFamily.bat) (fun _ => 0) ∘
        ChallengeIdx.sumEquiv.symm) :=
  opening.rbrKnowledgeSoundnessWorstCaseWith familyFront familyGuard _ extractor
    init impl familySource _ (knowledgeStateFunction init impl)
    (FullFamilyOpening.rbrKnowledgeSoundnessWorstCaseWith ScalarFamily.data 1
      ScalarFamily.bat pc pc.commitsTo_functional Function.injective_id init impl)
    (worstCase init impl)

/-- The actual original-scalar assembly is complete from every shared initial state. -/
theorem scalar_complete : (opening.assemble scalarFront).perfectCompleteness init impl
    scalarSource relOut :=
  opening.perfectCompleteness scalarFront init impl scalarSource scalarGuard guardedForm
    (fun hn => by omega)
    (ScalarOpening.perfectCompleteness ScalarFamily.data 1 ScalarFamily.layout ScalarFamily.bat
      pc init impl) (fun s => complete (pure s) impl)

/-- The actual full-family assembly is complete at the very same evaluation boundary. -/
theorem family_complete : (opening.assemble familyFront).perfectCompleteness init impl
    familySource relOut :=
  opening.perfectCompleteness familyFront init impl familySource familyGuard guardedForm
    (fun hn => by omega)
    (FullFamilyOpening.perfectCompleteness ScalarFamily.data 1 ScalarFamily.bat pc init impl)
    (fun s => complete (pure s) impl)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete nonconstant source and its honest oracle are accepted by the whole reduction. -/
theorem scalar_acceptance :
    Pr[fun ⟨⟨_, (prvOut, witOut)⟩, out⟩ =>
      (out, witOut) ∈ relOut ∧ prvOut = out | OptionT.mk do
        (simulateQ (QueryImpl.addLift (r := StateT σ ProbComp) impl
          (challengeQueryImpl (pSpec := ScalarOpening.pSpec ScalarFamily.data 1
            ScalarFamily.bat ++ₚ !p[])))
          ((opening.assemble scalarFront).toReduction.run
            (ScalarFamily.stmt, ScalarFamily.ost) ScalarFamily.source).run).run' (← init)] = 1 := by
  apply le_antisymm probEvent_le_one
  have h := scalar_complete init impl (ScalarFamily.stmt, ScalarFamily.ost)
    ScalarFamily.source ScalarFamily.source_related
  simp only [ENNReal.coe_zero, tsub_zero] at h
  convert h using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The partial-evaluation family of that source is also accepted by the whole reduction. -/
theorem family_acceptance :
    Pr[fun ⟨⟨_, (prvOut, witOut)⟩, out⟩ =>
      (out, witOut) ∈ relOut ∧ prvOut = out | OptionT.mk do
        (simulateQ (QueryImpl.addLift (r := StateT σ ProbComp) impl
          (challengeQueryImpl (pSpec := FullFamilyOpening.pSpec ScalarFamily.data 1
            ScalarFamily.bat ++ₚ !p[])))
          ((opening.assemble familyFront).toReduction.run
            (ScalarHead.nextStatement ScalarFamily.data 1 ScalarFamily.layout ScalarFamily.stmt
              ScalarFamily.α, ScalarFamily.ost)
            (ScalarFamily.layout.components ScalarFamily.source)).run).run' (← init)] = 1 := by
  apply le_antisymm probEvent_le_one
  have h := family_complete init impl _ _ ScalarFamily.seam_related
  simp only [ENNReal.coe_zero, tsub_zero] at h
  convert h using 1 <;> rfl

end RingSwitching.Packing.Tests.Opening

end
