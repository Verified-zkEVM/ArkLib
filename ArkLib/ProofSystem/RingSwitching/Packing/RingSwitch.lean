/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Knowledge
public import ArkLib.ProofSystem.RingSwitching.Packing.Head
public import ArkLib.OracleReduction.Security.GuardedBridges

/-!
# Scalar ring switching on the same commitment

The head checks a scalar claim about the unpacked source and derives `∑ A_c(y) p(y)` on the
Boolean cube. Product sumcheck reduces that sum to `A_c(r) v`; the terminal check executes the
multiplier's matrix evaluator and leaves `v = p(r)` for the original commitment to prove.
The original query and batching challenge remain beside that final evaluation claim.

The program sends one encoded component family, one degree-two polynomial per retained variable,
and the final value. It samples one batching challenge and one scalar per retained variable.
Completeness holds over commutative rings using an operational batching rule. Round-by-round
knowledge soundness uses a certified strategy, functional commitment semantics,
injective packed-coefficient transport and a finite challenge ring with no zero divisors.
The challenge-index error sum is exactly `bat.error + m * (2 / card C)`, including `m = 0`.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.RingSwitch
open OracleSpec OracleComp ProtocolSpec MvPolynomial CoordinateWise.ScalarRound
open scoped NNReal
private theorem card_head {B C : Type} [CommRing B] (data : PackingData B)
    {M : Type} (rule : BatchingRule C data.ιE) : Fintype.card (Head.pSpec (M := M) data
      rule).ChallengeIdx = 1 := by
  change Fintype.card (pSpecScalar Unit Unit).ChallengeIdx = 1
  decide

private theorem card_round (C : Type) [CommRing C] :
    Fintype.card (ProductSumcheck.Round.pSpec C).ChallengeIdx = 1 := by
  change Fintype.card (pSpecScalar Unit Unit).ChallengeIdx = 1
  decide

private theorem card_loop (C : Type) [CommRing C] (m : ℕ) :
    Fintype.card (ProductSumcheck.loopSpec C m).ChallengeIdx = m := by
  change Fintype.card (seqCompose (fun _ : Fin m => ProductSumcheck.Round.pSpec C)).ChallengeIdx = m
  rw [← Fintype.card_congr (seqComposeChallengeEquiv (fun _ : Fin m => ProductSumcheck.Round.pSpec
    C))]
  simp only [Fintype.card_sigma, card_round, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

private theorem card_tail (C : Type) [CommRing C] (m : ℕ) :
    Fintype.card (ProductSumcheck.pSpec C m).ChallengeIdx = m := by
  change Fintype.card (ProductSumcheck.loopSpec C m ++ₚ ProductSumcheck.Terminal.pSpec
    C).ChallengeIdx = m
  rw [← Fintype.card_congr (ChallengeIdx.sumEquiv
    (pSpec₁ := ProductSumcheck.loopSpec C m) (pSpec₂ := ProductSumcheck.Terminal.pSpec C)),
      Fintype.card_sum,
    card_loop]
  have hterm : Fintype.card (ProductSumcheck.Terminal.pSpec C).ChallengeIdx = 0 := by
    change Fintype.card (RingSwitching.pSpecMessage Unit).ChallengeIdx = 0
    decide
  rw [hterm, add_zero]

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  (layout : ClaimLayout data m)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  {M : Type} (messageEquiv : M ≃ (data.ιP → data.E))

section Program
variable (rule : BatchingRule C data.ιE) (pc : PackedCommitment data.P m)

/-- The generic head followed by the scalar-round sequence and terminal opening message. -/
def pSpec : ProtocolSpec (2 + (Fin.vsum (fun _ : Fin m => 2) + 1)) :=
  Head.pSpec (M := M) data rule ++ₚ ProductSumcheck.pSpec C m

instance : ∀ j, OracleInterface ((pSpec (M := M) data m rule).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend
    (pSpec₁ := Head.pSpec (M := M) data rule) (pSpec₂ := ProductSumcheck.pSpec C m)

instance [SampleableType C] : ∀ j, SampleableType ((pSpec (M := M) data m rule).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (pSpec₁ := Head.pSpec (M := M) data rule) (pSpec₂ := ProductSumcheck.pSpec C m)

/-- The oracle verifier preserving the commitment through the final evaluation claim. -/
def verifier : OracleVerifier []ₒ (Head.Input data m layout) pc.OStmt
    ((layout.Query × rule.Challenge) × ((Fin m → C) × C)) pc.OStmt (pSpec (M := M) data m rule) :=
  (Head.verifier data m layout messageEquiv rule pc).append (ProductSumcheck.verifier
    (Head.multiplier data m layout rule) pc)

/-- The prover packs the source and preserves the packed polynomial through the tail. -/
def reduction : OracleReduction []ₒ (Head.Input data m layout) pc.OStmt
    (layout.Source) ((layout.Query × rule.Challenge) × ((Fin m → C) × C)) pc.OStmt data.P⦃≤ 1⦄[X Fin
      m] (pSpec (M := M) data m rule) :=
  (Head.reduction data m layout messageEquiv rule pc).append (ProductSumcheck.reduction
    (Head.multiplier data m layout rule) pc)

omit [IsScalarTower B data.P C] in
/-- Materialization commutes with oracle-verifier append. -/
theorem verifier_toVerifier : (verifier data m layout messageEquiv rule pc).toVerifier =
    (Head.verifier data m layout messageEquiv rule pc).toVerifier.append
      (ProductSumcheck.verifier (Head.multiplier data m layout rule) pc).toVerifier :=
  OracleVerifier.append_toVerifier _ _

/-- Guarded form of the generic head followed by the tail. -/
def guardedForm : (verifier data m layout messageEquiv rule pc).toVerifier.GuardedForm := by
  let G := (Head.guardedForm data m layout messageEquiv rule pc).append
    (ProductSumcheck.guardedForm (Head.multiplier data m layout rule) pc)
  exact {
    check := G.check
    out := G.out
    verify_eq := fun stmt tr => by
      rw [verifier_toVerifier]
      exact G.verify_eq stmt tr }

instance : (reduction data m layout messageEquiv rule pc).prover.OutputIsPure :=
  Prover.OutputIsPure.append _ _
    (show (Head.prover data m layout messageEquiv rule pc).OutputIsPure from inferInstance)
    (show (ProductSumcheck.reduction (Head.multiplier data m layout rule) pc).prover.OutputIsPure
      from inferInstance)

/--
Perfect completeness for a challenge-algebra evaluation on the same commitment, from every
initial state.
-/
theorem perfectCompleteness [SampleableType C] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout messageEquiv rule pc).perfectCompleteness init impl
      (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × rule.Challenge)) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Head.reduction data m layout messageEquiv rule pc) (ProductSumcheck.reduction (Head.multiplier
      data m layout rule) pc)
    (Head.guardedForm data m layout messageEquiv rule pc) (ProductSumcheck.guardedForm
      (Head.multiplier data m layout rule) pc)
    (fun _ => Or.inl
      (show (Head.prover data m layout messageEquiv rule pc).OutputIsPure from inferInstance))
    (Head.perfectCompleteness data m layout messageEquiv rule pc init impl)
    (fun s => ProductSumcheck.perfectCompleteness (Head.multiplier data m layout rule) pc (pure s)
      impl)

end Program

section Security
variable (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The error function on appended challenge indices, with no terminal loss. -/
def rbrError [Fintype C] : (pSpec (M := M) data m bat.toBatchingRule).ChallengeIdx → ℝ≥0 :=
  Sum.elim (Head.rbrError (M := M) data bat) (ProductSumcheck.rbrError (C := C) (m := m)) ∘
    ChallengeIdx.sumEquiv.symm

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
-- Match the head and tail challenge types after unfolding the appended protocol specification.
set_option backward.isDefEq.respectTransparency false in
/-- Challenges in the generic head carry precisely the declared batching-strategy error. -/
theorem rbrError_head [Fintype C] (i : (Head.pSpec (M := M) data bat.toBatchingRule).ChallengeIdx) :
    rbrError (M := M) data m bat (ChallengeIdx.sumEquiv (.inl i)) = bat.error := by
  simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
  rfl

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
-- Match the head and tail challenge types after unfolding the appended protocol specification.
set_option backward.isDefEq.respectTransparency false in
/-- Each tail challenge carries the degree-two error. -/
theorem rbrError_tail [Fintype C] (i : (ProductSumcheck.pSpec C m).ChallengeIdx) :
    rbrError (M := M) data m bat (ChallengeIdx.sumEquiv (.inr i)) = 2 / Fintype.card C := by
  simp only [rbrError, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  exact ProductSumcheck.rbrError_eq i

/-- The concrete reduction is round-by-round knowledge sound on the original opening. -/
theorem rbrKnowledgeSoundness [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout messageEquiv bat.toBatchingRule
      pc).toVerifier.rbrKnowledgeSoundness init impl
      (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge)) (rbrError
        (M := M) data m bat) := by
  rw [verifier_toVerifier]
  apply Verifier.append_rbrKnowledgeSoundness_of_guarded_first
    _ _ (Head.guardedForm data m layout messageEquiv bat.toBatchingRule pc)
  · apply (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
    exact ⟨_, _, _, Head.rbrKnowledgeSoundnessWith data m layout messageEquiv bat pc
      hfunctional hinj init impl⟩
  · exact ProductSumcheck.rbrKnowledgeSoundness (Head.multiplier data m layout
    bat.toBatchingRule) pc hfunctional init impl

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
/-- The sum of the challenge errors is `ε + 2m/|C|`. -/
theorem rbrError_sum [Fintype C] : ∑ i, rbrError (M := M) data m bat i =
    bat.error + (m : ℝ≥0) * (2 / Fintype.card C) := by
  classical
  let e : (pSpec (M := M) data m bat.toBatchingRule).ChallengeIdx ≃
      (Head.pSpec (M := M) data bat.toBatchingRule).ChallengeIdx ⊕ (ProductSumcheck.pSpec C
        m).ChallengeIdx :=
    ChallengeIdx.sumEquiv.symm
  calc
    _ = ∑ j : (Head.pSpec (M := M) data bat.toBatchingRule).ChallengeIdx ⊕ (ProductSumcheck.pSpec C
      m).ChallengeIdx,
        Sum.elim (fun _ => bat.error) (fun _ => (2 : ℝ≥0) / Fintype.card C) j := by
      apply Fintype.sum_equiv e
      intro i
      change Sum.elim (Head.rbrError (M := M) data bat) ProductSumcheck.rbrError (e i) = _
      rcases h : e i with j | j
      · rfl
      · exact ProductSumcheck.rbrError_eq j
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
        card_head, card_tail, one_smul, nsmul_eq_mul]

omit [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C] in
/-- Appending an opening adds its challenge-error sum to the batching and sumcheck losses. -/
theorem append_rbrError_sum [Fintype C] {n : ℕ} (openingSpec : ProtocolSpec n)
    (openingError : openingSpec.ChallengeIdx → ℝ≥0) :
    (∑ i : ((pSpec (M := M) data m bat.toBatchingRule) ++ₚ openingSpec).ChallengeIdx,
      (Sum.elim (rbrError (M := M) data m bat) openingError ∘ ChallengeIdx.sumEquiv.symm) i) =
      bat.error + (m : ℝ≥0) * (2 / Fintype.card C) + ∑ i, openingError i := by
  classical
  simp only [Function.comp_def]
  rw [Equiv.sum_comp ChallengeIdx.sumEquiv.symm, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [rbrError_sum]

/-- Completeness and round-by-round knowledge soundness with total challenge error `ε +
  2m/|C|`. -/
theorem perfectCompleteness_and_rbrKnowledgeSoundness
    [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout messageEquiv bat.toBatchingRule pc).perfectCompleteness init impl
        (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge)) ∧
      (verifier data m layout messageEquiv bat.toBatchingRule
        pc).toVerifier.rbrKnowledgeSoundness init impl
        (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge))
        (rbrError (M := M) data m bat) ∧
      (∑ i, rbrError (M := M) data m bat i) = bat.error + (m : ℝ≥0) * (2 / Fintype.card C) :=
  ⟨perfectCompleteness data m layout messageEquiv bat.toBatchingRule pc init impl,
    rbrKnowledgeSoundness data m layout messageEquiv bat pc hfunctional hinj init impl,
    rbrError_sum (M := M) data m bat⟩

/-- The whole reduction is knowledge sound with error `bat.error + 2m/|C|`. -/
theorem knowledgeSoundness [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier data m layout messageEquiv bat.toBatchingRule pc).knowledgeSoundness init impl
      (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge))
      (bat.error + (m : ℝ≥0) * (2 / Fintype.card C)) := by
  simpa only [rbrError_sum] using
    OracleVerifier.knowledgeSoundness_of_rbrKnowledgeSoundness_of_guarded
      (guardedForm data m layout messageEquiv bat.toBatchingRule pc)
      (rbrKnowledgeSoundness data m layout messageEquiv bat pc hfunctional hinj init impl)

/-- The whole reduction is perfectly complete and knowledge sound with error
`bat.error + 2m/|C|`. -/
theorem perfectCompleteness_and_knowledgeSoundness
    [NoZeroDivisors C] [Fintype C] [SampleableType C]
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m layout messageEquiv bat.toBatchingRule pc).perfectCompleteness init impl
        (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge)) ∧
      (verifier data m layout messageEquiv bat.toBatchingRule pc).knowledgeSoundness init impl
        (Head.relIn data m layout pc) (pc.evalRelWithContext (layout.Query × bat.Challenge))
        (bat.error + (m : ℝ≥0) * (2 / Fintype.card C)) :=
  ⟨perfectCompleteness data m layout messageEquiv bat.toBatchingRule pc init impl,
    knowledgeSoundness data m layout messageEquiv bat pc hfunctional hinj init impl⟩

end Security

section Opening
variable {n : ℕ} {openingSpec : ProtocolSpec n}
  {StmtOut WitOut ιOut : Type} {OStmtOut : ιOut → Type}
  [∀ j, OracleInterface (OStmtOut j)]
  [∀ j, OracleInterface (openingSpec.Message j)]
  [∀ j, SampleableType (openingSpec.Challenge j)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
  {relOut : Set ((StmtOut × ∀ j, OStmtOut j) × WitOut)}

/-- A complete contextual opening closes the same-commitment scalar reduction. -/
theorem append_perfectCompleteness [SampleableType C]
    (rule : BatchingRule C data.ιE) (pc : PackedCommitment data.P m)
    (opening : OracleReduction []ₒ ((layout.Query × rule.Challenge) × ((Fin m → C) × C))
      pc.OStmt data.P⦃≤ 1⦄[X Fin m] StmtOut OStmtOut WitOut openingSpec)
    (guard : opening.toReduction.verifier.GuardedForm)
    (hopening : ∀ state : σ, opening.perfectCompleteness (pure state) impl
      (pc.evalRelWithContext (layout.Query × rule.Challenge)) relOut) :
    ((reduction data m layout messageEquiv rule pc).append opening).perfectCompleteness
      init impl (Head.relIn data m layout pc) relOut := by
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (reduction data m layout messageEquiv rule pc) opening
    (guardedForm data m layout messageEquiv rule pc) guard
    (fun _ => Or.inl inferInstance)
  · exact perfectCompleteness data m layout messageEquiv rule pc init impl
  · exact hopening

/-- A contextual opening with round-by-round knowledge soundness closes the reduction. -/
theorem append_rbrKnowledgeSoundness [NoZeroDivisors C] [Fintype C]
    [SampleableType C] (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)
    (hfunctional : pc.Functional) (hinj : Function.Injective (algebraMap data.P C))
    (opening : OracleVerifier []ₒ ((layout.Query × bat.Challenge) × ((Fin m → C) × C))
      pc.OStmt StmtOut OStmtOut openingSpec)
    (openingError : openingSpec.ChallengeIdx → ℝ≥0)
    (hopening : opening.toVerifier.rbrKnowledgeSoundness init impl
      (pc.evalRelWithContext (layout.Query × bat.Challenge)) relOut openingError) :
    Verifier.rbrKnowledgeSoundness init impl (Head.relIn data m layout pc) relOut
      ((verifier data m layout messageEquiv bat.toBatchingRule pc).append opening).toVerifier
        (Sum.elim (rbrError (M := M) data m bat) openingError ∘ ChallengeIdx.sumEquiv.symm) :=
  OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first _ _
    (guardedForm data m layout messageEquiv bat.toBatchingRule pc)
    (rbrKnowledgeSoundness data m layout messageEquiv bat pc hfunctional hinj init impl)
    hopening

end Opening
end RingSwitching.Packing.RingSwitch
