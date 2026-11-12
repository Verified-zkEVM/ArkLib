/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.Binius.BinaryBasefold.General
public import ArkLib.OracleReduction.Security.GuardedBridges
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ProductClaim

/-!
# Binary Basefold multilinear evaluation opening

The opening protocol reformats an evaluation claim without communication, then runs the
Binary Basefold core and query protocol. Exact first-codeword encodings give perfect completeness;
unique-radius compatibility gives round-by-round knowledge soundness.
The strict input relation uses exact first-codeword encodings; the relaxed input relation uses
unique-decoding-radius compatibility.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec AdditiveNTT MvPolynomial
open Binius.BinaryBasefold RingSwitching Sumcheck.Structured

open scoped NNReal

noncomputable section
namespace Binius.BinaryBasefold.Opening

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [Field K]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

variable [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)] [Algebra K L]

variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]

/-- An evaluation claim `t(r) = s` as the product claim `∑_y eq̃(r, y) · t(y) = s` for
`openingMultiplier`: the context carries `r` and `s`, and the target is `s`. -/
def productClaim (s : MLPEvalStatement L ℓ) : SumcheckBaseContext L ℓ × L :=
  (⟨s.t_eval_point, s.original_claim⟩, s.original_claim)

/-- The evaluation claim as an initial Binary Basefold statement. -/
def statement (s : MLPEvalStatement L ℓ) :
    Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0 :=
  initialStatement (productClaim s).1 (productClaim s).2

omit [Fintype L] [DecidableEq L] [SampleableType L] [NeZero ℓ] in
/-- The opening multiplier's product claim is the evaluation claim:
`∑_{y ∈ {0,1}^ℓ} eq(r, y) · t(y) = t(r)` for multilinear `t`. -/
theorem sum_openingMultiplier_mul_eq_eval (ctx : SumcheckBaseContext L ℓ)
    (t : MultilinearPoly L ℓ) :
    ∑ y : Fin ℓ → Fin 2, (openingMultiplier.polynomial ctx).val.eval (y : Fin ℓ → L) *
      t.val.eval (y : Fin ℓ → L) = t.val.eval ctx.t_eval_point := by
  have ht : MLE (fun y : Fin ℓ → Fin 2 => t.val.eval (y : Fin ℓ → L)) = t.val :=
    (is_multilinear_iff_eq_evals_zeroOne (p := t.val)).mp t.property
  have hsum := MLE_eval ctx.t_eval_point (fun y : Fin ℓ → Fin 2 =>
    t.val.eval (y : Fin ℓ → L))
  rw [ht] at hsum
  have heq (y : Fin ℓ → Fin 2) :
      eval (y : Fin ℓ → L) (eqPolynomial ctx.t_eval_point) =
        eqTilde (y : Fin ℓ → L) ctx.t_eval_point := eqPolynomial_symm _ _
  simp only [openingMultiplier, eqMultiplier, heq]
  rw [← hsum]

variable {StmtIn WitIn : Type}
variable (evalQuery : StmtIn → MLPEvalStatement L ℓ)
variable (witnessEquiv : WitIn ≃ MultilinearPoly L ℓ)

/-- Evaluation and unique-radius compatibility with the supplied first oracle. -/
def inputRelation : Set ((StmtIn ×
    (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn) :=
  {x | (evalQuery x.1.1).original_claim =
      (witnessEquiv x.2).val.eval (evalQuery x.1.1).t_eval_point ∧
    FirstOracleWitnessConsistent K β (witnessEquiv x.2) (getFirstOracle K β x.1.2)}

omit [SampleableType L] [DecidableEq K] in
/-- An initial relaxed witness certifies the evaluation of its own source polynomial. -/
theorem eval_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero
    (s : MLPEvalStatement L ℓ)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (h : ((statement s, ost), w) ∈ roundRelation (multpoly := openingMultiplier.polynomial) K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    s.original_claim = w.t.val.eval s.t_eval_point ∧
      FirstOracleWitnessConsistent K β w.t (getFirstOracle K β ost) := by
  obtain ⟨hsum, hfirst⟩ := sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero K β
    openingMultiplier.polynomial _ _ ost w h
  exact ⟨hsum.trans (sum_openingMultiplier_mul_eq_eval _ w.t), hfirst⟩

/-- Evaluation and exact first-codeword encoding for honest completeness. -/
def strictInputRelation : Set ((StmtIn ×
    (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn) :=
  {x | (evalQuery x.1.1).original_claim =
      (witnessEquiv x.2).val.eval (evalQuery x.1.1).t_eval_point ∧
    getFirstOracle K β x.1.2 = firstOracleEncoding K β (witnessEquiv x.2)}

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- The evaluation relation contains every product claim for `openingMultiplier` whose polynomial
is unique-radius compatible with the first oracle. -/
theorem mem_inputRelation_of_sum_eq (s : StmtIn)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (t : MultilinearPoly L ℓ)
    (hsum : (productClaim (evalQuery s)).2 = ∑ y : Fin ℓ → Fin 2,
      (openingMultiplier (productClaim (evalQuery s)).1).val.eval (y : Fin ℓ → L) *
        t.val.eval (y : Fin ℓ → L))
    (hfirst : FirstOracleWitnessConsistent K β t (getFirstOracle K β ost)) :
    ((s, ost), witnessEquiv.symm t) ∈
      inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate) := by
  rw [sum_openingMultiplier_mul_eq_eval] at hsum
  change (evalQuery s).original_claim =
      (witnessEquiv (witnessEquiv.symm t)).val.eval (evalQuery s).t_eval_point ∧ _
  rw [Equiv.apply_symm_apply]
  exact ⟨hsum, hfirst⟩

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- A member of the strict evaluation relation is a product claim with an exact first
encoding. -/
theorem sum_eq_and_getFirstOracle_eq_of_mem_strictInputRelation (s : StmtIn)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j) (w : WitIn)
    (h : ((s, ost), w) ∈
      strictInputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) :
    (productClaim (evalQuery s)).2 = ∑ y : Fin ℓ → Fin 2,
        (openingMultiplier (productClaim (evalQuery s)).1).val.eval (y : Fin ℓ → L) *
          (witnessEquiv w).val.eval (y : Fin ℓ → L) ∧
      getFirstOracle K β ost = firstOracleEncoding K β (witnessEquiv w) := by
  obtain ⟨hclaim, hencoding⟩ := h
  refine ⟨?_, hencoding⟩
  rw [sum_openingMultiplier_mul_eq_eval]
  exact hclaim

/-- The evaluation-claim opening: Binary Basefold at `openingMultiplier`. -/
noncomputable def openingVerifier (γ : ℕ) :=
  ProductClaim.openingVerifier K β openingMultiplier (productClaim ∘ evalQuery) γ (ϑ := ϑ)
    (h_rate := h_rate)

/-- The honest evaluation-claim opening. -/
noncomputable def openingReduction (γ : ℕ) :=
  ProductClaim.openingReduction K β openingMultiplier (productClaim ∘ evalQuery) witnessEquiv γ
    (ϑ := ϑ) (h_rate := h_rate)

/-- Round-by-round knowledge soundness of the evaluation-claim opening. -/
theorem openingVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundness init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) acceptRejectOracleRel
      ((openingVerifier K β evalQuery γ (ϑ := ϑ) (h_rate := h_rate)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (ProductClaim.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) :=
  ProductClaim.openingVerifier_rbrKnowledgeSoundness K β openingMultiplier
    (productClaim ∘ evalQuery) witnessEquiv _ γ init impl
    (mem_inputRelation_of_sum_eq K β evalQuery witnessEquiv)

/-- Perfect completeness of the evaluation-claim opening on exact first encodings. -/
theorem openingReduction_perfectCompleteness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (oracleProof := openingReduction K β evalQuery witnessEquiv γ (ϑ := ϑ) (h_rate := h_rate))
      (relation := strictInputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (init := init) (impl := impl) :=
  ProductClaim.openingReduction_perfectCompleteness K β openingMultiplier
    (productClaim ∘ evalQuery)
    witnessEquiv _ γ init impl
    (sum_eq_and_getFirstOracle_eq_of_mem_strictInputRelation K β evalQuery witnessEquiv)

/-- The shared first-oracle interface used by the opening protocol. -/
def abstractInput : AbstractOStmtIn L ℓ :=
  firstOracleInterface K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- Unique-radius compatibility determines the committed polynomial. -/
theorem abstractInput_functional :
    (abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).Functional :=
  firstOracleInterface_functional K β ϑ

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero R] in
/-- Every source has an exact first-oracle encoding in this interface. -/
theorem abstractInput_strictInitialCompatibility_honest (t : MultilinearPoly L ℓ) :
    (abstractInput K β (ϑ := ϑ) (h_rate := h_rate)).strictInitialCompatibility
      (t, honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_rate) t) :=
  firstOracleInterface_strictInitialCompatibility_honest K β ϑ t

/-- The one-field opening witness is equivalent to its polynomial. -/
def mlpWitnessEquiv : WitMLP L ℓ ≃ MultilinearPoly L ℓ where
  toFun := fun w => w.t
  invFun := fun t => ⟨t⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Binary Basefold multilinear opening protocol. -/
def mliopcs (γ : ℕ) : MLIOPCS L ℓ where
  toAbstractOStmtIn := abstractInput K β (ϑ := ϑ) (h_rate := h_rate)
  numRounds := _
  pSpec := (!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate)
  Oₘ := instOracleInterfaceMessageAppend
  O_challenges := instSampleableTypeChallengeAppend
  oracleReduction := openingReduction K β id mlpWitnessEquiv γ (ϑ := ϑ) (h_rate := h_rate)
  perfectCompleteness := openingReduction_perfectCompleteness K β id mlpWitnessEquiv γ _ _
  rbrKnowledgeError := ProductClaim.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)
  rbrKnowledgeSoundness := by
    intro σ init impl
    exact openingVerifier_rbrKnowledgeSoundness K β id mlpWitnessEquiv γ init impl

/-- The evaluation claim after discarding the surrounding context. -/
def contextualQuery (Context : Type) :
    Context × ((Fin ℓ → L) × L) → MLPEvalStatement L ℓ :=
  fun s => ⟨s.2.1, s.2.2⟩

/-- The opening verifier for a contextual evaluation claim. -/
def contextualVerifier (Context : Type) (γ : ℕ) :=
  openingVerifier K β (contextualQuery (L := L) (ℓ := ℓ) Context) γ
    (ϑ := ϑ) (h_rate := h_rate)

/-- The opening reduction with a plain polynomial witness. -/
def contextualReduction (Context : Type) (γ : ℕ) :=
  openingReduction K β (contextualQuery (L := L) (ℓ := ℓ) Context)
    (Equiv.refl (MultilinearPoly L ℓ)) γ (ϑ := ϑ) (h_rate := h_rate)

/-- Contextual evaluation and unique-radius first-oracle compatibility. -/
def contextualInputRelation (Context : Type) :=
  inputRelation K β (contextualQuery (L := L) (ℓ := ℓ) Context)
    (Equiv.refl (MultilinearPoly L ℓ)) (ϑ := ϑ) (h_rate := h_rate)

/-- Contextual evaluation and exact first-oracle encoding. -/
def contextualStrictInputRelation (Context : Type) :=
  strictInputRelation K β (contextualQuery (L := L) (ℓ := ℓ) Context)
    (Equiv.refl (MultilinearPoly L ℓ)) (ϑ := ϑ) (h_rate := h_rate)

/-- Round-by-round security for contextual evaluation opening. -/
theorem contextualVerifier_rbrKnowledgeSoundness (Context : Type) (γ : ℕ) {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundness init impl
      (contextualInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate))
      acceptRejectOracleRel
      ((contextualVerifier K β Context γ (ϑ := ϑ) (h_rate := h_rate)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (ProductClaim.openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) :=
  openingVerifier_rbrKnowledgeSoundness K β (contextualQuery Context) (Equiv.refl _) γ
    init impl

/-- Perfect completeness for exact contextual evaluation inputs. -/
theorem contextualReduction_perfectCompleteness (Context : Type) (γ : ℕ) {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (oracleProof := contextualReduction K β Context γ (ϑ := ϑ) (h_rate := h_rate))
      (relation := contextualStrictInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate))
      (init := init) (impl := impl) :=
  openingReduction_perfectCompleteness K β (contextualQuery Context) (Equiv.refl _) γ init impl

/-- Knowledge soundness of evaluation opening at the Binary Basefold bound, with an unbounded
extractor. -/
theorem openingVerifier_knowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (openingVerifier K β evalQuery γ (ϑ := ϑ) (h_rate := h_rate))
      (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  ProductClaim.openingVerifier_knowledgeSoundness K β openingMultiplier (productClaim ∘ evalQuery)
    witnessEquiv _ γ init impl
    (mem_inputRelation_of_sum_eq K β evalQuery witnessEquiv)

/-- Evaluation opening is perfectly complete on exact encodings and ordinarily knowledge sound
for unique-radius compatibility at the concrete Binary Basefold error. -/
theorem openingReduction_perfectCompleteness_and_knowledgeSoundness (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := openingReduction K β evalQuery witnessEquiv γ
          (ϑ := ϑ) (h_rate := h_rate))
        (relation := strictInputRelation K β evalQuery witnessEquiv
          (ϑ := ϑ) (h_rate := h_rate)) (init := init) (impl := impl) ∧
      OracleProof.knowledgeSoundness init impl
        (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
        (openingVerifier K β evalQuery γ (ϑ := ϑ) (h_rate := h_rate))
        (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  ⟨openingReduction_perfectCompleteness K β evalQuery witnessEquiv γ init impl,
    openingVerifier_knowledgeSoundness K β evalQuery witnessEquiv γ init impl⟩

/-- Contextual evaluation opening is ordinarily knowledge sound at the concrete error. -/
theorem contextualVerifier_knowledgeSoundness (Context : Type) (γ : ℕ) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (contextualInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate))
      (contextualVerifier K β Context γ (ϑ := ϑ) (h_rate := h_rate))
      (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  openingVerifier_knowledgeSoundness K β (contextualQuery Context) (Equiv.refl _) γ init impl

/-- Contextual evaluation opening is perfectly complete on exact encodings and ordinarily
knowledge sound for unique-radius compatibility at the concrete Binary Basefold error. -/
theorem contextualReduction_perfectCompleteness_and_knowledgeSoundness (Context : Type) (γ : ℕ)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
        (oracleProof := contextualReduction K β Context γ (ϑ := ϑ) (h_rate := h_rate))
        (relation := contextualStrictInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate))
        (init := init) (impl := impl) ∧
      OracleProof.knowledgeSoundness init impl
        (contextualInputRelation K β Context (ϑ := ϑ) (h_rate := h_rate))
        (contextualVerifier K β Context γ (ϑ := ϑ) (h_rate := h_rate))
        (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  ⟨contextualReduction_perfectCompleteness K β Context γ init impl,
    contextualVerifier_knowledgeSoundness K β Context γ init impl⟩

attribute [local instance] MLIOPCS.Oₘ MLIOPCS.O_challenges

/-- The multilinear opening oracle reduction is ordinarily knowledge sound at the concrete error. -/
theorem mliopcs_knowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (mliopcs K β γ (ϑ := ϑ) (h_rate := h_rate)).toRelInput
      (mliopcs K β γ (ϑ := ϑ) (h_rate := h_rate)).oracleReduction.toOracleVerifier
      (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) :=
  openingVerifier_knowledgeSoundness K β id mlpWitnessEquiv γ init impl

end Binius.BinaryBasefold.Opening
