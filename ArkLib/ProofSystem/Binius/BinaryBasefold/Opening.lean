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
-- The strict initial relation exposes dependent fold-index proof terms.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
-- The initial-fold identity unfolds the dependent fold implementation.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Folding
public import ArkLib.OracleReduction.Security.GuardedBridges
public import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations.Initial

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

/-- The evaluation claim as an initial Binary Basefold statement. -/
def statement (s : MLPEvalStatement L ℓ) :
    Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0 :=
  ⟨s.original_claim, Fin.elim0, ⟨s.t_eval_point, s.original_claim⟩⟩

/-- The canonical initial witness with equality-weighted sum-check polynomial. -/
def witness (s : MLPEvalStatement L ℓ) (t : MultilinearPoly L ℓ) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0 where
  t := t
  H := MvPolynomial.fixPrefix ℓ 0
    (computeInitialSumcheckPoly ℓ t (multiplier (statement s).ctx)) Fin.elim0
  f := getMidCodewords K β (h_ℓ_add_R_rate := h_rate) t Fin.elim0

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] in
/-- The canonical sum-check polynomial is the equality kernel times the source. -/
theorem witness_H_val (s : MLPEvalStatement L ℓ) (t : MultilinearPoly L ℓ) :
    (witness K β (h_rate := h_rate) s t).H.val = eqPolynomial s.t_eval_point * t.val := by
  simp [witness, MvPolynomial.fixPrefix, Sumcheck.Structured.coe_computeInitialSumcheckPoly,
    MvPolynomial.fixFirstVariablesOfMQP_zero, multiplier, eqMultiplier, statement]

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] in
/-- Boolean sum-check consistency is exactly the claimed source evaluation. -/
theorem sumcheckConsistencyProp_witness_iff (s : MLPEvalStatement L ℓ) (t : MultilinearPoly L ℓ) :
    sumcheckConsistencyProp (boolDomain L ℓ) s.original_claim
      (witness K β (h_rate := h_rate) s t).H ↔
      s.original_claim = t.val.eval s.t_eval_point := by
  unfold sumcheckConsistencyProp
  rw [sum_cube_boolDomain]
  simp only [witness_H_val, eval_mul]
  have ht : MLE (fun y : Fin ℓ → Fin 2 => t.val.eval (y : Fin ℓ → L)) = t.val :=
    (is_multilinear_iff_eq_evals_zeroOne (p := t.val)).mp t.property
  have hsum := MLE_eval s.t_eval_point (fun y : Fin ℓ → Fin 2 =>
    t.val.eval (y : Fin ℓ → L))
  rw [ht] at hsum
  have heq (y : Fin ℓ → Fin 2) :
      eval (y : Fin ℓ → L) (eqPolynomial s.t_eval_point) =
        eqTilde (y : Fin ℓ → L) s.t_eval_point := eqPolynomial_symm _ _
  simp only [heq]
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
    (h : ((statement s, ost), w) ∈ roundRelation (multpoly := multiplier) K β
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    s.original_claim = w.t.val.eval s.t_eval_point ∧
      FirstOracleWitnessConsistent K β w.t (getFirstOracle K β ost) := by
  rw [mem_roundRelation_zero_iff] at h
  obtain ⟨hsum, hstruct, hfirst, _⟩ := h
  have hH : w.H = (witness K β (h_rate := h_rate) s w.t).H := hstruct.1
  rw [hH] at hsum
  exact ⟨(sumcheckConsistencyProp_witness_iff K β s w.t).mp hsum, hfirst⟩

/-- The zero-message, zero-challenge statement reformatting verifier. -/
def frontVerifier : OracleVerifier []ₒ StmtIn
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0) !p[] where
  verify s _ := pure (statement (evalQuery s))
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun _ _ h => Sum.inl.inj h⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The reformatting verifier always accepts and preserves the oracle family. -/
def frontGuard :
    (frontVerifier K β evalQuery (ϑ := ϑ) (h_rate := h_rate)).toVerifier.GuardedForm where
  check _ _ := true
  out x _ := (statement (evalQuery x.1), x.2)
  verify_eq _ _ := rfl

/-- The extracted source is the backend witness's own polynomial. -/
def frontExtractor : Extractor.RoundByRound []ₒ
    (StmtIn := StmtIn ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j))
    (WitIn := WitIn)
    (WitOut := Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (pSpec := !p[]) (WitMid := fun _ => WitIn) where
  extractIn := fun _ w => w
  extractMid j := nomatch j
  extractOut _ _ w := witnessEquiv.symm w.t

/-- The initial evaluation relation as the knowledge state of the reformatting step. -/
def frontKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (frontVerifier K β evalQuery (ϑ := ϑ) (h_rate := h_rate)).KnowledgeStateFunction init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (roundRelation (multpoly := multiplier) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0)
      (frontExtractor K β witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) where
  toFun _ x _ w := (x, w) ∈ inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)
  toFun_empty _ _ h := h
  toFun_next j := nomatch j
  toFun_full x _tr w h := by
    have hp := eval_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero K β (evalQuery
      x.1) x.2 w
      ((frontGuard K β evalQuery).check_and_of_prEvent_pos h).2
    change (evalQuery x.1).original_claim =
        (witnessEquiv (witnessEquiv.symm w.t)).val.eval (evalQuery x.1).t_eval_point ∧ _
    simpa only [frontExtractor, Equiv.apply_symm_apply] using hp

omit [SampleableType L] [DecidableEq K] in
/-- Round-by-round security with no challenge positions. -/
theorem frontVerifier_rbrKnowledgeSoundnessWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWith init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (roundRelation (multpoly := multiplier) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0)
      (frontVerifier K β evalQuery (ϑ := ϑ) (h_rate := h_rate)).toVerifier
      (fun _ => WitIn) (frontExtractor K β witnessEquiv)
      (frontKnowledgeStateFunction K β evalQuery witnessEquiv init impl) (fun _ => 0) := by
  intro _ j
  exact Fin.elim0 j.1

/-- The honest reformatting prover constructs the canonical initial witness. -/
def frontProver : OracleProver []ₒ StmtIn
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0) WitIn
    (Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0) !p[] where
  PrvState _ := (StmtIn ×
    (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn
  input := id
  sendMessage j := nomatch j
  receiveChallenge j := nomatch j
  output st := pure ((statement (evalQuery st.1.1), st.1.2),
    witness K β (evalQuery st.1.1) (witnessEquiv st.2))

/-- The canonical prover and oracle-preserving verifier for statement reformatting. -/
def frontReduction := OracleReduction.mk
  (frontProver K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) (frontVerifier K β evalQuery)

instance : (frontProver K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)).OutputIsPure where
  output_is_pure := ⟨fun st => ((statement (evalQuery st.1.1), st.1.2),
    witness K β (evalQuery st.1.1) (witnessEquiv st.2)),
    fun _ => rfl⟩

/-- The reformatting verifier followed by the full Binary Basefold verifier. -/
def openingVerifier (γ : ℕ) := OracleVerifier.append
  (Stmt₃ := Bool) (OStmt₃ := fun _ : Empty => Unit)
  (Oₛ₃ := fun i : Empty => nomatch i)
  (frontVerifier K β evalQuery (ϑ := ϑ) (h_rate := h_rate))
  (FullBinaryBasefold.fullOracleVerifier K β γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The reformatting reduction followed by the full Binary Basefold reduction. -/
def openingReduction (γ : ℕ) := OracleReduction.append
  (Stmt₃ := Bool) (Wit₃ := Unit) (OStmt₃ := fun _ : Empty => Unit)
  (Oₛ₃ := fun i : Empty => nomatch i)
  (frontReduction K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
  (FullBinaryBasefold.fullOracleReduction K β γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The Binary Basefold challenge error transported through the zero-round prefix. -/
def openingError (γ : ℕ)
    (j : ((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (fun _ => 0)
    (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)) (ChallengeIdx.sumEquiv.symm j)

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] in
/-- The opening's challenge-error sum is bounded by the core and repeated-query errors. -/
theorem openingError_sum_le_concrete (γ : ℕ) :
    (∑ j, openingError K β γ (ϑ := ϑ) (h_rate := h_rate) j) ≤
      FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ := by
  classical
  let f : ((!p[] : ProtocolSpec 0).ChallengeIdx ⊕
      (fullPSpec K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) → ℝ≥0 :=
    Sum.elim (fun _ => 0)
      (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate))
  change (∑ j, f (ChallengeIdx.sumEquiv.symm j)) ≤ _
  rw [Equiv.sum_comp (e := ChallengeIdx.sumEquiv.symm) (g := f), Fintype.sum_sum_type]
  simp only [f, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add]
  exact FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete K β γ

instance instMessageInterface (γ : ℕ) : ∀ j, OracleInterface
    (((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).Message j) :=
  instOracleInterfaceMessageAppend

instance instChallengeSampleable (γ : ℕ) : ∀ j, SampleableType
    (((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).Challenge j) :=
  instSampleableTypeChallengeAppend

/-- Round-by-round knowledge soundness of the opening verifier. -/
theorem openingVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundness init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) acceptRejectOracleRel
      ((openingVerifier K β evalQuery γ (ϑ := ϑ) (h_rate := h_rate)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) := by
  exact OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (frontGuard K β evalQuery)
    ⟨_, frontExtractor K β witnessEquiv, frontKnowledgeStateFunction K β evalQuery witnessEquiv
      init impl,
      frontVerifier_rbrKnowledgeSoundnessWith K β evalQuery witnessEquiv init impl⟩
    (FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

-- The strict initial fold identity compares definitionally equal dependent domains.
set_option backward.isDefEq.respectTransparency false in
omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] in
/-- An exact first encoding and a valid evaluation give the strict initial relation. -/
theorem mem_strictRoundRelation_zero_witness (s : MLPEvalStatement L ℓ)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (t : MultilinearPoly L ℓ)
    (hs : s.original_claim = t.val.eval s.t_eval_point)
    (ho : getFirstOracle K β ost = firstOracleEncoding K β t) :
    ((statement s, ost), witness K β (h_rate := h_rate) s t) ∈
      strictRoundRelation (multpoly := multiplier) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0 := by
  classical
  dsimp only [strictRoundRelation, StrictRoundRelated, StrictOracleWitnessConsistent]
  refine ⟨(sumcheckConsistencyProp_witness_iff K β s t).mpr hs, ⟨rfl, rfl⟩, ?_⟩
  change StrictOracleFoldingConsistent K β t (0 : Fin (ℓ + 1)) Fin.elim0 ost
  dsimp only [StrictOracleFoldingConsistent]
  rintro ⟨j, hj⟩
  have hj0 : j = 0 := Nat.lt_one_iff.mp
    (lt_of_lt_of_eq hj (toOutCodewordsCount_zero ℓ ϑ))
  subst j
  funext y
  rw [iteratedFold_congr_steps_index K β (h_ℓ_add_R_rate := h_rate) (steps' := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod,
      Nat.zero_add])
    (h_destIdx_le := by simp only [Nat.zero_mul, Nat.zero_le])
    (h_steps_eq_steps' := by simp only [Nat.zero_mul])]
  rw [iteratedFold_zero_steps K β (h_ℓ_add_R_rate := h_rate) (i := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod])]
  have hy := congrFun ho (cast (by simp only [Fin.mk_zero', Nat.zero_mul]) y)
  simpa [getFirstOracle, firstOracleEncoding] using hy

/-- Evaluation and exact first-codeword encoding for honest completeness. -/
def strictInputRelation : Set ((StmtIn ×
    (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn) :=
  {x | (evalQuery x.1.1).original_claim =
      (witnessEquiv x.2).val.eval (evalQuery x.1.1).t_eval_point ∧
    getFirstOracle K β x.1.2 = firstOracleEncoding K β (witnessEquiv x.2)}

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] in
/-- Perfect completeness of reformatting at the exact input relation. -/
theorem frontReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (frontReduction K β evalQuery witnessEquiv
      (ϑ := ϑ) (h_rate := h_rate)).perfectCompleteness init impl
      (strictInputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (strictRoundRelation (multpoly := multiplier) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) := by
  apply Reduction.perfectCompleteness_of_run_support
  rintro ⟨s, ost⟩ w hw x hx
  let G := frontGuard K β evalQuery (ϑ := ϑ) (h_rate := h_rate)
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  have hp : (frontProver K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) w =
      pure (default, ((statement (evalQuery s), ost),
        witness K β (h_rate := h_rate) (evalQuery s) (witnessEquiv w))) := by
    simp [Prover.run, Prover.runToRound, frontProver]
    rfl
  change x ∈ support ((frontProver K β evalQuery witnessEquiv
    (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) w >>=
    fun r => pure (if G.check (s, ost) r.1 then some (r, G.out (s, ost) r.1) else none)) at hx
  rw [hp] at hx
  simp only [pure_bind, G, frontGuard, ↓reduceIte,
    mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, mem_strictRoundRelation_zero_witness K β (evalQuery s) ost (witnessEquiv w)
    hw.1 hw.2, rfl⟩

/-- Perfect completeness of the opening protocol on exact first encodings. -/
theorem openingReduction_perfectCompleteness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness
      (oracleProof := openingReduction K β evalQuery witnessEquiv γ (ϑ := ϑ) (h_rate := h_rate))
      (relation := strictInputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (init := init) (impl := impl) := by
  exact OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (frontGuard K β evalQuery)
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (frontReduction_perfectCompleteness K β evalQuery witnessEquiv init impl)
    (fun st => FullBinaryBasefold.fullOracleReduction_perfectCompleteness K β γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L)
      (init := pure st) (impl := impl))

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
  rbrKnowledgeError := openingError K β γ (ϑ := ϑ) (h_rate := h_rate)
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
      (openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) :=
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

/-- Ordinary knowledge soundness of evaluation opening at the concrete Binary Basefold error. -/
theorem openingVerifier_knowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.knowledgeSoundness init impl
      (inputRelation K β evalQuery witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
      (openingVerifier K β evalQuery γ (ϑ := ϑ) (h_rate := h_rate))
      (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) := by
  apply Verifier.knowledgeSoundness_error_mono init impl
    (openingError_sum_le_concrete K β γ (ϑ := ϑ) (h_rate := h_rate))
  exact Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (openingVerifier_rbrKnowledgeSoundness K β evalQuery witnessEquiv γ init impl)

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
