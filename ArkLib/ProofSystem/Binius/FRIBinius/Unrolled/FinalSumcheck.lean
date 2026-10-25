/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck.Extraction
public import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-!
# Final sumcheck step of the fused folding loop

The prover sends the final folded constant. The verifier checks the final sumcheck target
against the public multiplier evaluated at the folding challenges times that constant.
It never divides by the multiplier, and forwards the constant unchanged even when the
multiplier vanishes. The output retains the oracle family for the query phase.

As in Binary Basefold's final sumcheck module, this file groups the protocol, honest
perfect completeness, and round-by-round knowledge soundness. The extraction argument
decodes the first oracle and uses consistent folds to recover the product claim without
cancelling the multiplier; it does not assume exact input encoding.

The multiplier evaluator and output-context projection are explicit parameters.
FRI-Binius instantiates them with the ring-switching multiplier and the query's suffix.
The existing `Terminal` namespace is retained to preserve declaration names.
-/

@[expose] public section

variable {ι : Type} {oSpec : OracleSpec ι}

namespace Binius.FRIBinius.Unrolled.Terminal

/-! ## Protocol definitions -/

section Execution

open Binius.BinaryBasefold OracleSpec OracleComp ProtocolSpec AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type}
variable (evaluateMultiplier : Context → (Fin ℓ → L) → L)
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)
variable (outputContext : Context → SumcheckBaseContext L ℓ)

/-- The closing equation uses the received scalar, including at a zero multiplier. -/
def check (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) : Prop :=
  s.sumcheck_target = evaluateMultiplier s.ctx s.challenges * c

/-- Preserve challenges, target and final scalar, projecting only the unused query context. -/
def output (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) :
    FinalSumcheckStatementOut (L := L) (ℓ := ℓ) where
  ctx := outputContext s.ctx
  challenges := s.challenges
  sumcheck_target := s.sumcheck_target
  finalConstant := c

/-- The honest prover sends the value of its fully folded word at zero. -/
def prover {ϑ : ℕ} [NeZero ϑ] (outputContext : Context → SumcheckBaseContext L ℓ) :
    OracleProver (oSpec)
    (Statement (L := L) Context (Fin.last ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    Unit (pSpecFinalSumcheckStep (L := L)) where
  PrvState _ :=
    (Statement (L := L) Context (Fin.last ℓ) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)) ×
      Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ)
  input := id
  sendMessage
  | ⟨0, _⟩ => fun s => pure (s.2.f ⟨0, by simp only [zero_mem]⟩, s)
  receiveChallenge
  | ⟨0, h⟩ => nomatch h
  output s := pure ((output outputContext s.1.1 (s.2.f ⟨0, by simp only [zero_mem]⟩), s.1.2), ())

/-- Read the final scalar, abort on a failed multiplier check, and forward every oracle. -/
def verifier : OracleVerifier oSpec
    (Statement (L := L) Context (Fin.last ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (pSpecFinalSumcheckStep (L := L)) where
  verify s _ := do
    let c : L ← query (spec := [(pSpecFinalSumcheckStep (L := L)).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard (s.sumcheck_target = evaluateMultiplier s.ctx s.challenges * c)
    pure (output outputContext s c)
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The fused terminal reduction, with an executable scalar-message prover. -/
def reduction {ϑ : ℕ} [NeZero ϑ] (outputContext : Context → SumcheckBaseContext L ℓ)
    [DecidableEq K] := OracleReduction.mk
  (prover (oSpec := oSpec) K β outputContext (ϑ := ϑ) (h_rate := h_rate))
  (verifier (oSpec := oSpec) K β multiplier.evaluate outputContext)

variable [DecidableEq K]

/-- The terminal verifier is guarded by exactly the closing multiplier equation. -/
def guardedForm :
    (verifier (oSpec := oSpec) K β evaluateMultiplier outputContext (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.GuardedForm :=
  Verifier.GuardedForm.ofQueryGuard _ ⟨⟨0, rfl⟩, ()⟩
    (fun s c _ => check evaluateMultiplier s c)
    (hcheck := fun _ _ _ => by dsimp only [check]; infer_instance)
    (fun s c _ => output outputContext s c)
    (fun _ _ => rfl)

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] [Fact (ϑ ∣ ℓ)] in
/-- The guarded form forwards the input oracles without changing their contents. -/
theorem guardedForm_out
    (s : Statement (L := L) Context (Fin.last ℓ) ×
      ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (tr : (pSpecFinalSumcheckStep (L := L)).FullTranscript) :
    (guardedForm (oSpec := oSpec) K β evaluateMultiplier outputContext (ϑ := ϑ)
      (h_rate := h_rate)).out s tr =
      (output outputContext s.1 (tr.messages ⟨0, rfl⟩), s.2) := rfl

omit [Fintype L] [DecidableEq L] [NeZero ℓ] in
/-- Zero multiplier does not constrain the received scalar, but still requires a zero target. -/
theorem check_of_multiplier_zero (s : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (h : evaluateMultiplier s.ctx s.challenges = 0) :
    check evaluateMultiplier s c ↔ s.sumcheck_target = 0 := by
  simp [check, h]

omit [Field L] [Fintype L] [DecidableEq L] [NeZero ℓ] in
/-- The query phase always receives the scalar that was actually sent. -/
theorem output_finalConstant (s : Statement (L := L) Context (Fin.last ℓ)) (c : L) :
    (output outputContext s c).finalConstant = c := rfl

end Execution

/-! ## Security

### Perfect completeness -/

section Completeness

open Binius.BinaryBasefold MvPolynomial AdditiveNTT
open OracleComp ProtocolSpec

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R : ℕ} [NeZero ℓ] [NeZero R] {h_rate : ℓ + R < r}
variable {Context : Type}
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)

omit [NeZero ℓ] in
/-- The honest last-round scalar passes the fused guard for any public multiplier. -/
theorem check_honest (𝓑 : Fin 2 ↪ L)
    (s : Statement (L := L) Context (Fin.last ℓ))
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (hsum : sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) s.sumcheck_target w.H)
    (hstruct : WitnessStructuralInvariant K β (h_ℓ_add_R_rate := h_rate)
      (multpoly := multiplier.polynomial) s w) :
    check multiplier.evaluate s (w.f ⟨0, by simp only [zero_mem]⟩) := by
  classical
  unfold sumcheckConsistencyProp at hsum
  simp only [Fin.val_last] at hsum
  rw [Finset.sum_eq_single_of_mem (a := fun _ => 0)
    (by
      simp only [SumcheckDomain.mem_cube]
      intro i
      have hi := i.isLt
      omega)
    (fun b _ hb => (hb (by funext i; have hi := i.isLt; omega)).elim)] at hsum
  have hc : w.f ⟨0, by simp only [zero_mem]⟩ = w.t.val.eval s.challenges := by
    rw [hstruct.2]
    exact congr_fun (iteratedFold_to_level_ℓ_eval K β (h_ℓ_add_R_rate := h_rate)
      (t := w.t) (destIdx := ⟨Fin.last ℓ, by omega⟩)
      (h_destIdx := by simp only [Fin.val_last]) (challenges := s.challenges))
      ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [hstruct.1, Sumcheck.Structured.eval_projectToMidSumcheckPoly_last] at hsum
  unfold check
  rw [multiplier.evaluate_eq, hc]
  exact hsum

variable {ϑ : ℕ} [NeZero ϑ] [Fact (ϑ ∣ ℓ)]
variable (outputContext : Context → SumcheckBaseContext L ℓ)

/-- Strict last-round consistency implies the strict output folding relation consumed by
the query phase. This property is independent of the public multiplier. -/
theorem strict_output_of_honest
    (s : Statement (L := L) Context (Fin.last ℓ))
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (hw : w.f = getMidCodewords K β w.t s.challenges)
    (ho : StrictOracleFoldingConsistent K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
      (i := Fin.last ℓ) (t := w.t) (challenges := s.challenges) (oStmt := ost)) :
    ((output outputContext s (w.f ⟨0, by simp only [zero_mem]⟩), ost), ()) ∈
      strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) := by
  refine ⟨w.t, ho, ?_⟩
  funext y
  exact iteratedFold_lastOracle_eq_finalConstant K β s w ost hw ho y

/-- Perfect completeness of the fused terminal reduction from the strict last-round relation. -/
theorem perfectCompleteness [DecidableEq K] [SampleableType L] (𝓑 : Fin 2 ↪ L)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl (oSpec) (StateT σ ProbComp)) :
    (reduction (oSpec := oSpec) K β multiplier outputContext (ϑ := ϑ)
      (h_rate := h_rate)).perfectCompleteness
      init impl
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (strictFinalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)) := by
  classical
  apply Reduction.perfectCompleteness_of_guarded_prover_support _
    (guardedForm (oSpec := oSpec) K β multiplier.evaluate outputContext)
  intro ⟨s, ost⟩ w hin q hq
  let c : L := w.f ⟨0, by simp only [zero_mem]⟩
  have hp : (prover (oSpec := oSpec) K β outputContext (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) w =
      pure (((default : (pSpecFinalSumcheckStep (L := L)).Transcript 0).concat (m := 0) c),
        ((output outputContext s c, ost), ())) := rfl
  change q ∈ support ((prover (oSpec := oSpec) K β outputContext).run (s, ost) w) at hq
  rw [hp] at hq
  have heq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  obtain ⟨hsum, hstruct, horacles⟩ := hin
  refine ⟨?_, ?_, rfl⟩
  · change decide (s.sumcheck_target = multiplier.evaluate s.ctx s.challenges * c) = true
    exact decide_eq_true (check_honest K β multiplier 𝓑 s w hsum hstruct)
  · exact strict_output_of_honest K β outputContext s w ost hstruct.2 horacles

end Completeness

/-! ### Round-by-round knowledge soundness -/

section KnowledgeSoundness

open Binius.BinaryBasefold Binius.BinaryBasefold.CoreInteraction MvPolynomial
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ]
  {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type}
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)
variable (outputContext : Context → SumcheckBaseContext L ℓ)

/-- A passing terminal guard and consistent decoded folds recover the original product claim,
even when the public multiplier evaluates to zero. -/
theorem target_eq_product_of_consistent
    (s : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (p : MultilinearPoly L ℓ)
    (hdecode : extractMlp K β (h_ℓ_add_R_rate := h_rate) (i := 0)
      (f := getFirstOracle K β ost) = some p)
    (hfold : FinalSumcheckOracleConsistent K β (h_ℓ_add_R_rate := h_rate)
      (stmtOut := output outputContext s c) (oStmtOut := ost))
    (hcheck : check multiplier.evaluate s c) :
    s.sumcheck_target = (multiplier s.ctx).val.eval s.challenges * p.val.eval s.challenges := by
  have hc := eval_eq_final_constant_of_extractMlp_eq_some K β
    (h_ℓ_add_R_rate := h_rate) (output outputContext s c) ost p hdecode hfold
  change c = p.val.eval s.challenges at hc
  change s.sumcheck_target = multiplier.evaluate s.ctx s.challenges * c at hcheck
  rw [multiplier.evaluate_eq, hc] at hcheck
  exact hcheck

/-- The successful decoding branch of the terminal extractor. The remaining sumcheck
polynomial is constant, while the folded word is reconstructed from the decoded polynomial. -/
noncomputable def decodedWitness
    (s : Statement (L := L) Context (Fin.last ℓ)) (p : MultilinearPoly L ℓ) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) where
  t := p
  H := ⟨MvPolynomial.C s.sumcheck_target, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro n
    rw [MvPolynomial.degreeOf_C]
    exact Nat.zero_le _⟩
  f := getMidCodewords K β p s.challenges

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] in
/-- Recovering the product claim makes the decoded terminal witness structurally honest.
No nonzero assumption on either factor is required. -/
theorem decodedWitness_structural
    (s : Statement (L := L) Context (Fin.last ℓ)) (p : MultilinearPoly L ℓ)
    (h : s.sumcheck_target =
      (multiplier s.ctx).val.eval s.challenges * p.val.eval s.challenges) :
    WitnessStructuralInvariant K β (h_ℓ_add_R_rate := h_rate)
      (multpoly := multiplier.polynomial) s (decodedWitness K β s p) := by
  refine ⟨?_, rfl⟩
  apply SetLike.coe_eq_coe.mp
  rw [Sumcheck.Structured.coe_projectToMidSumcheckPoly_last]
  simp only [decodedWitness, h, MvPolynomial.C_mul]

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] in
/-- With no variables remaining, the constant target satisfies the local sumcheck equation. -/
theorem decodedWitness_sumcheck
    (s : Statement (L := L) Context (Fin.last ℓ)) (p : MultilinearPoly L ℓ)
    (𝓑 : Fin 2 ↪ L) :
    sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
      s.sumcheck_target (decodedWitness K β (h_rate := h_rate) s p).H := by
  unfold sumcheckConsistencyProp
  simp [decodedWitness]

/-- Successful decoding, consistent folds and the terminal guard recover the good branch of
the last-round knowledge invariant. The first oracle need only be uniquely decoding-close. -/
theorem decodedWitness_knowledgeInvariant
    (s : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (p : MultilinearPoly L ℓ) (𝓑 : Fin 2 ↪ L)
    (hdecode : extractMlp K β (h_ℓ_add_R_rate := h_rate) (i := 0)
      (f := getFirstOracle K β ost) = some p)
    (hfold : FinalSumcheckOracleConsistent K β (h_ℓ_add_R_rate := h_rate)
      (stmtOut := output outputContext s c) (oStmtOut := ost))
    (hcheck : check multiplier.evaluate s c) :
    KnowledgeInvariant K β (h_ℓ_add_R_rate := h_rate) (multpoly := multiplier.polynomial)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      s (decodedWitness K β s p) ost
      (sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
        s.sumcheck_target (decodedWitness K β (h_rate := h_rate) s p).H) := by
  refine Or.inr ⟨decodedWitness_sumcheck K β s p 𝓑, ?_, ?_, hfold.1⟩
  · exact decodedWitness_structural K β multiplier s p
      (target_eq_product_of_consistent K β multiplier outputContext s c ost p
        hdecode hfold hcheck)
  · exact (extractMlp_eq_some_iff_pairUniqueDecodingClose K β
      (h_ℓ_add_R_rate := h_rate) (f := getFirstOracle K β ost) (tpoly := p)).mp hdecode

/-- Decode the initial committed oracle, returning a total fallback when decoding fails.
The fallback is harmless: final consistency implies decoding succeeds, while a bad event
already satisfies the alternative branch of the input knowledge invariant. -/
noncomputable def extractWitness
    (s : Statement (L := L) Context (Fin.last ℓ))
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) :=
  match extractMlp K β (h_ℓ_add_R_rate := h_rate) (i := 0)
      (f := getFirstOracle K β ost) with
  | some p => decodedWitness K β s p
  | none => decodedWitness K β s 0

/-- Backward extraction across the final prover message, including the bad-event branch. -/
theorem extractWitness_knowledgeInvariant
    (s : Statement (L := L) Context (Fin.last ℓ)) (c : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (𝓑 : Fin 2 ↪ L)
    (hfold : FinalSumcheckFoldingState K β (h_ℓ_add_R_rate := h_rate)
      (input := (output outputContext s c, ost)))
    (hcheck : check multiplier.evaluate s c) :
    KnowledgeInvariant K β (h_ℓ_add_R_rate := h_rate) (multpoly := multiplier.polynomial)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      s (extractWitness K β s ost) ost
      (sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _)
        s.sumcheck_target (extractWitness K β s ost).H) := by
  rcases hfold with hconsistent | hbad
  · obtain ⟨p, hp⟩ := exists_extractMlp_eq_some_of_finalSumcheckOracleConsistent K β
      (output outputContext s c) ost hconsistent
    simp only [extractWitness, hp]
    exact decodedWitness_knowledgeInvariant K β multiplier outputContext s c ost p 𝓑
      hp hconsistent hcheck
  · exact Or.inl ((blockBadEventExists_iff_incrementalBadEventExists_last K β
      (h_ℓ_add_R_rate := h_rate) (ϑ := ϑ) (oStmt := ost)
      (challenges := s.challenges)).mp hbad)

/-- The terminal step consumes the last folding witness and produces no further witness. -/
def witnessFamily (m : Fin 2) : Type :=
  match m with
  | ⟨0, _⟩ => Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ)
  | ⟨1, _⟩ => Unit

/-- Round-by-round extraction for the fused terminal message. It uses the committed oracle,
not any polynomial supplied by the adversary as an auxiliary witness. -/
noncomputable def rbrExtractor :
    Extractor.RoundByRound (oSpec)
      (StmtIn := Statement (L := L) Context (Fin.last ℓ) ×
        (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j))
      (WitIn := Witness K β (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ))
      (WitOut := Unit) (pSpec := pSpecFinalSumcheckStep (L := L))
      (WitMid := witnessFamily K β (h_rate := h_rate)) where
  eqIn := rfl
  extractMid := fun m s _ _ => by
    have hm : m = 0 := by omega
    subst hm
    exact extractWitness K β s.1 s.2
  extractOut := fun _ _ _ => ()

/-- Before the terminal message, use the final loop invariant; after it, retain the guard
and the folding relation consumed by the query phase. -/
def knowledgeState (𝓑 : Fin 2 ↪ L) {m : Fin 2}
    (s : Statement (L := L) Context (Fin.last ℓ))
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (Fin.last ℓ) j)
    (tr : ProtocolSpec.Transcript m (pSpecFinalSumcheckStep (L := L)))
    (w : witnessFamily K β (h_rate := h_rate) m) : Prop :=
  match m with
  | ⟨0, _⟩ =>
    KnowledgeInvariant K β (h_ℓ_add_R_rate := h_rate) (multpoly := multiplier.polynomial)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      s w ost (sumcheckConsistencyProp (SumcheckDomain.uniform 𝓑 _) s.sumcheck_target w.H)
  | ⟨1, _⟩ =>
    let c : L := tr.messages ⟨0, rfl⟩
    check multiplier.evaluate s c ∧
      FinalSumcheckFoldingState K β (h_ℓ_add_R_rate := h_rate)
        (input := (output outputContext s c, ost))

/-- Certified knowledge states for the fused terminal verifier. -/
noncomputable def knowledgeStateFunction (𝓑 : Fin 2 ↪ L) {σ : Type}
    (init : ProbComp σ)
    (impl : QueryImpl (oSpec) (StateT σ ProbComp)) :
    (verifier (oSpec := oSpec) K β multiplier.evaluate outputContext (ϑ := ϑ)
      (h_rate := h_rate)).KnowledgeStateFunction init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (relOut := finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      (extractor := rbrExtractor (oSpec := oSpec) K β (ϑ := ϑ) (h_rate := h_rate)) where
  toFun := fun _ s tr w => knowledgeState K β multiplier outputContext 𝓑 s.1 s.2 tr w
  toFun_empty := fun _ _ => by rfl
  toFun_next := fun m _ s tr msg w => by
    have hm : m = 0 := by omega
    subst hm
    intro h
    exact extractWitness_knowledgeInvariant K β multiplier outputContext s.1 msg s.2 𝓑
      h.2 h.1
  toFun_full := fun s tr w h => by
    classical
    obtain ⟨hc, hr⟩ := (guardedForm (oSpec := oSpec) K β multiplier.evaluate outputContext
      (ϑ := ϑ) (h_rate := h_rate)).check_and_of_prEvent_pos h
    refine ⟨?_, hr⟩
    change s.1.sumcheck_target = multiplier.evaluate s.1.ctx s.1.challenges * _
    exact of_decide_eq_true hc

/-- No verifier challenge occurs in the terminal step. -/
def knowledgeError (i : (pSpecFinalSumcheckStep (L := L)).ChallengeIdx) : ℝ≥0 :=
  match i with
  | ⟨0, h⟩ => nomatch h

variable [SampleableType L]

/-- The fused terminal check is worst-case round-by-round knowledge sound with no additional
challenge error. Its substantive extraction obligations are certified above. -/
theorem rbrKnowledgeSoundnessWorstCaseWith (𝓑 : Fin 2 ↪ L) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl (oSpec) (StateT σ ProbComp)) :
    (verifier (oSpec := oSpec) K β multiplier.evaluate outputContext (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      (witnessFamily K β (h_rate := h_rate))
      (rbrExtractor K β (ϑ := ϑ) (h_rate := h_rate))
      (knowledgeStateFunction K β multiplier outputContext 𝓑 init impl)
      knowledgeError :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_isEmpty_challengeIdx _ _

omit [DecidableEq K] in
/-- Existential form of the terminal guarantee, for guarded sequential composition. -/
theorem rbrKnowledgeSoundnessWorstCase (𝓑 : Fin 2 ↪ L) {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl (oSpec) (StateT σ ProbComp)) :
    (verifier (oSpec := oSpec) K β multiplier.evaluate outputContext (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      knowledgeError := by
  classical
  exact (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, rbrKnowledgeSoundnessWorstCaseWith K β multiplier outputContext 𝓑 init impl⟩

end KnowledgeSoundness

end Binius.FRIBinius.Unrolled.Terminal
