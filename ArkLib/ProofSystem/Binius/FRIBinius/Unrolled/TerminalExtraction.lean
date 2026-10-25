/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Terminal
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps.FinalSumcheck.Extraction
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-!
# Extraction through the fused terminal check

The decoded first oracle fixes the packed polynomial. Consistency of its committed folds with
the terminal scalar identifies that scalar with the polynomial's evaluation. Combining this
identity with the terminal guard recovers the product claim without cancelling the multiplier.
This argument also covers a zero multiplier and does not assume exact input encoding.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Terminal

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
    Extractor.RoundByRound ([]ₒ)
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
    (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β multiplier.evaluate outputContext (ϑ := ϑ)
      (h_rate := h_rate)).KnowledgeStateFunction init impl
      (relIn := roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (relOut := finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      (extractor := rbrExtractor K β (ϑ := ϑ) (h_rate := h_rate)) where
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
    obtain ⟨hc, hr⟩ := (guardedForm K β multiplier.evaluate outputContext
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
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β multiplier.evaluate outputContext (ϑ := ϑ)
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
    (init : ProbComp σ) (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β multiplier.evaluate outputContext (ϑ := ϑ)
      (h_rate := h_rate)).toVerifier.rbrKnowledgeSoundnessWorstCase init impl
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := 𝓑) (multpoly := multiplier.polynomial) (Fin.last ℓ))
      (finalSumcheckRelOut K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate))
      knowledgeError := by
  classical
  exact (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
    ⟨_, _, _, rbrKnowledgeSoundnessWorstCaseWith K β multiplier outputContext 𝓑 init impl⟩

end Binius.FRIBinius.Unrolled.Terminal
