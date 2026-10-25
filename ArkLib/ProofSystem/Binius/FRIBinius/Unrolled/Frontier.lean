/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.Initial

/-!
# The zero-message batching-to-folding frontier

The shared batching head outputs a product-sumcheck statement and a packed polynomial.
This adapter initializes the folding witness without changing any committed oracle.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Frontier

open Binius.BinaryBasefold OracleSpec OracleComp MvPolynomial

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ] {h_rate : ℓ + R < r}
variable {Context : Type}
variable (multiplier : RingSwitching.Packing.ProductSumcheck.Multiplier Context L ℓ)

/-! ## Protocol definitions -/

/-- No prover messages are sent; only the internal folding witness is initialized. -/
noncomputable def prover : OracleProver ([]ₒ)
    (RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (MultilinearPoly L ℓ)
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0) !p[] where
  PrvState _ :=
    ((RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) ×
      MultilinearPoly L ℓ
  input := id
  sendMessage j := nomatch j
  receiveChallenge j := nomatch j
  output s := pure ((initialStatement s.1.1.ctx s.1.1.target, s.1.2),
    initialWitness K β multiplier.polynomial s.1.1.ctx s.2)

/-- Reformat the batching target and context, preserving every oracle. -/
def verifier : OracleVerifier ([]ₒ)
    (RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0) !p[] where
  verify s _ := pure (initialStatement s.ctx s.target)
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The no-communication adapter from the batching head to the folding loop. -/
noncomputable def reduction := OracleReduction.mk
  (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)) (verifier K β)

/-- The frontier has no checks and leaves all oracle contents unchanged. -/
def guardedForm :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).toVerifier.GuardedForm where
  check _ _ := true
  out s _ := (initialStatement s.1.ctx s.1.target, s.2)
  verify_eq _ _ := rfl

instance : (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)).OutputIsPure where
  output_is_pure := ⟨fun s => ((initialStatement s.1.1.ctx s.1.1.target, s.1.2),
    initialWitness K β multiplier.polynomial s.1.1.ctx s.2), fun _ => rfl⟩

variable [Fact (ϑ ∣ ℓ)]

/-! ## Security

### Relaxed relation and knowledge extraction -/

/-- Product-sum claim and uniquely decoding-close compatibility at the adapter input. -/
def inputRelation : Set
    (((RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) ×
      MultilinearPoly L ℓ) :=
  {x | x.1.1.target = ∑ y : Fin ℓ → Fin 2,
      (multiplier x.1.1.ctx).val.eval (y : Fin ℓ → L) * x.2.val.eval (y : Fin ℓ → L) ∧
    FirstOracleWitnessConsistent K β x.2 (getFirstOracle K β x.1.2)}

/-- The adapter extracts the packed polynomial carried by the backend witness. -/
def extractor : Extractor.RoundByRound ([]ₒ)
    (StmtIn := (RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j))
    (WitIn := MultilinearPoly L ℓ)
    (WitOut := Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (pSpec := !p[]) (WitMid := fun _ => MultilinearPoly L ℓ) where
  eqIn := rfl
  extractMid j := nomatch j
  extractOut _ _ w := w.t

variable [Fact (β 0 = 1)]

/-- Backward extraction preserves the product claim and the same relaxed commitment witness. -/
noncomputable def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).KnowledgeStateFunction
      init impl
      (inputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate))
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0)
      (extractor K β (ϑ := ϑ) (h_rate := h_rate)) where
  toFun _ s _ w := (s, w) ∈ inputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate)
  toFun_empty _ _ := Iff.rfl
  toFun_next j := nomatch j
  toFun_full s _ w h := by
    exact product_sum_and_compatibility_of_mem_roundRelation_zero K β multiplier.polynomial
      s.1.ctx s.1.target s.2 w
      ((guardedForm K β).check_and_of_prEvent_pos h).2

/-- Reformatting adds no challenge and no knowledge error. -/
theorem rbrKnowledgeSoundnessWorstCase {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).toVerifier
      |>.rbrKnowledgeSoundnessWorstCase init impl
      (inputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate))
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0)
      (fun _ => 0) := by
  apply (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr
  refine ⟨_, extractor K β, knowledgeStateFunction K β multiplier init impl, ?_⟩
  intro _ j
  exact Fin.elim0 j.1

omit [Fact (β 0 = 1)] in
/-- The first-oracle proximity relation packaged for the shared batching head. -/
noncomputable def commitment : RingSwitching.Packing.PackedCommitment L ℓ where
  ιC := Fin (toOutCodewordsCount ℓ ϑ 0)
  OStmt := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0
  Oᵢ := inferInstance
  commitsTo ost p := FirstOracleWitnessConsistent K β p (getFirstOracle K β ost)

omit [Fact (β 0 = 1)] [NeZero R] in
/-- The adapter input is exactly the shared product-sumcheck input relation, not a
strengthening to exact oracle encoding. -/
theorem inputRelation_eq_shared :
    inputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate) =
      RingSwitching.Packing.ProductSumcheck.rel multiplier
        (commitment K β (ϑ := ϑ) (h_rate := h_rate)) 0 := by
  ext ⟨⟨s, ost⟩, p⟩
  obtain ⟨ctx, challenges, target⟩ := s
  have hc : challenges = Fin.elim0 := funext fun i => Fin.elim0 i
  subst hc
  have h := (RingSwitching.Packing.ProductSumcheck.rel_zero multiplier
    (commitment K β (ϑ := ϑ) (h_rate := h_rate)) ctx target ost p).symm
  simp only [MvPolynomial.aeval_def] at h
  exact h

omit [Fact (β 0 = 1)] [NeZero R] in
/-- Unique-radius decoding supplies the functional commitment hypothesis required by the
batching head; this is a theorem, not an additional assumption on the fused protocol. -/
theorem commitment_functional :
    (commitment K β (ϑ := ϑ) (h_rate := h_rate)).Functional := by
  intro ost p q hp hq
  exact firstOracleWitnessConsistent_functional K β _ p q hp hq

/-! ### Strict relation and perfect completeness -/

omit [Fact (β 0 = 1)] in
/-- The completeness input uses the same product claim with exact first-oracle encoding. -/
def strictInputRelation : Set
    (((RingSwitching.Packing.ProductSumcheck.Statement Context L (m := ℓ) 0) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) ×
      MultilinearPoly L ℓ) :=
  {x | x.1.1.target = ∑ y : Fin ℓ → Fin 2,
      (multiplier x.1.1.ctx).val.eval (y : Fin ℓ → L) * x.2.val.eval (y : Fin ℓ → L) ∧
    getFirstOracle K β x.1.2 = firstOracleEncoding K β x.2}

omit [Fact (β 0 = 1)] in
/-- Exact input compatibility initializes the honest folding witness with probability one. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl ([]ₒ) (StateT σ ProbComp)) :
    (reduction K β multiplier (ϑ := ϑ) (h_rate := h_rate)).perfectCompleteness init impl
      (strictInputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate))
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0) := by
  apply Reduction.perfectCompleteness_of_guarded_prover_support _ (guardedForm K β)
  intro ⟨s, ost⟩ p hin q hq
  have hp : (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) p =
      pure (default, ((initialStatement s.ctx s.target, ost),
        initialWitness K β multiplier.polynomial s.ctx p)) := by
    simp [Prover.run, Prover.runToRound, prover]
    rfl
  change q ∈ support ((prover K β multiplier).run (s, ost) p) at hq
  rw [hp] at hq
  have heq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  exact ⟨rfl, mem_strictRoundRelation_initialWitness K β multiplier.polynomial
    s.ctx s.target p ost hin.1 hin.2, rfl⟩

omit [Fact (β 0 = 1)] in
/-- Exact commitment compatibility, used only for the honest completeness chain. -/
noncomputable def strictCommitment : RingSwitching.Packing.PackedCommitment L ℓ where
  ιC := Fin (toOutCodewordsCount ℓ ϑ 0)
  OStmt := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0
  Oᵢ := inferInstance
  commitsTo ost p := getFirstOracle K β ost = firstOracleEncoding K β p

omit [Fact (β 0 = 1)] [NeZero R] in
/-- The strict adapter input is precisely the shared relation with exact compatibility. -/
theorem strictInputRelation_eq_shared :
    strictInputRelation K β multiplier (ϑ := ϑ) (h_rate := h_rate) =
      RingSwitching.Packing.ProductSumcheck.rel multiplier
        (strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)) 0 := by
  ext ⟨⟨s, ost⟩, p⟩
  obtain ⟨ctx, challenges, target⟩ := s
  have hc : challenges = Fin.elim0 := funext fun i => Fin.elim0 i
  subst hc
  have h := (RingSwitching.Packing.ProductSumcheck.rel_zero multiplier
    (strictCommitment K β (ϑ := ϑ) (h_rate := h_rate)) ctx target ost p).symm
  simp only [MvPolynomial.aeval_def] at h
  exact h

end Binius.FRIBinius.Unrolled.Frontier
