/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.ProductClaim
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic
public import ArkLib.OracleReduction.Security.GuardedRoundByRound
public import ArkLib.OracleReduction.LogicStep

/-!
# From a product claim to the Binary Basefold loop

The shared ring-switching head outputs a product claim `s = ∑_y A(ctx)(y) · p(y)` for the packed
polynomial `p` committed by the first Binary Basefold oracle (`ProductSumcheck.rel` at round `0`).
This zero-message, zero-challenge reduction turns that claim into the initial statement and
witness of the Binary Basefold sum-check-and-fold loop for the same multiplier. It changes no
oracle and adds no error.

The relaxed input relation uses unique-radius compatibility of `p` with the first oracle
(`firstOracleInterface`); the strict input relation, used for perfect completeness, requires
the exact encoding.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled.Frontier

open Binius.BinaryBasefold OracleSpec OracleComp MvPolynomial RingSwitching
open RingSwitching.Packing (ProductSumcheck.Statement ProductSumcheck.rel ProductSumcheck.rel_zero)
open Sumcheck.Structured (Multiplier)

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)]
  [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ] {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type} (multiplier : Multiplier Context L ℓ)

/-! ## Protocol definitions -/

/-- The prover sends nothing; it builds the canonical initial witness of the packed polynomial. -/
noncomputable def prover : OracleProver []ₒ
    (ProductSumcheck.Statement Context L (m := ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (MultilinearPoly L ℓ)
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0) !p[] where
  PrvState _ := ((ProductSumcheck.Statement Context L (m := ℓ) 0) ×
    (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)) × MultilinearPoly L ℓ
  input := id
  sendMessage j := nomatch j
  receiveChallenge j := nomatch j
  output s := pure ((initialStatement s.1.1.ctx s.1.1.target, s.1.2),
    initialWitness K β multiplier.polynomial s.1.1.ctx s.2)

/-- The verifier reformats the product claim and forwards every oracle. -/
def verifier : OracleVerifier []ₒ
    (ProductSumcheck.Statement Context L (m := ℓ) 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
    (Statement (L := L) (ℓ := ℓ) Context 0)
    (OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0) !p[] where
  verify s _ := pure (initialStatement s.ctx s.target)
  outputOracle := .inl {
    embed := Function.Embedding.inl
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The honest prover and the reformatting verifier. -/
noncomputable def reduction := OracleReduction.mk
  (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)) (verifier K β)

/-- The verifier always accepts and leaves the oracles unchanged. -/
def guardedForm :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).toVerifier.GuardedForm where
  check _ _ := true
  out s _ := (initialStatement s.1.ctx s.1.target, s.2)
  verify_eq _ _ := rfl

instance : (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)).OutputIsPure where
  output_is_pure := ⟨fun s => ((initialStatement s.1.1.ctx s.1.1.target, s.1.2),
    initialWitness K β multiplier.polynomial s.1.1.ctx s.2), fun _ => rfl⟩

/-! ## Security

### Input relations -/

omit [Fintype L] [DecidableEq L] [NeZero ℓ] in
/-- Membership in a product-sumcheck relation at round `0`, for any statement: the challenge
prefix is empty. -/
theorem mem_rel_zero_iff (pc : Packing.PackedCommitment L ℓ)
    (s : ProductSumcheck.Statement Context L (m := ℓ) 0) (ost : ∀ j, pc.OStmt j)
    (p : MultilinearPoly L ℓ) :
    ((s, ost), p) ∈ ProductSumcheck.rel multiplier pc 0 ↔
      s.target = ∑ y : Fin ℓ → Fin 2,
        (multiplier s.ctx).val.eval (y : Fin ℓ → L) * p.val.eval (y : Fin ℓ → L) ∧
        pc.commitsTo ost p := by
  obtain ⟨ctx, challenges, target⟩ := s
  obtain rfl : challenges = Fin.elim0 := funext fun i => Fin.elim0 i
  exact ProductSumcheck.rel_zero multiplier pc ctx target ost p

/-! ### Round-by-round knowledge soundness -/

/-- The input witness is the initial witness's committed polynomial. -/
def extractor : Extractor.RoundByRound []ₒ
    (StmtIn := (ProductSumcheck.Statement Context L (m := ℓ) 0) ×
      (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j))
    (WitIn := MultilinearPoly L ℓ)
    (WitOut := Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (pSpec := !p[]) (WitMid := fun _ => MultilinearPoly L ℓ) where
  extractIn _ w := w
  extractMid j := nomatch j
  extractOut _ _ w := w.t

variable [Fact (β 0 = 1)]

/-- The knowledge state is the input relation; a relaxed round-`0` output witness returns the
product claim and unique-radius compatibility for its own polynomial. -/
noncomputable def knowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).KnowledgeStateFunction
      init impl
      (ProductSumcheck.rel multiplier
        (firstOracleInterface K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).toPackedCommitment 0)
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0)
      (extractor K β (ϑ := ϑ) (h_rate := h_rate)) where
  toFun _ s _ w := (s, w) ∈ ProductSumcheck.rel multiplier
    (firstOracleInterface K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).toPackedCommitment 0
  toFun_empty _ _ h := h
  toFun_next j := nomatch j
  toFun_full s _ w h :=
    (mem_rel_zero_iff multiplier _ s.1 s.2 w.t).mpr
      (sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero K β multiplier.polynomial
        s.1.ctx s.1.target s.2 w ((guardedForm K β).check_and_of_prEvent_pos h).2)

/-- The reduction is round-by-round knowledge sound with no challenge and no error, from the
product claim with unique-radius compatibility to the Binary Basefold round relation at `0`. -/
theorem rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier K β (Context := Context) (ϑ := ϑ) (h_rate := h_rate)).toVerifier
      |>.rbrKnowledgeSoundness init impl
      (ProductSumcheck.rel multiplier
        (firstOracleInterface K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).toPackedCommitment 0)
      (roundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0)
      (fun _ => 0) := by
  apply (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
  refine ⟨_, extractor K β, knowledgeStateFunction K β multiplier init impl, ?_⟩
  intro _ j
  exact Fin.elim0 j.1

/-! ### Perfect completeness -/

omit [Fact (β 0 = 1)] in
/-- From the product claim with an exact first encoding, the honest initial witness lies in the
strict Binary Basefold round relation at `0` with probability one. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction K β multiplier (ϑ := ϑ) (h_rate := h_rate)).perfectCompleteness init impl
      (ProductSumcheck.rel multiplier
        (firstOracleInterface K β (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_rate)).strictView.toPackedCommitment 0)
      (strictRoundRelation K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)
        (𝓑 := boolEmbedding L) (multpoly := multiplier.polynomial) 0) := by
  apply Reduction.perfectCompleteness_of_guarded_prover_support _ (guardedForm K β)
  intro ⟨s, ost⟩ p hin q hq
  obtain ⟨hs, ho⟩ := (mem_rel_zero_iff multiplier _ s ost p).mp hin
  have hp : (prover K β multiplier (ϑ := ϑ) (h_rate := h_rate)).run (s, ost) p =
      pure (default, ((initialStatement s.ctx s.target, ost),
        initialWitness K β multiplier.polynomial s.ctx p)) := by
    simp [Prover.run, Prover.runToRound, prover]
    rfl
  change q ∈ support ((prover K β multiplier).run (s, ost) p) at hq
  rw [hp] at hq
  obtain rfl := OracleComp.eq_of_mem_support_pure _ hq
  exact ⟨rfl, mem_strictRoundRelation_zero_initialWitness K β multiplier.polynomial
    s.ctx s.target p ost hs ho, rfl⟩

end Binius.FRIBinius.Unrolled.Frontier
