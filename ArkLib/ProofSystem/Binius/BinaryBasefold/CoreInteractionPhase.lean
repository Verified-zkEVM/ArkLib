/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps
import ArkLib.OracleReduction.Cast
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
## Binary Basefold Core Interaction Phase

This module contains the core interaction phase of the Binary Basefold IOP,
which combines, where both sumcheck and codeword folding occur in each round.

There are ℓ rounds in the core interaction phase, so there are ℓ + 1 states.
The i'th round receives the state i as input and outputs state i+1.

We define `(P, V)` as the following IOP, in which both parties have the common input
`[f], s ∈ L`, and `(r_0, ..., r_{ℓ-1}) ∈ L^ℓ`, and P has the further input
`t(X_0, ..., X_{ℓ-1}) ∈ L[X_0, ..., X_{ℓ-1}]^≤1`.

- P writes `h(X) := t(X) * eqTilde(r_0, ..., r_{ℓ-1}, X_0, ..., X_{ℓ-1})`.
- P and V both abbreviate `f^(0) := f` and `s_0 := s`, and execute the following loop:

  for `i in {0, ..., ℓ-1}` do
    P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...,
    w_{ℓ-i-2})`.
    V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`, and
    sends P `r'_i`.
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
      P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`

- P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
- V verifies: `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
namespace Binius.BinaryBasefold.CoreInteraction

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial Equiv
open scoped NNReal

set_option linter.style.longFile 2600

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section ComponentReductions
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

/-! ### Helper Lemmas for Fin Equality and Type Congruence -/

/-! Fin equality for 0 * ϑ = 0 -/
lemma fin_zero_mul_eq (h : 0 * ϑ < ℓ + 1) : (⟨0 * ϑ, h⟩ : Fin (ℓ + 1)) = 0 := by
  ext; simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod]

/-! Statement equality from Fin equality -/
lemma Statement.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Statement (L := L) (ℓ := ℓ) Context i = Statement (L := L) (ℓ := ℓ) Context j := by
  subst h; rfl

/-! OracleStatement index type equality from Fin equality -/
lemma OracleStatement.idx_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Fin (toOutCodewordsCount ℓ ϑ i) = Fin (toOutCodewordsCount ℓ ϑ j) := by
  subst h; rfl

/-! OracleStatement function HEq from Fin equality -/
lemma OracleStatement.heq_of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    HEq (fun k => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k)
        (fun k => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j k) := by
  subst h; rfl

/-! Witness equality from Fin equality -/
lemma Witness.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i =
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) j := by
  subst h; rfl

/-! Relation equality from Fin equality -/
lemma strictRoundRelation.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i ≍
    strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) j := by
  subst h; rfl

/-! Round relation equality from Fin equality -/
lemma roundRelation.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i ≍
    roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) j := by
  subst h; rfl

section FoldRelayRound -- foldRound + relay

@[reducible]
def foldRelayOracleVerifier (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (pSpec := pSpecFoldRelay (L:=L)) :=
  OracleVerifier.append
        (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecRelay)
    (foldOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i)
    (relayOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)


@[reducible]
def foldRelayOracleReduction (i : Fin ℓ)
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :=
  OracleReduction.append
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecRelay)
    (foldOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i
      (foldOracleProver 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i))
    (relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Perfect completeness of the non-commitment round reduction follows by append composition
    of the fold-round and the transfer-round reductions. -/
theorem foldRelayOracleReduction_perfectCompleteness
    (hInit : NeverFail init) (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge i)]
    [(i : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge i)] :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFoldRelay (L := L))
    (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc)
    (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ)
    (oracleReduction := foldRelayOracleReduction 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hNCR) (init := init) (impl := impl) := by
  sorry

/-! Flat form of RBR knowledge error for fold+relay: case split on challenge index
    instead of Sum.elim. Equal to the append-composed error (see foldRelayKnowledgeError_eq). -/
noncomputable def foldRelayKnowledgeError (i : Fin ℓ)
    (j : (pSpecFoldRelay (L := L)).ChallengeIdx) : ℝ≥0 :=
  match ChallengeIdx.sumEquiv.symm j with
  | Sum.inl j₁ => foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j₁
  | Sum.inr j₂ => relayKnowledgeError j₂

lemma foldRelayKnowledgeError_eq (i : Fin ℓ)
    (j : (pSpecFoldRelay (L := L)).ChallengeIdx) :
    foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j =
      Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        relayKnowledgeError (ChallengeIdx.sumEquiv.symm j) := by
  sorry

/-! RBR KS for Fold+Relay block: append then convert to flat error. -/
theorem foldRelayOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) i hNCR).rbrKnowledgeSoundness (init := init) (impl := impl)
      (relIn := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) i.castSucc  (mp := mp))
      (relOut := roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) i.succ  (mp := mp))
      (rbrKnowledgeError := foldRelayKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  sorry

end FoldRelayRound -- foldRound + relay

section FoldCommitRound -- foldRound + commit

@[reducible]
def foldCommitOracleVerifier (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
    OracleVerifier.append (oSpec := []ₒ)
      (pSpec₁ := pSpecFold (L:=L))
      (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (V₁ := foldOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i)
      (V₂ := commitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR)


@[reducible]
def foldCommitOracleReduction (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :=
  OracleReduction.append (oSpec := []ₒ)
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (R₁ := foldOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i
      (foldOracleProver 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i))
    (R₂ := commitOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Perfect completeness for Fold+Commitment block by append composition. -/
theorem foldCommitOracleReduction_perfectCompleteness
    (hInit : NeverFail init) (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge i)]
    [(i : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge i)]
    [(j : (pSpecCommit (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Fintype ((pSpecCommit (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)]
    [(j : (pSpecCommit (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Inhabited ((pSpecCommit (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)] :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFoldCommit (𝔽q := 𝔽q) (β := β)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ)
    (oracleReduction := foldCommitOracleReduction 𝔽q β (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR) (init := init) (impl := impl) := by
  sorry

/-! Flat form of RBR knowledge error for fold+commit: case split on the two component
    challenge families directly, then re-embed via `ChallengeIdx.sumEquiv` at call sites. -/
noncomputable def foldCommitKnowledgeError (i : Fin ℓ)
    (j : (pSpecFoldCommit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) : ℝ≥0 :=
  match ChallengeIdx.sumEquiv.symm j with
  | Sum.inl j₁ => foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j₁
  | Sum.inr _ => 0

/-! RBR KS for Fold+Commitment block: append then convert to flat error. -/
theorem foldCommitOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) i hCR).rbrKnowledgeSoundness (init := init) (impl := impl)
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc )
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ )
      (rbrKnowledgeError := foldCommitKnowledgeError 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  sorry

end FoldCommitRound

section IteratedSumcheckFoldComposition
/-!
## Composed Components (SumcheckFold)

Iterative composition across ℓ rounds: for each i, use Fold+Commitment when
`isCommitmentRound ℓ ϑ i`, otherwise use Fold+Relay. We rely on the fixed-size
block verifiers/reductions built earlier to avoid dependent casts.
-/
section composedOracleVerifiers
def nonLastSingleBlockOracleVerifier (bIdx : Fin (ℓ / ϑ - 1)) :=
  let _ := mp
  let _ := 𝓑
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i: Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
    ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleVerifier :=
    OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (V := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
          isNeCommitmentRound (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) bIdx (x := i.val)
            (hx := by omega)
        exact foldRelayOracleVerifier (L := L) 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ hNCR
      )
  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv : Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n := ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq : fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ : ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega
  let lastOracleVerifier := foldCommitOracleVerifier 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
    (hCR := isCommitmentRoundOfNonLastBlock (𝓡 := 𝓡) (r := r) bIdx)
  let nonLastSingleBlockOracleVerifier :=
    OracleVerifier.append (oSpec := []ₒ)
      (Stmt₁ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m := ℓ) (h₁ := by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Stmt₂ := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Stmt₃ := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₁ := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ, Nat.lt_of_add_right_lt h1_succ⟩)
      (OStmt₂ := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmt₃ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ + 1)))
      (pSpec₁ := pSpecFoldRelaySequence (L := L) (n := ϑ - 1))
      (pSpec₂ := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (V₁ := firstFoldRelayRoundsOracleVerifier.castOutSimple (h_stmt := by rfl) (h_ostmt := by rfl))
      (V₂ := OracleVerifier.castInOut (V := lastOracleVerifier)
          (StmtIn₁ := (Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
          (StmtIn₂ := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
          (StmtOut₁ := Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
          (StmtOut₂ := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
          (OStmtIn₁ := (OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
          (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
          (OStmtOut₁ := OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
          (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
          (pSpec := pSpecFoldCommit 𝔽q β ⟨↑bIdx * ϑ + (ϑ - 1), h1⟩)
          (h_stmtIn := by
            apply Statement.of_fin_eq
            simp? [Fin.castSucc, Fin.eta])
          (h_stmtOut := by
            apply Statement.of_fin_eq
            ext; simp? [Fin.val_succ]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le),
              Nat.add_mul, Nat.one_mul])
          (h_idxIn := by
            apply OracleStatement.idx_eq
            simp? [Fin.castSucc, Fin.eta])
          (h_idxOut := by
            apply OracleStatement.idx_eq
            ext; simp? [Fin.val_succ]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le),
              Nat.add_mul, Nat.one_mul])
          (h_ostmtIn := by
            apply OracleStatement.heq_of_fin_eq
            simp? [Fin.castSucc, Fin.eta])
          (h_ostmtOut := by
            apply OracleStatement.heq_of_fin_eq
            ext; simp only [Fin.succ_mk]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le),
              Nat.add_mul, Nat.one_mul])
          (h_Oₛᵢ := by
            apply instOracleStatementBinaryBasefold_heq_of_fin_eq
            ext; simp only [Fin.castSucc, Fin.castAdd_mk])
      )
  nonLastSingleBlockOracleVerifier

def nonLastBlocksOracleVerifier :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, by omega⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨0 * ϑ, by omega⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context ⟨(ℓ / ϑ - 1) * ϑ, by
      apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (pSpec := pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let _ := mp
  let _ := 𝓑
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let res := OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun (bIdx : Fin (ℓ / ϑ - 1)) =>
        pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ) bIdx)
      (V := fun bIdx => nonLastSingleBlockOracleVerifier (L := L) 𝔽q β (mp := mp)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (bIdx := bIdx))
  res

def lastBlockOracleVerifier :=
  let _ := 𝓑
  have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx := by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx := by omega)⟩
  let V : OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L := L) (ϑ := ϑ)) := by
    let cur := OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (V := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
          lastBlockIdx_isNeCommitmentRound i
        exact foldRelayOracleVerifier (L := L) 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ hNCR
      )
    exact OracleVerifier.castInOut (V := cur)
      (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
      (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
      (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (pSpec := pSpecLastBlock (L := L) (ϑ := ϑ))
      (h_stmtIn := by
        apply Statement.of_fin_eq
        ext; simp?)
      (h_stmtOut := by
        apply Statement.of_fin_eq
        ext
        simp? [Fin.val_last]
        have : bIdx * ϑ + ϑ = ℓ := by
          have h_div : ϑ ∣ ℓ := hdiv.out
          have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
          have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
          dsimp only [bIdx]
          rw [Nat.sub_mul, h_mul, Nat.one_mul]; omega
        simp only [this])
      (h_idxIn := by
        apply OracleStatement.idx_eq
        ext; simp?)
      (h_idxOut := by
        apply OracleStatement.idx_eq
        ext
        simp? [Fin.val_last]
        have : bIdx * ϑ + ϑ = ℓ := by
          have h_div : ϑ ∣ ℓ := hdiv.out
          have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
          have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
          dsimp only [bIdx]
          rw [Nat.sub_mul, h_mul, Nat.one_mul]; omega
        simp only [this])
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        ext; simp?)
      (h_ostmtOut := by
        apply OracleStatement.heq_of_fin_eq
        ext
        simp only [Fin.val_last]
        have : bIdx * ϑ + ϑ = ℓ := by
          have h_div : ϑ ∣ ℓ := hdiv.out
          have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
          have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
          dsimp only [bIdx]
          rw [Nat.sub_mul, h_mul, Nat.one_mul]; omega
        simp only [this])
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
  V

@[reducible]
def sumcheckFoldOracleVerifier :=
  let nonLastBlocksOracleVerifier := nonLastBlocksOracleVerifier (L := L)
    𝔽q β (mp := mp) (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let lastOracleVerifier := lastBlockOracleVerifier 𝔽q β
    (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let sumcheckFoldOV : OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
     :=
    (OracleVerifier.append (oSpec := []ₒ)
      (V₁ := nonLastBlocksOracleVerifier)
      (V₂ := lastOracleVerifier)
    ).castInOut
      (h_stmtIn := by
        apply Statement.of_fin_eq
        apply fin_zero_mul_eq)
      (h_stmtOut := by rfl)
      (h_idxIn := by
        apply OracleStatement.idx_eq
        apply fin_zero_mul_eq)
      (h_idxOut := by rfl)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        apply fin_zero_mul_eq)
      (h_ostmtOut := by rfl)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        ext; simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod])
  sumcheckFoldOV

end composedOracleVerifiers

section composedOracleRedutions

def nonLastSingleBlockOracleReduction (bIdx : Fin (ℓ / ϑ - 1)) :=
  let _ := mp
  let _ := 𝓑
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i : Fin (ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let wit := fun i : Fin (ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleReduction :=
    OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (Wit := wit) (m := ϑ - 1)
      (pSpec := fun _ => pSpecFoldRelay (L := L))
      (R := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ
            ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
          isNeCommitmentRound (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := ϑ) bIdx
            (x := i.val) (hx := by omega)
        exact foldRelayOracleReduction (L := L) 𝔽q β (mp := mp)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
          (i := ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) hNCR
      )
  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv : Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n := ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq : fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ : ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega
  let lastOracleReduction := foldCommitOracleReduction 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
    (hCR := isCommitmentRoundOfNonLastBlock (𝓡 := 𝓡) (r := r) bIdx)
  let nonLastSingleBlockReduction :=
    OracleReduction.append (oSpec := []ₒ)
      (Stmt₁ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m := ℓ) (h₁ := by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Stmt₂ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Stmt₃ := Statement (L := L) (ℓ := ℓ) Context ⟨(bIdx + 1) * ϑ,
        bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m := ℓ) (h₁ := by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (Wit₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Wit₃ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m := ℓ) (h₁ := by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (OStmt₂ := OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmt₃ := OracleStatement 𝔽q β ϑ ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec₁ := pSpecFoldRelaySequence (L := L) (n := ϑ - 1))
      (pSpec₂ := pSpecFoldCommit 𝔽q β ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (R₁ := firstFoldRelayRoundsOracleReduction.castOutSimple (h_stmt := by rfl) (h_ostmt := by rfl)
        (h_wit := by rfl))
      (R₂ := OracleReduction.castInOut (R := lastOracleReduction)
        (StmtIn₁ := (Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
        (StmtIn₂ := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
        (StmtOut₁ := Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
        (StmtOut₂ := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
        (OStmtIn₁ := (OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
        (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
        (OStmtOut₁ := OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
        (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ + 1)))
        (WitIn₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc)
        (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
        (WitOut₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
        (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ + 1)))
        (pSpec := pSpecFoldCommit 𝔽q β ⟨↑bIdx * ϑ + (ϑ - 1), h1⟩)
        (h_stmtIn := by
          apply Statement.of_fin_eq
          simp only [Fin.castSucc, Fin.castAdd_mk])
        (h_stmtOut := by
          apply Statement.of_fin_eq
          ext; simp only [Fin.succ_mk]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_idxIn := by
          apply OracleStatement.idx_eq
          simp only [Fin.castSucc, Fin.castAdd_mk])
        (h_idxOut := by
          apply OracleStatement.idx_eq
          ext; simp only [Fin.succ_mk]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_ostmtIn := by
          apply OracleStatement.heq_of_fin_eq
          simp only [Fin.castSucc, Fin.castAdd_mk])
        (h_ostmtOut := by
          apply OracleStatement.heq_of_fin_eq
          ext; simp only [Fin.succ_mk]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_witIn := by
          apply Witness.of_fin_eq
          simp only [Fin.castSucc, Fin.castAdd_mk])
        (h_witOut := by
          apply Witness.of_fin_eq
          ext; simp only [Fin.succ_mk]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_Oₛᵢ := by
          apply instOracleStatementBinaryBasefold_heq_of_fin_eq
          ext; simp only [Fin.castSucc, Fin.castAdd_mk])
      )
  nonLastSingleBlockReduction

def nonLastBlocksOracleReduction :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, by omega⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨0 * ϑ, by omega⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨0 * ϑ, by omega⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context ⟨(ℓ / ϑ - 1) * ϑ, by
      apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨(ℓ / ϑ - 1) * ϑ, by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨(ℓ / ϑ - 1) * ϑ, by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (pSpec := pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let _ := mp
  let _ := 𝓑
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i : Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i : Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let res := OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt) (Wit := wit)
      (pSpec := fun (bIdx : Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ) bIdx)
      (R := fun bIdx => nonLastSingleBlockOracleReduction (L := L) 𝔽q β (mp := mp)
        (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (bIdx := bIdx))
  res

def lastBlockOracleReduction :=
  let _ := 𝓑
  have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx := by omega)⟩
  let oStmt := fun i : Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx := by omega)⟩
  let wit := fun i : Fin (ϑ + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx := by omega)⟩
  let V : OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L := L) (ϑ := ϑ)) := by
      let cur := OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := stmt)
        (OStmt := oStmt)
        (Wit := wit)
        (pSpec := fun _ => pSpecFoldRelay (L := L))
        (R := fun i => by
          have hNCR : ¬ isCommitmentRound ℓ ϑ
              ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact foldRelayOracleReduction (L := L) 𝔽q β (mp := mp)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑 := 𝓑) (i := ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) hNCR
        )
      exact OracleReduction.castInOut (R := cur)
        (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
        (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
        (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) ⟨bIdx * ϑ, by
            apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x := 0) (hx := by omega)⟩)
        (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
        (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
        (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (Fin.last ℓ))
        (pSpec := pSpecLastBlock (L := L) (ϑ := ϑ))
        (h_stmtIn := by
          apply Statement.of_fin_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
        (h_stmtOut := by
          apply Statement.of_fin_eq
          ext
          simp only [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp only [bIdx]
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp only [this])
        (h_idxIn := by
          apply OracleStatement.idx_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
        (h_idxOut := by
          apply OracleStatement.idx_eq
          ext
          simp only [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp only [bIdx]
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp only [this])
        (h_ostmtIn := by
          apply OracleStatement.heq_of_fin_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
        (h_ostmtOut := by
          apply OracleStatement.heq_of_fin_eq
          ext
          simp only [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp only [bIdx]
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp only [this])
        (h_witIn := by
          apply Witness.of_fin_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
        (h_witOut := by
          apply Witness.of_fin_eq
          ext
          simp only [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp only [this])
        (h_Oₛᵢ := by
          apply instOracleStatementBinaryBasefold_heq_of_fin_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
  V

def sumcheckFoldOracleReduction : OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      0)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ)
      (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)) :=
  OracleReduction.append (oSpec := []ₒ)
    (pSpec₁ := pSpecNonLastBlocks 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecLastBlock (L := L) (ϑ := ϑ))
    (R₁ := nonLastBlocksOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (ϑ := ϑ))
    (R₂ := lastBlockOracleReduction 𝔽q β (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (ϑ := ϑ)).castInOut
      (h_stmtIn := by
        apply Statement.of_fin_eq
        apply fin_zero_mul_eq)
      (h_stmtOut := by rfl)
      (h_witIn := by
        apply Witness.of_fin_eq
        apply fin_zero_mul_eq)
      (h_witOut := by rfl)
      (h_idxIn := by
        apply OracleStatement.idx_eq
        apply fin_zero_mul_eq)
      (h_idxOut := by rfl)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        apply fin_zero_mul_eq)
      (h_ostmtOut := by rfl)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        ext; simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod])

end composedOracleRedutions

section SecurityProps

variable {σ : Type} {init : ProbComp σ}
  {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Perfect completeness for a single non-last block -/
lemma nonLastSingleBlockOracleReduction_perfectCompleteness
    (hInit : NeverFail init) (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (pSpec := pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ) (h₁:=by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (oracleReduction := nonLastSingleBlockOracleReduction 𝔽q β (ϑ := ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) bIdx) := by
  sorry

/-! Perfect completeness for the last block -/
lemma lastBlockOracleReduction_perfectCompleteness (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (pSpec := pSpecLastBlock (L := L) (ϑ := ϑ))
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (oracleReduction := lastBlockOracleReduction 𝔽q β (mp := mp) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)) := by
  sorry

/-! RBR knowledge error for last block: seqCompose of foldRelay over ϑ rounds. -/
noncomputable def lastBlockRbrKnowledgeError
    (k : (pSpecLastBlock (L := L) (ϑ := ϑ)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨(ℓ / ϑ - 1) * ϑ + ij.1, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ ij.1⟩ ij.2

/-! Perfect completeness for the core interaction oracle reduction -/
theorem sumcheckFoldOracleReduction_perfectCompleteness (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (mp := mp) (𝓑 := 𝓑))
      (init := init)
      (impl := impl) := by
  sorry
theorem lastBlockOracleVerifier_rbrKnowledgeSoundness :
    OracleVerifier.rbrKnowledgeSoundness init impl
      (roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) ⟨(ℓ / ϑ - 1) * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (lastBlockOracleVerifier 𝔽q β (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (rbrKnowledgeError := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-! The commitment-round index inside a non-last block. -/
def nonLastSingleBlockCommitIdx (bIdx : Fin (ℓ / ϑ - 1)) : Fin ℓ :=
  ⟨bIdx * ϑ + (ϑ - 1), by
    let fv : Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n := ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    change bIdx.val * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  ⟩

/-! RBR knowledge error for the fold-relay prefix inside one non-last block. -/
noncomputable def nonLastSingleBlockFoldRelayRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1))
    (k : (pSpecFoldRelaySequence (L := L) (n := ϑ - 1)).ChallengeIdx) : ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  foldRelayKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + ij.1, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx ij.1⟩ ij.2

/-! RBR knowledge error for one non-last block (fold-relay prefix + fold-commit suffix). -/
noncomputable def nonLastSingleBlockRbrKnowledgeError (bIdx : Fin (ℓ / ϑ - 1))
    (k : (pSpecFullNonLastBlock 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (nonLastSingleBlockFoldRelayRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx)
    (foldCommitKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := nonLastSingleBlockCommitIdx (ℓ := ℓ) (ϑ := ϑ) bIdx))
    (ChallengeIdx.sumEquiv.symm k)

/-! RBR KS for one non-last block verifier. -/
theorem nonLastSingleBlockOracleVerifier_rbrKnowledgeSoundness
    (bIdx : Fin (ℓ / ϑ - 1)) :
    (nonLastSingleBlockOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) bIdx).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ) (h₁:=by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩ : Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (rbrKnowledgeError := nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) bIdx) := by
  sorry

/-! RBR knowledge error for non-last blocks: seqCompose over non-last blocks. -/
noncomputable def nonLastBlocksRbrKnowledgeError
    (k : (pSpecNonLastBlocks 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) :
    ℝ≥0 :=
  let ij := seqComposeChallengeIdxToSigma k
  nonLastSingleBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ij.1 ij.2

/-! RBR KS for non-last blocks verifier (seqCompose of nonLastSingleBlock). -/
theorem nonLastBlocksOracleVerifier_rbrKnowledgeSoundness :
    (nonLastBlocksOracleVerifier 𝔽q β (mp := mp) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (rbrKnowledgeError := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

/-! RBR knowledge error for sumcheck-fold: append of non-last blocks and last block. -/
noncomputable def sumcheckFoldKnowledgeError (j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := nonLastBlocksRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (g := lastBlockRbrKnowledgeError (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (ChallengeIdx.sumEquiv.symm j)

/-! Round-by-round knowledge soundness for the sumcheck fold oracle verifier.
    Proof: append (nonLastBlocks, lastBlock) has RBR KS by append_rbrKnowledgeSoundness;
    then castInOut preserves it; finally rbrKnowledgeSoundness_of_eq_error gives the flat
    sumcheckFoldKnowledgeError. The error equality (flat = Sum.elim form) remains. -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β (mp := mp) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ) )
      (rbrKnowledgeError := sumcheckFoldKnowledgeError (L := L) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  sorry

end SecurityProps

end IteratedSumcheckFoldComposition
end ComponentReductions

section CoreInteractionPhaseReduction

@[reducible]
def coreInteractionOracleVerifier :
  OracleVerifier (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleVerifier.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L := L))
    (V₁ := sumcheckFoldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := BBF_SumcheckMultiplierParam))
    (V₂ := finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))

/-! The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :
    OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (StmtOut := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (WitOut := Unit)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecCoreInteraction 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  OracleReduction.append (oSpec := []ₒ)
    (Stmt₁ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ := ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) 0)
    (Wit₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) (Fin.last ℓ))
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) (mp := BBF_SumcheckMultiplierParam))
    (R₂ := finalSumcheckOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-! Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) 0)
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑))
      (init := init)
      (impl := impl) := by
  sorry

noncomputable def coreInteractionOracleRbrKnowledgeError (j : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-! Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)) := by
  sorry

/-! The final-sumcheck step has only a `P_to_V` round, so there are no verifier challenges
(`ChallengeIdx` is empty). -/
lemma challengeIdx_pSpecFinalSumcheckStep_isEmpty :
    IsEmpty (ChallengeIdx (pSpecFinalSumcheckStep (L := L))) where
  false := fun ⟨i, hdir⟩ => by
    have hdir₁ : (pSpecFinalSumcheckStep (L := L)).dir i = Direction.P_to_V := by
      fin_cases i <;> simp [pSpecFinalSumcheckStep]
    rw [hdir₁] at hdir
    exact absurd hdir (by decide : Direction.P_to_V ≠ Direction.V_to_P)

lemma finalSumcheckKnowledgeError_sum_eq_zero :
    (∑ i : (pSpecFinalSumcheckStep (L := L)).ChallengeIdx, finalSumcheckKnowledgeError i) = (0 : ℝ≥0) := by
  classical
  have hu : (Finset.univ : Finset (ChallengeIdx (pSpecFinalSumcheckStep (L := L)))) = ∅ := by
    ext x
    exact False.elim (challengeIdx_pSpecFinalSumcheckStep_isEmpty.false x)
  simp [hu]

/-! ### Arithmetic for `sumcheckFoldKnowledgeError_le` (bad-event cardinality aggregation) -/

/-- After reindexing fold rounds by blocks, exponents are `ℓ + 𝓡 - u * ϑ` for
    `u = 1, …, B - 1` with `B = ℓ / ϑ`. -/
def innerPowSum (B ϑ 𝓡 ℓ : ℕ) : ℕ :=
  ∑ u ∈ Finset.Icc 1 (B - 1), 2 ^ (ℓ + 𝓡 - u * ϑ)

/-- Total `ℕ` bad-event cardinality summed across fold RBR charges (before dividing by `|L|`). -/
def foldBadEventCardSum (ℓ ϑ 𝓡 : ℕ) : ℕ :=
  let B := ℓ / ϑ
  ϑ * innerPowSum B ϑ 𝓡 ℓ + ϑ * 2 ^ 𝓡

/-- Helper: `x < 2^x` for all natural `x`, used in the geometric-series bound for fold bad events. -/
lemma x_lt_two_pow (x : ℕ) : x < 2 ^ x := by
  induction x with
  | zero => simp
  | succ x IH =>
    calc
      x + 1 < 2 ^ x + 1 := Nat.add_lt_add_right IH 1
      _ ≤ 2 ^ x + 2 ^ x := Nat.add_le_add_left (by omega) _
      _ = 2 ^ (x + 1) := by ring

lemma sum_powers (x B : ℕ) (hB : 1 ≤ B) :
  x * ∑ y ∈ Finset.range B, 2 ^ (y * x) ≤ 2 ^ (B * x) - 2 ^ x + x := by
  induction B with
  | zero => omega
  | succ B IH =>
    by_cases hB0 : B = 0
    · subst hB0
      simp
    · have hB_ge_1 : 1 ≤ B := by omega
      have IH_inst := IH hB_ge_1
      have h_sum : x * ∑ y ∈ Finset.range (B + 1), 2 ^ (y * x)
        = x * 2 ^ (B * x) + x * ∑ y ∈ Finset.range B, 2 ^ (y * x) := by
        rw [Finset.range_add_one, Finset.sum_insert (by simp only [mem_range, lt_self_iff_false,
          not_false_eq_true]), mul_add, add_comm]
      have h3 : (x + 1) * 2 ^ (B * x) ≤ 2 ^ ((B + 1) * x) := by
        have h_pow : 2 ^ ((B + 1) * x) = 2 ^ x * 2 ^ (B * x) := by
          have : (B + 1) * x = x + B * x := by ring
          rw [this, pow_add]
        rw [h_pow]
        have h_x_le : x + 1 ≤ 2 ^ x := x_lt_two_pow x
        exact Nat.mul_le_mul_right (2 ^ (B * x)) h_x_le
      have h4 : x * 2 ^ (B * x) + 2 ^ (B * x) = (x + 1) * 2 ^ (B * x) := by ring
      have h5 : 2 ^ x ≤ 2 ^ (B * x) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      omega

/-! Auxiliary reindexings for `sumcheckFoldKnowledgeError_displayMass_le`. -/

lemma sum_Icc_one_pred_sub_reindex {B ϑ : ℕ} (f : ℕ → ℕ) (hB : 1 ≤ B) :
    ∑ u ∈ Finset.Icc 1 (B - 1), f ((B - u) * ϑ) =
      ∑ w ∈ Finset.Icc 1 (B - 1), f (w * ϑ) := by
  classical
  refine Finset.sum_bij (fun u hu => B - u) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_Icc] at hu ⊢
    constructor <;> omega
  · intro u1 hu1 u2 hu2 heq
    simp only [Finset.mem_Icc] at hu1 hu2
    have hu1B : u1 ≤ B := by omega
    have hu2B : u2 ≤ B := by omega
    calc
      u1 = B - (B - u1) := (Nat.sub_sub_self hu1B).symm
      _ = B - (B - u2) := congrArg (Nat.sub B) heq
      _ = u2 := Nat.sub_sub_self hu2B
  · intro w hw
    simp only [Finset.mem_Icc] at hw ⊢
    refine ⟨B - w, ?_, ?_⟩
    · constructor <;> omega
    · have hwB : w ≤ B := by omega
      exact Nat.sub_sub_self hwB
  · intro u hu
    rfl

lemma sum_range_pred_eq_sum_Icc {B : ℕ} (f : ℕ → ℕ) (hB : 1 ≤ B) :
    ∑ j ∈ Finset.range (B - 1), f (j + 1) = ∑ u ∈ Finset.Icc 1 (B - 1), f u := by
  classical
  refine Finset.sum_bij (fun j hj => j + 1) ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc]; omega
  · intro j1 hj1 j2 hj2 heq
    simp only [Finset.mem_range] at hj1 hj2
    exact Nat.succ.inj heq
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    refine ⟨w - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · exact Nat.sub_add_cancel hw.1
  · intro j hj; rfl

lemma sum_fin_eq_sum_Icc_pred {B : ℕ} (f : ℕ → ℕ) (hB : 1 ≤ B) :
    (∑ x : Fin (B - 1), f (x.val + 1)) = ∑ u ∈ Finset.Icc 1 (B - 1), f u := by
  rw [Finset.sum_fin_eq_sum_range]
  trans (∑ j ∈ Finset.range (B - 1), f (j + 1))
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  exact sum_range_pred_eq_sum_Icc f hB

/-- `∑_{w=1}^{B-1} f w + f 0 = ∑_{v=0}^{B-1} f v` when `B ≥ 1`. -/
lemma sum_range_eq_Icc_add_zero {B : ℕ} (f : ℕ → ℕ) (hB : 1 ≤ B) :
    (∑ w ∈ Finset.Icc 1 (B - 1), f w) + f 0 = ∑ v ∈ Finset.range B, f v := by
  classical
  cases B with
  | zero => simp at hB
  | succ B' =>
    simp only [Nat.succ_sub_succ, Nat.sub_zero]
    have hmid' := sum_range_pred_eq_sum_Icc (f := f) (B := Nat.succ B') hB
    simp only [Nat.succ_sub_succ, Nat.sub_zero] at hmid'
    rw [Finset.sum_range_succ' (f := f) (n := B'), ← hmid', add_comm]

lemma innerPowSum_add_two_pow_eq_mul_sum_range {ℓ ϑ 𝓡 B : ℕ} [NeZero ℓ]
    (hBϑ : B * ϑ = ℓ) (hϑ : 0 < ϑ) :
    innerPowSum B ϑ 𝓡 ℓ + 2 ^ 𝓡 = 2 ^ 𝓡 * ∑ v ∈ Finset.range B, 2 ^ (v * ϑ) := by
  classical
  have hB : 1 ≤ B := by
    rcases B with _ | b
    · rw [Nat.zero_mul] at hBϑ
      exact absurd hBϑ.symm (NeZero.ne ℓ)
    · exact Nat.succ_le_succ (Nat.zero_le b)
  rw [innerPowSum]
  have hpow (u : ℕ) (hu : u ∈ Finset.Icc 1 (B - 1)) :
      2 ^ (ℓ + 𝓡 - u * ϑ) = 2 ^ 𝓡 * 2 ^ ((B - u) * ϑ) := by
    simp only [Finset.mem_Icc] at hu
    have h_le_ub : u ≤ B := by omega
    have hub : u * ϑ ≤ B * ϑ := Nat.mul_le_mul_right ϑ h_le_ub
    have hexp : ℓ + 𝓡 - u * ϑ = 𝓡 + (B - u) * ϑ := by
      rw [show ℓ + 𝓡 = B * ϑ + 𝓡 by rw [← hBϑ]]
      rw [add_comm (B * ϑ)]
      rw [Nat.add_sub_assoc hub 𝓡]
      rw [← Nat.mul_sub_right_distrib, add_comm]
    rw [hexp, pow_add, mul_comm]
  have h_reidx :
      ∑ u ∈ Finset.Icc 1 (B - 1), 2 ^ ((B - u) * ϑ) = ∑ w ∈ Finset.Icc 1 (B - 1), 2 ^ (w * ϑ) :=
    sum_Icc_one_pred_sub_reindex (fun k => 2 ^ k) hB
  have hsum_eq :
      ∑ u ∈ Finset.Icc 1 (B - 1), 2 ^ (ℓ + 𝓡 - u * ϑ) =
        ∑ u ∈ Finset.Icc 1 (B - 1), 2 ^ 𝓡 * 2 ^ ((B - u) * ϑ) :=
    Finset.sum_congr rfl fun u hu => hpow u hu
  rw [hsum_eq]
  simp_rw [← Finset.mul_sum]
  rw [h_reidx]
  have hmid :
      2 ^ 𝓡 * ∑ w ∈ Finset.Icc 1 (B - 1), 2 ^ (w * ϑ) + 2 ^ 𝓡 =
        2 ^ 𝓡 * (∑ w ∈ Finset.Icc 1 (B - 1), 2 ^ (w * ϑ) + 1) := by
    nth_rw 2 [show 2 ^ 𝓡 = 2 ^ 𝓡 * 1 from by rw [Nat.mul_one]]
    rw [← Nat.mul_add]
  rw [hmid]
  have hr := sum_range_eq_Icc_add_zero (fun v => 2 ^ (v * ϑ)) hB
  simp only [Nat.mul_zero, pow_zero, Nat.zero_mul] at hr
  exact congrArg (fun z => 2 ^ 𝓡 * z) hr

lemma foldBadEventCardSum_le_two_pow :
    foldBadEventCardSum ℓ ϑ 𝓡 ≤ 2 ^ (ℓ + 𝓡) := by
  classical
  set B := ℓ / ϑ with hBdef
  have hBϑ : B * ϑ = ℓ := by rw [hBdef]; exact Nat.div_mul_cancel hdiv.out
  have hϑ : 0 < ϑ := Nat.pos_of_neZero ϑ
  have hB1 : 1 ≤ B := by
    rcases B with _ | b
    · rw [Nat.zero_mul] at hBϑ
      exact absurd hBϑ.symm (NeZero.ne ℓ)
    · exact Nat.succ_le_succ (Nat.zero_le b)
  have hinner :=
    innerPowSum_add_two_pow_eq_mul_sum_range (ℓ := ℓ) (ϑ := ϑ) (𝓡 := 𝓡) (B := B) hBϑ hϑ
  unfold foldBadEventCardSum
  dsimp only
  rw [← mul_add, hinner]
  have h1 := sum_powers ϑ B hB1
  have hmono :
      2 ^ 𝓡 * (ϑ * ∑ v ∈ Finset.range B, 2 ^ (v * ϑ)) ≤
        2 ^ 𝓡 * (2 ^ (B * ϑ) - 2 ^ ϑ + ϑ) :=
    Nat.mul_le_mul_left (2 ^ 𝓡) h1
  have hϑle : 2 ^ (B * ϑ) - 2 ^ ϑ + ϑ ≤ 2 ^ (B * ϑ) := by
    have hϑ : ϑ ≤ 2 ^ ϑ := Nat.le_of_lt (x_lt_two_pow ϑ)
    have h_exp : ϑ ≤ B * ϑ := by
      calc
        ϑ = 1 * ϑ := (Nat.one_mul ϑ).symm
        _ ≤ B * ϑ := Nat.mul_le_mul_right ϑ hB1
    have hmon : 2 ^ ϑ ≤ 2 ^ (B * ϑ) :=
      (Nat.pow_le_pow_iff_right (Nat.lt_succ_self 1)).2 h_exp
    calc
      2 ^ (B * ϑ) - 2 ^ ϑ + ϑ ≤ 2 ^ (B * ϑ) - 2 ^ ϑ + 2 ^ ϑ := Nat.add_le_add_left hϑ _
      _ = 2 ^ (B * ϑ) := Nat.sub_add_cancel hmon
  have h2 := Nat.mul_le_mul_left (2 ^ 𝓡) hϑle
  have h3 :
      ϑ * 2 ^ 𝓡 * ∑ v ∈ Finset.range B, 2 ^ (v * ϑ) =
        2 ^ 𝓡 * (ϑ * ∑ v ∈ Finset.range B, 2 ^ (v * ϑ)) := by
    ring
  rw [← Nat.mul_assoc, h3]
  calc
    2 ^ 𝓡 * (ϑ * ∑ v ∈ Finset.range B, 2 ^ (v * ϑ))
        ≤ 2 ^ 𝓡 * (2 ^ (B * ϑ) - 2 ^ ϑ + ϑ) := hmono
    _ ≤ 2 ^ 𝓡 * 2 ^ (B * ϑ) := h2
    _ = 2 ^ (𝓡 + B * ϑ) := by rw [← pow_add]
    _ = 2 ^ (ℓ + 𝓡) := by congr 1; rw [hBϑ, add_comm]

lemma foldBadEventCardSum_eq_displaySums
    (h_nonLastDest_le_ℓ : ∀ x : Fin (ℓ / ϑ - 1), x.val * ϑ + ϑ ≤ ℓ)
    (h_lastDest_le_ℓ : (ℓ / ϑ - 1) * ϑ + ϑ ≤ ℓ) :
    foldBadEventCardSum ℓ ϑ 𝓡 =
      (∑ x : Fin (ℓ / ϑ - 1), ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
        + (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
        + (∑ _ : Fin ϑ, 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ))) := by
  classical
  let B := ℓ / ϑ
  have hB1 : 1 ≤ B := by
    rcases h : B with _ | b
    · have hℓ0 : ℓ = 0 := by
        calc
          ℓ = B * ϑ := (Nat.div_mul_cancel hdiv.out).symm
          _ = 0 * ϑ := by rw [h]
          _ = 0 := by rw [Nat.zero_mul]
      exact absurd hℓ0 (NeZero.ne ℓ)
    · exact Nat.succ_le_succ (Nat.zero_le b)
  have h_lastQuot_pos : 0 < ℓ / ϑ := by
    by_contra hq
    have hq0 : ℓ / ϑ = 0 := Nat.eq_zero_of_not_pos hq
    have hdiv_mul : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
    rw [hq0, zero_mul] at hdiv_mul
    exact (Nat.ne_of_gt (Nat.pos_of_neZero ℓ)) hdiv_mul.symm
  have h_boundary : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
    calc
      (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by
        rw [Nat.add_mul, one_mul]
      _ = (ℓ / ϑ) * ϑ := by
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt h_lastQuot_pos)]
      _ = ℓ := Nat.div_mul_cancel hdiv.out
  have hidx (x : Fin (ℓ / ϑ - 1)) : x.val * ϑ + ϑ = (x.val + 1) * ϑ := by
    rw [Nat.add_mul, one_mul]
  have hA :
      (∑ x : Fin (ℓ / ϑ - 1), ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) =
        (ϑ - 1) * (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) := by
    classical
    -- Expand to sums on `Finset.univ`, use `Finset.sum_const` on the inner sum, then
    -- `Finset.mul_sum` to factor `(ϑ - 1)`.
    change
      (Finset.univ : Finset (Fin (ℓ / ϑ - 1))).sum (fun x =>
          (Finset.univ : Finset (Fin (ϑ - 1))).sum fun _ =>
            2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) =
        (ϑ - 1) *
          (Finset.univ : Finset (Fin (ℓ / ϑ - 1))).sum (fun x => 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
    trans
      (Finset.univ : Finset (Fin (ℓ / ϑ - 1))).sum (fun x =>
        ((ϑ - 1) : ℕ) * 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
    · refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_comm]
    rw [← Finset.mul_sum]
  have hC :
      ∑ _ : Fin ϑ, 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) = ϑ * 2 ^ 𝓡 := by
    rw [h_boundary]
    have hsub : ℓ + 𝓡 - ℓ = 𝓡 := Nat.add_sub_self_left ℓ 𝓡
    simp_rw [hsub]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hT :
      (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) = innerPowSum B ϑ 𝓡 ℓ := by
    simp_rw [hidx]
    dsimp [B]
    simp only [innerPowSum]
    exact sum_fin_eq_sum_Icc_pred (B := B) (fun u => 2 ^ (ℓ + 𝓡 - u * ϑ)) hB1
  unfold foldBadEventCardSum
  dsimp only
  have hRHS :
      (∑ x : Fin (ℓ / ϑ - 1), ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
        + (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
        + (∑ _ : Fin ϑ, 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)))
        = ϑ * innerPowSum B ϑ 𝓡 ℓ + ϑ * 2 ^ 𝓡 := by
    rw [hA, hT, hC]
    have hϑ_pos : 0 < ϑ := Nat.pos_of_neZero ϑ
    have hadd : (ϑ - 1) + 1 = ϑ := Nat.sub_add_cancel hϑ_pos
    let i := innerPowSum B ϑ 𝓡 ℓ
    have hip : (ϑ - 1) * i + i = ϑ * i := by
      nth_rw 2 [← Nat.one_mul i]
      rw [← Nat.add_mul]
      exact congrArg (fun t : ℕ => t * i) hadd
    have hperm : (ϑ - 1) * i + i + ϑ * 2 ^ 𝓡 = i + (ϑ - 1) * i + ϑ * 2 ^ 𝓡 :=
      congrArg (fun t : ℕ => t + ϑ * 2 ^ 𝓡) (Nat.add_comm ((ϑ - 1) * i) i)
    have hip' : i + (ϑ - 1) * i = ϑ * i := by
      rw [Nat.add_comm]
      exact hip
    rw [hperm, hip']
  exact hRHS.symm

/-- Display inequality for fold knowledge-error charges written as `2/|L| + |S^k|/|L|`.

The side conditions `h_nonLastDest_le_ℓ` and `h_lastDest_le_ℓ` ensure each destination index
`b·ϑ + ϑ` in groups A and B lies below `ℓ` (matching ϑ-block boundaries when `ϑ ∣ ℓ`), and the
last-block boundary reaches `ℓ`.

Under `AdditiveNTT.Comp.compSDomain_card` and `hF₂`, with `|𝔽q| = 2`, one has `|S^k| = 2^{ℓ+𝓡 - k}`. The same regrouping
as in `sumcheckFoldKnowledgeError_le` reads informally as:

```
(∑_{b : Fin(ℓ/ϑ-1)} ∑_{i : Fin(ϑ-1)}  (2/|L| + |S^{bϑ+ϑ}|/|L|))   -- A: relay folds in non-last blocks
+ (∑_{b : Fin(ℓ/ϑ-1)}                  (2/|L| + |S^{bϑ+ϑ}|/|L|))   -- B: commit folds in non-last blocks
+ (∑_{i : Fin ϑ}                      (2/|L| + |S^ℓ|/|L|))         -- C: relay folds in the last block
  ≤  2·ℓ/|L|  +  2^{ℓ+𝓡}/|L|.
```

Proof summary:
- rewrite `Fintype.card (sDomain …)` with `AdditiveNTT.Comp.compSDomain_card`, then replace `Fintype.card 𝔽q` using `hF₂`;
- split each summand with `Finset.sum_add_distrib`, separating the `2/|L|` part from powers `2^{ℓ+𝓡-k}/|L|`;
- the `2/|L|` contribution totals `2·ℓ/|L|` (there are exactly `ℓ` challenges across groups A–C);
- bad-event numerators assemble to `foldBadEventCardSum` (`foldBadEventCardSum_eq_displaySums`), bounded by
  `2^{ℓ+𝓡}` through `foldBadEventCardSum_le_two_pow` and the geometric estimate `sum_powers`.

The cardinality side of `foldBadEventCardSum_le_two_pow` is driven by how often each block boundary
`bIdx·ϑ + ϑ` appears: group A repeats `(ϑ - 1)` relay rounds per non-last block, group B one commit per
non-last block, and group C collects the last-block relay rounds ending at exponent `𝓡` on domain
`ℓ`.
See `innerPowSum` and `sum_powers` above for the reindexing.
-/
lemma sumcheckFoldKnowledgeError_displayMass_le
    (h_nonLastDest_le_ℓ : ∀ x : Fin (ℓ / ϑ - 1), x.val * ϑ + ϑ ≤ ℓ)
    (h_lastDest_le_ℓ : (ℓ / ϑ - 1) * ϑ + ϑ ≤ ℓ) :
    (∑ x : Fin (ℓ / ϑ - 1), ∑ x_1 : Fin (ϑ - 1),
        ((2 : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
              ⟨x.val * ϑ + ϑ, by
                have hle := h_nonLastDest_le_ℓ x
                omega⟩) : ℝ≥0) / (Fintype.card L : ℝ≥0)))
      +
      (∑ x : Fin (ℓ / ϑ - 1),
        ((2 : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
              ⟨x.val * ϑ + ϑ, by
                have hle := h_nonLastDest_le_ℓ x
                omega⟩) : ℝ≥0) / (Fintype.card L : ℝ≥0)))
      +
      (∑ x : Fin ϑ,
        ((2 : ℝ≥0) / (Fintype.card L : ℝ≥0)
          + (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
              ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
                have _ := h_lastDest_le_ℓ
                omega⟩) : ℝ≥0) / (Fintype.card L : ℝ≥0)))
      ≤
    2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  classical
  have H_card : Fintype.card 𝔽q = 2 := hF₂.out
  have hcard_nonLast (x : Fin (ℓ / ϑ - 1)) :
      (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
        ⟨x.val * ϑ + ϑ, by
          have hle := h_nonLastDest_le_ℓ x
          omega⟩) : ℝ≥0)
      = (2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) : ℝ≥0) := by
    have hle := h_nonLastDest_le_ℓ x
    have hk : x.val * ϑ + ϑ < r := lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) hle
    have hkRate : x.val * ϑ + ϑ < ℓ + 𝓡:= by
      have hRpos : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
      exact lt_of_le_of_lt hle (Nat.lt_add_of_pos_right hRpos)
    have hNat :
        Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨x.val * ϑ + ϑ, hk⟩) =
          2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) := by
      calc
        Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨x.val * ϑ + ϑ, hk⟩)
            = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) :=
          by
            have hcard :=
              AdditiveNTT.Comp.compSDomain_card
                (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨x.val * ϑ + ϑ, hk⟩ hkRate
            simpa [sDomain, AdditiveNTT.Comp.compSDomain_eq_canonicalSDomain] using hcard
        _ = 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) := by rw [H_card]
    exact_mod_cast hNat
  have hcard_last :
      (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate)
        ⟨(ℓ / ϑ - 1) * ϑ + ϑ, by
          have hle := h_lastDest_le_ℓ
          omega⟩) : ℝ≥0)
      = (2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) : ℝ≥0) := by
    have hle := h_lastDest_le_ℓ
    have hk : (ℓ / ϑ - 1) * ϑ + ϑ < r := lt_r_of_le_ℓ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) hle
    have hkRate : (ℓ / ϑ - 1) * ϑ + ϑ < ℓ + 𝓡 := by
      have hRpos : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
      exact lt_of_le_of_lt hle (Nat.lt_add_of_pos_right hRpos)
    have hNat :
        Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨(ℓ / ϑ - 1) * ϑ + ϑ, hk⟩) =
          2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) := by
      calc
        Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨(ℓ / ϑ - 1) * ϑ + ϑ, hk⟩)
            = (Fintype.card 𝔽q) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) :=
          by
            have hcard :=
              AdditiveNTT.Comp.compSDomain_card
                (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
                (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨(ℓ / ϑ - 1) * ϑ + ϑ, hk⟩ hkRate
            simpa [sDomain, AdditiveNTT.Comp.compSDomain_eq_canonicalSDomain] using hcard
        _ = 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) := by rw [H_card]
    exact_mod_cast hNat
  simp_rw [hcard_nonLast, hcard_last]
  simp_rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  let Aconst : ℝ≥0 :=
      (↑(ℓ / ϑ) - 1) * ((↑ϑ - 1) * (2 / (Fintype.card L : ℝ≥0)))
        + ((↑(ℓ / ϑ) - 1) * (2 / (Fintype.card L : ℝ≥0)))
        + (↑ϑ * (2 / (Fintype.card L : ℝ≥0)))
  let Bbad : ℝ≥0 :=
      (∑ x : Fin (ℓ / ϑ - 1), (↑ϑ - 1) * (2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)))
        + (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0))
        + (↑ϑ * (2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)))
  let lhsExpr : ℝ≥0 :=
      (↑(ℓ / ϑ) - 1) * ((↑ϑ - 1) * (2 / (Fintype.card L : ℝ≥0)))
        + (∑ x : Fin (ℓ / ϑ - 1), (↑ϑ - 1) * (2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)))
        + (((↑(ℓ / ϑ) - 1) * (2 / (Fintype.card L : ℝ≥0)))
          + (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)))
        + (↑ϑ * (2 / (Fintype.card L : ℝ≥0))
          + ↑ϑ * (2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)))
  have h_lhsExpr : lhsExpr = Aconst + Bbad := by
    dsimp [lhsExpr, Aconst, Bbad]; ring
  change lhsExpr ≤ 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0)
  rw [h_lhsExpr]
  have hQuotPos : 0 < ℓ / ϑ := by
    by_contra hq
    have hq0 : ℓ / ϑ = 0 := Nat.eq_zero_of_not_pos hq
    have hmul : (ℓ / ϑ) * ϑ = ℓ := Nat.div_mul_cancel hdiv.out
    rw [hq0, zero_mul] at hmul
    exact (Nat.ne_of_gt (Nat.pos_of_neZero ℓ)) hmul.symm
  have hCoeffNat : (ℓ / ϑ - 1) * (ϑ - 1) + (ℓ / ϑ - 1) + ϑ = ℓ := by
    have hϑ_pos : 0 < ϑ := Nat.pos_of_neZero ϑ
    calc
      (ℓ / ϑ - 1) * (ϑ - 1) + (ℓ / ϑ - 1) + ϑ
          = (ℓ / ϑ - 1) * ((ϑ - 1) + 1) + ϑ := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = (ℓ / ϑ - 1) * ϑ + ϑ := by rw [Nat.sub_add_cancel hϑ_pos]
      _ = ((ℓ / ϑ - 1) + 1) * ϑ := by rw [Nat.add_mul, one_mul]
      _ = (ℓ / ϑ) * ϑ := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hQuotPos)]
      _ = ℓ := Nat.div_mul_cancel hdiv.out
  have hA :
      Aconst = 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    dsimp [Aconst]
    have hCoeff :
        (↑(ℓ / ϑ) - 1) * (↑ϑ - 1) + (↑(ℓ / ϑ) - 1) + ↑ϑ = (ℓ : ℝ≥0) := by
      exact_mod_cast hCoeffNat
    calc
      (↑(ℓ / ϑ) - 1) * ((↑ϑ - 1) * (2 / (Fintype.card L : ℝ≥0))) +
          ((↑(ℓ / ϑ) - 1) * (2 / (Fintype.card L : ℝ≥0))) +
          (↑ϑ * (2 / (Fintype.card L : ℝ≥0)))
          = ((↑(ℓ / ϑ) - 1) * (↑ϑ - 1) + (↑(ℓ / ϑ) - 1) + ↑ϑ) *
              (2 / (Fintype.card L : ℝ≥0)) := by ring
      _ = (ℓ : ℝ≥0) * (2 / (Fintype.card L : ℝ≥0)) := by rw [hCoeff]
      _ = 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0) := by ring
  rw [hA]
  have hB : Bbad ≤ (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
    have hcardL_pos : (0 : ℝ≥0) < (Fintype.card L : ℝ≥0) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card L)
    have h_mul_goal : Bbad * (Fintype.card L : ℝ≥0) ≤ (2 ^ (ℓ + 𝓡) : ℝ≥0) := by
      let hdis :
          foldBadEventCardSum ℓ ϑ 𝓡 =
            (∑ x : Fin (ℓ / ϑ - 1), ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
              + (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
              + (∑ _ : Fin ϑ, 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ))) :=
        foldBadEventCardSum_eq_displaySums h_nonLastDest_le_ℓ h_lastDest_le_ℓ
      let N1 :=
        (∑ x : Fin (ℓ / ϑ - 1), ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
      let N2 := (∑ x : Fin (ℓ / ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))
      let N3 := (∑ _ : Fin ϑ, 2 ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)))
      have hdis' : foldBadEventCardSum ℓ ϑ 𝓡 = N1 + N2 + N3 := hdis
      have hLne : (Fintype.card L : ℝ≥0) ≠ 0 := by
        norm_cast
        exact (Nat.pos_iff_ne_zero.mp Fintype.card_pos)
      have h_ident :
          Bbad * (Fintype.card L : ℝ≥0) = (foldBadEventCardSum ℓ ϑ 𝓡 : ℝ≥0) := by
        have hϑ1 : 1 ≤ ϑ := Nat.succ_le_of_lt (Nat.pos_of_neZero ϑ)
        have hcast_ϑsub :
            ((ϑ - 1 : ℕ) : ℝ≥0) = (↑ϑ : ℝ≥0) - 1 := by norm_cast
        have h_pow_cast (n : ℕ) :
            ((2 ^ n : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ n := by norm_cast
        dsimp [Bbad]
        -- Expand `(s₁ + s₂ + s₃) * |L|` and cancel each `/ |L|` factor.
        rw [add_mul, add_mul]
        have h_term (x : Fin (ℓ / ϑ - 1)) :
            ((↑ϑ : ℝ≥0) - 1) * ((2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0)) * (Fintype.card L : ℝ≥0)
              = ((↑ϑ : ℝ≥0) - 1) * (2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) := by
          rw [mul_assoc ((↑ϑ : ℝ≥0) - 1) ((2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0))
              (Fintype.card L),
            div_mul_cancel₀ ((2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) hLne]
        have h_term2 (x : Fin (ℓ / ϑ - 1)) :
            ((2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) / (Fintype.card L : ℝ≥0))
                * (Fintype.card L : ℝ≥0)
              = (2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) := by
          rw [div_mul_cancel₀ ((2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) hLne]
        have h_term3 :
            (↑ϑ * ((2 : ℝ≥0) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ))
                  / (Fintype.card L : ℝ≥0))) * (Fintype.card L : ℝ≥0)
              = ↑ϑ * (2 : ℝ≥0) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) := by
          rw [mul_assoc (↑ϑ : ℝ≥0) ((2 : ℝ≥0) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ)) / (Fintype.card L : ℝ≥0))
              (Fintype.card L),
            div_mul_cancel₀ ((2 : ℝ≥0) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ))) hLne]
        rw [Finset.sum_mul (s := Finset.univ), Finset.sum_mul (s := Finset.univ)]
        rw [Finset.sum_congr rfl (fun x _ => h_term x),
          Finset.sum_congr rfl (fun x _ => h_term2 x), h_term3]
        have hc :
            ((foldBadEventCardSum ℓ ϑ 𝓡 : ℕ) : ℝ≥0) = ((N1 + N2 + N3 : ℕ) : ℝ≥0) :=
          congrArg Nat.cast hdis'
        rw [hc, Nat.cast_add, Nat.cast_add]
        have hA_nat (x : Fin (ℓ / ϑ - 1)) :
            (ϑ - 1) * 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) =
              ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)) := by
          simp [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_comm]
        have hA :
            (∑ x : Fin (ℓ / ϑ - 1), ((↑ϑ : ℝ≥0) - 1) * (2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) = ↑N1 := by
          dsimp [N1]
          rw [Nat.cast_sum (R := ℝ≥0) (ι := Fin (ℓ / ϑ - 1)) (s := Finset.univ)
            (f := fun x : Fin (ℓ / ϑ - 1) =>
              ∑ _ : Fin (ϑ - 1), 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [← hA_nat x, Nat.cast_mul, hcast_ϑsub, h_pow_cast]
        have hB :
            (∑ x : Fin (ℓ / ϑ - 1), (2 : ℝ≥0) ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ))) = ↑N2 := by
          dsimp [N2]
          rw [Nat.cast_sum (R := ℝ≥0) (ι := Fin (ℓ / ϑ - 1)) (s := Finset.univ)
            (f := fun x : Fin (ℓ / ϑ - 1) => 2 ^ (ℓ + 𝓡 - (x.val * ϑ + ϑ)))]
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [h_pow_cast]
        have hC_nat : N3 = ϑ * 2 ^ 𝓡 := by
          dsimp [N3]
          have hb : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
            calc
              (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by rw [Nat.add_mul, one_mul]
              _ = (ℓ / ϑ) * ϑ := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hQuotPos)]
              _ = ℓ := Nat.div_mul_cancel hdiv.out
          have hsub : ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ) = 𝓡 := by rw [hb, Nat.add_sub_self_left]
          simp_rw [hsub]
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        have hC :
            (↑ϑ * (2 : ℝ≥0) ^ (ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ))) = ↑N3 := by
          have hexp : ℓ + 𝓡 - ((ℓ / ϑ - 1) * ϑ + ϑ) = 𝓡 := by
            have hb : (ℓ / ϑ - 1) * ϑ + ϑ = ℓ := by
              calc
                (ℓ / ϑ - 1) * ϑ + ϑ = ((ℓ / ϑ - 1) + 1) * ϑ := by rw [Nat.add_mul, one_mul]
                _ = (ℓ / ϑ) * ϑ := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hQuotPos)]
                _ = ℓ := Nat.div_mul_cancel hdiv.out
            rw [hb, Nat.add_sub_self_left]
          rw [hexp, hC_nat, Nat.cast_mul, h_pow_cast]
        rw [hA, hB, hC]
      rw [h_ident]
      exact_mod_cast foldBadEventCardSum_le_two_pow
    exact (le_div_iff₀ hcardL_pos).2 h_mul_goal
  have h_main :=
    add_le_add_left hB (2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0))
  simp only [add_comm, add_left_comm, add_assoc] at h_main ⊢
  exact h_main

/-!
Total knowledge error for the sumcheck-and-fold phase of Binary Basefold.

Here
`∑_j sumcheckFoldKnowledgeError j ≤ 2·ℓ/|L| + 2^{ℓ+𝓡}/|L|`,
matching the conservative display in DP24 Construction 4.12: a Thaler / Theorem 4.17-style
aggregate for the per-round `2/|L|` (Schwartz–Zippel) charges together with a Proposition 4.23-style
bad-event term `2^{ℓ+𝓡}/|L|` for fold-oracle collisions when `|𝔽q| = 2`.

Paper versus formal accounting: the prose around Proposition 4.23 often packages fold bad events via
a coarse union bound into a single `|L|` denominator. Here `foldKnowledgeError` records finer
per-challenge masses along the actual `pSpecFoldRelay` / `pSpecFoldCommit` split and ϑ-block
schedule; their sum telescopes to something typically strictly smaller than the headline bound (for
example ϑ = 1 yields `(2^{ℓ+𝓡} - 2^{𝓡})/|L|` in the bad-event part alone). The one-sided inequality
is the correct statement for composing with `Verifier.knowledgeSoundness_error_mono` without altering
the reference RHS.

Proof outline: split `pSpecSumcheckFold` into `pSpecNonLastBlocks` and
`pSpecLastBlock`, reindex `seqCompose` challenges into nested sums over block indices and inner
fold protocols, identify each
block's charges with `foldRelayKnowledgeError` / `foldCommitKnowledgeError` and then with
`foldKnowledgeError` via `h_foldRelay_round_sum` and `h_foldCommit_round_sum`, expand to the display
`2/|L| + |S^k|/|L|`, and close with `sumcheckFoldKnowledgeError_displayMass_le`.

Equality with the paper display RHS is not expected for arbitrary parameters unless the RHS is
specialized or redefined to match the telescoping sum.

Declared with `maxHeartbeats 200000` because the final bookkeeping expands and normalizes large nested
`Finset` sums.
-/
set_option maxHeartbeats 200000 in
theorem sumcheckFoldKnowledgeError_le :
    (∑ j : (pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx,
        sumcheckFoldKnowledgeError (L := L) 𝔽q β j)
    ≤ 2 * (ℓ : ℝ≥0) / (Fintype.card L : ℝ≥0)
      + (2 ^ (ℓ + 𝓡) : ℝ≥0) / (Fintype.card L : ℝ≥0) := by
  sorry

end CoreInteractionPhaseReduction

end Binius.BinaryBasefold.CoreInteraction
