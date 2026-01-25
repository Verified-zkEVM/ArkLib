/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Steps
import ArkLib.OracleReduction.Cast

-- Note: should filter errors when doing compilation

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

noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open scoped NNReal

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

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- Fin equality for 0 * ϑ = 0 -/
lemma fin_zero_mul_eq (h : 0 * ϑ < ℓ + 1) : (⟨0 * ϑ, h⟩ : Fin (ℓ + 1)) = 0 := by
  ext; simp only [zero_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod]

omit [Field L] [Fintype L] [DecidableEq L] [CharP L 2] [SelectableType L] [NeZero ℓ] in
/-- Statement equality from Fin equality -/
lemma Statement.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Statement (L := L) (ℓ := ℓ) Context i = Statement (L := L) (ℓ := ℓ) Context j := by
  subst h; rfl

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- OracleStatement index type equality from Fin equality -/
lemma OracleStatement.idx_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Fin (toOutCodewordsCount ℓ ϑ i) = Fin (toOutCodewordsCount ℓ ϑ j) := by
  subst h; rfl

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] hdiv in
/-- OracleStatement function HEq from Fin equality -/
lemma OracleStatement.heq_of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    HEq (fun k => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i k)
        (fun k => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j k) := by
  subst h; rfl

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- Witness equality from Fin equality -/
lemma Witness.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i =
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) j := by
  subst h; rfl

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] h_β₀_eq_1 in
/-- Relation equality from Fin equality -/
lemma strictRoundRelation.of_fin_eq {i j : Fin (ℓ + 1)} (h : i = j) :
    strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i ≍
    strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) j := by
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
    (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.succ)
    (pSpec := pSpecFoldRelay (L:=L)) :=
  OracleReduction.append
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecRelay)
        (foldOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i)
    (relayOracleReduction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hNCR)


variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness of the non-commitment round reduction follows by append composition
    of the fold-round and the transfer-round reductions. -/
theorem foldRelayOracleReduction_perfectCompleteness
    (hInit : init.neverFails) (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge i)]
    [(i : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge i)] :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFoldRelay (L:=L))
    (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc)
    (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ)
    (oracleReduction := foldRelayOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑:=𝓑) i hNCR) (init := init) (impl := impl) := by
  unfold foldRelayOracleReduction pSpecFoldRelay
  apply OracleReduction.append_perfectCompleteness
  · -- Perfect completeness of foldOracleReduction
    exact foldOracleReduction_perfectCompleteness (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (init := init) (impl := impl) hInit i
  · -- Perfect completeness of relayOracleReduction
    exact relayOracleReduction_perfectCompleteness (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (init := init) (impl := impl) hInit i hNCR

/-- RBR Knowledge Soundness of the non-commitment round verifier via append composition
    of fold-round and transfer-round RBR KS. -/
theorem foldRelayOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i) :
    (foldRelayOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hNCR).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) i.castSucc  (mp := mp))
      (relOut := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) i.succ  (mp := mp))
      (rbrKnowledgeError := fun m => foldKnowledgeError 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨m, by
        match m with
        | ⟨0, h0⟩ => nomatch h0
        | ⟨1, h1⟩ => rfl
      ⟩) := by
  unfold foldRelayOracleVerifier pSpecFoldRelay
  suffices h : OracleVerifier.rbrKnowledgeSoundness init impl (roundRelation 𝔽q β i.castSucc)
      (roundRelation 𝔽q β i.succ)
      ((foldOracleVerifier 𝔽q β i).append (relayOracleVerifier 𝔽q β i hNCR))
      (Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        relayKnowledgeError ∘ ChallengeIdx.sumEquiv.symm) by
    convert h using 1
    funext m
    simp only [Function.comp, ChallengeIdx.sumEquiv, Equiv.symm]
    dsimp
    split
    · congr 1; ext; simp
    · omega
  exact OracleVerifier.append_rbrKnowledgeSoundness _ _
    (foldOracleVerifier_rbrKnowledgeSoundness 𝔽q β i)
    (relayOracleVerifier_rbrKnowledgeSoundness 𝔽q β i hNCR)

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
    OracleVerifier.append (oSpec:=[]ₒ)
      (pSpec₁ := pSpecFold (L:=L))
      (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (V₁ := foldOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i)
      (V₂ := commitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR)

@[reducible]
def foldCommitOracleReduction (i : Fin ℓ)
    (hCR : isCommitmentRound ℓ ϑ i) :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) Context i.castSucc)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.castSucc)
    (StmtOut := Statement (L := L) Context i.succ)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) i.succ)
    (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  OracleReduction.append (oSpec:=[]ₒ)
    (pSpec₁ := pSpecFold (L:=L))
    (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (R₁ := foldOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i)
    (R₂ := commitOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR)

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for Fold+Commitment block by append composition. -/
theorem foldCommitOracleReduction_perfectCompleteness
    (hInit : init.neverFails) (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    [(i : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge i)]
    [(i : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge i)]
    [(j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Fintype ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)]
    [(j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Inhabited ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)] :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ)
      (oracleReduction := foldCommitOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR) (init := init) (impl := impl) := by
  unfold foldCommitOracleReduction pSpecFoldCommit
  apply OracleReduction.append_perfectCompleteness
  · -- Perfect completeness of foldOracleReduction
    exact foldOracleReduction_perfectCompleteness (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (init := init) (impl := impl) hInit i
  · -- Perfect completeness of commitOracleReduction
    exact commitOracleReduction_perfectCompleteness (L := L) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) (init := init) (impl := impl) hInit i hCR

/-- RBR KS for Fold+Commitment block by append composition. -/
theorem foldCommitOracleVerifier_rbrKnowledgeSoundness
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (foldCommitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i hCR).rbrKnowledgeSoundness
      init impl
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.castSucc )
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) i.succ )
      (rbrKnowledgeError := fun _ => foldKnowledgeError 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ⟨1, by rfl⟩
      ) := by
  unfold foldCommitOracleVerifier pSpecFoldCommit
  have herr : (fun _ => foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i ⟨1, by rfl⟩) =
      (Sum.elim (foldKnowledgeError 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
        (commitKnowledgeError 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) ∘
        (ChallengeIdx.sumEquiv (pSpec₁ := pSpecFold (L := L))
          (pSpec₂ := pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)).symm) := by
    funext m
    simp only [Function.comp, ChallengeIdx.sumEquiv, Equiv.symm]
    dsimp
    split
    · simp [foldKnowledgeError]
    · next hlt =>
      exfalso
      have hv := m.1.isLt
      have hp := m.2
      simp only [ProtocolSpec.append, Fin.vappend_eq_append, Fin.append, Fin.addCases,
        Direction.not_P_to_V_eq_V_to_P] at hp
      split at hp <;> simp_all <;> omega
  rw [herr]
  exact OracleVerifier.append_rbrKnowledgeSoundness _ _
    (foldOracleVerifier_rbrKnowledgeSoundness 𝔽q β i)
    (commitOracleVerifier_rbrKnowledgeSoundness 𝔽q β i hCR)

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
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i: Fin (ϑ - 1 + 1) => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
    ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleVerifier :=
    OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (V := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          := isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
        exact foldRelayOracleVerifier (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
          ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ hNCR
      )
  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv: Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n:=ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq: fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ :  ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega

  let lastOracleVerifier := foldCommitOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
    (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩) (hCR:=isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)

  let nonLastSingleBlockOracleVerifier :=
    OracleVerifier.append (oSpec:=[]ₒ)
      (Stmt₁:=Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Stmt₂:=Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Stmt₃:=Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₁:=OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ, Nat.lt_of_add_right_lt h1_succ⟩)
      (OStmt₂:=OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmt₃:=OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ+1)))
      (pSpec₁:=pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1))
      (pSpec₂:=pSpecFoldCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (V₁:= firstFoldRelayRoundsOracleVerifier.castOutSimple (h_stmt := by rfl) (h_ostmt := by rfl))
      (V₂:= OracleVerifier.castInOut (V := lastOracleVerifier)
          (StmtIn₁ := (Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
          (StmtIn₂ := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
          (StmtOut₁ := Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
          (StmtOut₂ := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
          (OStmtIn₁ := (OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
          (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
          (OStmtOut₁ := OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
          (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ+1)))
          (pSpec := pSpecFoldCommit 𝔽q β ⟨↑bIdx * ϑ + (ϑ - 1), h1⟩)
          (h_stmtIn := by
            apply Statement.of_fin_eq
            simp [Fin.castSucc, Fin.eta])
          (h_stmtOut := by
            apply Statement.of_fin_eq
            ext; simp [Fin.val_succ]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
          (h_idxIn := by
            apply OracleStatement.idx_eq
            simp [Fin.castSucc, Fin.eta])
          (h_idxOut := by
            apply OracleStatement.idx_eq
            ext; simp [Fin.val_succ]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
          (h_ostmtIn := by
            apply OracleStatement.heq_of_fin_eq
            simp [Fin.castSucc, Fin.eta])
          (h_ostmtOut := by
            apply OracleStatement.heq_of_fin_eq
            ext; simp [Fin.val_succ]
            rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
          (h_Oₛᵢ := by
            apply instOracleStatementBinaryBasefold_heq_of_fin_eq
            ext; simp only [Fin.castSucc, Fin.castAdd_mk])
      )

  nonLastSingleBlockOracleVerifier

def nonLastBlocksOracleVerifier :
  OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, by omega⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨0 * ϑ, by omega⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (pSpec := pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let res := OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) bIdx)
      (V := fun bIdx => nonLastSingleBlockOracleVerifier (L:=L) 𝔽q β (mp := mp)
        (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (bIdx:=bIdx))
  res

def lastBlockOracleVerifier :=
  have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ:=ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let V:  OracleVerifier []ₒ (StmtIn := Statement (L := L) (ℓ := ℓ) Context
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ)) := by
    let cur := OracleVerifier.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (V := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩
          := lastBlockIdx_isNeCommitmentRound i
        exact foldRelayOracleVerifier (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
          ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ hNCR
      )
    exact OracleVerifier.castInOut (V := cur)
      (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      -- (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        -- ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
      (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      -- (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
      (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ))
      (h_stmtIn := by
        apply Statement.of_fin_eq
        ext; simp)
      (h_stmtOut := by
        apply Statement.of_fin_eq
        ext
        simp [Fin.val_last]
        have : bIdx * ϑ + ϑ = ℓ := by
          have h_div : ϑ ∣ ℓ := hdiv.out
          have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
          have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
          dsimp only [bIdx]
          rw [Nat.sub_mul, h_mul, Nat.one_mul]; omega
        simp only [this])
      (h_idxIn := by
        apply OracleStatement.idx_eq
        ext; simp)
      (h_idxOut := by
        apply OracleStatement.idx_eq
        ext
        simp [Fin.val_last]
        have : bIdx * ϑ + ϑ = ℓ := by
          have h_div : ϑ ∣ ℓ := hdiv.out
          have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
          have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
          dsimp only [bIdx]
          rw [Nat.sub_mul, h_mul, Nat.one_mul]; omega
        simp only [this])
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        ext; simp)
      (h_ostmtOut := by
        apply OracleStatement.heq_of_fin_eq
        ext
        simp [Fin.val_last]
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
  let nonLastBlocksOracleVerifier := nonLastBlocksOracleVerifier (L:=L) 𝔽q β (mp := mp) (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)

  let lastOracleVerifier := lastBlockOracleVerifier 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)

  let sumcheckFoldOV : OracleVerifier []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
     :=
    (OracleVerifier.append (oSpec:=[]ₒ)
      (V₁:=nonLastBlocksOracleVerifier)
      (V₂:=lastOracleVerifier)
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
  let stmt : Fin (ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let oStmt := fun i: Fin (ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let wit := fun i: Fin (ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
  let firstFoldRelayRoundsOracleReduction :=
    OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt)
      (Wit := wit) (m := ϑ - 1)
      (pSpec := fun i => pSpecFoldRelay (L:=L))
      (R := fun i => by
        have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
          := isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
        exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) hNCR
      )

  let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
    let fv: Fin ϑ := ⟨ϑ - 1, by
      have h := NeZero.one_le (n:=ϑ)
      exact Nat.sub_one_lt_of_lt h
    ⟩
    have h_eq: fv.val = ϑ - 1 := by rfl
    change ↑bIdx * ϑ + fv.val < ℓ + 0
    apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
  let h1_succ :  ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega

  let lastOracleReduction := foldCommitOracleReduction 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
    (hCR:=isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)

  let nonLastSingleBlockOracleReduction :=
    OracleReduction.append (oSpec:=[]ₒ)
      (Stmt₁:=Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Stmt₂:=Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Stmt₃:=Statement (L := L) (ℓ := ℓ) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (Wit₁:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (Wit₂:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (Wit₃:=Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (OStmt₁:=OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨bIdx * ϑ, by
        apply Nat.lt_trans (m:=ℓ) (h₁:=by
          change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin (ϑ)).val < ℓ + 0
          apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
        ) (by omega)
      ⟩)
      (OStmt₂:=OracleStatement 𝔽q β ϑ ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
      (OStmt₃:=OracleStatement 𝔽q β ϑ ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (pSpec₁:=pSpecFoldRelaySequence (L:=L) (n:=ϑ - 1))
      (pSpec₂:=pSpecFoldCommit 𝔽q β ⟨bIdx * ϑ + (ϑ - 1), h1⟩)
      (R₁:=firstFoldRelayRoundsOracleReduction.castOutSimple (h_stmt := by rfl) (h_ostmt := by rfl) (h_wit := by rfl)
      )
      (R₂:= OracleReduction.castInOut (R := lastOracleReduction)
        (StmtIn₁ := (Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
        (StmtIn₂ := Statement (L := L) Context ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
        (StmtOut₁ := Statement Context (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
        (StmtOut₂ := Statement (L := L) Context ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
        (OStmtIn₁ := (OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).castSucc))
        (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + (ϑ - 1), h1_succ⟩)
        (OStmtOut₁ := OracleStatement 𝔽q β ϑ (⟨↑bIdx * ϑ + (ϑ - 1), h1⟩ : Fin ℓ).succ)
        (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩ : Fin (ℓ+1)))
        (pSpec := pSpecFoldCommit 𝔽q β ⟨↑bIdx * ϑ + (ϑ - 1), h1⟩)
        (h_stmtIn := by
          apply Statement.of_fin_eq
          simp [Fin.castSucc, Fin.eta])
        (h_stmtOut := by
          apply Statement.of_fin_eq
          ext; simp [Fin.val_succ]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_idxIn := by
          apply OracleStatement.idx_eq
          simp [Fin.castSucc, Fin.eta])
        (h_idxOut := by
          apply OracleStatement.idx_eq
          ext; simp [Fin.val_succ]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_ostmtIn := by
          apply OracleStatement.heq_of_fin_eq
          simp [Fin.castSucc, Fin.eta])
        (h_ostmtOut := by
          apply OracleStatement.heq_of_fin_eq
          ext; simp [Fin.val_succ]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_witIn := by
          apply Witness.of_fin_eq
          simp [Fin.castSucc, Fin.eta])
        (h_witOut := by
          apply Witness.of_fin_eq
          ext; simp [Fin.val_succ]
          rw [Nat.add_assoc, Nat.sub_add_cancel (by exact NeZero.one_le), Nat.add_mul, Nat.one_mul])
        (h_Oₛᵢ := by
          apply instOracleStatementBinaryBasefold_heq_of_fin_eq
          ext; simp only [Fin.castSucc, Fin.castAdd_mk, Nat.add_left_cancel_iff])
      )

  nonLastSingleBlockOracleReduction

def nonLastBlocksOracleReduction :
  OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context ⟨0 * ϑ, by omega⟩)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨0 * ϑ, by omega⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) ⟨0 * ϑ, by omega⟩)

    (StmtOut := Statement (L := L) (ℓ:=ℓ) Context ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ ⟨(ℓ / ϑ - 1) *ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (pSpec := pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let res := OracleReduction.seqCompose (oSpec := []ₒ)
      (Stmt := stmt)
      (OStmt := oStmt) (Wit := wit)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) bIdx)
        (R := fun bIdx => nonLastSingleBlockOracleReduction (L:=L) 𝔽q β (mp := mp)
        (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (bIdx:=bIdx))
  res

def lastBlockOracleReduction :=
  have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ
    ⟨bIdx * ϑ + i, by  apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let wit := fun i: Fin (ϑ + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let V:  OracleReduction []ₒ (StmtIn := Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (OStmtIn := OracleStatement 𝔽q β ϑ
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (StmtOut := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ)) := by
      let cur := OracleReduction.seqCompose (oSpec := []ₒ)
        (Stmt := stmt)
        (OStmt := oStmt)
        (Wit := wit)
        (pSpec := fun i => pSpecFoldRelay (L:=L))
        (R := fun i => by
          have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
            lastBlockIdx_isNeCommitmentRound i
          exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) hNCR
        )
      exact OracleReduction.castInOut (R := cur)
        (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ, by
          apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
        (OStmtIn₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
        (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
          ⟨bIdx * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
        (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
        (OStmtOut₂ := OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
        (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
        (pSpec := pSpecLastBlock (L:=L) (ϑ:=ϑ))
        (h_stmtIn := by
          apply Statement.of_fin_eq
          ext; simp)
        (h_stmtOut := by
          apply Statement.of_fin_eq
          ext
          simp [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp only [bIdx];
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp [this])
        (h_idxIn := by
          apply OracleStatement.idx_eq
          ext; simp)
        (h_idxOut := by
          apply OracleStatement.idx_eq
          ext
          simp [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp only [bIdx]
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp [this])
        (h_ostmtIn := by
          apply OracleStatement.heq_of_fin_eq
          ext; simp)
        (h_ostmtOut := by
          apply OracleStatement.heq_of_fin_eq
          ext
          simp [Fin.val_last]
          have : bIdx * ϑ + ϑ = ℓ := by
            have h_div : ϑ ∣ ℓ := hdiv.out
            have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
            have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
            dsimp [bIdx]
            rw [Nat.sub_mul, h_mul, Nat.one_mul]
            omega
          simp [this])
          (h_witIn := by
            apply Witness.of_fin_eq
            ext; simp)
          (h_witOut := by
            apply Witness.of_fin_eq
            ext
            simp [Fin.val_last]
            have : bIdx * ϑ + ϑ = ℓ := by
              have h_div : ϑ ∣ ℓ := hdiv.out
              have h_mod : ℓ % ϑ = 0 := Nat.mod_eq_zero_of_dvd h_div
              have h_mul : ℓ / ϑ * ϑ = ℓ := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h_mod)
              rw [Nat.sub_mul, h_mul, Nat.one_mul]
              omega
            simp [this])
        (h_Oₛᵢ := by
          apply instOracleStatementBinaryBasefold_heq_of_fin_eq
          ext; simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])

  V

def sumcheckFoldOracleReduction : OracleReduction []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ) Context 0)
    (OStmtIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (WitIn := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (StmtOut := Statement (L := L) (ℓ:=ℓ) Context (Fin.last ℓ))
    (OStmtOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (WitOut := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)) :=
  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let nonLastSingleBlockOracleReduction := nonLastBlocksOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (ϑ := ϑ)

  let lastOracleReduction := lastBlockOracleReduction 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)

  (OracleReduction.append (oSpec:=[]ₒ)
    (pSpec₁ := pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecLastBlock (L:=L) (ϑ:=ϑ))
    (R₁:=nonLastSingleBlockOracleReduction)
    (R₂:=lastOracleReduction)
  ).castInOut
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

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for a single non-last block -/
lemma nonLastSingleBlockOracleReduction_perfectCompleteness (hInit : init.neverFails)
    (bIdx : Fin (ℓ / ϑ - 1)) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨bIdx * ϑ, by
          apply Nat.lt_trans (m:=ℓ) (h₁:=by
            change bIdx.val * ϑ + (⟨0, by exact Nat.pos_of_neZero ϑ⟩: Fin ϑ).val < ℓ + 0
            apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
          ) (by omega)
        ⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨(bIdx + 1) * ϑ, bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx⟩)
      (oracleReduction := nonLastSingleBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) bIdx) := by
  unfold nonLastSingleBlockOracleReduction; simp only
  -- At this point the goal is perfectCompleteness for an `append`.
  apply OracleReduction.append_perfectCompleteness
    (rel₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
      ⟨bIdx * ϑ + (ϑ - 1), by
        -- matches the index used by the append midpoint in the definition
        let fv: Fin ϑ := ⟨ϑ - 1, by
          have h := NeZero.one_le (n:=ϑ)
          exact Nat.sub_one_lt_of_lt h
        ⟩
        change ↑bIdx * ϑ + fv.val < ℓ + 1
        apply bIdx_mul_ϑ_add_i_lt_ℓ_succ (m:=1)
      ⟩)
    (impl := impl) (init := init)

  · -- Perfect completeness of the fold+relay sequence part (`seqCompose`), output-cast is rfl
    apply OracleReduction.castInOut_perfectCompleteness
      (h_stmtIn := by
        apply Statement.of_fin_eq;
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_stmtOut := by rfl)
      (h_witIn := by
        apply Witness.of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_witOut := by rfl)
      (h_idxIn := by
        apply OracleStatement.idx_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_idxOut := by rfl)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_ostmtOut := by rfl)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_relIn := by
        apply strictRoundRelation.of_fin_eq
        simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
      (h_relOut := by rfl)
      (impl := impl) (init := init)
  --   ⊢ OracleReduction.perfectCompleteness init impl (strictRoundRelation 𝔽q β ⟨↑bIdx * ϑ + ↑0, ⋯⟩)
  -- (strictRoundRelation 𝔽q β ⟨↑bIdx * ϑ + (ϑ - 1), ⋯⟩)
  -- (OracleReduction.seqCompose (fun i ↦ Statement Context ⟨↑bIdx * ϑ + ↑i, ⋯⟩)
  --   (fun i ↦ OracleStatement 𝔽q β ϑ ⟨↑bIdx * ϑ + ↑i, ⋯⟩) (fun i ↦ Witness 𝔽q β ⟨↑bIdx * ϑ + ↑i, ⋯⟩) fun i ↦
  --   foldRelayOracleReduction 𝔽q β ⟨↑bIdx * ϑ + ↑i, ⋯⟩ ⋯)
    let stmt : Fin (ϑ - 1 + 1) → Type :=
      fun i => Statement (L := L) (ℓ := ℓ) Context ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let oStmt := fun i: Fin (ϑ - 1 + 1) =>
      OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let wit := fun i: Fin (ϑ - 1 + 1) =>
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
        ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ bIdx i⟩
    let foldRelayRoundsPerfectCompleteness := OracleReduction.seqCompose_perfectCompleteness
        (oSpec := []ₒ) (m := ϑ - 1)
        (pSpec := fun _ : Fin (ϑ - 1) => pSpecFoldRelay (L:=L))
        (Stmt := stmt)
        (OStmt := oStmt)
        (Wit := wit)
        (R := fun i => by
          have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩
            := isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
          exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) hNCR
        )
        (rel := fun i ↦
          strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
            (⟨↑bIdx * ϑ + ↑i, by simp only [bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ]⟩ : Fin (ℓ + 1)))
        (init := init) (impl := impl) (hInit := hInit)
    apply foldRelayRoundsPerfectCompleteness
    intro (i : Fin (ϑ - 1))
    have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩ :=
      isNeCommitmentRound (r:=r) (ℓ:=ℓ) (𝓡:=𝓡) (ϑ:=ϑ) bIdx (x:=i.val) (hx:=by omega)
    let res := foldRelayOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := init) (impl := impl)
      (hInit := hInit) (i := ⟨bIdx * ϑ + i, bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ bIdx i⟩) (hNCR := hNCR)
    exact res
  · -- Perfect completeness of the final fold+commit round, via castInOut
    have h_ϑ_gt_zero : ϑ > 0 := Nat.pos_of_neZero ϑ
    apply OracleReduction.castInOut_perfectCompleteness
      (h_stmtIn := by
        apply Statement.of_fin_eq;
        simp only [Fin.castSucc_mk])
      (h_stmtOut := by
        apply Statement.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_witIn := by
        apply Witness.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_witOut := by
        apply Witness.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_idxIn := by
        apply OracleStatement.idx_eq;
        simp only [Fin.castSucc_mk])
      (h_idxOut := by
        apply OracleStatement.idx_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_ostmtIn := by
        apply OracleStatement.heq_of_fin_eq;
        simp only [Fin.castSucc_mk])
      (h_ostmtOut := by
        apply OracleStatement.heq_of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (h_Oₛᵢ := by
        apply instOracleStatementBinaryBasefold_heq_of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relIn := by
        apply strictRoundRelation.of_fin_eq
        simp only [Fin.castSucc_mk])
      (h_relOut := by
        apply strictRoundRelation.of_fin_eq;
        simp only [Fin.succ_mk, Fin.mk.injEq, Nat.add_mul]; omega)
      (impl := impl) (init := init)

    let h1 : ↑bIdx * ϑ + (ϑ - 1) < ℓ := by
      let fv: Fin ϑ := ⟨ϑ - 1, by
        have h := NeZero.one_le (n:=ϑ)
        exact Nat.sub_one_lt_of_lt h
      ⟩
      have h_eq: fv.val = ϑ - 1 := by rfl
      change ↑bIdx * ϑ + fv.val < ℓ + 0
      apply bIdx_mul_ϑ_add_i_lt_ℓ_succ
    let h1_succ :  ↑bIdx * ϑ + (ϑ - 1) < ℓ + 1 := by omega

    exact foldCommitOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := init) (impl := impl)
      (hCR := isCommitmentRoundOfNonLastBlock (𝓡:=𝓡) (r:=r) bIdx)
      (i := ⟨bIdx * ϑ + (ϑ - 1), h1⟩) (hInit := hInit)

/-- Perfect completeness for the last block -/
lemma lastBlockOracleReduction_perfectCompleteness (hInit : init.neverFails) :
    OracleReduction.perfectCompleteness (init := init) (impl := impl)
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (oracleReduction := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)) := by
  have h_ϑ_le_ℓ : ϑ ≤ ℓ := Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (by exact hdiv.out)
  apply OracleReduction.castInOut_perfectCompleteness
    (h_stmtIn := by
      apply Statement.of_fin_eq;
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero])
    (h_stmtOut := by
      apply Statement.of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_witIn := by
      apply Witness.of_fin_eq -- ⊢ ⟨(ℓ / ϑ - 1) * ϑ + ↑0, ⋯⟩ = ⟨(ℓ / ϑ - 1) * ϑ, ⋯⟩
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_witOut := by
      apply Witness.of_fin_eq; -- ⊢ ⟨(ℓ / ϑ - 1) * ϑ + ↑(Fin.last ϑ), ⋯⟩ = Fin.last ℓ
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_idxIn := by
      apply OracleStatement.idx_eq;
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_idxOut := by
      apply OracleStatement.idx_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_ostmtIn := by
      apply OracleStatement.heq_of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_ostmtOut := by
      apply OracleStatement.heq_of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (h_Oₛᵢ := by
      apply instOracleStatementBinaryBasefold_heq_of_fin_eq
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_relIn := by
      apply strictRoundRelation.of_fin_eq
      apply Fin.eq_of_val_eq; simp only [Nat.sub_mul, one_mul, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        add_zero])
    (h_relOut := by
      apply strictRoundRelation.of_fin_eq;
      apply Fin.eq_of_val_eq; simp only [Fin.val_last, Nat.sub_mul];
      rw [Nat.div_mul_cancel (by exact hdiv.out), Nat.one_mul]; omega)
    (impl := impl) (init := init)

  let bIdx := ℓ / ϑ - 1
  let stmt : Fin (ϑ + 1) → Type := fun i => Statement (L := L) (ℓ := ℓ) Context
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let oStmt := fun i: Fin (ϑ + 1) => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨bIdx * ϑ + i, by  apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩
  let wit := fun i: Fin (ϑ + 1) => Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
    ⟨bIdx * ϑ + i, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩

  let foldRelayRoundsPerfectCompleteness := OracleReduction.seqCompose_perfectCompleteness
    (oSpec := []ₒ) (m := ϑ)
    (Stmt := stmt)
    (OStmt := oStmt)
    (Wit := wit)
    (pSpec := fun i => pSpecFoldRelay (L:=L))
    (R := fun i => by
      have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
        lastBlockIdx_isNeCommitmentRound i
      exact foldRelayOracleReduction (L:=L) 𝔽q β (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑:=𝓑) (i:=⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) hNCR
    )
    (rel := fun i ↦
      strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        (⟨↑bIdx * ϑ + ↑i, lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (hx:=by omega)⟩ : Fin (ℓ + 1)))
    (init := init) (impl := impl) (hInit := hInit)
  apply foldRelayRoundsPerfectCompleteness
  intro (i : Fin ϑ)
  have hNCR : ¬ isCommitmentRound ℓ ϑ ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩ :=
        lastBlockIdx_isNeCommitmentRound i
  let res := foldRelayOracleReduction_perfectCompleteness 𝔽q β (mp := mp) (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := init) (impl := impl)
    (hInit := hInit) (i := ⟨bIdx * ϑ + i, lastBlockIdx_mul_ϑ_add_fin_lt_ℓ i⟩) (hNCR := hNCR)
  exact res

/-- Perfect completeness for the core interaction oracle reduction -/
theorem sumcheckFoldOracleReduction_perfectCompleteness :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
      (oracleReduction := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
      (init := init)
      (impl := impl) := by
  unfold sumcheckFoldOracleReduction pSpecSumcheckFold

  let stmt : Fin (ℓ / ϑ - 1 + 1) → Type :=
    fun i => Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let oStmt := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩
  let wit := fun i: Fin (ℓ / ϑ - 1 + 1) =>
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ)
      ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩

  apply OracleReduction.castInOut_perfectCompleteness
    (pSpec := pSpecSumcheckFold 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (StmtIn₁ := stmt 0)
    (StmtIn₂ := Statement (L := L) (ℓ := ℓ) Context 0)
    (ιₛᵢ₁ := Fin (toOutCodewordsCount ℓ ϑ ⟨0 * ϑ, by omega⟩))
    (ιₛᵢ₂ := Fin (toOutCodewordsCount ℓ ϑ 0))
    (OStmtIn₁ := fun i => OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨0 * ϑ, by omega⟩ i)
    (OStmtIn₂ := fun i => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 i)
    (WitIn₁ := wit 0)
    (WitIn₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (StmtOut₁ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (StmtOut₂ := Statement (L := L) (ℓ := ℓ) Context (Fin.last ℓ))
    (ιₛₒ₁ := Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (ιₛₒ₂ := Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (OStmtOut₁ := fun i => OracleStatement 𝔽q β ϑ (Fin.last ℓ) i)
    (OStmtOut₂ := fun i => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) i)
    (WitOut₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (WitOut₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (relIn₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
    (relIn₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
    (relOut₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
    (relOut₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
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
    (h_relIn := by
      apply strictRoundRelation.of_fin_eq
      apply fin_zero_mul_eq)
    (h_relOut := by rfl)
    (impl := impl)
    (init := init)
  apply OracleReduction.append_perfectCompleteness
    (rel₁ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨0 * ϑ, by omega⟩)
    (rel₂ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑)
        ⟨(ℓ / ϑ - 1) * ϑ, by apply lastBlockIdx_mul_ϑ_add_x_lt_ℓ_succ (x:=0) (hx:=by omega)⟩)
    (rel₃ := strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ))
    (pSpec₁ := pSpecNonLastBlocks 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecLastBlock (L:=L) (ϑ:=ϑ))
    (R₁ := nonLastBlocksOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (R₂ := lastBlockOracleReduction 𝔽q β (ϑ:=ϑ) (mp := mp) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))
    (impl := impl)
    (init := init)
  ·
    -- Perfect completeness of nonLastBlocksOracleReduction
    unfold nonLastBlocksOracleReduction
    apply OracleReduction.seqCompose_perfectCompleteness
      (Stmt := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        Statement (L := L) (ℓ := ℓ) Context ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (OStmt := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        OracleStatement 𝔽q β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (Wit := fun i : Fin (ℓ / ϑ - 1 + 1) =>
        Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (rel := fun i => strictRoundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) ⟨i * ϑ, blockIdx_mul_ϑ_lt_ℓ_succ i⟩)
      (pSpec := fun (bIdx: Fin (ℓ / ϑ - 1)) => pSpecFullNonLastBlock 𝔽q β (ϑ:=ϑ) bIdx)
      (R := fun bIdx => nonLastSingleBlockOracleReduction (L:=L) 𝔽q β (mp := mp)
        (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (bIdx:=bIdx))
      (impl := impl)
      (init := init)
      hInit
    intro bIdx
    -- Prove perfectCompleteness for each individual block
    exact nonLastSingleBlockOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (hInit := by exact hInit) (bIdx:=bIdx)
  · -- Perfect completeness of lastBlockOracleReduction
    exact lastBlockOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) (mp := mp)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (init := init) (impl := impl) hInit

def NBlockMessages := 2 * (ϑ - 1) + 3

def sumcheckFoldKnowledgeError := fun j : (pSpecSumcheckFold 𝔽q β (ϑ:=ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
    if hj: (j.val % NBlockMessages (ϑ:=ϑ)) % 2 = 1 then
      foldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨j / NBlockMessages (ϑ:=ϑ) * ϑ + ((j % NBlockMessages (ϑ:=ϑ)) / 2 + 1), by
          sorry⟩ ⟨1, rfl⟩
    else 0 -- this case never happens

/-- Round-by-round knowledge soundness for the sumcheck fold oracle verifier -/
theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness :
    (sumcheckFoldOracleVerifier 𝔽q β (mp := mp) (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecSumcheckFold 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
      (relOut := roundRelation (mp := mp) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ) )
      (rbrKnowledgeError := sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ)) := by
  unfold sumcheckFoldOracleVerifier pSpecSumcheckFold
  sorry

end SecurityProps

end IteratedSumcheckFoldComposition
end ComponentReductions

section CoreInteractionPhaseReduction

/-- The final oracle verifier that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (V₁ := sumcheckFoldOracleVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (mp := BBF_SumcheckMultiplierParam))
    (V₂ := finalSumcheckVerifier 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))

/-- The final oracle reduction that composes sumcheckFold with finalSumcheckStep -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append (oSpec:=[]ₒ)
    (Stmt₁ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) 0)
    (Stmt₂ := Statement (L := L) (ℓ:=ℓ) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (Stmt₃ := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (Wit₁ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) 0)
    (Wit₂ := Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ:=ℓ) (Fin.last ℓ))
    (Wit₃ := Unit)
    (OStmt₁ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0)
    (OStmt₂ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (OStmt₃ := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ))
    (pSpec₁ := pSpecSumcheckFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (pSpec₂ := pSpecFinalSumcheckStep (L:=L))
    (R₁ := sumcheckFoldOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (mp := BBF_SumcheckMultiplierParam))
    (R₂ := finalSumcheckOracleReduction 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- Perfect completeness for the core interaction oracle reduction -/
theorem coreInteractionOracleReduction_perfectCompleteness (hInit : init.neverFails)
    [(j : pSpecFold.ChallengeIdx) → Fintype ((pSpecFold (L := L)).Challenge j)]
    [(j : pSpecFold.ChallengeIdx) → Inhabited ((pSpecFold (L := L)).Challenge j)]
    [(j : pSpecFold.ChallengeIdx) → SelectableType ((pSpecFold (L := L)).Challenge j)]
    [(i : Fin ℓ) → (j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Fintype ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)]
    [(i : Fin ℓ) → (j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      Inhabited ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)]
    [(i : Fin ℓ) → (j : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).ChallengeIdx) →
      SelectableType ((pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Challenge j)] :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := strictRoundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0)
      (relOut := strictFinalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (oracleReduction := coreInteractionOracleReduction 𝔽q β (ϑ:=ϑ) (𝓑:=𝓑))
      (init := init)
      (impl := impl) := by
  unfold coreInteractionOracleReduction pSpecCoreInteraction
  apply OracleReduction.append_perfectCompleteness
  · -- Perfect completeness of sumcheckFoldOracleReduction
    exact sumcheckFoldOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (mp := BBF_SumcheckMultiplierParam)
      (init := init) (impl := impl)
  · -- Perfect completeness of finalSumcheckOracleReduction
    exact finalSumcheckOracleReduction_perfectCompleteness 𝔽q β (ϑ:=ϑ) (𝓑:=𝓑) init impl

def coreInteractionOracleRbrKnowledgeError (j : (pSpecCoreInteraction 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx) : ℝ≥0 :=
    Sum.elim
      (f := fun i => sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
      (g := fun i => finalSumcheckKnowledgeError (L := L) i)
      (ChallengeIdx.sumEquiv.symm j)

/-- Round-by-round knowledge soundness for the core interaction oracle verifier -/
theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness :
    (coreInteractionOracleVerifier 𝔽q β (𝓑 := 𝓑)).rbrKnowledgeSoundness init impl
      (pSpec := pSpecCoreInteraction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
      (relIn := roundRelation (mp := BBF_SumcheckMultiplierParam) 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
      (relOut := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
      (rbrKnowledgeError := coreInteractionOracleRbrKnowledgeError 𝔽q β (ϑ:=ϑ)) := by
  unfold coreInteractionOracleVerifier pSpecCoreInteraction
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (init:=init) (impl:=impl)
    (rel₁ := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) 0 )
    (rel₂ := roundRelation 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑:=𝓑) (Fin.last ℓ) )
    (rel₃ := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) )
    (V₁ := sumcheckFoldOracleVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (V₂ := finalSumcheckVerifier 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ:=ϑ))
    (Oₛ₃:=by exact fun i ↦ by exact OracleInterface.instDefault)
    (rbrKnowledgeError₁ := sumcheckFoldKnowledgeError 𝔽q β (ϑ:=ϑ))
    (rbrKnowledgeError₂ := finalSumcheckKnowledgeError (L := L))
    (h₁ := by apply sumcheckFoldOracleVerifier_rbrKnowledgeSoundness)
    (h₂ := by apply finalSumcheckOracleVerifier_rbrKnowledgeSoundness)

end CoreInteractionPhaseReduction

end
end Binius.BinaryBasefold.CoreInteraction
