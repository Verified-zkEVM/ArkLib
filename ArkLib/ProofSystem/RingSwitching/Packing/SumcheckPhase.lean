/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FinalAlgebra
import ArkLib.ProofSystem.RingSwitching.Packing.Spec
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Relocation sumcheck and the final consistency step

Second phase of the interactive packing reduction. After batching, the target `s₀` is (for
an honest prover) the Boolean-cube sum of `h = A · t'` — the packed polynomial times the
public multiplier built from the basis decomposition of eq̃ — so its correctness is exactly a
degree-2 sumcheck claim. Running that sumcheck *relocates* the claim: after `ℓ'` rounds, the
statement about `t'` is anchored at the fresh random point `r'` assembled from the round
challenges, which is what the downstream opening can consume.

* **Iterated rounds** — the `ℓ'`-fold loop of the structured single sumcheck round
  (re-exported from `Sumcheck/Structured/SingleRound` at degree 2): each round, the prover
  sends the round polynomial, the verifier checks it against the running target and folds in
  a fresh challenge. This loop is the main source of the reduction's knowledge error
  (`2/|L|` per round).
* **Final step** — the prover sends the residual value `s' = t'(r')`; the verifier checks
  the last running target against `(eq̃-consistency value) · s'` — where the consistency
  value reconstructs, from the column coordinates of the final eq̃-tensor, what the multiplier
  contributes at `r'` — and outputs the evaluation claim `t'(r') = s'`. The verifier is the
  family-shared one-message check-then-update verifier
  (`RingSwitching.guardedMessageRoundOracleVerifier`).

## Protocol steps ([DP24] Construction 3.1, steps 6–9)

6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u` (column coordinates with basis on the left tensor
    factor).
9. `V` requires
   `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.

## Security

Per-round and final-step extractors, knowledge-state functions and composed statements.
Each sumcheck challenge contributes `2/|L|`; the final message adds no challenge error.
Final-step completeness, knowledge-state obligations and worst-case security are proved.
Loop knowledge soundness remains admitted; batching security is proved in `BatchingPhase.lean`.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24]
-/

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')

section IteratedSumcheckStep

/-! ## Per-round prover / verifier (re-exported from `Sumcheck.Structured.SingleRound`)

The `iteratedSumcheck*` wrappers specialize the structured single-round definitions to
`Context := RingSwitchingBaseContext κ L K ℓ` and `OStmtIn := aOStmtIn.OStmtIn`.
They are reducible so the sequential loop can access the underlying verifier and reduction. -/

-- Ring-switching uses the plain degree-2 round polynomial (`H = P · t`), so the wrappers pin
-- `d := 2` when specializing the degree-generic `Sumcheck.Structured.round*` definitions.

@[reducible]
def iteratedSumcheckPrvState (i : Fin ℓ') : Fin (2 + 1) → Type :=
  Sumcheck.Structured.roundPrvState (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def getIteratedSumcheckProverFinalOutput (i : Fin ℓ')
    (finalPrvState : iteratedSumcheckPrvState κ L K P ℓ ℓ' aOStmtIn i 2) :
    ((Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ
      × (∀ j, aOStmtIn.OStmtIn j)) × SumcheckWitness L ℓ' i.succ) :=
  Sumcheck.Structured.getRoundProverFinalOutput (L := L) ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i finalPrvState

@[reducible]
def iteratedSumcheckOracleProver (i : Fin ℓ') :
    OracleProver (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleProver (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleVerifier (i : Fin ℓ') :
    OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleVerifier (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

@[reducible]
def iteratedSumcheckOracleReduction (i : Fin ℓ') :
    OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) :=
  Sumcheck.Structured.roundOracleReduction (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) := by
  unfold OracleReduction.perfectCompleteness
  intro stmtIn witIn h_relIn
  simp only
  sorry

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := fun _messageIdx => SumcheckWitness L ℓ' i.castSucc) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun ⟨stmtIn, oStmtIn⟩ fullTranscript witOut => by
    exact {
      t' := witOut.t',
      H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtIn.ctx) (t := witOut.t')
        (i := i.castSucc) (challenges := stmtIn.challenges)
    }

/-- This follows the KState of `foldKStateProp` -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witMid : SumcheckWitness L ℓ' i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  -- Ground-truth polynomial from witness
  let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i)
    (h := witMid.H)
  -- Checks available after message 1 (P -> V : hᵢ(X))
  let get_Hᵢ := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 1 ≤ m.val) =>
    let ⟨msgsUpTo, _⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le hm⟩, by simp [pSpecSumcheckRound]; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    h_i
  let get_rᵢ' := fun (m: Fin (2 + 1)) (tr: Transcript m (pSpecSumcheckRound L)) (hm: 2 ≤ m.val) =>
    let ⟨msgsUpTo, chalsUpTo⟩ := Transcript.equivMessagesChallenges (k := m)
      (pSpec := pSpecSumcheckRound L) tr
    let i_msg1 : ((pSpecSumcheckRound L).take m m.is_le).MessageIdx :=
      ⟨⟨0, Nat.lt_of_succ_le (Nat.le_trans (by decide) hm)⟩, by simp; rfl⟩
    let h_i : L⦃≤ 2⦄[X] := msgsUpTo i_msg1
    let i_msg2 : ((pSpecSumcheckRound L).take m m.is_le).ChallengeIdx :=
      ⟨⟨1, Nat.lt_of_succ_le hm⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let r_i' : L := chalsUpTo i_msg2
    r_i'
  match m with
  | ⟨0, _⟩ => -- equiv s relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, h1⟩ => -- P sends hᵢ(X)
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks :=
        let h_i := get_Hᵢ (m := ⟨1, h1⟩) (tr := tr) (hm := by simp only [le_refl])
        let explicitVCheck :=
          (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmt.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, h2⟩ => -- implied by the accepted output relation
    let h_i := get_Hᵢ (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [Nat.one_le_ofNat])
    let r_i' := get_rᵢ' (m := ⟨2, h2⟩) (tr := tr) (hm := by simp only [le_refl])
    -- A successful evaluation can occur at a root of a dishonest round polynomial's
    -- difference. Do not require equality of polynomials or truth of the old target here.
    witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid
    ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
    ∧ (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmt.sumcheck_target
    ∧ h_i.val.eval r_i' = h_star.val.eval r_i'

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K P ℓ ℓ' h_l
      (i := i) (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun _ _ => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_castSucc, cast_eq,
      Set.mem_ofPred_eq, iteratedSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmtIn tr msg witMid => by
    obtain ⟨stmt, oStmt⟩ := stmtIn
    fin_cases m
    · -- m = 0: succ = 1, castSucc = 0
      unfold iteratedSumcheckKStateProp
      simp only [masterKStateProp, iteratedSumcheckRbrExtractor, true_and]
      simp only [Fin.succ_mk, Fin.castSucc_mk]
      tauto
    · -- m = 1: dir 1 = V_to_P, contradicts hDir
      simp at hDir
  toFun_full := fun _ _ _ _ => by
    sorry

section
local instance : DecidableEq K := Classical.decEq K

omit [Fintype K] [DecidableEq K] in
/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L] (i : Fin ℓ')
    (hfunctional : aOStmtIn.Functional) :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun j => roundKnowledgeError L ℓ' i) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  use fun _ => SumcheckWitness L ℓ' i.castSucc
  use iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i
  use iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i
  intro stmtIn witIn prover j
  sorry

end

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

/-- The prover for the final sumcheck step -/
noncomputable def finalSumcheckProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  PrvState := fun
    | 0 => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ')
    | _ => Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j) × SumcheckWitness L ℓ' (Fin.last ℓ') × L
  input := fun ⟨⟨stmt, oStmt⟩, wit⟩ => (stmt, oStmt, wit)

  sendMessage
  | ⟨0, _⟩ => fun ⟨stmtIn, oStmtIn, witIn⟩ => do
    let s' : L := witIn.t'.val.eval stmtIn.challenges
    pure ⟨s', (stmtIn, oStmtIn, witIn, s')⟩

  receiveChallenge
  | ⟨0, h⟩ => nomatch h -- No challenges in this step

  output := fun ⟨stmtIn, oStmtIn, witIn, s'⟩ => do
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmtIn.challenges
      original_claim := s'
    }
    let witOut : WitMLP L ℓ' := {
      t := witIn.t'
    }
    pure (⟨stmtOut, oStmtIn⟩, witOut)

/-- The verifier for the final sumcheck step, as an instance of the family-shared
check-then-update one-message verifier (`RingSwitching.guardedMessageRoundOracleVerifier`,
`RoundVerifiers.lean`): query the final constant `s'` (step 7), then

8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
   decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`;
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
   `⋅ e_u) ⋅ s'` (abort on failure), and hands the accepted claim
   to the downstream opening. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) :=
  guardedMessageRoundOracleVerifier
    (check := fun stmtIn (s' : L) =>
      stmtIn.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s')
    (accept := fun stmtIn s' =>
      { t_eval_point := stmtIn.challenges,
        original_claim := s' })

omit [NeZero κ] [Nontrivial L] [Fintype L] [Fintype K] [DecidableEq K]
    [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Exact final verifier execution: rejection aborts and acceptance forwards the message itself. -/
theorem finalSumcheckVerifier_verify
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : FullTranscript (pSpecFinalSumcheck L)) :
    let msg : L := tr.messages ⟨0, rfl⟩
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.verify (stmt, oStmt) tr =
      (if stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
          stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching * msg then
        pure (⟨stmt.challenges, msg⟩, oStmt) else failure) := by
  apply guardedMessageRoundOracleVerifier_verify

/-- The oracle reduction for the final sumcheck step -/
noncomputable def finalSumcheckOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L) where
  prover := finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn
  verifier := finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn

omit [NeZero κ] [Nontrivial L] [DecidableEq L] [Fintype L] [Fintype K]
    [DecidableEq K] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/-- The honest final prover sends the packed evaluation and forwards that same opening. -/
theorem finalSumcheckProver_run
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : RingSwitching.SumcheckWitness L ℓ' (Fin.last ℓ')) :
    (finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).run (stmt, oStmt) wit =
      pure ((fun | ⟨0, _⟩ => MvPolynomial.eval stmt.challenges wit.t'.val),
        (⟨stmt.challenges, MvPolynomial.eval stmt.challenges wit.t'.val⟩, oStmt), ⟨wit.t'⟩) := by
  have hstep : (finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).runToRound (Fin.last 1)
      (stmt, oStmt) wit = pure
        ((fun | ⟨0, _⟩ => MvPolynomial.eval stmt.challenges wit.t'.val),
          (stmt, oStmt, wit, MvPolynomial.eval stmt.challenges wit.t'.val)) := by
    refine (Prover.runToRound_succ (0 : Fin 1) (stmt, oStmt) wit
      (finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn)).trans ?_
    rw [Prover.processRound_of_dir_eq_P_to_V (0 : Fin 1) rfl]
    simp only [Fin.castSucc_zero, Prover.runToRound_zero_of_prover_first,
      finalSumcheckProver, liftM_pure, pure_bind]
    congr 2
    funext i
    fin_cases i
    rfl
  unfold Prover.run
  rw [hstep]
  simp only [finalSumcheckProver, liftM_pure, pure_bind]
  rfl


omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
set_option backward.isDefEq.respectTransparency false in
/-- Perfect completeness of the final reduction for every initial oracle-state distribution. -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn).perfectCompleteness init impl
      (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')) aOStmtIn.toRelInput := by
  unfold OracleReduction.perfectCompleteness
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  obtain ⟨_, hs, hsum, hcompat⟩ := hIn
  have hc := (RingSwitching.final_consistency P h_l stmt wit hs).mp hsum
  have hp := finalSumcheckProver_run κ L K P ℓ ℓ' aOStmtIn stmt oStmt wit
  simp only [OracleReduction.toReduction, finalSumcheckOracleReduction,
    Reduction.run, hp, liftM_pure, pure_bind, Verifier.run, finalSumcheckVerifier_verify,
    FullTranscript.messages, hc, if_pos, OptionT.run_pure, Option.getM_some] at hx
  simp only [support_pure, Set.mem_singleton_iff] at hx
  refine ⟨_, hx, ?_, rfl⟩
  exact ⟨rfl, hcompat⟩

/-- The final step has no challenge rounds and contributes no knowledge error. -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := 0

/-- The round-by-round extractor for the final sumcheck step -/
noncomputable def finalSumcheckRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ')
      × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' (Fin.last ℓ'))
    (WitOut := WitMLP L ℓ')
    (pSpec := pSpecFinalSumcheck L)
    (WitMid := fun _m => SumcheckWitness L ℓ' (Fin.last ℓ')) where
  eqIn := rfl
  extractMid := fun _m ⟨_, _⟩ _trSucc witMidSucc => witMidSucc

  extractOut := fun ⟨stmtIn, _⟩ _tr witOut => {
    t' := witOut.t,
    H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := stmtIn.ctx) (t := witOut.t)
      (i := Fin.last ℓ') (challenges := stmtIn.challenges)
  }

/- This follows the KState of `finalSumcheckKStateProp` in `BinaryBasefold`.
though the multiplier poly is different. -/
def finalSumcheckKStateProp {m : Fin (1 + 1)} (tr : Transcript m (pSpecFinalSumcheck L))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (witMid : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) : Prop :=
  match m with
  | ⟨0, _⟩ => -- same as relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := Fin.last ℓ')
      (stmt := stmt) (oStmt := oStmt) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- implied by relOut + local checks via extractOut proofs
    let tr_so_far := (pSpecFinalSumcheck L).take 1 (by omega)
    let i_msg0 : tr_so_far.MessageIdx := ⟨⟨0, by omega⟩, rfl⟩
    let c : L := (ProtocolSpec.Transcript.equivMessagesChallenges (k := 1)
      (pSpec := pSpecFinalSumcheck L) tr).1 i_msg0
    let stmtOut : MLPEvalStatement L ℓ' := {
      t_eval_point := stmt.challenges,
      original_claim := c
    }
    let sumcheckFinalLocalCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c
    let final_eval : Prop := witMid.t'.val.eval stmt.challenges = c
    sumcheckFinalLocalCheck ∧ final_eval
    ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid
    ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L]
    [DecidableEq L] in
/-- An accepted final message preserves knowledge for the same anchored residual witness. -/
theorem finalSumcheckKStateProp_next (m : Fin 1) (hDir : (pSpecFinalSumcheck L).dir m = .P_to_V)
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : (pSpecFinalSumcheck L).Transcript m.castSucc)
    (msg : (pSpecFinalSumcheck L).Type m)
    (wit : RingSwitching.SumcheckWitness L ℓ' (Fin.last ℓ'))
    (h : finalSumcheckKStateProp κ L K P ℓ ℓ' h_l aOStmtIn (tr.concat msg) stmt wit oStmt) :
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt wit oStmt := by
  fin_cases m
  simp only [finalSumcheckKStateProp] at h ⊢
  obtain ⟨hc, heval, hs, hcompat⟩ := h
  refine ⟨trivial, hs, ?_, hcompat⟩
  apply (RingSwitching.final_consistency P h_l stmt wit hs).mpr
  rw [heval]
  exact hc

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L]
    [NeZero ℓ] [NeZero ℓ'] in
set_option backward.isDefEq.respectTransparency false in
/--
A positive-probability related output satisfies the final knowledge state under output
extraction.
-/
theorem finalSumcheckKStateProp_full {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : FullTranscript (pSpecFinalSumcheck L))
    (wit : WitMLP L ℓ')
    (h : Pr[ fun out => (out, wit) ∈ aOStmtIn.toRelInput |
      OptionT.mk do
        (simulateQ impl ((finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.run
          (stmt, oStmt) tr)).run' (← init)] > 0) :
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l aOStmtIn (m := Fin.last 1) tr stmt
      ((finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn).extractOut
        (stmt, oStmt) tr wit) oStmt := by
  rw [Verifier.run, finalSumcheckVerifier_verify] at h
  split at h
  · rename_i hc
    change Pr[ fun out => (out, wit) ∈ aOStmtIn.toRelInput |
      OptionT.mk (init >>= fun _ => pure
        (some ((⟨stmt.challenges, tr.messages ⟨0, rfl⟩⟩ : MLPEvalStatement L ℓ'), oStmt)))] > 0 at h
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨out, hout, hr⟩ := h
    simp only [OptionT.mem_support_iff, OptionT.run_mk, support_bind_const, support_pure,
      Set.mem_singleton_iff] at hout
    have ho := Option.some.inj hout.1
    subst out
    change (tr.messages ⟨0, rfl⟩ : L) = MvPolynomial.eval stmt.challenges wit.t.val ∧
      aOStmtIn.initialCompatibility (wit.t, oStmt) at hr
    simpa only [finalSumcheckKStateProp, finalSumcheckRbrExtractor,
      witnessStructuralInvariant, true_and, and_true] using ⟨hc, hr.1.symm, hr.2⟩
  · change Pr[ fun out => (out, wit) ∈ aOStmtIn.toRelInput |
      OptionT.mk (init >>= fun _ => pure none)] > 0 at h
    simp [probEvent_pos_iff] at h

/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).KnowledgeStateFunction init impl
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (extractor := finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
  where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    finalSumcheckKStateProp κ L K P ℓ ℓ' h_l
    (m := m) (tr := tr) (stmt := stmt) (witMid := witMid) (oStmt := oStmt)
  toFun_empty := fun stmt witMid => by
    simp only [sumcheckRoundRelation, sumcheckRoundRelationProp, Fin.val_last, cast_eq,
      Set.mem_ofPred_eq, finalSumcheckKStateProp, masterKStateProp, true_and]
  toFun_next := fun m hDir stmt tr msg witMid h => by
    rcases stmt with ⟨stmt, oStmt⟩
    change finalSumcheckKStateProp κ L K P ℓ ℓ' h_l aOStmtIn tr stmt witMid oStmt
    exact finalSumcheckKStateProp_next κ L K P ℓ ℓ' h_l aOStmtIn
      m hDir stmt oStmt tr msg witMid h
  toFun_full := fun stmt tr witOut h => by
    rcases stmt with ⟨stmt, oStmt⟩
    exact finalSumcheckKStateProp_full.{0} κ L K P ℓ ℓ' h_l aOStmtIn
      init impl stmt oStmt tr witOut h

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
/-- Exact worst-case knowledge soundness: there are no challenge bad events in the final step. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.rbrKnowledgeSoundnessWorstCaseWith
      init impl (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      aOStmtIn.toRelInput (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
      (finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
      (finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl)
      (fun _ => finalSumcheckRbrKnowledgeError) := by
  rintro _ ⟨j, hj⟩
  fin_cases j
  cases hj

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
/-- Worst-case knowledge soundness with the final extractor and knowledge state. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl (sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      aOStmtIn.toRelInput (fun _ => finalSumcheckRbrKnowledgeError) :=
  ⟨(fun _ => SumcheckWitness L ℓ' (Fin.last ℓ')),
    finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn,
    finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl,
    finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith
      κ L K P ℓ ℓ' h_l aOStmtIn init impl⟩

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
/-- Prover-averaged knowledge soundness of the zero-challenge final reduction. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase
      κ L K P ℓ ℓ' h_l aOStmtIn init impl)

end FinalSumcheckStep

section LargeFieldReduction

/-- Composed oracle verifier for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleVerifier :=
  OracleVerifier.seqCompose (m := ℓ') (oSpec := []ₒ)
    (pSpec := fun _ => pSpecSumcheckRound L)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (V := fun (i: Fin ℓ') => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)

/-- Composed oracle reduction for the SumcheckStep (seqCompose over ℓ') -/
@[reducible]
def sumcheckLoopOracleReduction :
    OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecSumcheckLoop L ℓ')
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := SumcheckWitness L ℓ' (Fin.last ℓ')) :=
  OracleReduction.seqCompose (m:=ℓ') (oSpec:=[]ₒ)
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun (i: Fin ℓ') => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)

/-- Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleVerifier :=
  OracleVerifier.append (oSpec:=[]ₒ)
    (V₁:=sumcheckLoopOracleVerifier κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (V₂:=finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (pSpec₂:=pSpecFinalSumcheck L)

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness :
    OracleReduction.perfectCompleteness
    (oracleReduction := coreInteractionOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (init := init)
    (impl := impl) := by
  refine OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ')) _ _
    (Verifier.GuardedForm.ofEmpty _ (fun stmt =>
      (⟨0, fun _ => 0, stmt.1.ctx⟩, stmt.2)))
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨fun _ => 0, 0⟩, stmt.2)))
    (fun _ => Or.inl inferInstance) ?_ ?_
  · apply OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers
      (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
      (R := fun i => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (hP := fun _ => inferInstance)
      (hV := fun _ => Verifier.GuardedForm.ofEmpty _ (fun stmt =>
        (⟨0, fun _ => 0, stmt.1.ctx⟩, stmt.2)))
      (h := fun i s =>
        iteratedSumcheckOracleReduction_perfectCompleteness (κ := κ) (L := L) (K := K)
          (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
          (init := pure s) (impl := impl) i)
  · intro s
    exact finalSumcheckOracleReduction_perfectCompleteness (κ := κ) (L := L) (K := K)
      (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn)
      (init := pure s) (impl := impl)

/-- RBR knowledge error for a degree-`d` sumcheck loop, obtained from the `seqCompose`
challenge-index decomposition. -/
def sumcheckLoopRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecSumcheckLoopWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  let ij := ProtocolSpec.seqComposeChallengeIdxToSigma
    (pSpec := fun _ : Fin ℓ' => pSpecSumcheckRoundWithDegree L d) j
  Sumcheck.Structured.roundKnowledgeError L ℓ' ij.1 d

def sumcheckLoopRbrKnowledgeError (j : (pSpecSumcheckLoop L ℓ').ChallengeIdx) : ℝ≥0 :=
  sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' 2 j

/-- RBR knowledge error for the core interaction with a degree-`d` sumcheck loop. The loop
contributes `d / |L|` per sumcheck challenge; the final message contributes no error. -/
def coreInteractionRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecCoreInteractionWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' d)
    (g := fun _ => finalSumcheckRbrKnowledgeError)
    (ChallengeIdx.sumEquiv.symm j)

/-- Standard Binius ring-switching RBR knowledge error (`d = 2`) with exact final-step splitting. -/
def coreInteractionRbrKnowledgeError (j : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  coreInteractionRbrKnowledgeErrorWithDegree L ℓ' 2 j

-- TODO: iteratedSumcheckLoop_rbrKnowledgeSoundness

section
local instance : DecidableEq K := Classical.decEq K

omit [Fintype K] [DecidableEq K] in
/-- RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hfunctional : aOStmtIn.Functional) :
    OracleVerifier.rbrKnowledgeSoundness
    (verifier := coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) 0)
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' 0)
    (WitOut := WitMLP L ℓ')
    (init := init)
    (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
    (relOut := aOStmtIn.toRelInput)
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  sorry


end

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase
