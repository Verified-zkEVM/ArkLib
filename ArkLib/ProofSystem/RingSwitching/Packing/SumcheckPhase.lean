/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.Spec
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.RingSwitching.Packing.FinalAlgebra
public import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.GuardedRoundByRound
public import ArkLib.OracleReduction.Composition.Sequential.Append
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Security.GuardedRoundByRound

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

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
  sends the round polynomial, the verifier checks it against the running target (aborting on
  failure) and folds in a fresh challenge. This loop is the main source of the reduction's
  knowledge error (`2/|L|` per round).
* **Final step** — the prover sends the residual value `s' = t'(r')`; the verifier checks
  the last running target against `(eq̃-consistency value) · s'` — where the consistency
  value reconstructs, from the row coordinates of the final eq̃-tensor, what the multiplier
  contributes at `r'` (`compute_final_eq_value_eq_eval`) — and, if it passes, outputs the
  evaluation claim `t'(r') = s'`. The verifier is the family-shared one-message
  check-then-update verifier (`RingSwitching.messageRoundOracleVerifier`).

## Protocol steps ([DP24] Construction 3.1, steps 6–9)

6. P and V execute the following loop:
   for `i ∈ {0, ..., ℓ'-1}` do
     P sends V the polynomial `hᵢ(X) := Σ_{w ∈ {0,1}^{ℓ'-i-1}} h(r'₀, ..., r'_{i-1}, X, w₀, ...,
     w_{ℓ'-i-2})`.
     V requires `sᵢ ?= hᵢ(0) + hᵢ(1)`. V samples `r'ᵢ ← L`, sets `s_{i+1} := hᵢ(r'ᵢ)`,
     and sends P `r'ᵢ`.
7. `P` computes `s' := t'(r'_0, ..., r'_{ℓ'-1})` and sends `V` `s'`.
8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
    decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u` (row coordinates on the right tensor
    factor).
9. `V` requires
   `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1}) ⋅ e_u) ⋅ s'`.

## Security

* Completeness: `iteratedSumcheckOracleReduction_perfectCompleteness`,
  `finalSumcheckOracleReduction_perfectCompleteness`, and their composition
  `coreInteraction_perfectCompleteness` through the guarded-verifier composition theorems.
* Worst-case round-by-round knowledge soundness of a round,
  `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase`, with error `2/|L|` for every
  fixed round message; `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` is its averaged
  form. An extraction failure means the sent round polynomial differs from the honest round
  polynomial of a compatible packed polynomial (`iteratedSumcheck_extractionFailure_imp`).
  The challenge must then be a common point of the two. Under `hUnique : aOStmtIn.Functional` the
  honest polynomial is fixed before the challenge, so `prob_eval_eq_le` bounds this by `2/|L|`.
* The final step sends no challenge, so `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase`
  holds at any error.
* These per-round and final-step results are sorry-free and axiom-clean under their stated
  hypotheses (`hUnique` and `[NoZeroDivisors L]`). Each is primarily stated with the extractor
  and knowledge-state function named (`…_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`), with
  the existential and averaged forms as corollaries.
* The composite `coreInteraction_rbrKnowledgeSoundnessWorstCase` (sumcheck loop, then final step)
  is **unconditional**: it is composed from these by the guarded worst-case composition theorems
  `OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded` and
  `OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`, and is sorry-free and
  axiom-clean under the same hypotheses. `coreInteraction_rbrKnowledgeSoundness` is its averaged
  form.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
-/

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

The per-round protocol code lives in `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`
as `round{PrvState, OracleProver, OracleVerifier, OracleReduction}`,
`getRoundProverFinalOutput`, and `roundKnowledgeError`, parameterized over a generic
`Context : Type` and `OStmtIn : ιₛᵢ → Type`. The round verifier aborts on a failed round check
(`Sumcheck.Structured.roundOracleVerifierGuardedForm`).

The wrappers below specialize `Context := RingSwitchingBaseContext κ L K ℓ` and
`OStmtIn := aOStmtIn.OStmtIn`. They keep the `iteratedSumcheck*` names (these are what the
sumcheck loop iterates over) and are `@[reducible]` so that the soundness proofs and the
seqCompose loop can access fields like `.KnowledgeStateFunction` / `.rbrKnowledgeSoundness`
through them. -/

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

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

/-- The round verifier's guard and verdict as data. -/
def iteratedSumcheckGuardedForm (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier.GuardedForm :=
  Sumcheck.Structured.roundOracleVerifierGuardedForm (L := L) ℓ' (boolDomain L ℓ')
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) (d := 2) i

omit [Fintype L] [DecidableEq L] [SampleableType L] [NeZero ℓ'] in
/-- The honest round polynomial sums over the Boolean values to the running target. -/
theorem sum_getSumcheckRoundPoly_boolDomain (i : Fin ℓ')
    (H : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)]) :
    ∑ b ∈ (boolDomain L ℓ').points i, (getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i H).val.eval b =
      ∑ x ∈ (boolDomain L (ℓ' - i.castSucc)).cube, H.val.eval x :=
  sum_getSumcheckRoundPoly_uniform ℓ' (boolEmbedding L) i H

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L] [Fintype K]
  [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- The honest round output: the next round polynomial is the structured projection at the
extended challenges, and the round polynomial evaluates at the challenge to its Boolean sum. -/
theorem iteratedSumcheck_honest_next (i : Fin ℓ')
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (wit : SumcheckWitness L ℓ' i.castSucc)
    (hs : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit) (h : L⦃≤ 2⦄[X]) (c : L) :
    (getRoundProverFinalOutput ℓ' (RingSwitchingBaseContext κ L K ℓ P)
        (OStmtIn := aOStmtIn.OStmtIn) 2 i (stmt, oStmt, wit, h, c)).2.H.val =
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmt.ctx) (t := wit.t') (i := i.succ)
        (challenges := Fin.snoc stmt.challenges c)).val := by
  have hdim : ℓ' - i - 1 = ℓ' - i.succ := by simp only [Fin.val_succ]; omega
  rw [getRoundProverFinalOutput_H ℓ' i stmt oStmt wit h c hdim]
  unfold witnessStructuralInvariant at hs
  rw [hs]
  exact projectToMidSumcheckPolyWithParam_succ ℓ' _ _ _ i _ c hdim

omit [Fintype L] [Fintype K] [DecidableEq K] [NeZero κ] [NeZero ℓ] [NeZero ℓ'] in
theorem iteratedSumcheckOracleReduction_perfectCompleteness (i : Fin ℓ') :
    OracleReduction.perfectCompleteness
      (pSpec := pSpecSumcheckRound L)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (oracleReduction := iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
      (init := init)
      (impl := impl) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  let h := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i wit.H
  let : ∀ j, OracleInterface ((pSpecSumcheckRound L).Challenge j) :=
    fun _ => OracleInterface.instDefault
  let sample : OracleComp ([]ₒ + [(pSpecSumcheckRound L).Challenge]ₒ) L :=
    liftM (query (spec := [(pSpecSumcheckRound L).Challenge]ₒ) ⟨⟨1, rfl⟩, ()⟩ :
      OracleComp [(pSpecSumcheckRound L).Challenge]ₒ L)
  let out := fun c : L => getRoundProverFinalOutput ℓ'
    (RingSwitchingBaseContext κ L K ℓ P) (OStmtIn := aOStmtIn.OStmtIn) 2 i
    (stmt, oStmt, wit, h, c)
  have hp : (iteratedSumcheckOracleProver κ L K P ℓ ℓ' aOStmtIn i).run
      (stmt, oStmt) wit = (do
        let c ← sample
        pure (FullTranscript.mk2 (pSpec := pSpecSumcheckRound L) h c, (out c).1, (out c).2)) := by
    simp only [pSpecSumcheckRound, ChallengeIdx, Challenge, Prover.run,
      Fin.reduceLast, iteratedSumcheckOracleProver, roundOracleProver,
      Sumcheck.Structured.pSpecSumcheckRound, Fin.isValue, MessageIdx, Message,
      Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two,
      Prover.runToRound, reduceAdd, Fin.induction_two', Prover.processRound,
      bind_pure_comp, pure_bind, liftM_pure, LawfulApplicative.map_pure,
      HasQuery.instOfMonadLift_query, sample, h, out]
    change (sample >>= fun c => pure
      (((default : (pSpecSumcheckRound L).Transcript 0).concat (m := 0) h).concat (m := 1) c,
        (out c).1, (out c).2)) = _
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro c
    congr 1
    exact congrArg (fun tr => (tr, (out c).1, (out c).2))
      (FullTranscript.mk2_eq_snoc_snoc (pSpec := pSpecSumcheckRound L) h c).symm
  obtain ⟨-, hs, hcons, hcompat⟩ := hIn
  have hc : (∑ b ∈ (boolDomain L ℓ').points i, h.val.eval b) = stmt.sumcheck_target := by
    rw [hcons]
    exact sum_getSumcheckRoundPoly_boolDomain L ℓ' i wit.H
  have hrel (c : L) : ((out c).1, (out c).2) ∈
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ := by
    have hnext := iteratedSumcheck_honest_next κ L K P ℓ ℓ' h_l aOStmtIn i stmt oStmt wit hs h c
    refine ⟨trivial, hnext, ?_, hcompat⟩
    have hdim : ℓ' - i - 1 = ℓ' - i.succ := by simp only [Fin.val_succ]; omega
    change h.val.eval c = ∑ x ∈ (boolDomain L (ℓ' - ↑i.succ)).cube, (out c).2.H.val.eval x
    rw [getRoundProverFinalOutput_H ℓ' i stmt oStmt wit h c hdim]
    exact eval_getSumcheckRoundPoly_uniform ℓ' (boolEmbedding L) i wit.H c hdim
  let G :
      (iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i).toReduction.verifier.GuardedForm :=
    iteratedSumcheckGuardedForm κ L K P ℓ ℓ' aOStmtIn i
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ MonadAttach.support ((iteratedSumcheckOracleProver κ L K P ℓ ℓ' aOStmtIn i).run
    (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp, bind_assoc] at hx
  simp only [pure_bind] at hx
  obtain ⟨c, _, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  rw [show G.check (stmt, oStmt) (FullTranscript.mk2 h c) = true from decide_eq_true hc] at hx
  simp only [↓reduceIte, mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, hrel c, rfl⟩

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

/-- Witness type at each message index of a sumcheck round. At messages `0` and `1` it is the
input-round witness; after the challenge it is the output-round witness, so that `extractOut` is
the identity. `extractMid` at message `1` reprojects the output witness to the input round. -/
def iteratedSumcheckWitMid (i : Fin ℓ') : Fin (2 + 1) → Type :=
  fun m => match m with
  | ⟨0, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨1, _⟩ => SumcheckWitness L ℓ' i.castSucc
  | ⟨2, _⟩ => SumcheckWitness L ℓ' i.succ

noncomputable def iteratedSumcheckRbrExtractor (i : Fin ℓ') :
  Extractor.RoundByRound []ₒ
    (StmtIn := (Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) i.castSucc) × (∀ j, aOStmtIn.OStmtIn j))
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L)
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i)) where
  eqIn := rfl
  extractMid := fun m ⟨stmtIn, _⟩ _tr witMidSucc =>
    match m with
    | ⟨0, _⟩ => witMidSucc  -- WitMid 1 → WitMid 0, both SumcheckWitness i.castSucc
    | ⟨1, _⟩ =>
      -- WitMid 2 → WitMid 1: extract backward from the output witness using input challenges
      {
        t' := witMidSucc.t',
        H := projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := stmtIn.ctx) (t := witMidSucc.t')
          (i := i.castSucc) (challenges := stmtIn.challenges)
      }
  extractOut := fun _stmtIn _fullTranscript witOut => witOut

/-- Knowledge state of a sumcheck round:
- `m = 0`: the input relation (`masterKStateProp` at `i.castSucc`);
- `m = 1`: after `P` sends `hᵢ(X)`, the round check holds and `hᵢ` is the honest round polynomial;
- `m = 2`: after `V` sends `r'ᵢ`, the round check holds and the output statement and witness
  satisfy `masterKStateProp` at `i.succ`. -/
def iteratedSumcheckKStateProp (i : Fin ℓ') (m : Fin (2 + 1))
    (tr : Transcript m (pSpecSumcheckRound L))
    (stmtMid : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (witMid : iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i) m)
    (oStmtMid : ∀ j, aOStmtIn.OStmtIn j) :
    Prop :=
  match m with
  | ⟨0, _⟩ => -- Same as relIn
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l
      aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks := True)
  | ⟨1, _⟩ => -- After P sends hᵢ(X), before V sends r'ᵢ
    let h_star : ↥L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') (i := i) (h := witMid.H)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.castSucc)
      (stmt := stmtMid) (oStmt := oStmtMid) (wit := witMid)
      (localChecks :=
        let explicitVCheck :=
          (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmtMid.sumcheck_target
        let localizedRoundPolyCheck := h_i = h_star
        explicitVCheck ∧ localizedRoundPolyCheck
      )
  | ⟨2, _⟩ => -- After V sends r'ᵢ: the output state (witMid is already SumcheckWitness i.succ)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ :=
      { ctx := stmtMid.ctx, sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtMid.challenges r_i' }
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.succ)
      (stmt := stmtOut) (oStmt := oStmtMid) (wit := witMid)
      (localChecks :=
        (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = stmtMid.sumcheck_target
      )

/-- Knowledge state function (KState) for single round -/
def iteratedSumcheckKnowledgeStateFunction (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).KnowledgeStateFunction init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    iteratedSumcheckKStateProp κ L K P ℓ ℓ' h_l
      (i := i) (m := m) (tr := tr) (stmtMid := stmt) (witMid := witMid) (oStmtMid := oStmt)
  toFun_empty := fun ⟨stmt, oStmt⟩ wit => by
    rfl
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
  toFun_full := fun ⟨stmt, oStmt⟩ tr witOut h => by
    change (pSpecSumcheckRound L).FullTranscript at tr
    obtain ⟨hcheck, hrel⟩ :=
      (iteratedSumcheckGuardedForm κ L K P ℓ ℓ' aOStmtIn i).check_and_of_prEvent_pos h
    exact ⟨of_decide_eq_true hcheck, hrel.2⟩

section
local instance : DecidableEq K := Classical.decEq K

omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K] [NeZero ℓ]
  [NeZero ℓ'] in
/-- An extraction failure at a round challenge is a disagreement of the sent round polynomial with
the honest round polynomial of a compatible packed polynomial, at which the challenge is a common
point of the two. -/
theorem iteratedSumcheck_extractionFailure_imp (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (tr : Transcript (⟨1, rfl⟩ : (pSpecSumcheckRound L).ChallengeIdx).1.castSucc
      (pSpecSumcheckRound L)) (r_i' : L)
    (hfail : rbrExtractionFailureEvent
      (iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
        (init := init) (impl := impl) i).toFun
      (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
      ⟨1, rfl⟩ stmtOStmtIn tr r_i') :
    ∃ t' : MultilinearPoly L ℓ',
      aOStmtIn.initialCompatibility (t', stmtOStmtIn.2) ∧
      let h_star : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i
        (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
          (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
          (ctx := stmtOStmtIn.1.ctx) (t := t')
          (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges))
      let h_i : L⦃≤ 2⦄[X] := tr ⟨0, Nat.zero_lt_one⟩
      h_i ≠ h_star ∧ h_i.val.eval r_i' = h_star.val.eval r_i' := by
  obtain ⟨witMid, hbefore, hafter⟩ := hfail
  obtain ⟨hcheck, hs, hcons, hcompat⟩ := hafter
  set h_i : L⦃≤ 2⦄[X] := tr ⟨0, Nat.zero_lt_one⟩
  have hdim : ℓ' - i - 1 = ℓ' - i.succ := by simp only [Fin.val_succ]; omega
  refine ⟨witMid.t', hcompat, fun heq => hbefore ⟨⟨hcheck, heq⟩, rfl, ?_, hcompat⟩, ?_⟩
  · -- the before-state consistency follows from the round check and the honest round sum
    change stmtOStmtIn.1.sumcheck_target = _
    rw [← hcheck]
    change (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b) = _
    rw [heq]
    exact sum_getSumcheckRoundPoly_boolDomain L ℓ' i _
  · -- the after-state consistency is the round polynomial's value at the challenge
    change h_i.val.eval r_i' = ∑ x ∈ (boolDomain L (ℓ' - ↑i.succ)).cube, witMid.H.val.eval x
      at hcons
    rw [hcons]
    unfold witnessStructuralInvariant at hs
    rw [hs]
    have key := eval_getSumcheckRoundPoly_uniform ℓ' (boolEmbedding L) i
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
        (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)) r_i' hdim
    rw [projectToMidSumcheckPolyWithParam_succ ℓ' _ _ _ i _ r_i' hdim] at key
    exact key.symm

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- For a fixed round message, the probability over the round challenge that extraction fails is
at most `2/|L|`, when the oracle statement determines the packed polynomial. -/
theorem iteratedSumcheck_extractionFailure_le [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (tr : Transcript (⟨1, rfl⟩ : (pSpecSumcheckRound L).ChallengeIdx).1.castSucc
      (pSpecSumcheckRound L)) :
    Pr{let c ← $ᵗ L}[rbrExtractionFailureEvent
      (iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
        (init := init) (impl := impl) i).toFun
      (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
      ⟨1, rfl⟩ stmtOStmtIn tr c] ≤ roundKnowledgeError L ℓ' i := by
  have : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  by_cases hcompat : ∃ t : MultilinearPoly L ℓ',
      aOStmtIn.initialCompatibility (t, stmtOStmtIn.2)
  · obtain ⟨t₀, ht₀⟩ := hcompat
    let h_star : L⦃≤ 2⦄[X] := getSumcheckRoundPoly ℓ' (boolDomain L ℓ') i
      (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := t₀)
        (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges))
    let h_i : L⦃≤ 2⦄[X] := tr ⟨0, Nat.zero_lt_one⟩
    by_cases hne : h_i = h_star
    · -- the sent polynomial is the honest one, so no challenge makes extraction fail
      refine (prEvent_eq_zero_of_forall_not _ _ fun c hfail => ?_).le.trans _root_.zero_le
      obtain ⟨t', ht', hne', -⟩ := iteratedSumcheck_extractionFailure_imp κ L K P ℓ ℓ' h_l
        aOStmtIn i stmtOStmtIn tr c hfail
      rw [hUnique stmtOStmtIn.2 t' t₀ ht' ht₀] at hne'
      exact hne' hne
    · refine (prEvent_mono _ _ _ (fun c hfail => ?_)).trans
        (prob_eval_eq_le (d := 2) hne)
      obtain ⟨t', ht', -, heval⟩ := iteratedSumcheck_extractionFailure_imp κ L K P ℓ ℓ' h_l
        aOStmtIn i stmtOStmtIn tr c hfail
      rw [hUnique stmtOStmtIn.2 t' t₀ ht' ht₀] at heval
      exact heval
  · refine (prEvent_eq_zero_of_forall_not _ _ fun c hfail => ?_).le.trans _root_.zero_le
    obtain ⟨t', ht', -⟩ := iteratedSumcheck_extractionFailure_imp κ L K P ℓ ℓ' h_l
      aOStmtIn i stmtOStmtIn tr c hfail
    exact hcompat ⟨t', ht'⟩

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Worst-case RBR knowledge soundness for a single round oracle verifier, naming the extractor
`iteratedSumcheckRbrExtractor` and the knowledge-state function
`iteratedSumcheckKnowledgeStateFunction`, with error `2/|L|` at the round challenge: the bound
holds for every input statement and every sent round polynomial, over the round challenge alone.
`hUnique` says the oracle statement determines the packed polynomial. -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor
    [NoZeroDivisors L] (hUnique : aOStmtIn.Functional) (i : Fin ℓ') :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (verifier := (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (WitMid := iteratedSumcheckWitMid L ℓ' i)
      (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
      (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i)
      (rbrKnowledgeError := fun _ => roundKnowledgeError L ℓ' i) :=
  Verifier.rbrKnowledgeSoundnessWorstCaseWith_of_two_message
    (pSpec := pSpecSumcheckRound L) rfl rfl
    (iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
    (iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i)
    (iteratedSumcheck_extractionFailure_le κ L K P ℓ ℓ' h_l aOStmtIn hUnique i)

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Existential worst-case RBR knowledge soundness for a single round oracle verifier, with error
`2/|L|`: a corollary of
`iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`. -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) (i : Fin ℓ') :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun _ => roundKnowledgeError L ℓ' i) :=
  (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr ⟨_, _, _,
    iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor κ L K P ℓ ℓ'
      h_l aOStmtIn hUnique i⟩

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- RBR knowledge soundness for a single round oracle verifier, with error `2/|L|` at the round
challenge: the averaged form of `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun _ => roundKnowledgeError L ℓ' i) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l aOStmtIn
      hUnique i)

end

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

omit [NeZero κ] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- At the last round, a structured witness polynomial is the public multiplier value times the
packed polynomial's value at the challenges. -/
theorem finalProjectedEval
    (stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (wit : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (hs : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit) :
    wit.H.val.eval (fun _ => 0) = compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
        wit.t'.val.eval stmt.challenges := by
  rw [show wit.H.val = _ from hs]
  change MvPolynomial.eval _ (fixFirstVariablesOfMQP ℓ' (Fin.last ℓ') _ _) = _
  rw [MvPolynomial.eval_fixFirstVariablesOfMQP_last]
  simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, Polynomial.aeval_X,
    map_mul]
  rw [compute_final_eq_value_eq_eval]

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- At the last round the Boolean cube is a single point, so sumcheck consistency is equality of
the target with the witness polynomial's value. -/
theorem finalConsistency_iff
    (stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (wit : SumcheckWitness L ℓ' (Fin.last ℓ')) :
    sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target wit.H ↔
      stmt.sumcheck_target = wit.H.val.eval (fun _ => 0) := by
  classical
  unfold sumcheckConsistencyProp
  have he : (∑ x ∈ (boolDomain L (ℓ' - (Fin.last ℓ' : Fin (ℓ' + 1)))).cube,
      wit.H.val.eval x) = wit.H.val.eval (fun _ => 0) := by
    apply Finset.sum_eq_single (fun _ => 0)
    · intro b _ hb
      apply False.elim
      apply hb
      funext i
      exact Fin.elim0 (Fin.cast (Nat.sub_self ℓ') i)
    · intro h
      exfalso
      apply h
      simp only [SumcheckDomain.cube, Fintype.mem_piFinset]
      intro i
      exact Fin.elim0 (Fin.cast (Nat.sub_self ℓ') i)
  rw [he]

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
check-then-update one-message verifier (`RingSwitching.messageRoundOracleVerifier`,
`RoundVerifiers.lean`): query the final constant `s'` (step 7), then

8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
   decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`;
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
   `⋅ e_u) ⋅ s'` (**abort** on failure), and hands the accepted claim `t'(r') = s'` to the
   downstream opening. The output claim is `s'` itself, not `e ⋅ s'`: the opening is of `t'`. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) :=
  messageRoundOracleVerifier
    (check := fun stmtIn (s' : L) =>
      stmtIn.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s')
    (accept := fun stmtIn s' => { t_eval_point := stmtIn.challenges, original_claim := s' })

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

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] [NeZero κ] [NeZero ℓ]
  [NeZero ℓ'] in
/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (oracleReduction := finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn)
      (init := init) (impl := impl) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  have hs := hIn.2.1
  have hc : stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
        wit.t'.val.eval stmt.challenges :=
    ((finalConsistency_iff κ L K P ℓ ℓ' stmt wit).mp hIn.2.2.1).trans
      (finalProjectedEval κ L K P ℓ ℓ' h_l stmt wit hs)
  have hp : (finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).run (stmt, oStmt) wit =
      pure (FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L)
        (wit.t'.val.eval stmt.challenges),
        ((⟨stmt.challenges, wit.t'.val.eval stmt.challenges⟩ : MLPEvalStatement L ℓ'), oStmt),
        (⟨wit.t'⟩ : WitMLP L ℓ')) := by
    rw [FullTranscript.mk1_eq_snoc]
    rfl
  let G :
      (finalSumcheckOracleReduction κ L K P ℓ ℓ' h_l aOStmtIn).toReduction.verifier.GuardedForm :=
    messageRoundOracleVerifierGuardedForm _ _
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ MonadAttach.support ((finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).run
    (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp, pure_bind, show G.check (stmt, oStmt)
    (FullTranscript.mk1 (wit.t'.val.eval stmt.challenges)) = true from decide_eq_true hc] at hx
  simp only [↓reduceIte, mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, ⟨rfl, hIn.2.2.2⟩, rfl⟩

/-- RBR knowledge error for the final sumcheck step -/
def finalSumcheckRbrKnowledgeError : ℝ≥0 := (1 : ℝ≥0) / (Fintype.card L)

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

/-- Knowledge state of the final step. After the message, the final check holds, the sent
constant is the packed polynomial's value at the challenges, the packed polynomial is
compatible, and the witness polynomial is structured. -/
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
    let sumcheckFinalLocalCheck : Prop :=
      let eq_tilde_eval : L := compute_final_eq_value κ L K P ℓ ℓ' h_l
        stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching
      stmt.sumcheck_target = eq_tilde_eval * c
    let final_eval : Prop := witMid.t'.val.eval stmt.challenges = c
    sumcheckFinalLocalCheck ∧ final_eval
    ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
    ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid

omit [Fintype L] [Fintype K] [DecidableEq K] in
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
  toFun_next := fun m hDir (stmt, oStmt) tr msg witMid h => by
    have hm : m = 0 := Subsingleton.elim _ _
    subst m
    obtain ⟨hc, he, ho, hs⟩ := h
    change True ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid ∧
      sumcheckConsistencyProp (boolDomain L _) stmt.sumcheck_target witMid.H ∧
      aOStmtIn.initialCompatibility (witMid.t', oStmt)
    refine ⟨trivial, hs, (finalConsistency_iff κ L K P ℓ ℓ' stmt witMid).mpr ?_, ho⟩
    rw [finalProjectedEval κ L K P ℓ ℓ' h_l stmt witMid hs]
    exact hc.trans (congrArg (_ * ·) he.symm)
  toFun_full := fun (stmt, oStmt) tr witOut h => by
    change (pSpecFinalSumcheck L).FullTranscript at tr
    obtain ⟨hc, hrel⟩ := (messageRoundOracleVerifierGuardedForm _ _).check_and_of_prEvent_pos h
    exact ⟨of_decide_eq_true hc, hrel.1.symm, hrel.2, rfl⟩

section
local instance : DecidableEq K := Classical.decEq K

omit [NeZero κ] [Fintype K] [DecidableEq K] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Worst-case round-by-round knowledge soundness for the final sumcheck step, naming the extractor
`finalSumcheckRbrExtractor` and the knowledge-state function `finalSumcheckKnowledgeStateFunction`.
The step sends no challenge, so the round-by-round error is vacuous. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor
    [NoZeroDivisors L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (verifier := (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (WitMid := fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
      (extractor := finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn)
      (kSF := finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  intro stmtIn ⟨j, hj⟩
  cases j using Fin.cases with
  | zero => simp at hj
  | succ j => exact Fin.elim0 j

omit [NeZero κ] [Fintype K] [DecidableEq K] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Existential worst-case round-by-round knowledge soundness for the final sumcheck step: a
corollary of `finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase [NoZeroDivisors L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier.rbrKnowledgeSoundnessWorstCase
      init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) :=
  (Verifier.rbrKnowledgeSoundnessWorstCase_iff_exists_with init impl _ _ _ _).mpr ⟨_, _, _,
    finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCaseWith_rbrExtractor κ L K P ℓ ℓ' h_l
      aOStmtIn init impl⟩

omit [NeZero κ] [Fintype K] [DecidableEq K] [SampleableType L] [NeZero ℓ] [NeZero ℓ'] in
/-- Round-by-round knowledge soundness for the final sumcheck step: the averaged form of
`finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase`. -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l aOStmtIn
      init impl)

end

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
## Security of the composed core interaction
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [NeZero κ] [Fintype L] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum), composed from the
round and final-step completeness by the guarded-verifier composition theorems. -/
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
contributes `d / |L|` per sumcheck challenge. The final step sends no challenge, so the `g` branch
ranges over an empty index type and contributes nothing. -/
def coreInteractionRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecCoreInteractionWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' d)
    (g := fun _ => finalSumcheckRbrKnowledgeError (L := L))
    (ChallengeIdx.sumEquiv.symm j)

/-- Standard Binius ring-switching RBR knowledge error (`d = 2`) with exact final-step splitting. -/
def coreInteractionRbrKnowledgeError (j : (pSpecCoreInteraction L ℓ').ChallengeIdx) : ℝ≥0 :=
  coreInteractionRbrKnowledgeErrorWithDegree L ℓ' 2 j

section
local instance : DecidableEq K := Classical.decEq K

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Worst-case round-by-round knowledge soundness for the core interaction (sumcheck loop, then
final step), at error `2/|L|` per sumcheck challenge.

Composed from the per-round and final-step worst-case theorems by the guarded worst-case
composition theorems `OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded` and
`OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first`. Each round verifier is
guarded by its own check (`iteratedSumcheckGuardedForm`), and the composed sumcheck loop by
`Verifier.GuardedForm.ofEmpty`, available because the ambient oracle specification is empty.
Sorry-free and axiom-clean under `hUnique` and `[NoZeroDivisors L]`. -/
theorem coreInteraction_rbrKnowledgeSoundnessWorstCase [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) :
    Verifier.rbrKnowledgeSoundnessWorstCase init impl
      (verifier := (coreInteractionOracleVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (relOut := aOStmtIn.toRelInput) (coreInteractionRbrKnowledgeError L ℓ') :=
  OracleVerifier.append_rbrKnowledgeSoundnessWorstCase_of_guarded_first _ _
    (Verifier.GuardedForm.ofEmpty _ (fun stmt => (⟨0, fun _ => 0, stmt.1.ctx⟩, stmt.2)))
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (OracleVerifier.seqCompose_rbrKnowledgeSoundnessWorstCase_of_guarded _ _ _
      (fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i) _
      (fun i => iteratedSumcheckGuardedForm κ L K P ℓ ℓ' aOStmtIn i) _
      (fun i => iteratedSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l
        aOStmtIn hUnique i))
    (finalSumcheckOracleVerifier_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l aOStmtIn
      init impl)

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- Round-by-round knowledge soundness for the core interaction (sumcheck loop, then final
step): the averaged form of `coreInteraction_rbrKnowledgeSoundnessWorstCase`. Sorry-free and
axiom-clean under `hUnique` and `[NoZeroDivisors L]`. -/
theorem coreInteraction_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) :
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
    (rbrKnowledgeError := coreInteractionRbrKnowledgeError (L:=L) (ℓ':=ℓ')) :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl
    (coreInteraction_rbrKnowledgeSoundnessWorstCase κ L K P ℓ ℓ' h_l aOStmtIn hUnique)

end

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase
