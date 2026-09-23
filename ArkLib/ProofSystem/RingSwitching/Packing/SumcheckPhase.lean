/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.Spec
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase.Algebra
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase.Projection
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase.Probability
public import ArkLib.ToVCVio.Simulation
public import ArkLib.OracleReduction.Composition.Sequential.General
public import ArkLib.OracleReduction.Composition.Sequential.Append
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Security.RoundByRound
public import ArkLib.OracleReduction.Completeness

/-!
# ArkLib.ProofSystem.RingSwitching.Packing.SumcheckPhase

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal ProbabilityTheory
open Sumcheck.Structured


/-!
# Relocation sumcheck and the final consistency step

Second phase of the interactive packing reduction. After batching, the target `s₀` is (for
an honest prover) the Boolean-cube sum of `h = A · t'` — the packed polynomial times the
public multiplier built from the basis decomposition of eq̃ — so its correctness is exactly a
degree-2 sumcheck claim. Running that sumcheck *relocates* the claim: after `ℓ'` rounds, the
statement about `t'` is anchored at the fresh random point `r'` assembled from the round
challenges, which is what the downstream opening can consume.

* **Iterated rounds** — the `ℓ'`-fold loop reuses the structured degree-2 prover.
  The local verifier rejects an inconsistent round polynomial and otherwise folds in
  a fresh challenge. This loop is the main source of the reduction's knowledge error
  (`2/|L|` per round).
* **Final step** — the prover sends the residual value `s' = t'(r')`; the verifier checks
  the last running target against `(eq̃-consistency value) · s'` — where the consistency
  value reconstructs, from the row coordinates of the final eq̃-tensor, what the multiplier
  contributes at `r'` — and outputs the evaluation claim `t'(r') = s'` after the check passes.

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

## Security statements

Per-round and final-step extractors, knowledge-state functions, knowledge errors (`2/|L|`
per round, `1/|L|` at the final step), and the composed statements for the whole
loop-plus-final-step interaction. Soundness uses functional input-oracle compatibility;
the final multiplier identity uses the separately proved coordinate laws.

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

/-! ## Per-round prover and guarded verifier

The prover state, honest prover, output computation, and error expression reuse
`ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`, parameterized over a generic
context and external oracle statements. The local verifier preserves rejection on a failed
round check, which the terminal knowledge-state proof needs.

For backwards compatibility, the wrappers below preserve the original autobound signature
(via the surrounding variable block — `κ L K ℓ ℓ' aOStmtIn`) by specializing
`Context := RingSwitchingBaseContext κ L K ℓ` and `OStmtIn := aOStmtIn.OStmtIn`. They keep
the `iteratedSumcheck*` names (these are what the sumcheck loop iterates over) and are
`@[reducible]` so that subsequent soundness proofs and the seqCompose loop can still
access fields like `.KnowledgeStateFunction` / `.rbrKnowledgeSoundness` through them. -/

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
    (pSpec := pSpecSumcheckRound L) where
  verify := fun stmt challenges => do
    let h : L⦃≤ 2⦄[X] ← query (spec := [(pSpecSumcheckRound L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard ((∑ b ∈ (boolDomain L ℓ').points i, h.val.eval b) = stmt.sumcheck_target)
    let c : L := challenges ⟨1, rfl⟩
    pure {
      ctx := stmt.ctx
      sumcheck_target := h.val.eval c
      challenges := Fin.snoc stmt.challenges c }
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro j; rfl }

@[reducible]
def iteratedSumcheckOracleReduction (i : Fin ℓ') :
    OracleReduction (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (OStmtIn := aOStmtIn.OStmtIn)
    (WitIn := SumcheckWitness L ℓ' i.castSucc)
    (StmtOut := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ)
    (OStmtOut := aOStmtIn.OStmtIn)
    (WitOut := SumcheckWitness L ℓ' i.succ)
    (pSpec := pSpecSumcheckRound L) where
  prover := iteratedSumcheckOracleProver κ L K P ℓ ℓ' aOStmtIn i
  verifier := iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [NeZero κ] [Fintype L] [SampleableType L] [Fintype K] [DecidableEq K]
  [NeZero ℓ] [NeZero ℓ'] in
private lemma iteratedSumcheckVerifier_run_eq_guarded (i : Fin ℓ')
    (stmt : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : (pSpecSumcheckRound L).FullTranscript) :
    Verifier.run (stmt, oStmt) tr
      (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier =
    if (∑ b ∈ (boolDomain L ℓ').points i,
        (tr.messages ⟨0, rfl⟩).val.eval b) = stmt.sumcheck_target then
      pure ({
        ctx := stmt.ctx
        sumcheck_target := (tr.messages ⟨0, rfl⟩).val.eval (tr.challenges ⟨1, rfl⟩)
        challenges := Fin.snoc stmt.challenges (tr.challenges ⟨1, rfl⟩) }, oStmt)
    else failure := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, iteratedSumcheckOracleVerifier]
  erw [simulateQ_bind]
  erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
  erw [_root_.bind_pure_simulateQ_comp]
  simp only [guard_eq]
  erw [simulateQ_bind]
  erw [simulateQ_ite]
  simp only [OptionT.simulateQ_failure]
  split
  · rename_i h_check
    erw [if_pos h_check]
    erw [simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    rfl
  · rename_i h_check
    erw [if_neg h_check]
    rfl

omit [Fintype L] [Fintype K] [DecidableEq K] [NeZero κ] [NeZero ℓ] in
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
    simp only [pSpecSumcheckRound, ChallengeIdx, Challenge, cast_ofNat, Prover.run,
      Fin.reduceLast, iteratedSumcheckOracleProver, roundOracleProver,
      Sumcheck.Structured.pSpecSumcheckRound, Fin.isValue, MessageIdx, Message,
      cons_val_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_castSucc,
      Lean.Elab.WF.paramLet, cons_val_one, Fin.castSucc_one, Fin.succ_one_eq_two,
      Prover.runToRound, reduceAdd, Prod.mk.eta, Fin.induction_two', Prover.processRound,
      toPFunctor_emptySpec, bind_pure_comp, pure_bind, liftM_pure, LawfulApplicative.map_pure,
      HasQuery.instOfMonadLift_query, map_bind, Functor.map_map, sample, h, out]
    change (sample >>= fun c => pure
      (((default : (pSpecSumcheckRound L).Transcript 0).concat (m := 0) h).concat (m := 1) c,
        (out c).1, (out c).2)) = _
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro c
    congr 1
    exact congrArg (fun tr => (tr, (out c).1, (out c).2))
      (FullTranscript.mk2_eq_snoc_snoc (pSpec := pSpecSumcheckRound L) h c).symm
  have hc : (∑ b ∈ (boolDomain L ℓ').points i, h.val.eval b) =
      stmt.sumcheck_target := by
    rw [hIn.2.2.1]
    dsimp only [h]
    rw [getSumcheckRoundPoly_bool_eq]
    change (∑ b ∈ univ.map (boolEmbedding L),
      (Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) i wit.H).val.eval b) =
        ∑ x ∈ Fintype.piFinset (fun _ : Fin (ℓ' - i) => univ.map (boolEmbedding L)),
          wit.H.val.eval x
    rw [Finset.sum_map]
    change (∑ b : Fin 2, _) = _
    rw [Fin.sum_univ_two]
    exact Binius.BinaryBasefold.getSumcheckRoundPoly_sum_eq
      (𝓑 := boolEmbedding L) (i := i) (h := wit.H)
  have hrel (c : L) : ((out c).1, (out c).2) ∈
      sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ := by
    have hnext : (out c).2.H =
        Binius.BinaryBasefold.projectToNextSumcheckPoly ℓ' i wit.H c :=
      Subtype.ext (getRoundProverFinalOutput_H i stmt oStmt wit h c)
    refine ⟨trivial, ?_, ?_, hIn.2.2.2⟩
    · change (out c).2.H.val = (projectToMidSumcheckPolyWithParam ℓ'
        (RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l) stmt.ctx wit.t'
          i.succ (Fin.snoc stmt.challenges c)).val
      rw [hnext]
      rw [show wit.H = _ from Subtype.ext hIn.2.1]
      exact projectToMidSumcheckPolyWithParam_succ_ringswitching κ L K P ℓ ℓ' h_l
        stmt.ctx wit.t' i stmt.challenges c
    · change h.val.eval c = ∑ x ∈ (boolDomain L (ℓ' - ↑i.succ)).cube,
        (out c).2.H.val.eval x
      rw [hnext]
      dsimp only [h]
      rw [getSumcheckRoundPoly_bool_eq]
      change (Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) i wit.H).val.eval c =
        ∑ x ∈ Fintype.piFinset (fun _ : Fin (ℓ' - i.succ) => univ.map (boolEmbedding L)),
          (Binius.BinaryBasefold.projectToNextSumcheckPoly ℓ' i wit.H c).val.eval x
      exact Binius.BinaryBasefold.projectToNextSumcheckPoly_sum_eq (L := L)
        (𝓑 := boolEmbedding L) (ℓ := ℓ') i wit.H c
  let G :
      (iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i).toReduction.verifier.GuardedForm :=
    {
    check := fun s tr => decide ((∑ b ∈ (boolDomain L ℓ').points i,
      (tr.messages ⟨0, rfl⟩).val.eval b) = s.1.sumcheck_target)
    out := fun s tr => ({
        ctx := s.1.ctx
        sumcheck_target := (tr.messages ⟨0, rfl⟩).val.eval (tr.challenges ⟨1, rfl⟩)
        challenges := Fin.snoc s.1.challenges (tr.challenges ⟨1, rfl⟩) }, s.2)
    verify_eq := by
      intro ⟨s, o⟩ tr
      change Verifier.run (s, o) tr
        (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).toVerifier = _
      erw [iteratedSumcheckVerifier_run_eq_guarded]
      simp only [decide_eq_true_eq] }
  rw [Reduction.run_eq_of_guarded_verifier _ G] at hx
  change x ∈ _root_.support ((iteratedSumcheckOracleProver κ L K P ℓ ℓ' aOStmtIn i).run
    (stmt, oStmt) wit >>= fun r => pure
      (if G.check (stmt, oStmt) r.1 then some (r, G.out (stmt, oStmt) r.1) else none)) at hx
  rw [hp, bind_assoc] at hx
  simp only [pure_bind] at hx
  obtain ⟨c, _, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
  simp only [G, FullTranscript.mk2, FullTranscript.messages, FullTranscript.challenges,
    hc, decide_true, if_true, mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, hrel c, rfl⟩

open scoped NNReal

-- Lifted to `Sumcheck.Structured.roundKnowledgeError` (degree-neutral). Binius ring-switching is
-- the degree-2 case, so this Binius-local abbrev pins `d := 2`.
abbrev roundKnowledgeError (L : Type) [Fintype L] (ℓ : ℕ) (i : Fin ℓ) : NNReal :=
  Sumcheck.Structured.roundKnowledgeError L ℓ i 2

/-- Witness type at each message index for the iterated sumcheck step
  (counterpart of BBF `foldWitMid`, ported from HEAD `iteratedSumcheckWitMid`).
  At m=0,1 we have the input-round witness; at m=2 we have the output-round witness so that
  `extractOut` can be the identity. The reprojection back to the input witness happens in
  `extractMid` at m=1. -/
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

/-- KState for the iterated sumcheck step, ported from HEAD `iteratedSumcheckKStateProp`
(Profile frame, `𝓑 := boolEmbedding L`; the built-in `sumcheckConsistencyProp` conjunct of the
flat `masterKStateProp` carries the round-consistency check):
- m=0: same as relIn (`masterKStateProp` at `i.castSucc`, `localChecks := True`).
- m=1: after P sends hᵢ(X), before V sends r'ᵢ (`explicitVCheck ∧ localizedRoundPolyCheck`).
- m=2: after V sends r'ᵢ — OUTPUT state (`masterKStateProp` at `i.succ` with `stmtOut`,
  `witMid : SumcheckWitness i.succ`, `localChecks := explicitVCheck`). -/
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
  | ⟨2, _⟩ => -- After V sends r'ᵢ: use OUTPUT state (witMid is already SumcheckWitness i.succ)
    let h_i : ↥L⦃≤ 2⦄[X] := tr.messages ⟨0, rfl⟩
    let r_i' : L := tr.challenges ⟨1, rfl⟩
    let stmtOut : Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.succ :=
      { ctx := stmtMid.ctx, sumcheck_target := h_i.val.eval r_i',
        challenges := Fin.snoc stmtMid.challenges r_i' }
    let oStmtOut := oStmtMid
    let witOut := witMid
    RingSwitching.masterKStateProp κ L K P ℓ ℓ' h_l aOStmtIn
      (stmtIdx := i.succ)
      (stmt := stmtOut) (oStmt := oStmtOut) (wit := witOut)
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
  toFun_full := fun ⟨stmtIn, oStmtIn⟩ tr witOut h_relOut => by
    change (pSpecSumcheckRound L).FullTranscript at tr
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at h_relOut
    rcases h_relOut with ⟨stmtOut, oStmtOut, h_output, h_relOut⟩
    erw [iteratedSumcheckVerifier_run_eq_guarded] at h_output
    rw [OptionT.mem_support_iff] at h_output
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop] at h_output
    rcases h_output with ⟨s, _hs_init, h_output⟩
    by_cases h_check : (∑ b ∈ (boolDomain L ℓ').points i,
        (tr.messages ⟨0, rfl⟩).val.eval b) = stmtIn.sumcheck_target
    · rw [if_pos h_check] at h_output
      change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure (some _) : OracleComp []ₒ (Option _))).run' s) at h_output
      rw [simulateQ_pure] at h_output
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure (some _) : StateT σ ProbComp _).run s) at h_output
      rw [StateT.run_pure] at h_output
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at h_output
      have h_stmt := congrArg Prod.fst h_output
      have h_oracle := congrArg Prod.snd h_output
      change stmtOut = _ at h_stmt
      change oStmtOut = oStmtIn at h_oracle
      rw [h_stmt, h_oracle] at h_relOut
      change _ ∧ _ at h_relOut
      change _ ∧ _
      exact ⟨h_check, h_relOut.2⟩
    · rw [if_neg h_check] at h_output
      change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure none : OracleComp []ₒ (Option _))).run' s) at h_output
      rw [simulateQ_pure] at h_output
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at h_output
      rw [StateT.run_pure] at h_output
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff,
        Option.some_ne_none] at h_output

section
local instance : DecidableEq K := Classical.decEq K

local instance : ∀ j, OracleInterface ((pSpecSumcheckRound L).Challenge j) :=
  fun _ => OracleInterface.instDefault

noncomputable local instance instFieldOfIsDomainSumcheckPhase [NoZeroDivisors L] : Field L :=
  letI : IsDomain L := NoZeroDivisors.to_isDomain L
  Fintype.fieldOfDomain L

omit [NeZero κ] [SampleableType L] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
lemma iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck [NoZeroDivisors L] (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) (r_i' : L)
    (doomEscape : rbrExtractionFailureEvent
      (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
        (init := init) (impl := impl) i)
      (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
      (i := ⟨1, rfl⟩) (stmtIn := stmtOStmtIn) (transcript := FullTranscript.mk1 h_i)
      (challenge := r_i')) :
    ∃ witMid : SumcheckWitness L ℓ' i.succ,
      aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2) ∧
      let witBefore : SumcheckWitness L ℓ' i.castSucc :=
        (iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i).extractMid
          (m := 1) stmtOStmtIn (FullTranscript.mk2 h_i r_i') witMid
      let h_star : L⦃≤ 2⦄[X] :=
        Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) i witBefore.H
      Binius.BinaryBasefold.badSumcheckEventProp r_i' h_i h_star := by
  classical
  unfold rbrExtractionFailureEvent at doomEscape
  rcases doomEscape with ⟨witMid, h_kState_before_false, h_kState_after_true⟩
  simp only [iteratedSumcheckKnowledgeStateFunction] at h_kState_before_false h_kState_after_true
  unfold iteratedSumcheckKStateProp at h_kState_before_false h_kState_after_true
  simp only [Fin.isValue, Fin.castSucc_one, Fin.succ_one_eq_two, Nat.reduceAdd]
    at h_kState_before_false h_kState_after_true
  simp only [Transcript.concat]
    at h_kState_before_false h_kState_after_true
  unfold masterKStateProp witnessStructuralInvariant at h_kState_before_false h_kState_after_true
  simp only [iteratedSumcheckRbrExtractor, Fin.isValue]
    at h_kState_before_false h_kState_after_true
  -- After-state (m=2) truths.
  have h_explicit_after :
      (∑ b ∈ (boolDomain L ℓ').points i, h_i.val.eval b)
        = stmtOStmtIn.1.sumcheck_target := h_kState_after_true.1
  have h_sumcheck_after :
      sumcheckConsistencyProp (boolDomain L _) (Polynomial.eval r_i' h_i.val) witMid.H :=
    h_kState_after_true.2.2.1
  have h_wit_struct_after :
      witMid.H.val = (projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
        (i := i.succ) (challenges := Fin.snoc stmtOStmtIn.1.challenges r_i')).val :=
    h_kState_after_true.2.1
  have h_init_compat : aOStmtIn.initialCompatibility (witMid.t', stmtOStmtIn.2) :=
    h_kState_after_true.2.2.2
  -- The extracted before-witness at m=1.
  let H_before : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
    projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
      (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
      (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
      (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
  let h_star_extracted : L⦃≤ 2⦄[X] :=
    Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := H_before)
  have h_eval_eq_extracted : Polynomial.eval r_i' h_i.val
      = Polynomial.eval r_i' h_star_extracted.val := by
    unfold Sumcheck.Structured.sumcheckConsistencyProp at h_sumcheck_after
    -- Advance the mid-poly by fixing its first variable to the new challenge.
    have h_next :=
      projectToMidSumcheckPolyWithParam_succ_ringswitching (κ := κ) (L := L) (K := K) (P := P)
        (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (ctx := stmtOStmtIn.1.ctx) (t := witMid.t')
        (i := i) (challenges := stmtOStmtIn.1.challenges) (r_i' := r_i')
    -- Rewrite `witMid.H` as the next projection of `H_before`.
    rw [h_wit_struct_after] at h_sumcheck_after
    rw [← h_next] at h_sumcheck_after
    -- The Boolean-domain cube is definitionally the homogeneous Boolean product.
    have h_proj_sum :=
      Binius.BinaryBasefold.projectToNextSumcheckPoly_sum_eq (L := L) (𝓑 := boolEmbedding L)
        (ℓ := ℓ') (i := i) (Hᵢ := H_before) (rᵢ := r_i')
    exact h_sumcheck_after.trans h_proj_sum.symm
  have h_hi_ne_extracted : h_i ≠ h_star_extracted := by
    intro h_eq
    apply h_kState_before_false
    refine ⟨⟨h_explicit_after, ?_⟩, ?_, ?_, ?_⟩
    · dsimp only [h_star_extracted, H_before] at h_eq ⊢
      exact h_eq.trans (getSumcheckRoundPoly_bool_eq L ℓ' i _).symm
    · -- witnessStructuralInvariant at m=1 collapses to `True` (input witness is the projection).
      trivial
    · -- sumcheckConsistencyProp of the before-witness follows from `getSumcheckRoundPoly_sum_eq`.
      change sumcheckConsistencyProp (boolDomain L _) stmtOStmtIn.1.sumcheck_target _
      unfold Sumcheck.Structured.sumcheckConsistencyProp
      -- goal: sumcheck_target = ∑ over cube of H_before
      have h_sum_eq :=
        Binius.BinaryBasefold.getSumcheckRoundPoly_sum_eq (L := L) (𝓑 := boolEmbedding L)
          (ℓ := ℓ') (i := i) (h := H_before)
      rw [h_eq] at h_explicit_after
      rw [← h_explicit_after]
      dsimp only [h_star_extracted, H_before] at h_sum_eq ⊢
      simpa only [points_boolDomain, Finset.sum_map,
        Fin.sum_univ_two, boolDomain, SumcheckDomain.points_uniform,
        SumcheckDomain.cube_uniform] using h_sum_eq
    · -- initialCompatibility is preserved by extractMid(m=1) since t' is unchanged.
      exact h_init_compat
  have h_bad_extracted : Binius.BinaryBasefold.badSumcheckEventProp r_i' h_i h_star_extracted :=
    ⟨h_hi_ne_extracted, h_eval_eq_extracted⟩
  refine ⟨witMid, h_init_compat, ?_⟩
  dsimp only [h_star_extracted, H_before, iteratedSumcheckRbrExtractor]
  exact h_bad_extracted


omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
lemma iteratedSumcheck_doom_escape_probability_bound [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) (i : Fin ℓ')
    (stmtOStmtIn : (Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) i.castSucc)
      × (∀ j, aOStmtIn.OStmtIn j))
    (h_i : (pSpecSumcheckRound L).Message ⟨0, rfl⟩) :
    Pr_{ let y ← $ᵖ L }[
      rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y ] ≤
      roundKnowledgeError L ℓ' i := by
  classical
  let compatPred : Sumcheck.Structured.MultilinearPoly L ℓ' → Prop := fun t =>
    aOStmtIn.initialCompatibility (t, stmtOStmtIn.2)
  by_cases hCompat : ∃ t : Sumcheck.Structured.MultilinearPoly L ℓ', compatPred t
  · rcases hCompat with ⟨t_fixed, h_t_fixed_compat⟩
    let H_fixed : L⦃≤ 2⦄[X Fin (ℓ' - i.castSucc)] :=
      projectToMidSumcheckPolyWithParam (L := L) (ℓ := ℓ')
        (param := RingSwitching_SumcheckMultParam κ L K P ℓ ℓ' h_l)
        (ctx := stmtOStmtIn.1.ctx) (t := t_fixed)
        (i := i.castSucc) (challenges := stmtOStmtIn.1.challenges)
    let h_star_fixed : L⦃≤ 2⦄[X] :=
      Binius.BinaryBasefold.getSumcheckRoundPoly ℓ' (boolEmbedding L) (i := i) (h := H_fixed)
    have h_prob_mono := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun y => Binius.BinaryBasefold.badSumcheckEventProp y h_i h_star_fixed)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        have h_t_eq : witMid.t' = t_fixed :=
          hUnique stmtOStmtIn.2 witMid.t' t_fixed
            h_mid_compat h_t_fixed_compat
        dsimp only [h_star_fixed, H_fixed]
        rw [← h_t_eq]
        dsimp only [iteratedSumcheckRbrExtractor] at h_bad_extracted ⊢
        exact h_bad_extracted)
    apply le_trans h_prob_mono
    have h_sz := probability_bound_badSumcheckEventProp (h_i := h_i) (h_star := h_star_fixed)
    conv_rhs =>
      simp only [roundKnowledgeError, Sumcheck.Structured.roundKnowledgeError]
      rw [ENNReal.coe_div (hr := by simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero,
        not_false_eq_true])]
      simp only [ENNReal.coe_ofNat, ENNReal.coe_natCast]
    exact h_sz
  · have h_prob_mono_false := Probability.Pr_le_Pr_of_implies (D := $ᵖ L)
      (f := fun y => rbrExtractionFailureEvent
        (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn
          (init := init) (impl := impl) i)
        (extractor := iteratedSumcheckRbrExtractor.{0} κ L K P ℓ ℓ' h_l aOStmtIn i)
        ⟨1, rfl⟩ stmtOStmtIn (FullTranscript.mk1 h_i) y)
      (g := fun _ => False)
      (h_imp := by
        intro y h_doom
        obtain ⟨witMid, h_mid_compat, _h_bad_extracted⟩ :=
          iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck
            (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
            (aOStmtIn := aOStmtIn) (impl := impl) (init := init)
            (i := i) (stmtOStmtIn := stmtOStmtIn) (h_i := h_i) (r_i' := y)
            (doomEscape := h_doom)
        exact (hCompat ⟨witMid.t', h_mid_compat⟩).elim)
    refine le_trans h_prob_mono_false ?_
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le]

omit [NeZero κ] [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
/-- RBR knowledge soundness for a single round oracle verifier -/
theorem iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L]
    (hUnique : aOStmtIn.Functional) (i : Fin ℓ') :
    (iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
      (fun _ => roundKnowledgeError L ℓ' i) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  let : ∀ j, Fintype ((pSpecSumcheckRound L).Challenge j)
    | ⟨⟨0, _⟩, h⟩ => False.elim (by simp at h)
    | ⟨⟨1, _⟩, _⟩ => inferInstanceAs (Fintype L)
  let : ∀ j, Inhabited ((pSpecSumcheckRound L).Challenge j)
    | ⟨⟨0, _⟩, h⟩ => False.elim (by simp at h)
    | ⟨⟨1, _⟩, _⟩ => ⟨(0 : L)⟩
  let : OracleSpec.Inhabited []ₒ := { inhabitedB := fun j => PEmpty.elim j }
  let : OracleSpec.Fintype [(pSpecSumcheckRound L).Challenge]ₒ :=
    { fintypeB := fun j => inferInstanceAs (Fintype ((pSpecSumcheckRound L).Challenge j.1)) }
  let : OracleSpec.Inhabited [(pSpecSumcheckRound L).Challenge]ₒ :=
    { inhabitedB := fun j => inferInstanceAs (Inhabited ((pSpecSumcheckRound L).Challenge j.1)) }
  let : IsUniformSpec ([]ₒ + [(pSpecSumcheckRound L).Challenge]ₒ) :=
    IsUniformSpec.ofFintypeInhabited _
  exact OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    (pSpec := pSpecSumcheckRound L) (init := init) (impl := impl)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.castSucc)
    (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i.succ)
    (WitMid := iteratedSumcheckWitMid (L := L) (ℓ' := ℓ') (i := i))
    (rbrKnowledgeError := fun _ => roundKnowledgeError L ℓ' i)
    (kSF := iteratedSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn i)
    (extractor := iteratedSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn i)
    (hDir0 := rfl) (hDir1 := rfl)
    (hbound := fun stmtOStmtIn msg₀ => iteratedSumcheck_doom_escape_probability_bound
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (hUnique := hUnique) (i := i)
      (stmtOStmtIn := stmtOStmtIn) (h_i := msg₀))

end

end IteratedSumcheckStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step
-/

omit [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] in
private theorem finalProjectedEval (hCoord : CoordinateLaws P)
    (stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (wit : SumcheckWitness L ℓ' (Fin.last ℓ'))
    (hs : witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt wit) :
    wit.H.val.eval (fun _ => 0) = compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
        wit.t'.val.eval stmt.challenges := by
  rw [show wit.H.val = _ from hs]
  change MvPolynomial.eval _ (fixFirstVariablesOfMQP ℓ' (Fin.last ℓ') _ _) = _
  rw [eval_fixFirstVariables_last]
  simp only [computeRoundPoly, RingSwitching_SumcheckMultParam, Polynomial.aeval_X,
    map_mul]
  exact congrArg (· * wit.t'.val.eval stmt.challenges)
    (compute_A_MLE_eval_eq_final_eq_value κ L K P hCoord ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching)

omit [NeZero κ] [Fintype L] [DecidableEq L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
private theorem finalConsistency_iff
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

/-- The final verifier queries the constant `s'` (step 7), then

8. `V` sets `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))` and
   decomposes `e =: Σ_{u ∈ {0,1}^κ} β_u ⊗ e_u`;
9. `V` requires `s_{ℓ'} ?= (Σ_{u ∈ {0,1}^κ} eq̃(u_0, ..., u_{κ-1}, r''_0, ..., r''_{κ-1})`
   `⋅ e_u) ⋅ s'` (fail on rejection), and hands the accepted claim
   to the downstream opening. -/
noncomputable def finalSumcheckVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (OStmtIn := aOStmtIn.OStmtIn)
    (StmtOut := MLPEvalStatement L ℓ')
    (OStmtOut := aOStmtIn.OStmtIn)
    (pSpec := pSpecFinalSumcheck L) where
  verify := fun stmtIn _ => do
    let s' : L ← query (spec := [(pSpecFinalSumcheck L).Message]ₒ) ⟨⟨0, rfl⟩, ()⟩
    guard (stmtIn.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmtIn.ctx.t_eval_point stmtIn.challenges stmtIn.ctx.r_batching * s')
    pure { t_eval_point := stmtIn.challenges, original_claim := s' }
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun a b h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro i; rfl }

omit [NeZero κ] [Nontrivial L] [Fintype L] [SampleableType L]
    [Fintype K] [DecidableEq K] [NeZero ℓ] [NeZero ℓ'] in
private theorem finalVerifier_run
    (stmt : Statement (L := L) (ℓ := ℓ')
      (RingSwitchingBaseContext κ L K ℓ P) (Fin.last ℓ'))
    (oStmt : ∀ j, aOStmtIn.OStmtIn j) (tr : FullTranscript (pSpecFinalSumcheck L)) :
    Verifier.run (stmt, oStmt) tr
      (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier =
      let c : L := tr.messages ⟨0, rfl⟩
      if stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
          stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
            c then
        pure ((⟨stmt.challenges, c⟩ : MLPEvalStatement L ℓ'), oStmt)
      else failure := by
  classical
  simp only [Verifier.run, OracleVerifier.toVerifier, finalSumcheckVerifier]
  erw [simulateQ_bind]
  erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
  erw [_root_.bind_pure_simulateQ_comp]
  simp only [guard_eq]
  erw [simulateQ_bind]
  erw [simulateQ_ite]
  simp only [OptionT.simulateQ_failure]
  split
  · rename_i hc
    erw [if_pos hc, simulateQ_pure]
    simp only [pure_bind]
    erw [simulateQ_pure]
    simp only [_root_.map_pure]
    rfl
  · rename_i hc
    erw [if_neg hc]
    rfl

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
  verifier := finalSumcheckVerifier (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
    (h_l := h_l) (aOStmtIn := aOStmtIn)

omit [Fintype L] [Fintype K] [DecidableEq K] [SampleableType L] in
/-- Perfect completeness for the final sumcheck step -/
theorem finalSumcheckOracleReduction_perfectCompleteness {σ : Type}
    (hCoord : CoordinateLaws P)
    (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleReduction.perfectCompleteness
    (pSpec := pSpecFinalSumcheck L)
    (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (relOut := aOStmtIn.toRelInput)
    (oracleReduction := finalSumcheckOracleReduction (κ := κ) (L := L) (K := K) (P := P)
      (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l) (aOStmtIn := aOStmtIn))
      (init := init) (impl := impl) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro ⟨stmt, oStmt⟩ wit hIn x hx
  have hs := hIn.2.1
  have hc : stmt.sumcheck_target = compute_final_eq_value κ L K P ℓ ℓ' h_l
      stmt.ctx.t_eval_point stmt.challenges stmt.ctx.r_batching *
        wit.t'.val.eval stmt.challenges :=
    ((finalConsistency_iff κ L K P ℓ ℓ' stmt wit).mp hIn.2.2.1).trans
      (finalProjectedEval κ L K P ℓ ℓ' h_l hCoord stmt wit hs)
  have hp : (finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).run (stmt, oStmt) wit =
      pure (FullTranscript.mk1 (pSpec := pSpecFinalSumcheck L)
        (wit.t'.val.eval stmt.challenges),
        ((⟨stmt.challenges, wit.t'.val.eval stmt.challenges⟩ : MLPEvalStatement L ℓ'), oStmt),
        (⟨wit.t'⟩ : WitMLP L ℓ')) := by
    simp only [pSpecFinalSumcheck, pSpecMessage, ChallengeIdx, Challenge, Prover.run,
      Fin.reduceLast, finalSumcheckProver, reduceAdd, Fin.isValue, MessageIdx, Message,
      cons_val_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_last,
      Lean.Elab.WF.paramLet, Prover.runToRound, Fin.induction_one', Prover.processRound,
      toPFunctor_emptySpec, bind_pure_comp, pure_bind, liftM_pure,
      LawfulApplicative.map_pure, PFunctor.FreeM.pure_inj]
    congr 1
    exact (FullTranscript.mk1_eq_snoc (pSpec := pSpecFinalSumcheck L)
      (wit.t'.val.eval stmt.challenges)).symm
  unfold Reduction.run at hx
  change x ∈ _root_.support (do
    let proverResult ← liftM ((finalSumcheckProver κ L K P ℓ ℓ' aOStmtIn).run
      (stmt, oStmt) wit)
    let stmtOut ← liftM (Verifier.run (stmt, oStmt) proverResult.1
      (finalSumcheckVerifier κ L K P ℓ ℓ' h_l aOStmtIn).toVerifier).run
    let out ← stmtOut.getM
    pure (proverResult, out) : OptionT (OracleComp _) _).run at hx
  rw [hp] at hx
  simp only [liftM_pure, pure_bind] at hx
  erw [finalVerifier_run] at hx
  simp only [FullTranscript.mk1, FullTranscript.messages] at hx
  rw [if_pos hc] at hx
  simp only [OptionT.run_pure] at hx
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
    ∧ aOStmtIn.initialCompatibility ⟨witMid.t', oStmt⟩
    ∧ witnessStructuralInvariant κ L K P ℓ ℓ' h_l stmt witMid

omit [Fintype L] [Fintype K] [DecidableEq K] in
/-- The knowledge state function for the final sumcheck step -/
noncomputable def finalSumcheckKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) (hCoord : CoordinateLaws P) :
    (finalSumcheckVerifier (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)).KnowledgeStateFunction init impl
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
    rw [finalProjectedEval κ L K P ℓ ℓ' h_l hCoord stmt witMid hs]
    exact hc.trans (congrArg (_ * ·) he.symm)
  toFun_full := fun (stmt, oStmt) tr witOut h => by
    change (pSpecFinalSumcheck L).FullTranscript at tr
    simp only [StateT.run'_eq, gt_iff_lt, probEvent_pos_iff, Prod.exists] at h
    obtain ⟨stmtOut, oStmtOut, hmem, hrel⟩ := h
    erw [finalVerifier_run κ L K P ℓ ℓ' h_l aOStmtIn stmt oStmt tr] at hmem
    rw [OptionT.mem_support_iff] at hmem
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨s, _, hmem⟩ := hmem
    split at hmem
    · rename_i hc
      change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure (some _) : OracleComp []ₒ (Option _))).run' s) at hmem
      rw [simulateQ_pure] at hmem
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure (some _) : StateT σ ProbComp _).run s) at hmem
      rw [StateT.run_pure] at hmem
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff,
        Option.some.injEq] at hmem
      have hstmt := congrArg Prod.fst hmem
      have ho := congrArg Prod.snd hmem
      change stmtOut = _ at hstmt
      change oStmtOut = oStmt at ho
      rw [hstmt, ho] at hrel
      exact ⟨hc, hrel.1.symm, hrel.2, rfl⟩
    · change some (stmtOut, oStmtOut) ∈ _root_.support
        ((simulateQ impl (pure none : OracleComp []ₒ (Option _))).run' s) at hmem
      rw [simulateQ_pure] at hmem
      change some (stmtOut, oStmtOut) ∈ _root_.support
        (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at hmem
      rw [StateT.run_pure] at hmem
      simp only [_root_.map_pure, support_pure, Set.mem_singleton_iff,
        reduceCtorEq] at hmem

section
local instance : DecidableEq K := Classical.decEq K

omit [Fintype K] [DecidableEq K] [SampleableType L] in
/-- Round-by-round knowledge soundness for the final sumcheck step -/
theorem finalSumcheckOracleVerifier_rbrKnowledgeSoundness [NoZeroDivisors L] {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hCoord : CoordinateLaws P) :
    (finalSumcheckVerifier (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn)).rbrKnowledgeSoundness init impl
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (relOut := aOStmtIn.toRelInput)
      (rbrKnowledgeError := fun _ => finalSumcheckRbrKnowledgeError (L := L)) := by
  let _ : IsDomain L := NoZeroDivisors.to_isDomain L
  classical
  use (fun _ => SumcheckWitness L ℓ' (Fin.last ℓ'))
  use finalSumcheckRbrExtractor κ L K P ℓ ℓ' h_l aOStmtIn
  use finalSumcheckKnowledgeStateFunction κ L K P ℓ ℓ' h_l aOStmtIn init impl hCoord
  intro stmtIn witIn prover ⟨j, hj⟩
  cases j using Fin.cases with
  | zero => simp at hj
  | succ j => exact Fin.elim0 j

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
    (V₂ := finalSumcheckVerifier (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn))
    (pSpec₂:=pSpecFinalSumcheck L)

/-- Large-field reduction: Sumcheck seqCompose, then append FinalSum -/
@[reducible]
def coreInteractionOracleReduction :=
  OracleReduction.append
    (R₁ := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
    (pSpec₁:=pSpecSumcheckLoop L ℓ')
    (R₂ := finalSumcheckOracleReduction (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (h_l := h_l) (aOStmtIn := aOStmtIn))
    (pSpec₂:=pSpecFinalSumcheck L)

/-!
## RBR Knowledge Soundness Components for Single Round
-/

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [Fintype L] [Fintype K] [DecidableEq K] in
/-- Perfect completeness for large-field reduction (Sumcheck ++ FinalSum) -/
theorem coreInteraction_perfectCompleteness (hCoord : CoordinateLaws P) :
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
      (hCoord := hCoord) (init := pure s) (impl := impl)

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
contributes `d / |L|` per sumcheck challenge; the final sumcheck contributes `1 / |L|`. -/
def coreInteractionRbrKnowledgeErrorWithDegree (d : ℕ)
    (j : (pSpecCoreInteractionWithDegree L ℓ' d).ChallengeIdx) : ℝ≥0 :=
  Sum.elim
    (f := sumcheckLoopRbrKnowledgeErrorWithDegree L ℓ' d)
    (g := fun _ => finalSumcheckRbrKnowledgeError (L := L))
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
    (hCoord : CoordinateLaws P) (hUnique : aOStmtIn.Functional) :
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
  apply OracleVerifier.append_rbrKnowledgeSoundness
    (rel₂ := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
    (rbrKnowledgeError₁ := sumcheckLoopRbrKnowledgeError L ℓ')
    (rbrKnowledgeError₂ := fun _ => finalSumcheckRbrKnowledgeError (L := L))
  · exact OracleVerifier.seqCompose_rbrKnowledgeSoundness
      (init := init) (impl := impl)
      (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
      (V := fun i => iteratedSumcheckOracleVerifier κ L K P ℓ ℓ' aOStmtIn i)
      (rbrKnowledgeError := fun i _ => roundKnowledgeError L ℓ' i)
      (h := fun i => iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness
        κ L K P ℓ ℓ' h_l aOStmtIn hUnique i)
  · exact finalSumcheckOracleVerifier_rbrKnowledgeSoundness
      κ L K P ℓ ℓ' h_l aOStmtIn init impl hCoord


end

end LargeFieldReduction
end
end RingSwitching.SumcheckPhase
