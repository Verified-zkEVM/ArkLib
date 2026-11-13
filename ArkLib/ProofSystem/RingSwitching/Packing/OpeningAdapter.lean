/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.OracleReduction.Composition.Sequential.OracleCompleteness
public import ArkLib.OracleReduction.LogicStep
public import ArkLib.OracleReduction.Composition.Sequential.NoAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.GuardedRoundByRound

/-!
# Contextual adapters for multilinear opening protocols

A zero-round projection discards public query context and wraps the packed polynomial in
`WitMLP`. Appending an `MLIOPCS` gives an opening at the contextual evaluation relation used
by ring switching. Completeness uses honest compatibility; round-by-round knowledge
soundness uses the supplied opening's security field.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.OpeningAdapter
open OracleSpec OracleComp ProtocolSpec MvPolynomial Sumcheck.Structured
open scoped NNReal
variable {L : Type} [CommRing L] {m : ℕ} (M : MLIOPCS L m) (Context : Type)
attribute [local instance] MLIOPCS.Oₘ MLIOPCS.O_challenges

/-- The contextual evaluation statement with its query context projected away. -/
def project (s : Context × ((Fin m → L) × L)) : MLPEvalStatement L m := ⟨s.2.1, s.2.2⟩

/-- A zero-round projection preserving all commitment oracles. -/
def projectionVerifier : OracleVerifier []ₒ (Context × ((Fin m → L) × L)) M.OStmtIn
    (MLPEvalStatement L m) M.OStmtIn !p[] where
  verify s _ := pure (project Context s)
  outputOracle := .inl {
    embed := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
    hEq := fun _ => rfl
    outputInterface_heq := fun _ => HEq.rfl }

/-- The projection always accepts and preserves the commitment oracle statements. -/
def projectionGuard : (projectionVerifier M Context).toVerifier.GuardedForm where
  check _ _ := true
  out s _ := (project Context s.1, s.2)
  verify_eq _ _ := rfl

/-- Wrap the polynomial witness while projecting the public evaluation statement. -/
def projectionProver : OracleProver []ₒ (Context × ((Fin m → L) × L)) M.OStmtIn
    (MultilinearPoly L m) (MLPEvalStatement L m) M.OStmtIn (WitMLP L m) !p[] where
  PrvState _ := ((Context × ((Fin m → L) × L)) × (∀ j, M.OStmtIn j)) × MultilinearPoly L m
  input := id
  sendMessage i := nomatch i
  receiveChallenge i := nomatch i
  output s := pure ((project Context s.1.1, s.1.2), ⟨s.2⟩)

/-- The oracle-preserving projection reduction. -/
def projectionReduction := OracleReduction.mk (projectionProver M Context)
  (projectionVerifier M Context)

/-- The projection extractor unwraps the polynomial witness. -/
def projectionExtractor : Extractor.RoundByRound []ₒ
    (StmtIn := (Context × ((Fin m → L) × L)) × (∀ j, M.OStmtIn j))
    (WitIn := MultilinearPoly L m) (WitOut := WitMLP L m)
    (pSpec := !p[]) (WitMid := fun _ => MultilinearPoly L m) where
  extractIn := fun _ w => w
  extractMid i := nomatch i
  extractOut _ _ w := w.t

/-- The evaluation relation is invariant under the projection and witness wrapper. -/
def projectionKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (projectionVerifier M Context).KnowledgeStateFunction init impl
      (M.toAbstractOStmtIn.toPackedCommitment.evalRelWithContext (C := L) Context) M.toRelInput
      (projectionExtractor M Context) where
  toFun _ s _ w := (s, w) ∈ M.toAbstractOStmtIn.toPackedCommitment.evalRelWithContext (C := L)
    Context
  toFun_empty _ _ h := h
  toFun_next i := nomatch i
  toFun_full s tr w h := by
    have hp := ((projectionGuard M Context).check_and_of_prEvent_pos h).2
    exact hp

/-- Projection introduces no challenges or knowledge error. -/
theorem projectionVerifier_rbrKnowledgeSoundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (projectionVerifier M Context).toVerifier.rbrKnowledgeSoundness init impl
      (M.toAbstractOStmtIn.toPackedCommitment.evalRelWithContext (C := L) Context) M.toRelInput
      (fun _ => 0) := by
  apply (Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
  exact ⟨_, projectionExtractor M Context, projectionKnowledgeStateFunction M Context init impl,
    fun _ i => Fin.elim0 i.1⟩

/-- Honest contextual evaluation claims project to honest opening inputs. -/
theorem projectionReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (projectionReduction M Context).perfectCompleteness init impl
      (M.toAbstractOStmtIn.strictView.toPackedCommitment.evalRelWithContext (C := L) Context)
      M.toStrictRelInput := by
  apply Reduction.perfectCompleteness_of_guarded_prover_support _ (projectionGuard M Context)
  intro s p hp q hq
  change q ∈ support ((projectionProver M Context).run s p) at hq
  have hrun : (projectionProver M Context).run s p =
      pure (default, (project Context s.1, s.2), (⟨p⟩ : WitMLP L m)) := by
    simp [Prover.run, Prover.runToRound, projectionProver]
    rfl
  rw [hrun] at hq
  have hq := OracleComp.eq_of_mem_support_pure _ hq
  subst q
  exact ⟨rfl, hp, rfl⟩

/-- Message interfaces of the context projection followed by the opening. -/
instance instMessageInterface :
    ∀ j, OracleInterface (((!p[] : ProtocolSpec 0) ++ₚ M.pSpec).Message j) :=
  ProtocolSpec.instOracleInterfaceMessageAppend

/-- Challenge samplers of the context projection followed by the opening. -/
instance instChallengeSampleable :
    ∀ j, SampleableType (((!p[] : ProtocolSpec 0) ++ₚ M.pSpec).Challenge j) :=
  ProtocolSpec.instSampleableTypeChallengeAppend

/-- A general multilinear opening accepting contextual evaluation inputs. -/
def reduction : OracleProof []ₒ (Context × ((Fin m → L) × L)) M.OStmtIn
    (MultilinearPoly L m) ((!p[] : ProtocolSpec 0) ++ₚ M.pSpec) := OracleReduction.append (Oₛ₃ :=
      fun i : Empty => nomatch i)
  (projectionReduction M Context) M.oracleReduction

/-- A complete general opening yields a complete contextual opening. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.perfectCompleteness (oracleProof := reduction M Context)
      (relation := M.toAbstractOStmtIn.strictView.toPackedCommitment.evalRelWithContext (C := L)
        Context)
      (init := init) (impl := impl) := by
  apply OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) (projectionReduction M Context) M.oracleReduction
    (projectionGuard M Context)
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
  · exact projectionReduction_perfectCompleteness M Context init impl
  · intro state
    exact M.perfectCompleteness

/-- Security of a general opening transports to its contextual adapter. -/
theorem rbrKnowledgeSoundness
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    OracleProof.rbrKnowledgeSoundness init impl
      (M.toAbstractOStmtIn.toPackedCommitment.evalRelWithContext (C := L) Context)
      (reduction M Context).toOracleVerifier
      (Sum.elim (fun _ => 0) M.rbrKnowledgeError ∘ ChallengeIdx.sumEquiv.symm) := by
  exact OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) (projectionVerifier M Context)
    M.oracleReduction.toOracleVerifier
    (projectionGuard M Context)
    (projectionVerifier_rbrKnowledgeSoundness M Context init impl) M.rbrKnowledgeSoundness

end RingSwitching.Packing.OpeningAdapter
