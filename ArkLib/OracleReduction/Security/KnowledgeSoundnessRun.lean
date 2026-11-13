/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Acceptance
public import ArkLib.OracleReduction.Security.SoundnessInitialization

/-!
# Execution forms of ordinary knowledge soundness

Pure extractors depending on the statement, output witness and transcript can discard query
logs. These characterizations retain the shared oracle state at the prover/verifier boundary.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
  {V : Verifier oSpec StmtIn StmtOut pSpec} {ε : ℝ≥0}

/-- A named knowledge-soundness bound valid from every deterministic initial state also holds
for an arbitrary distribution of initial states. -/
theorem knowledgeSoundnessWith_of_forall_pure
    {E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec}
    (h : ∀ s : σ, V.knowledgeSoundnessWith (pure s) impl relIn relOut E ε) :
    V.knowledgeSoundnessWith init impl relIn relOut E ε := by
  intro Aux stmt aux P
  dsimp only
  rw [OptionT.prEvent_eq_run]
  apply prEvent_bind_le_of_forall_le_of_support _ _ _
  intro s _
  simpa only [knowledgeSoundnessWith, OptionT.prEvent_eq_run, pure_bind,
    OptionT.run_mk] using h s Aux stmt aux P

/-- Express the game for a pure output-and-transcript extractor at the execution boundary. -/
theorem knowledgeSoundnessWith_iff_run
    (e : StmtIn → WitOut → pSpec.FullTranscript → Option WitIn) :
    V.knowledgeSoundnessWith init impl relIn relOut
      (Extractor.Straightline.ofTranscriptAndOutput e) ε ↔
    ∀ (Aux : Type) (stmt : StmtIn) (aux : Aux)
      (P : Prover oSpec StmtIn Aux StmtOut WitOut pSpec),
      Pr{let r ← (do
        let s ← init
        let z ← (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (P.run stmt aux)).run s
        let v ← (simulateQ impl (V.run stmt z.1.1)).run z.2
        pure (z.1, v.1))}[
          r.2.elim False (fun out =>
            (∀ w ∈ e stmt r.1.2.2 r.1.1, (stmt, w) ∉ relIn) ∧
              (out, r.1.2.2) ∈ relOut)] ≤ ε := by
  unfold knowledgeSoundnessWith
  apply forall_congr'; intro Aux
  apply forall_congr'; intro stmt
  apply forall_congr'; intro aux
  apply forall_congr'; intro P
  apply Iff.of_eq
  apply congrArg (fun r : ENNReal => r ≤ (ε : ENNReal))
  rw [Reduction.ofTranscriptAndOutput_game_eq_map, OptionT.run_map, simulateQ_map,
    OptionT.prEvent_eq_run]
  simp only [StateT.run'_eq, Reduction.run_run_eq_bind, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, StateT.run_map,
    QueryImpl.addLift_def, liftComp_eq_liftM, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.liftTarget_self]
  apply prEvent_bind_congr
  intro s
  rw [prEvent_map, prEvent_map]
  apply prEvent_bind_congr
  intro z
  rw [bind_pure_comp, prEvent_map, bind_pure_comp, prEvent_map]
  apply prEvent_congr
  intro v
  cases v.1 <;> rfl

/-- Guarded knowledge soundness is exactly the accepted failed-extraction event on the actual
prover transcript and output witness. -/
theorem GuardedForm.knowledgeSoundnessWith_iff (G : V.GuardedForm)
    (e : StmtIn → WitOut → pSpec.FullTranscript → Option WitIn) :
    V.knowledgeSoundnessWith init impl relIn relOut
      (Extractor.Straightline.ofTranscriptAndOutput e) ε ↔
    ∀ (Aux : Type) (stmt : StmtIn) (aux : Aux)
      (P : Prover oSpec StmtIn Aux StmtOut WitOut pSpec),
      Pr{let z ← (do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (P.run stmt aux)).run s)}[
        G.check stmt z.1.1 = true ∧
          (∀ w ∈ e stmt z.1.2.2 z.1.1, (stmt, w) ∉ relIn) ∧
            (G.out stmt z.1.1, z.1.2.2) ∈ relOut] ≤ ε := by
  rw [knowledgeSoundnessWith_iff_run]
  apply forall_congr'; intro Aux
  apply forall_congr'; intro stmt
  apply forall_congr'; intro aux
  apply forall_congr'; intro P
  apply Iff.of_eq
  apply congrArg (fun r : ENNReal => r ≤ (ε : ENNReal))
  simp only [G.run_state, pure_bind, ← bind_assoc]
  rw [bind_pure_comp, prEvent_map]
  apply prEvent_congr
  intro z
  cases G.check stmt z.1.1 <;> simp

/-- The identity verifier is perfectly knowledge sound at the extractor that returns its output
witness. This named version is the empty-chain base case. -/
theorem id_knowledgeSoundnessWith (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (rel : Set (StmtIn × WitIn)) :
    (Verifier.id : Verifier oSpec StmtIn StmtIn !p[]).knowledgeSoundnessWith init impl rel rel
      (Extractor.Straightline.ofTranscriptAndOutput (fun _ w _ => some w)) 0 := by
  let G : (Verifier.id : Verifier oSpec StmtIn StmtIn !p[]).GuardedForm :=
    ⟨fun _ _ => true, fun s _ => s, fun _ _ => rfl⟩
  rw [G.knowledgeSoundnessWith_iff]
  intro Aux stmt aux P
  rw [ENNReal.coe_zero, le_zero_iff]
  apply prEvent_eq_zero_of_forall_not
  rintro z ⟨_, hf, hr⟩
  exact hf z.1.2.2 rfl hr

end Verifier
