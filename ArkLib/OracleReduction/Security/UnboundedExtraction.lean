/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Security.Acceptance

/-!
# Unbounded straightline extraction

`Verifier.knowledgeSoundness` asks for *some* straightline extractor and bounds neither its running
time nor its computability. This file shows what that contract amounts to.

The classical witness selector `Extractor.Straightline.choose` ignores the execution and returns a
valid input witness whenever one exists. Its extraction fails exactly on input statements outside
the input language (`Set.forall_mem_chooseWitness_notMem_iff`). Hence the existential contract is
equivalent to `Verifier.relationSoundness`: on every input statement outside the input language,
the prover outputs a pair in the output relation with probability at most the error
(`Verifier.knowledgeSoundness_iff_relationSoundness`).

The direction from knowledge soundness uses that extraction loses no probability mass. This holds
for the interpreter `StateT σ ProbComp` of these games, since an oracle computation never fails;
an interpreter with missing mass needs an explicit losslessness premise on the extractor.

Relation soundness differs from `Verifier.soundness` in two ways: the output witness is the one
the prover actually supplies, and its type is fixed. Language soundness for the output language
implies it (`Verifier.relationSoundness_of_soundness`); the converse needs the prover to be able to
supply an output witness.

An existential knowledge-soundness theorem therefore certifies extraction in the cryptographic
sense only together with a resource bound on a named extractor, stated through
`Verifier.knowledgeSoundnessWith`.
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

section Erasure

variable {ι : Type} {spec : OracleSpec ι} {σ α β γ δ : Type}
  (init : ProbComp σ) (pImpl : QueryImpl spec (StateT σ ProbComp))

/-- A map commutes with the interpretation of an execution under `StateT σ ProbComp`. -/
private theorem map_simulate_run (X : OptionT (OracleComp spec) α) (h : α → γ) :
    h <$> (OptionT.mk (do (simulateQ pImpl X.run).run' (← init)) : OptionT ProbComp α) =
      OptionT.mk (do (simulateQ pImpl (h <$> X).run).run' (← init)) := by
  simp [OptionT.run_map, simulateQ_map, StateT.run'_eq, OptionT.ext_iff, Functor.map_map]

/-- Appending an oracle computation whose result is discarded leaves the distribution of an
interpreted execution unchanged: under `StateT σ ProbComp` that computation loses no mass. -/
private theorem simulate_run_bind_liftM_discard (R : OptionT (OracleComp spec) α)
    (Y : α → OracleComp spec β) (g : α → γ) :
    (OptionT.mk (do (simulateQ pImpl (R >>= fun r =>
      (liftM (Y r) : OptionT (OracleComp spec) β) >>= fun _ => pure (g r)).run).run' (← init)) :
        OptionT ProbComp γ) =ᵈ
      (OptionT.mk (do (simulateQ pImpl (g <$> R).run).run' (← init)) : OptionT ProbComp γ) := by
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  rw [OptionT.prEvent_mk, OptionT.prEvent_mk]
  refine (EvalDistEq.bind_right (m := ProbComp) init fun s => ?_).prEvent_eq _
  simp only [OptionT.run_bind, OptionT.run_map, Option.elimM, simulateQ_bind, simulateQ_map,
    StateT.run'_eq, StateT.run_bind, StateT.run_map, map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.bind_right (m := ProbComp) _ fun (p : Option α × σ) => ?_
  obtain ⟨o, s'⟩ := p
  cases o with
  | none => simp
  | some r =>
    simp only [Option.elim_some, OptionT.run_monadLift]
    simpa using EvalDistEq.map_const ((simulateQ pImpl (Y r)).run s') (some (g r))

/-- An event of an execution extended by a discarded oracle computation has the probability of a
corresponding event of the execution itself. -/
private theorem prEvent_simulate_run_bind_liftM (R : OptionT (OracleComp spec) α)
    (k : α → OptionT (OracleComp spec) δ) (Y : α → OracleComp spec β) (f : α → β → δ)
    (g : α → γ) (P : δ → Prop) (Q : γ → Prop)
    (hk : ∀ r, k r = (liftM (Y r) : OptionT (OracleComp spec) β) >>= fun e => pure (f r e))
    (hPQ : ∀ r e, P (f r e) ↔ Q (g r)) :
    Pr{let x ← (OptionT.mk (do (simulateQ pImpl (R >>= k).run).run' (← init)) :
        OptionT ProbComp δ)}[P x] =
    Pr{let x ← (OptionT.mk (do (simulateQ pImpl (g <$> R).run).run' (← init)) :
        OptionT ProbComp γ)}[Q x] := by
  obtain rfl : k = _ := funext hk
  have hP : P <$> (R >>= fun r => (liftM (Y r) : OptionT (OracleComp spec) β) >>=
      fun e => pure (f r e)) =
      R >>= fun r => (liftM (Y r) : OptionT (OracleComp spec) β) >>= fun _ => pure (Q (g r)) := by
    simp only [map_bind, map_pure, hPQ]
  have hL := prEvent_map (OptionT.mk (do (simulateQ pImpl (R >>= fun r =>
      (liftM (Y r) : OptionT (OracleComp spec) β) >>= fun e => pure (f r e)).run).run' (← init)) :
        OptionT ProbComp δ) P id
  have hR := prEvent_map (OptionT.mk (do (simulateQ pImpl (g <$> R).run).run' (← init)) :
        OptionT ProbComp γ) Q id
  rw [map_simulate_run, hP] at hL
  rw [map_simulate_run, Functor.map_map] at hR
  exact hL.symm.trans
    (((simulate_run_bind_liftM_discard init pImpl R Y (Q ∘ g)).prEvent_eq id).trans hR)

end Erasure

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The straightline extractor that ignores the execution and returns the classical witness
selector's choice for the input statement. -/
def Extractor.Straightline.choose (relIn : Set (StmtIn × WitIn)) :
    Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec :=
  Extractor.Straightline.ofTranscript fun stmtIn _ => relIn.chooseWitness stmtIn

namespace Verifier

/-- **Relation soundness** with error `soundnessError`: for every private input type `Aux`, input
statement outside the language of `relIn`, private input `aux : Aux`, and malicious prover with
that input type, the execution with the honest verifier outputs a pair `(stmtOut, witOut)` in
`relOut` with probability at most `soundnessError`.

The output witness is the one the prover supplies. Unlike `Verifier.soundness`, this definition
fixes the output witness type and tests the output relation rather than its language. -/
def relationSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (soundnessError : ℝ≥0) : Prop :=
  ∀ Aux : Type,
  ∀ stmtIn ∉ relIn.language,
  ∀ aux : Aux,
  ∀ prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    Pr{let ⟨⟨_, _, witOut⟩, stmtOut⟩ ← OptionT.mk do
      (simulateQ pImpl ((Reduction.mk prover verifier).run stmtIn aux).run).run' (← init)}[
        (stmtOut, witOut) ∈ relOut] ≤ soundnessError

/-- The classical selector's knowledge game reduces to relation soundness: outside the input
language its bad event is a valid output pair, and inside it the event is impossible. -/
theorem knowledgeSoundnessWith_choose_of_relationSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {soundnessError : ℝ≥0}
    (h : verifier.relationSoundness init impl relIn relOut soundnessError) :
    verifier.knowledgeSoundnessWith init impl relIn relOut
      (Extractor.Straightline.choose relIn) soundnessError := by
  intro Aux stmtIn aux prover
  change Pr{let result ← OptionT.mk do
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      (do
        let ⟨⟨pr, out⟩, plog, vlog⟩ ← (Reduction.mk prover verifier).runWithLog stmtIn aux
        let extracted ← liftM ((Extractor.Straightline.ofTranscript
          fun stmtIn _ => relIn.chooseWitness stmtIn) stmtIn pr.2.2 pr.1 plog.fst vlog).run
        pure (stmtIn, extracted, out, pr.2.2)).run).run' (← init)}[
      (∀ p ∈ result.2.1, (result.1, p) ∉ relIn) ∧ (result.2.2.1, result.2.2.2) ∈ relOut] ≤ _
  rw [Reduction.ofTranscript_game_eq_map, ← map_simulate_run, prEvent_map]
  simp only [Set.forall_mem_chooseWitness_notMem_iff]
  by_cases hstmtIn : stmtIn ∈ relIn.language
  · simp only [hstmtIn, not_true_eq_false, false_and, prEvent_false, zero_le]
  · simpa [hstmtIn] using h Aux stmtIn hstmtIn aux prover

/-- Every extractor's knowledge game bounds relation soundness. The extraction step is discarded
by distribution, since an oracle computation interpreted in `StateT σ ProbComp` loses no mass. -/
theorem relationSoundness_of_knowledgeSoundnessWith
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec} {soundnessError : ℝ≥0}
    (h : verifier.knowledgeSoundnessWith init impl relIn relOut extractor soundnessError) :
    verifier.relationSoundness init impl relIn relOut soundnessError := by
  intro Aux stmtIn hstmtIn aux prover
  refine le_of_eq_of_le ?_ (h Aux stmtIn aux prover)
  rw [Set.not_mem_language_iff] at hstmtIn
  rw [← Reduction.runWithLog_discard_logs_eq_run]
  symm
  refine prEvent_simulate_run_bind_liftM init _ _ _
    (fun r => liftM (extractor stmtIn r.1.1.2.2 r.1.1.1 r.2.1.fst r.2.2).run)
    (fun r e => (stmtIn, e, r.1.2, r.1.1.2.2)) Prod.fst _ _ (fun r => ?_) fun r e => ?_
  · obtain ⟨⟨⟨_, _, _⟩, _⟩, _, _⟩ := r
    simp
  · simp [hstmtIn]

/-- The classical selector satisfies the knowledge game exactly when the verifier is relation
sound. -/
theorem knowledgeSoundnessWith_choose_iff
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {soundnessError : ℝ≥0} :
    verifier.knowledgeSoundnessWith init impl relIn relOut
      (Extractor.Straightline.choose relIn) soundnessError ↔
      verifier.relationSoundness init impl relIn relOut soundnessError :=
  ⟨relationSoundness_of_knowledgeSoundnessWith init impl,
    knowledgeSoundnessWith_choose_of_relationSoundness init impl⟩

/-- Knowledge soundness, which places no resource bound on its extractor, is equivalent to
relation soundness. -/
theorem knowledgeSoundness_iff_relationSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {soundnessError : ℝ≥0} :
    verifier.knowledgeSoundness init impl relIn relOut soundnessError ↔
      verifier.relationSoundness init impl relIn relOut soundnessError :=
  ⟨fun ⟨_, h⟩ => relationSoundness_of_knowledgeSoundnessWith init impl h,
    fun h => ⟨_, knowledgeSoundnessWith_choose_of_relationSoundness init impl h⟩⟩

/-- Soundness for the languages of the two relations implies relation soundness, since a valid
output pair has its statement in the output language. -/
theorem relationSoundness_of_soundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {soundnessError : ℝ≥0}
    (h : verifier.soundness init impl relIn.language relOut.language soundnessError) :
    verifier.relationSoundness init impl relIn relOut soundnessError := by
  intro Aux stmtIn hstmtIn aux prover
  exact (prEvent_mono _ _ _ fun x hx => ⟨_, hx, rfl⟩).trans
    (h Aux WitOut aux prover stmtIn hstmtIn)

end Verifier

end
