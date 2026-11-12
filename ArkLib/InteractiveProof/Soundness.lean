/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.QueryTracking.QueryLog

/-!
# Adaptive public-coin interactive security

This module uses the legacy `ProtocolSpec`, `Prover`, and `Verifier` representation.
Shared game execution is independent of that representation and lives in `ArkLib.Security`.

After the shared oracle is initialized, the adversary chooses a statement and private state,
then continues as an interactive prover. Verifier messages come from a separate challenge
interface. Admissibility may constrain the total selected queries of both adversary phases,
and a statement-size bound may be applied to the verifier's decision. The verifier's oracle
interface contains the shared public queries, and its random messages come from the separate
challenge handler.

## References

* [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][CY24]

[CY24]: https://snargsbook.org/
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory QueryImpl

/-- The statement chooser and interactive prover share an oracle interface. The continuation
receives the chooser's output state and the chosen statement. -/
structure AdaptiveProver {ι : Type} (spec : OracleSpec ι) (Stmt Out WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) where
  Aux : Type
  choose : OracleComp spec (Stmt × Aux)
  prover : Prover spec Stmt Aux Out WitOut pSpec

namespace AdaptiveProver

variable {ι : Type} {spec : OracleSpec ι} {Stmt Out WitOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n}

/-- Embed a fixed statement and auxiliary input as a chooser that makes no oracle queries. -/
def fixed {Aux : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover spec Stmt Aux Out WitOut pSpec) : AdaptiveProver spec Stmt Out WitOut pSpec :=
  ⟨Aux, pure (stmt, aux), P⟩

/-- Run a public-oracle adversary in a game with an additional private-oracle interface. -/
instance coeAddPrivateOracles {κ : Type} {privateSpec : OracleSpec κ} :
    CoeTail (AdaptiveProver spec Stmt Out WitOut pSpec)
      (AdaptiveProver (spec + privateSpec) Stmt Out WitOut pSpec) where
  coe A := {
    Aux := A.Aux
    choose := liftCompLeft A.choose
    prover := {
      PrvState := A.prover.PrvState
      input := A.prover.input
      sendMessage i s := liftCompLeft (A.prover.sendMessage i s)
      receiveChallenge i s := liftCompLeft (A.prover.receiveChallenge i s)
      output s := liftCompLeft (A.prover.output s) } }

/-- Run both adversarial phases, drawing verifier messages through the challenge interface. -/
def run (P : AdaptiveProver spec Stmt Out WitOut pSpec) :
    OracleComp (spec + [pSpec.Challenge]ₒ) (Stmt × FullTranscript pSpec × WitOut) := do
  let a ← liftComp P.choose (spec + [pSpec.Challenge]ₒ)
  let pr ← P.prover.run a.1 a.2
  return (a.1, pr.1, pr.2.2)

/-- Bound the combined chooser and prover queries satisfying `counts`. Verifier messages are
excluded. A selector on the public summand also excludes private draws. -/
def IsQueryBound (P : AdaptiveProver spec Stmt Out WitOut pSpec)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) : Prop :=
  P.run.IsQueryBoundP (publicQuerySelector counts) t

end AdaptiveProver

namespace Verifier

variable {ι κ κE σ Stmt Out Wit WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ} {extractorSpec : OracleSpec κE}
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (privateImpl : QueryImpl privateSpec ProbComp)

/-- Initialize the shared oracle, choose the statement, and run the public-coin interaction.
The prover can sample through `privateSpec`, while the verifier queries `oSpec`. -/
def adaptiveSoundnessExp (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    ProbComp (Option (Stmt × Out)) :=
  AdaptiveGame.run init
    (impl + privateImpl + challengeQueryImpl) P.run
    (fun (x, tr, _) => liftCompLeft (liftCompLeft (V.run x tr).run))
    (fun a out => out.map (a.1, ·))

/-- Interactive adaptive soundness with an explicit adversary-admissibility condition. -/
def adaptiveSoundness (langIn : Set Stmt) (langOut : Set Out)
    (admissible : (WitOut : Type) →
      AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  ∀ WitOut, AdaptiveGame.Bounded (admissible WitOut)
    (V.adaptiveSoundnessExp init impl privateImpl) (nargSoundFailEvent langIn langOut) error

/-- Adaptive soundness at a public-query budget shared by the chooser and prover. -/
def adaptiveSoundnessQueryBounded (langIn : Set Stmt) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveSoundness init impl privateImpl langIn langOut
    (fun _ P => P.IsQueryBound (publicQuerySelector counts) t) error

/-- A named extractor sees the chosen statement, output witness, transcript, and public query
logs of both sides. Its oracle access is set by the extractor handler. -/
abbrev AdaptiveExtractor (oSpec : OracleSpec ι) (extractorSpec : OracleSpec κE)
    (Stmt Wit WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Stmt → WitOut → FullTranscript pSpec → QueryLog oSpec → QueryLog oSpec →
    OptionT (OracleComp extractorSpec) Wit

/-- Run the interactive knowledge experiment. The extractor receives the prover's public log
from both phases, the verifier's public log, and the full transcript. -/
def adaptiveKnowledgeSoundnessExp
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    ProbComp (Stmt × Option Wit × Option Out × WitOut) :=
  AdaptiveGame.runWithExtractor init
    (impl + privateImpl + challengeQueryImpl)
    extractorImpl P.run.withQueryLog
    (fun ((x, tr, _), _) => liftCompLeft (liftCompLeft (V.run x tr).run.withQueryLog))
    (fun ((x, tr, wOut), logP) (_, logV) => extract x wOut tr logP.fst.publicQueries logV)
    (fun ((x, _, wOut), _) (out, _) wIn => (x, wIn, out, wOut))

/-- Bound extraction failure for one named extractor against every admissible adversary. -/
def adaptiveKnowledgeSoundnessWithExtractor
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (admissible : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded admissible
    (V.adaptiveKnowledgeSoundnessExp init impl privateImpl extractorImpl extract)
    (relationKSFailEvent relIn relOut) error

/-- Bound extraction failure for one named extractor and a public-query budget. -/
def adaptiveKnowledgeSoundnessQueryBoundedWithExtractor
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveKnowledgeSoundnessWithExtractor init impl privateImpl extractorImpl
    relIn relOut extract (fun P => P.IsQueryBound (publicQuerySelector counts) t) error

/-- One extractor for all query budgets, chosen before the budget and adversary. -/
def adaptiveKnowledgeSoundnessQueryBounded
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (counts : ι → Prop) [DecidablePred counts] (error : ℕ → ENNReal) : Prop :=
  ∃ extract, ∀ t, V.adaptiveKnowledgeSoundnessQueryBoundedWithExtractor init impl privateImpl
    extractorImpl relIn relOut extract counts t (error t)

end Verifier

section FixedProver

variable {ι κ Stmt Aux Out WitOut : Type} {src : OracleSpec ι} {dst : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n}

private def mapProverOracles (route : QueryImpl src (OracleComp dst))
    (P : Prover src Stmt Aux Out WitOut pSpec) : Prover dst Stmt Aux Out WitOut pSpec where
  PrvState := P.PrvState
  input := P.input
  sendMessage i s := simulateQ route (P.sendMessage i s)
  receiveChallenge i s := simulateQ route (P.receiveChallenge i s)
  output s := simulateQ route (P.output s)

private theorem simulateQ_run_mapProverOracles {m : Type → Type} [Monad m] [LawfulMonad m]
    (route : QueryImpl src (OracleComp dst)) (impl : QueryImpl src m) (impl' : QueryImpl dst m)
    (challenges : QueryImpl [pSpec.Challenge]ₒ m)
    (hRoute : ∀ q, simulateQ impl' (route q) = impl q)
    (P : Prover src Stmt Aux Out WitOut pSpec) (stmt : Stmt) (aux : Aux) :
    simulateQ (impl' + challenges) ((mapProverOracles route P).run stmt aux) =
      simulateQ (impl + challenges) (P.run stmt aux) := by
  have hComp {α : Type} (oa : OracleComp src α) :
      simulateQ impl' (simulateQ route oa) = simulateQ impl oa := by
    rw [← QueryImpl.simulateQ_compose]
    exact congrArg (fun handler => simulateQ handler oa) (funext hRoute)
  have hRound (i : Fin (n + 1)) :
      simulateQ (impl' + challenges) ((mapProverOracles route P).runToRound i stmt aux) =
        simulateQ (impl + challenges) (P.runToRound i stmt aux) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      simp only [Prover.runToRound, Fin.induction_succ] at ih ⊢
      simp only [Prover.processRound, simulateQ_bind, ih]
      refine bind_congr fun ⟨tr, s⟩ => ?_
      split
      · simp [mapProverOracles, hComp, QueryImpl.simulateQ_add_liftM_left, simulateQ_bind]
        congr 1
      · simp [mapProverOracles, hComp, QueryImpl.simulateQ_add_liftM_left]
  simp only [Prover.run, simulateQ_bind, hRound]
  refine bind_congr fun ⟨tr, s⟩ => ?_
  simp [mapProverOracles, hComp, QueryImpl.simulateQ_add_liftM_left]

end FixedProver

namespace Verifier

variable {ι κ σ Stmt Out : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (privateImpl : QueryImpl privateSpec ProbComp)

/-- A constant chooser makes the same execution as the fixed-statement reduction game. -/
theorem adaptiveSoundnessExp_fixed {Aux WitOut : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover (oSpec + privateSpec) Stmt Aux Out WitOut pSpec) :
    V.adaptiveSoundnessExp init impl privateImpl (AdaptiveProver.fixed stmt aux P) =
      (fun out : Option ((FullTranscript pSpec × Out × WitOut) × Out) =>
        out.map (fun result => (stmt, result.2))) <$>
        (do StateT.run' (simulateQ
          (impl + privateImpl + challengeQueryImpl)
          ((Reduction.mk P V.liftOracles).run stmt aux).run) (← init)) := by
  rw [Reduction.run_run_eq_bind]
  simp only [adaptiveSoundnessExp, AdaptiveGame.run, AdaptiveProver.run, AdaptiveProver.fixed,
    liftCompLeft, Verifier.liftOracles,
    liftComp_pure, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc,
    StateT.run'_eq, map_bind, StateT.run_bind, StateT.run_pure, Functor.map_map]
  congr 1
  funext st
  congr 1
  funext a
  congr 1
  funext v
  cases v.1 <;> rfl

/-- Ordinary soundness is equivalent to adaptive soundness for constant choosers whose
prover uses the public oracles. -/
theorem soundness_iff_adaptiveSoundness_fixed (langIn : Set Stmt) (langOut : Set Out)
    (error : ℝ≥0) :
    V.soundness init impl langIn langOut error ↔
      V.adaptiveSoundness init impl privateImpl langIn langOut
        (fun WitOut A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover oSpec Stmt Aux Out WitOut pSpec),
          A = AdaptiveProver.fixed stmt aux P) error := by
  let combined := impl + privateImpl
  let challenges : QueryImpl [pSpec.Challenge]ₒ (StateT σ ProbComp) :=
    challengeQueryImpl.liftTarget _
  have hEvent (stmt : Stmt) {Aux WitOut : Type} (aux : Aux)
      (P : Prover oSpec Stmt Aux Out WitOut pSpec) :
      let A := AdaptiveProver.fixed stmt aux P
      Pr{let out ← V.adaptiveSoundnessExp (WitOut := WitOut) init impl privateImpl A}[
        nargSoundFailEvent langIn langOut out] =
      Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
        StateT.run' (simulateQ (impl + challengeQueryImpl)
          ((Reduction.mk P V).run stmt aux).run) (← init)}[stmt ∉ langIn ∧ stmtOut ∈ langOut] := by
    dsimp only
    let fixed := AdaptiveProver.fixed stmt aux P
    let A : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec := fixed
    let lifted : Prover (oSpec + privateSpec) Stmt Aux Out WitOut pSpec :=
      mapProverOracles (fun q => query (spec := oSpec + privateSpec) (.inl q)) P
    have hFixed : A = AdaptiveProver.fixed stmt aux lifted := by
      simp [A, fixed, AdaptiveProver.fixed, liftCompLeft]
      rfl
    have hRun : simulateQ (combined + challenges) (lifted.run stmt aux) =
        simulateQ (impl + challenges) (P.run stmt aux) := by
      apply simulateQ_run_mapProverOracles
      intro q
      simp [combined]
    have hReduction :
        simulateQ (combined + challenges) ((Reduction.mk lifted V.liftOracles).run stmt aux).run =
          simulateQ (impl + challenges) ((Reduction.mk P V).run stmt aux).run := by
      rw [Reduction.run_run_eq_bind, Reduction.run_run_eq_bind]
      simp only [simulateQ_bind, hRun, Verifier.run, Verifier.liftOracles, OptionT.run_mk,
        QueryImpl.simulateQ_add_liftComp_left, simulateQ_pure]
      simp only [combined, QueryImpl.add_lift_right, QueryImpl.simulateQ_add_liftComp_left]
    change Pr{let out ← V.adaptiveSoundnessExp init impl privateImpl A}[
      nargSoundFailEvent langIn langOut out] = _
    rw [hFixed, adaptiveSoundnessExp_fixed, prEvent_map, OptionT.prEvent_mk]
    simp only [combined, QueryImpl.add_lift_right] at hReduction ⊢
    rw [hReduction]
    simp only [challenges]
    congr 2
    funext out
    cases out <;> simp [nargSoundFailEvent]
  constructor
  · intro h WitOut A hA
    obtain ⟨Aux, stmt, aux, P, rfl⟩ := hA
    rw [hEvent stmt aux P]
    by_cases hStmt : stmt ∉ langIn
    · simpa only [hStmt, not_false_eq_true, true_and, QueryImpl.addLift_def,
        QueryImpl.add_lift_right, QueryImpl.liftTarget_self] using h Aux WitOut aux P stmt hStmt
    · rw [OptionT.prEvent_mk]
      refine (prEvent_mono _ _ (fun _ => False) (fun out ho => ?_)).trans ?_
      · cases out <;> simp_all
      · simp
  · intro h Aux WitOut aux P stmt hStmt
    let fixed := AdaptiveProver.fixed stmt aux P
    have hA := h WitOut fixed ⟨Aux, stmt, aux, P, rfl⟩
    rw [hEvent stmt aux P] at hA
    simpa only [hStmt, not_false_eq_true, true_and, QueryImpl.addLift_def, QueryImpl.add_lift_right,
      QueryImpl.liftTarget_self] using hA

end Verifier

namespace AdaptiveProver

variable {ι Stmt Proof Out : Type} {spec : OracleSpec ι}

local instance : ProverOnly (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1) where
  prover_first' := rfl

local instance : ∀ i, SampleableType ((⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge i) :=
  fun i => isEmptyElim i

/-- Treat a NARG adversary as a one-message prover by sending the NARG string it has already
generated in its chooser phase. The message phase uses no queries. The prover returns
a dummy output statement; the verifier supplies the output used by the experiment. -/
def ofNARG [Inhabited Out] (P : OracleComp spec (Stmt × Proof)) :
    AdaptiveProver spec Stmt Out Unit (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1) where
  Aux := Proof
  choose := P
  prover :=
    { PrvState := fun _ => Proof
      input := Prod.snd
      sendMessage := fun i π => by
        have hi : i = ⟨0, rfl⟩ := Subtype.ext (Fin.eq_zero _)
        subst i
        exact pure (π, π)
      receiveChallenge := fun i => isEmptyElim i
      output := fun _ => pure (default, ()) }

theorem run_ofNARG [Inhabited Out] (P : OracleComp spec (Stmt × Proof)) :
    (ofNARG (Out := Out) P).run =
      (fun a => (a.1, Fin.cons a.2 (fun i => i.elim0), ())) <$>
        liftComp P (spec + [(⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge]ₒ'
          challengeOracleInterface) := by
  unfold run
  simp only [Prover.run_of_prover_first, ofNARG, monadLift_pure, liftComp_pure,
    map_pure, bind_pure_comp]
  congr 1
  funext a
  congr 2
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- The embedding of a NARG adversary preserves its public-query budget. -/
theorem isQueryBound_ofNARG [Inhabited Out] (P : OracleComp spec (Stmt × Proof))
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ)
    (hP : P.IsQueryBoundP counts t) : (ofNARG (Out := Out) P).IsQueryBound counts t := by
  rw [IsQueryBound, run_ofNARG]
  simp only [isQueryBoundP_map_iff]
  rw [liftComp_def]
  let target := spec + [(⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge]ₒ'
    challengeOracleInterface
  apply hP.simulateQ_of_step
  · intro q _
    change (liftM (target.query (.inl q)) : OracleComp target _).IsQueryBoundP
      (publicQuerySelector counts) 1
    simp [isQueryBoundP_query_iff]
  · intro q hq
    change (liftM (target.query (.inl q)) : OracleComp target _).IsQueryBoundP
      (publicQuerySelector counts) 0
    simp [isQueryBoundP_query_iff, publicQuerySelector, hq]

end AdaptiveProver

namespace Verifier

variable {ι κ σ Stmt Proof Out : Type} {oSpec : OracleSpec ι}
  {privateSpec : OracleSpec κ} [Inhabited Out]
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The one-message interactive game on an embedded NARG adversary is the NARG experiment. -/
theorem adaptiveSoundnessExp_ofNARG (privateImpl : QueryImpl privateSpec ProbComp)
    (P : OracleComp (oSpec + privateSpec) (Stmt × Proof)) :
    V.adaptiveSoundnessExp init impl privateImpl (AdaptiveProver.ofNARG P) =
      adaptiveNARGSoundnessExp init impl privateImpl V P := by
  simp only [adaptiveSoundnessExp, adaptiveNARGSoundnessExp, AdaptiveGame.run,
    AdaptiveProver.run_ofNARG, liftCompLeft, bind_map_left, simulateQ_bind, simulateQ_pure]
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self]
  simp only [QueryImpl.simulateQ_add_liftComp_left]

/-- Interactive adaptive soundness at a public-query budget implies its NARG specialization
at the same budget. -/
theorem adaptiveNARGSoundnessQueryBounded_of_adaptiveSoundnessQueryBounded
    (langIn : Set Stmt) (langOut : Set Out) (counts : ι → Prop) [DecidablePred counts]
    (t : ℕ) (error : ENNReal)
    (h : V.adaptiveSoundnessQueryBounded init impl (QueryImpl.id' unifSpec)
      langIn langOut counts t error) :
    V.adaptiveNARGSoundnessQueryBounded init impl langIn langOut counts t error := by
  intro P hP
  have hRun := h Unit (AdaptiveProver.ofNARG P)
    (AdaptiveProver.isQueryBound_ofNARG P _ _ hP)
  simpa only [adaptiveSoundnessExp_ofNARG] using hRun

end Verifier

namespace Verifier

variable {ι κ σ Stmt Out Wit WitOut : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (privateImpl : QueryImpl privateSpec ProbComp)

/-- Embed a public-oracle extractor into the combined legacy interface, exposing only public
queries from the legacy logs. -/
def AdaptiveExtractor.forCombinedOracles
    (extract : AdaptiveExtractor oSpec oSpec Stmt Wit WitOut pSpec) :
    Extractor.Straightline (oSpec + privateSpec) Stmt Wit WitOut pSpec :=
  fun x wOut tr logP logV =>
    OptionT.mk (liftCompLeft (extract x wOut tr logP.publicQueries logV.publicQueries).run)

/-- For a fixed chooser, the named adaptive extractor has exactly the same failure probability
as the ordinary straightline extractor. -/
theorem adaptiveKnowledgeSoundness_fixed_probability
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec)
    {Aux : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover (oSpec + privateSpec) Stmt Aux Out WitOut pSpec) :
    Pr{let out ← (V.adaptiveKnowledgeSoundnessExp init impl privateImpl impl extract
      (AdaptiveProver.fixed stmt aux P))}[relationKSFailEvent relIn relOut out] =
    let pImpl := impl + privateImpl + challengeQueryImpl (pSpec := pSpec)
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk P V.liftOracles).runWithLog stmt aux
      let wit ← OptionT.lift (liftCompLeft
        (AdaptiveExtractor.forCombinedOracles extract stmt witOut transcript
          proveQueryLog.fst verifyQueryLog).run)
      return (stmt, wit, stmtOut, witOut)
    Pr{let ⟨x, wit, out, outWit⟩ ← OptionT.mk do
      (simulateQ pImpl exec.run).run' (← init)}[
        (∀ w ∈ wit, (x, w) ∉ relIn) ∧ (out, outWit) ∈ relOut] := by
  have hP : (AdaptiveProver.fixed stmt aux P).run.withQueryLog =
      (fun a => ((stmt, a.1.1, a.1.2.2), a.2)) <$> P.runWithLog stmt aux := by
    simp only [AdaptiveProver.fixed, AdaptiveProver.run, liftComp_pure, pure_bind,
      bind_pure_comp, Prover.runWithLog, withQueryLog, simulateQ_map, WriterT.run_map]
    rfl
  have hV (tr : FullTranscript pSpec) :
      (simulateQ loggingOracle
        ((V.liftOracles (targetSpec := oSpec + privateSpec)).run stmt tr)).run =
        (fun a => (a.1, QueryLog.inl a.2)) <$>
          liftCompLeft (V.run stmt tr).run.withQueryLog := by
    change (liftCompLeft (V.run stmt tr).run).withQueryLog = _
    simp only [liftCompLeft, withQueryLog_liftComp_left, map_eq_pure_bind]
  rw [OptionT.prEvent_mk]
  simp only [adaptiveKnowledgeSoundnessExp, AdaptiveGame.runWithExtractor, AdaptiveGame.execute,
    hP, bind_map_left, monadLift_self, Reduction.runWithLog,
    OptionT.run_bind, OptionT.lift, ← monadLift_liftM_OptionT, OptionT.run_monadLift, Option.elimM,
    Option.elim_some, OptionT.run_pure, hV, Option.getM, bind_assoc, simulateQ_bind,
    StateT.run'_bind', simulateQ_pure, pure_bind]
  simp only [QueryImpl.add_lift_right, liftCompLeft, ← liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_map, StateT.run_map, bind_map_left, QueryLog.publicQueries]
  -- Compare the extraction event after each of the three common stateful draws.
  apply prEvent_bind_congr
  intro state
  apply prEvent_bind_congr
  intro proverResult
  apply prEvent_bind_congr
  rintro ⟨⟨out, log⟩, state'⟩
  cases out with
  | none => simp [relationKSFailEvent]
  | some out =>
    simp only [OptionT.run_pure, simulateQ_pure, StateT.run_pure, pure_bind, Option.elim_some,
      AdaptiveExtractor.forCombinedOracles, OptionT.run_mk, QueryLog.publicQueries,
      QueryLog.fst_inl,
      liftCompLeft, simulateQ_map, QueryImpl.simulateQ_add_liftComp_left,
      StateT.run_map,
      bind_map_left, bind_pure_comp, StateT.run'_eq, Functor.map_map, map_pure]
    apply prEvent_congr
    intro w
    cases w.1 <;> simp [relationKSFailEvent, and_comm]

/-- Ordinary knowledge soundness for a named extractor is the adaptive predicate on
constant choosers, using the same extractor. -/
theorem knowledgeSoundnessWith_iff_adaptiveKnowledgeSoundnessWithExtractor_fixed
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec) (error : ℝ≥0) :
    V.liftOracles.knowledgeSoundnessWith init (impl + privateImpl) relIn relOut
      (AdaptiveExtractor.forCombinedOracles extract) error ↔
      V.adaptiveKnowledgeSoundnessWithExtractor init impl privateImpl impl relIn relOut extract
        (fun A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover (oSpec + privateSpec) Stmt Aux Out WitOut pSpec),
          A = AdaptiveProver.fixed stmt aux P)
        error := by
  constructor
  · intro h A hA
    obtain ⟨Aux, stmt, aux, P, rfl⟩ := hA
    refine (adaptiveKnowledgeSoundness_fixed_probability V init impl privateImpl relIn relOut
      extract stmt aux P).le.trans ?_
    simpa only [← monadLift_liftM_OptionT, ← liftComp_eq_liftM, liftCompLeft,
      OptionT.run_bind, OptionT.run_monadLift, OptionT.lift, OptionT.run_mk,
      monadLift_self, map_eq_pure_bind, QueryImpl.addLift_def, QueryImpl.add_lift_right,
      QueryImpl.liftTarget_self] using h Aux stmt aux P
  · intro h Aux stmt aux P
    have hBound := (adaptiveKnowledgeSoundness_fixed_probability V init impl privateImpl
      relIn relOut extract stmt aux P).ge.trans (h _ ⟨Aux, stmt, aux, P, rfl⟩)
    simpa only [← monadLift_liftM_OptionT, ← liftComp_eq_liftM, liftCompLeft,
      OptionT.run_bind, OptionT.run_monadLift, OptionT.lift, OptionT.run_mk,
      monadLift_self, map_eq_pure_bind, QueryImpl.addLift_def, QueryImpl.add_lift_right,
      QueryImpl.liftTarget_self] using hBound

end Verifier

/-! ## One-message specializations -/

private theorem withQueryLog_map {ι α β : Type} {spec : OracleSpec ι}
    (f : α → β) (p : OracleComp spec α) :
    (f <$> p).withQueryLog = (fun a => (f a.1, a.2)) <$> p.withQueryLog := by
  simp [withQueryLog, simulateQ_map, WriterT.run_map]

namespace AdaptiveProver
variable {ι Stmt Proof Out WitOut : Type} {spec : OracleSpec ι}

local instance : ∀ i, OracleInterface
    ((⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge i) := challengeOracleInterface

/-- Eliminate the empty challenge interface of a one-message protocol. -/
def eraseChallenges :
    QueryImpl (spec + [(⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge]ₒ)
      (OracleComp spec)
  | .inl q => query q
  | .inr q => isEmptyElim q.1

private theorem lift_eraseChallenges {α : Type}
    (p : OracleComp (spec + [(⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge]ₒ) α) :
    liftComp (simulateQ eraseChallenges p) _ = p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q next ih =>
    rcases q with q | q
    · simp only [simulateQ_bind, simulateQ_spec_query, eraseChallenges, liftComp_bind]
      let target := spec + [(⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1).Challenge]ₒ
      change (liftM (target.query (.inl q)) >>= _) = _
      simp only [ih]
    · exact isEmptyElim q.1

/-- Flatten a one-message interactive adversary, retaining all chooser and prover queries. -/
def toNARG (P : AdaptiveProver spec Stmt Out WitOut
    (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) : OracleComp spec (Stmt × Proof) :=
  (fun a => (a.1, a.2.1 0)) <$> simulateQ eraseChallenges P.run

/-- Flattening followed by the oracle lift only forgets the trivial interaction structure. -/
theorem lift_toNARG (P : AdaptiveProver spec Stmt Out WitOut
    (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    liftComp P.toNARG _ = (fun a => (a.1, a.2.1 0)) <$> P.run := by
  rw [toNARG, liftComp_map, lift_eraseChallenges]

private theorem lift_toNARG_withQueryLog
    (P : AdaptiveProver spec Stmt Out WitOut
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    liftComp P.toNARG.withQueryLog _ =
      (fun a => ((a.1.1, a.1.2.1 0), a.2.fst)) <$> P.run.withQueryLog := by
  have h := congrArg (fun p => (fun a => (a.1, a.2.fst)) <$> p.withQueryLog)
    (lift_toNARG P)
  simpa only [withQueryLog_liftComp_left, withQueryLog_map, Functor.map_map,
    QueryLog.fst_inl, id_map'] using h

/-- Flattening keeps the public-query budget of the entire interactive adversary. -/
theorem isQueryBound_toNARG (P : AdaptiveProver spec Stmt Out WitOut
    (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1))
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ)
    (h : P.IsQueryBound counts t) : P.toNARG.IsQueryBoundP counts t := by
  rw [toNARG, isQueryBoundP_map_iff]
  apply h.simulateQ_of_step
  · intro q hq
    rcases q with q | q
    · simp [eraseChallenges, isQueryBoundP_query_iff, publicQuerySelector] at hq ⊢
    · exact isEmptyElim q.1
  · intro q hq
    rcases q with q | q
    · simpa [eraseChallenges, isQueryBoundP_query_iff, publicQuerySelector] using hq
    · exact isEmptyElim q.1
end AdaptiveProver

namespace Verifier
variable {ι κ σ Stmt Proof Out WitOut : Type} {oSpec : OracleSpec ι}
  {privateSpec : OracleSpec κ}
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (privateImpl : QueryImpl privateSpec ProbComp)

/-- Flattening a one-message adversary leaves the soundness experiment unchanged. -/
theorem adaptiveSoundnessExp_toNARG
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    adaptiveNARGSoundnessExp init impl privateImpl V P.toNARG =
      V.adaptiveSoundnessExp init impl privateImpl P := by
  have h := AdaptiveProver.lift_toNARG P
  have heq (tr : FullTranscript (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
      Fin.cons (tr 0) (fun i => i.elim0) = tr := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  unfold adaptiveNARGSoundnessExp adaptiveSoundnessExp AdaptiveGame.run
  congr 1
  funext s
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self]
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl + privateImpl.liftTarget _)
    (QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1))))]
  simp only [liftComp_bind, liftComp_pure]
  rw [h]
  simp only [bind_map_left, heq]
  rfl
end Verifier

namespace Verifier
variable {ι κ κE σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι}
  {privateSpec : OracleSpec κ} {extractorSpec : OracleSpec κE} [Inhabited Out]
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A one-message interactive protocol has exactly the adaptive NARG soundness contract. -/
theorem adaptiveSoundnessQueryBounded_iff_adaptiveNARGSoundnessQueryBounded
    (langIn : Set Stmt) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    V.adaptiveSoundnessQueryBounded init impl (QueryImpl.id' unifSpec)
      langIn langOut counts t error ↔
    V.adaptiveNARGSoundnessQueryBounded init impl langIn langOut counts t error := by
  refine ⟨adaptiveNARGSoundnessQueryBounded_of_adaptiveSoundnessQueryBounded V init impl
    langIn langOut counts t error, ?_⟩
  intro h WitOut P hP
  have hRun := h P.toNARG (P.isQueryBound_toNARG _ _ hP)
  simpa only [adaptiveSoundnessExp_toNARG] using hRun

/-- Use a NARG extractor on the single proof message, ignoring the trivial output witness. -/
def AdaptiveExtractor.ofNARG
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit) :
    AdaptiveExtractor oSpec extractorSpec Stmt Wit Unit
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1) :=
  fun x _ tr => E x (tr 0)

/-- The embedded NARG experiment has the same logs and extraction result, with a unit witness. -/
theorem adaptiveKnowledgeSoundnessExp_ofNARG
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (P : OracleComp (oSpec + privateSpec) (Stmt × Proof)) :
    V.adaptiveKnowledgeSoundnessExp init impl privateImpl extractorImpl
      (AdaptiveExtractor.ofNARG E) (AdaptiveProver.ofNARG P) =
      (fun a => (a.1, a.2.1, a.2.2, ())) <$>
        adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl V E P := by
  simp only [adaptiveKnowledgeSoundnessExp, AdaptiveProver.run_ofNARG,
    withQueryLog_map, withQueryLog_liftComp_left, AdaptiveGame.runWithExtractor,
    AdaptiveGame.execute, adaptiveNARGKnowledgeSoundnessExp,
    map_bind, bind_map_left, simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc,
    Functor.map_map, StateT.run'_bind', StateT.run'_pure']
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left,
    AdaptiveExtractor.ofNARG, QueryLog.fst_inl, Fin.cons_zero, Verifier.run]
  simp [runVerifierWithLog, liftCompLeft, QueryImpl.simulateQ_add_liftM_left,
    QueryLog.publicQueries]
end Verifier

namespace Verifier
variable {ι κ κE σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι}
  {privateSpec : OracleSpec κ} {extractorSpec : OracleSpec κE}
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Flattening preserves the one-message knowledge experiment for the supplied extractor. -/
theorem adaptiveKnowledgeSoundnessExp_toNARG
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out Unit
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    V.adaptiveKnowledgeSoundnessExp init impl privateImpl extractorImpl
      (AdaptiveExtractor.ofNARG E) P =
      (fun a => (a.1, a.2.1, a.2.2, ())) <$>
        adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl V E P.toNARG := by
  have heq (tr : FullTranscript (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
      Fin.cons (tr 0) (fun i => i.elim0) = tr := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  simp only [adaptiveKnowledgeSoundnessExp, adaptiveNARGKnowledgeSoundnessExp,
    AdaptiveGame.runWithExtractor, AdaptiveGame.execute, simulateQ_bind, simulateQ_pure,
    pure_bind, bind_assoc, map_bind]
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self]
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl + privateImpl.liftTarget _)
    (QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)))) P.toNARG.withQueryLog]
  rw [AdaptiveProver.lift_toNARG_withQueryLog]
  simp [simulateQ_map, bind_map_left, runVerifierWithLog, liftCompLeft, heq,
    AdaptiveExtractor.ofNARG,
    Verifier.run, QueryImpl.simulateQ_add_liftM_left,
    StateT.run'_eq, map_bind, QueryLog.publicQueries]
end Verifier

/-- With a trivial output witness, the relation-valued failure event is the NARG event. -/
theorem relationKSFailEvent_unit {Stmt Wit Out : Type}
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (a : Stmt × Option Wit × Option Out) :
    relationKSFailEvent relIn (langOut ×ˢ Set.univ) (a.1, a.2.1, a.2.2, ()) =
      nargKSFailEvent relIn langOut a := by
  rcases a with ⟨x, w, y⟩
  cases w <;> cases y <;> simp [relationKSFailEvent, nargKSFailEvent]

namespace Verifier
variable {ι κE σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι}
  {extractorSpec : OracleSpec κE} [Inhabited Out]
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))

/-- The one-message knowledge contract preserves the named extractor, both public logs,
its oracle permissions, and the adversary's query budget. -/
theorem adaptiveKnowledgeSoundnessQueryBoundedWithExtractor_iff_adaptiveNARGKnowledgeSoundness
    (relIn : Set (Stmt × Wit)) (langOut : Set Out)
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    V.adaptiveKnowledgeSoundnessQueryBoundedWithExtractor init impl (QueryImpl.id' unifSpec)
      extractorImpl relIn (langOut ×ˢ Set.univ) (AdaptiveExtractor.ofNARG E) counts t error ↔
    V.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init impl extractorImpl
      relIn langOut E counts t error := by
  constructor
  · intro h P hP
    have hRun := h (AdaptiveProver.ofNARG P) (AdaptiveProver.isQueryBound_ofNARG P _ _ hP)
    simpa only [adaptiveKnowledgeSoundnessExp_ofNARG, prEvent_map, relationKSFailEvent_unit]
      using hRun
  · intro h P hP
    have hRun := h P.toNARG (P.isQueryBound_toNARG _ _ hP)
    simpa only [adaptiveKnowledgeSoundnessExp_toNARG, prEvent_map, relationKSFailEvent_unit]
      using hRun

/-- The same one-message identification holds without a finite query-bound assumption. -/
theorem adaptiveKnowledgeSoundness_iff_adaptiveNARGKnowledgeSoundness
    (relIn : Set (Stmt × Wit)) (langOut : Set Out)
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit) (error : ENNReal) :
    V.adaptiveKnowledgeSoundnessWithExtractor init impl (QueryImpl.id' unifSpec)
      extractorImpl relIn (langOut ×ˢ Set.univ) (AdaptiveExtractor.ofNARG E)
      (fun _ => True) error ↔
    V.adaptiveNARGKnowledgeSoundnessWithExtractor init impl extractorImpl
      relIn langOut E error := by
  constructor
  · intro h P
    have hRun := h (AdaptiveProver.ofNARG P) True.intro
    simpa only [adaptiveKnowledgeSoundnessExp_ofNARG, prEvent_map, relationKSFailEvent_unit]
      using hRun
  · intro h P _
    have hRun := h P.toNARG
    simpa only [adaptiveKnowledgeSoundnessExp_toNARG, prEvent_map, relationKSFailEvent_unit]
      using hRun
end Verifier

namespace Verifier

/-- The one-message soundness equivalence also covers adversaries without any finite budget. -/
theorem adaptiveSoundness_iff_adaptiveNARGSoundness
    {ι σ Stmt Proof Out : Type} {oSpec : OracleSpec ι} [Inhabited Out]
    (V : NonInteractiveVerifier Proof oSpec Stmt Out)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (langIn : Set Stmt) (langOut : Set Out) (error : ENNReal) :
    V.adaptiveSoundness init impl (QueryImpl.id' unifSpec)
      langIn langOut (fun _ _ => True) error ↔
    V.adaptiveNARGSoundness init impl langIn langOut error := by
  constructor
  · intro h P
    have hRun := h Unit (AdaptiveProver.ofNARG P) True.intro
    simpa only [adaptiveSoundnessExp_ofNARG] using hRun
  · intro h WitOut P _
    have hRun := h P.toNARG
    simpa only [adaptiveSoundnessExp_toNARG] using hRun

end Verifier
