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
open scoped NNReal ProbabilityTheory

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
  {oSpec : OracleSpec ι} {proverSpec : OracleSpec κ} {extractorSpec : OracleSpec κE}
  [MonadLiftT (OracleComp oSpec) (OracleComp proverSpec)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl proverSpec (StateT σ ProbComp))

/-- Sample the oracle once, choose the statement, run the public-coin interaction, and
retain the chosen statement with the verifier's optional output. -/
def adaptiveSoundnessExp (P : AdaptiveProver proverSpec Stmt Out WitOut pSpec) :
    ProbComp (Option (Stmt × Out)) :=
  AdaptiveGame.run init (impl.addLift challengeQueryImpl) P.run
    (fun a => liftComp (liftM (V.run a.1 a.2.1).run : OracleComp proverSpec _) _)
    (fun a out => out.map (a.1, ·))

/-- Interactive adaptive soundness with an explicit adversary-admissibility condition. The
condition may be specialized to a public-query selector and a common budget. -/
def adaptiveSoundness (langIn : Set Stmt) (langOut : Set Out)
    (admissible : (WitOut : Type) → AdaptiveProver proverSpec Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  ∀ WitOut, AdaptiveGame.Bounded (admissible WitOut) (V.adaptiveSoundnessExp init impl)
    (nargSoundFailEvent langIn langOut) error

/-- Adaptive soundness at a public-query budget shared by the chooser and prover. -/
def adaptiveSoundnessQueryBounded (langIn : Set Stmt) (langOut : Set Out)
    (counts : κ → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveSoundness init impl langIn langOut (fun _ P => P.IsQueryBound counts t) error

/-- A named extractor sees the chosen statement, output witness, transcript, and public query
logs of both sides. Its oracle access is set by the extractor handler. -/
abbrev AdaptiveExtractor (oSpec : OracleSpec ι) (extractorSpec : OracleSpec κE)
    (Stmt Wit WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  Stmt → WitOut → FullTranscript pSpec → QueryLog oSpec → QueryLog oSpec →
    OptionT (OracleComp extractorSpec) Wit

/-- Run the interactive knowledge experiment. The adversary's public log covers the chooser
and the interaction. The supplied `publicLog` observer determines which prover-side log the
extractor sees. Use `adaptiveKnowledgeSoundnessWithPrivateCoins` for the canonical projection. -/
def adaptiveKnowledgeSoundnessExp
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (publicLog : QueryLog proverSpec → QueryLog oSpec)
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (P : AdaptiveProver proverSpec Stmt Out WitOut pSpec) :
    ProbComp (Stmt × Option Wit × Option Out × WitOut) :=
  AdaptiveGame.runWithExtractor init (impl.addLift challengeQueryImpl) extractorImpl
    P.run.withQueryLog
    (fun a => liftComp (liftM (V.run a.1.1 a.1.2.1).run.withQueryLog : OracleComp proverSpec _) _)
    (fun a v => extract a.1.1 a.1.2.2 a.1.2.1 (publicLog a.2.fst) v.2)
    (fun a v wit => (a.1.1, wit, v.1, a.1.2.2))

/-- Bound extraction failure for one named extractor against every admissible adversary. -/
def adaptiveKnowledgeSoundnessWithExtractor
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (publicLog : QueryLog proverSpec → QueryLog oSpec)
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (admissible : AdaptiveProver proverSpec Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded admissible (V.adaptiveKnowledgeSoundnessExp init impl
    extractorImpl publicLog extract) (relationKSFailEvent relIn relOut) error

/-- One extractor for all query budgets, chosen before the budget and adversary. -/
def adaptiveKnowledgeSoundnessQueryBounded
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (publicLog : QueryLog proverSpec → QueryLog oSpec)
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (counts : κ → Prop) [DecidablePred counts] (error : ℕ → ENNReal) : Prop :=
  ∃ extract, ∀ t, V.adaptiveKnowledgeSoundnessWithExtractor init impl extractorImpl
    publicLog relIn relOut extract (fun P => P.IsQueryBound counts t) (error t)

end Verifier

namespace Verifier

variable {ι κ κE σ Stmt Out Wit WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ} {extractorSpec : OracleSpec κE}
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (privateImpl : QueryImpl privateSpec ProbComp)
  (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))

/-- Interactive adaptive knowledge soundness for a named extractor and one public-query
budget. Both adversarial phases can draw private coins. Those draws and verifier messages
are excluded from the budget and the extractor's prover-side log. -/
def adaptiveKnowledgeSoundnessWithPrivateCoins
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : AdaptiveExtractor oSpec extractorSpec Stmt Wit WitOut pSpec)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveKnowledgeSoundnessWithExtractor init (impl.addLift privateImpl) extractorImpl
    QueryLog.fst relIn relOut extract (fun P => P.IsQueryBound (publicQuerySelector counts) t) error

/-- The same named extractor must work for every public-query budget. -/
def adaptiveKnowledgeSoundnessWithPrivateCoinsQueryBounded
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (counts : ι → Prop) [DecidablePred counts] (error : ℕ → ENNReal) : Prop :=
  ∃ extract, ∀ t, V.adaptiveKnowledgeSoundnessWithPrivateCoins init impl privateImpl
    extractorImpl relIn relOut extract counts t (error t)

end Verifier

namespace Verifier

variable {ι σ Stmt Out : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A constant chooser makes the same execution as the fixed-statement reduction game. -/
theorem adaptiveSoundnessExp_fixed {Aux WitOut : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover oSpec Stmt Aux Out WitOut pSpec) :
    V.adaptiveSoundnessExp init impl (AdaptiveProver.fixed stmt aux P) =
      (fun out : Option ((FullTranscript pSpec × Out × WitOut) × Out) =>
        out.map (fun result => (stmt, result.2))) <$>
        (do StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
          ((Reduction.mk P V).run stmt aux).run) (← init)) := by
  rw [Reduction.run_run_eq_bind]
  simp only [adaptiveSoundnessExp, AdaptiveGame.run, AdaptiveProver.run, AdaptiveProver.fixed,
    liftComp_pure, monadLift_self, pure_bind, simulateQ_bind, simulateQ_pure, bind_assoc,
    StateT.run'_eq, map_bind, StateT.run_bind, StateT.run_pure, Functor.map_map]
  congr 1
  funext st
  congr 1
  funext a
  congr 1
  funext v
  cases v.1 <;> rfl

/-- Ordinary soundness is precisely adaptive soundness restricted to constant choosers. -/
theorem soundness_iff_adaptiveSoundness_fixed (langIn : Set Stmt) (langOut : Set Out)
    (error : ℝ≥0) :
    V.soundness init impl langIn langOut error ↔
      V.adaptiveSoundness init impl langIn langOut
        (fun _ A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover oSpec Stmt Aux Out _ pSpec),
          A = AdaptiveProver.fixed stmt aux P) error := by
  have hEvent (stmt : Stmt) (hStmt : stmt ∉ langIn) {Aux WitOut : Type} (aux : Aux)
      (P : Prover oSpec Stmt Aux Out WitOut pSpec) :
      Pr{let out ← V.adaptiveSoundnessExp init impl (AdaptiveProver.fixed stmt aux P)}[
        nargSoundFailEvent langIn langOut out] =
      Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
        StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
          ((Reduction.mk P V).run stmt aux).run) (← init)}[stmtOut ∈ langOut] := by
    rw [adaptiveSoundnessExp_fixed, prEvent_map, OptionT.prEvent_mk]
    congr 2
    funext out
    cases out <;> simp [nargSoundFailEvent, hStmt]
  constructor
  · intro h WitOut A hA
    obtain ⟨Aux, stmt, aux, P, rfl⟩ := hA
    by_cases hStmt : stmt ∉ langIn
    · rw [hEvent stmt hStmt aux P]
      exact h Aux WitOut aux P stmt hStmt
    · rw [adaptiveSoundnessExp_fixed, prEvent_map]
      refine (prEvent_mono _ _ (fun _ => False) (fun out h => ?_)).trans ?_
      · cases out <;> simp_all [nargSoundFailEvent]
      · simp
  · intro h Aux WitOut aux P stmt hStmt
    have hA := h WitOut (AdaptiveProver.fixed stmt aux P) ⟨Aux, stmt, aux, P, rfl⟩
    rw [hEvent stmt hStmt aux P] at hA
    exact hA

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
    V.adaptiveSoundnessExp init (impl.addLift privateImpl) (AdaptiveProver.ofNARG P) =
      adaptiveNARGSoundnessExp init impl privateImpl V P := by
  simp only [adaptiveSoundnessExp, adaptiveNARGSoundnessExp, AdaptiveGame.run,
    AdaptiveProver.run_ofNARG, bind_map_left, simulateQ_bind, simulateQ_pure,
    ← liftComp_eq_liftM]
  rw [show (impl.addLift privateImpl).addLift (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1))) =
    (impl.addLift privateImpl) + challengeQueryImpl.liftTarget (StateT σ ProbComp) from rfl]
  simp only [QueryImpl.simulateQ_add_liftComp_left]

/-- Interactive adaptive soundness at a public-query budget implies its NARG specialization
at the same budget. -/
theorem adaptiveNARGSoundnessQueryBounded_of_adaptiveSoundnessQueryBounded
    (langIn : Set Stmt) (langOut : Set Out) (counts : ι → Prop) [DecidablePred counts]
    (t : ℕ) (error : ENNReal)
    (h : V.adaptiveSoundnessQueryBounded init (impl.addLift (QueryImpl.id' unifSpec))
      langIn langOut (publicQuerySelector counts) t error) :
    V.adaptiveNARGSoundnessQueryBounded init impl langIn langOut counts t error := by
  intro P hP
  have hRun := h Unit (AdaptiveProver.ofNARG P)
    (AdaptiveProver.isQueryBound_ofNARG P _ _ hP)
  simpa only [adaptiveSoundnessExp_ofNARG] using hRun

end Verifier

namespace Verifier

variable {ι σ Stmt Out Wit WitOut : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- For a fixed chooser, the named adaptive extractor has exactly the same failure probability
as the ordinary straightline extractor. -/
theorem adaptiveKnowledgeSoundness_fixed_probability
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec)
    {Aux : Type} (stmt : Stmt) (aux : Aux) (P : Prover oSpec Stmt Aux Out WitOut pSpec) :
    Pr{let out ← (V.adaptiveKnowledgeSoundnessExp init impl impl id extract
      (AdaptiveProver.fixed stmt aux P))}[relationKSFailEvent relIn relOut out] =
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk P V).runWithLog stmt aux
      let wit ← liftM (extract stmt witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmt, wit, stmtOut, witOut)
    Pr{let ⟨x, wit, out, outWit⟩ ← OptionT.mk do
      StateT.run' (simulateQ (impl.addLift challengeQueryImpl) exec.run) (← init)}[
        (∀ w ∈ wit, (x, w) ∉ relIn) ∧ (out, outWit) ∈ relOut] := by
  have hP : (AdaptiveProver.fixed stmt aux P).run.withQueryLog =
      (fun a => ((stmt, a.1.1, a.1.2.2), a.2)) <$> P.runWithLog stmt aux := by
    simp only [AdaptiveProver.fixed, AdaptiveProver.run, liftComp_pure, pure_bind,
      bind_pure_comp, Prover.runWithLog, withQueryLog, simulateQ_map, WriterT.run_map]
    rfl
  have hV (tr : FullTranscript pSpec) :
      (simulateQ loggingOracle (V.run stmt tr)).run = (V.run stmt tr).run.withQueryLog := rfl
  rw [OptionT.prEvent_mk]
  simp only [adaptiveKnowledgeSoundnessExp, AdaptiveGame.runWithExtractor, AdaptiveGame.execute,
    hP, bind_map_left, id_eq, monadLift_self, Reduction.runWithLog,
    OptionT.run_bind, ← monadLift_liftM_OptionT, OptionT.run_monadLift, Option.elimM,
    Option.elim_some, OptionT.run_pure, hV, Option.getM, bind_assoc, simulateQ_bind,
    StateT.run'_bind', simulateQ_pure, pure_bind]
  simp only [liftComp_eq_liftM, QueryImpl.simulateQ_addLift_liftM_left]
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
    simp only [OptionT.run_pure, simulateQ_pure, StateT.run_pure, pure_bind,
      Option.elim_some, bind_pure_comp, simulateQ_map,
      QueryImpl.simulateQ_addLift_liftM_left, StateT.run'_eq, StateT.run_map,
      Functor.map_map, map_pure, monadLift_self]
    apply prEvent_congr
    intro w
    cases w.1 <;> simp [relationKSFailEvent, and_comm]

/-- Ordinary knowledge soundness for a named extractor is the adaptive predicate on
constant choosers, using the same extractor. -/
theorem knowledgeSoundnessWith_iff_adaptiveKnowledgeSoundnessWithExtractor_fixed
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec) (error : ℝ≥0) :
    V.knowledgeSoundnessWith init impl relIn relOut extract error ↔
      V.adaptiveKnowledgeSoundnessWithExtractor init impl impl id relIn relOut extract
        (fun A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover oSpec Stmt Aux Out WitOut pSpec), A = AdaptiveProver.fixed stmt aux P)
        error := by
  constructor
  · intro h A hA
    obtain ⟨Aux, stmt, aux, P, rfl⟩ := hA
    exact (adaptiveKnowledgeSoundness_fixed_probability V init impl relIn relOut extract
      stmt aux P).le.trans (h Aux stmt aux P)
  · intro h Aux stmt aux P
    exact (adaptiveKnowledgeSoundness_fixed_probability V init impl relIn relOut extract
      stmt aux P).ge.trans (h _ ⟨Aux, stmt, aux, P, rfl⟩)

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
      V.adaptiveSoundnessExp init (impl.addLift privateImpl) P := by
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
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl.addLift privateImpl)
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
    V.adaptiveSoundnessQueryBounded init (impl.addLift (QueryImpl.id' unifSpec))
      langIn langOut (publicQuerySelector counts) t error ↔
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
    V.adaptiveKnowledgeSoundnessExp init (impl.addLift privateImpl) extractorImpl
      QueryLog.fst (AdaptiveExtractor.ofNARG E) (AdaptiveProver.ofNARG P) =
      (fun a => (a.1, a.2.1, a.2.2, ())) <$>
        adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl V E P := by
  simp only [adaptiveKnowledgeSoundnessExp, AdaptiveProver.run_ofNARG,
    withQueryLog_map, withQueryLog_liftComp_left, AdaptiveGame.runWithExtractor,
    AdaptiveGame.execute, adaptiveNARGKnowledgeSoundnessExp,
    map_bind, bind_map_left, simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc,
    Functor.map_map, StateT.run'_bind', StateT.run'_pure']
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left,
    AdaptiveExtractor.ofNARG, QueryLog.fst_inl, Fin.cons_zero, Verifier.run]
  simp [runVerifierWithLog, QueryImpl.simulateQ_add_liftM_left, QueryLog.publicQueries]
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
    V.adaptiveKnowledgeSoundnessExp init (impl.addLift privateImpl) extractorImpl
      QueryLog.fst (AdaptiveExtractor.ofNARG E) P =
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
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl.addLift privateImpl)
    (QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)))) P.toNARG.withQueryLog]
  rw [AdaptiveProver.lift_toNARG_withQueryLog]
  simp [simulateQ_map, bind_map_left, runVerifierWithLog, heq, AdaptiveExtractor.ofNARG,
    Verifier.run, QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftM_left,
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
theorem adaptiveKnowledgeSoundnessWithPrivateCoins_iff_adaptiveNARGKnowledgeSoundness
    (relIn : Set (Stmt × Wit)) (langOut : Set Out)
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) Wit)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    V.adaptiveKnowledgeSoundnessWithPrivateCoins init impl (QueryImpl.id' unifSpec)
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
    V.adaptiveKnowledgeSoundnessWithExtractor init (impl.addLift (QueryImpl.id' unifSpec))
      extractorImpl QueryLog.fst relIn (langOut ×ˢ Set.univ) (AdaptiveExtractor.ofNARG E)
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
    V.adaptiveSoundness init (impl.addLift (QueryImpl.id' unifSpec))
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
