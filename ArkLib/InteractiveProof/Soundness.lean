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

/-- Run a public-oracle adversary in a game that also offers private uniform coins. -/
instance coeAddPrivateOracles :
    CoeTail (AdaptiveProver spec Stmt Out WitOut pSpec)
      (AdaptiveProver (spec + unifSpec) Stmt Out WitOut pSpec) where
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

variable {ι σ Stmt Out Wit WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {oSpec : OracleSpec ι}
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Initialize the shared oracle, choose the statement, and run the public-coin interaction.
The prover can sample through `unifSpec`, while the verifier queries `oSpec`. -/
def adaptiveSoundnessExp (P : AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec) :
    ProbComp (Option (Stmt × Out)) :=
  AdaptiveGame.run init
    (impl + QueryImpl.id' unifSpec + challengeQueryImpl) P.run
    (fun (x, tr, _) => liftCompLeft (liftCompLeft (V.run x tr).run))
    (fun a out => out.map (a.1, ·))

/-- Interactive adaptive soundness with an explicit adversary-admissibility condition. -/
def adaptiveSoundness (langIn : Set Stmt) (langOut : Set Out)
    (admissible : (WitOut : Type) →
      AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  ∀ WitOut, AdaptiveGame.Bounded (admissible WitOut)
    (V.adaptiveSoundnessExp init impl) (nargSoundFailEvent langIn langOut) error

/-- Adaptive soundness at a public-query budget shared by the chooser and prover. -/
def adaptiveSoundnessQueryBounded (langIn : Set Stmt) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveSoundness init impl langIn langOut
    (fun _ P => P.IsQueryBound (publicQuerySelector counts) t) error

/-- Run the interactive knowledge experiment with a straight-line extractor. The extractor
receives the prover's public log from both phases, the verifier's public log, and the full
transcript. It runs after the execution, in the final shared state: its public queries go to
`impl` and its private coins are uniform. -/
def adaptiveKnowledgeSoundnessExp
    (extract : Extractor.StraightlineWithCoins oSpec Stmt Wit WitOut pSpec)
    (P : AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec) :
    ProbComp (Stmt × Option Wit × Option Out × WitOut) :=
  AdaptiveGame.runWithExtractor init
    (impl + QueryImpl.id' unifSpec + challengeQueryImpl)
    (impl.addLift (QueryImpl.id' unifSpec)) P.run.withQueryLog
    (fun ((x, tr, _), _) => liftCompLeft (liftCompLeft (V.run x tr).run.withQueryLog))
    (fun ((x, tr, wOut), logP) (_, logV) => extract x wOut tr logP.fst.publicQueries logV)
    (fun ((x, _, wOut), _) (out, _) wIn => (x, wIn, out, wOut))

/-- Bound extraction failure for one named straight-line extractor against every admissible
adversary. -/
def adaptiveKnowledgeSoundnessWithExtractor
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.StraightlineWithCoins oSpec Stmt Wit WitOut pSpec)
    (admissible : AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec → Prop)
    (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded admissible
    (V.adaptiveKnowledgeSoundnessExp init impl extract)
    (relationKSFailEvent relIn relOut) error

/-- Bound extraction failure for one named extractor and a public-query budget. -/
def adaptiveKnowledgeSoundnessQueryBoundedWithExtractor
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.StraightlineWithCoins oSpec Stmt Wit WitOut pSpec)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveKnowledgeSoundnessWithExtractor init impl
    relIn relOut extract (fun P => P.IsQueryBound (publicQuerySelector counts) t) error

/-- One extractor for all query budgets, chosen before the budget and adversary.
The query bound constrains the adversary, not the extractor; no computability or efficiency
requirement is imposed on extraction. Classical witness selection can therefore recover an
input witness whenever one exists. See `Verifier.knowledgeSoundness_iff_relationSoundness`
for the analogous collapse to relation soundness in the ordinary interactive game. -/
def adaptiveKnowledgeSoundnessQueryBounded
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (counts : ι → Prop) [DecidablePred counts] (error : ℕ → ENNReal) : Prop :=
  ∃ extract, ∀ t, V.adaptiveKnowledgeSoundnessQueryBoundedWithExtractor init impl
    relIn relOut extract counts t (error t)

end Verifier

section FixedProver

variable {ι κ Stmt Aux Out WitOut : Type} {src : OracleSpec ι} {dst : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Route a prover's oracle queries through `route`, leaving its messages and state unchanged. -/
def mapProverOracles (route : QueryImpl src (OracleComp dst))
    (P : Prover src Stmt Aux Out WitOut pSpec) : Prover dst Stmt Aux Out WitOut pSpec where
  PrvState := P.PrvState
  input := P.input
  sendMessage i s := simulateQ route (P.sendMessage i s)
  receiveChallenge i s := simulateQ route (P.receiveChallenge i s)
  output s := simulateQ route (P.output s)

/-- Interpreting a routed prover equals interpreting the original prover with the composed
handler. -/
theorem simulateQ_run_mapProverOracles {m : Type → Type} [Monad m] [LawfulMonad m]
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

section PrivateCoins

namespace AdaptiveProver

variable {ι κ Stmt Out WitOut : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- The oracles of a uniform-coin adversary run. -/
local notation "RunSpec" => (oSpec + unifSpec) + [pSpec.Challenge]ₒ

/-- Compile an adversary's custom private sampler to uniform private coins. Each private
request runs `sampler` on `unifSpec`; public queries pass through unchanged. -/
def normalizePrivateCoins (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec where
  Aux := P.Aux
  choose := OracleComp.normalizePrivateCoins sampler P.choose
  prover := mapProverOracles (privateCoinsImpl sampler) P.prover

/-- Forward the public and private-coin queries of a run to the left summand. -/
private def runLeft : QueryImpl (oSpec + unifSpec) (OracleComp RunSpec) :=
  fun q => liftM ((RunSpec).query (.inl q))

/-- Forward the verifier messages of a run to the right summand. -/
private def runRight : QueryImpl [pSpec.Challenge]ₒ (OracleComp RunSpec) :=
  fun q => liftM ((RunSpec).query (.inr q))

/-- Route a whole adversary run: compile private requests with `sampler`, and forward public
queries and verifier messages unchanged. -/
def privateCoinsRunImpl (sampler : QueryImpl privateSpec ProbComp) :
    QueryImpl ((oSpec + privateSpec) + [pSpec.Challenge]ₒ) (OracleComp RunSpec) :=
  (fun q => liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
      (privateCoinsImpl (publicSpec := oSpec) sampler q) :
      QueryImpl (oSpec + privateSpec) (OracleComp RunSpec)) +
    (fun q => liftM ((RunSpec).query (.inr q)) :
      QueryImpl [pSpec.Challenge]ₒ (OracleComp RunSpec))

private theorem runLeft_add_runRight :
    (runLeft (oSpec := oSpec) (pSpec := pSpec) + runRight (oSpec := oSpec) (pSpec := pSpec)) =
      QueryImpl.id' RunSpec := by
  funext q
  rcases q with q | q <;> rfl

private theorem simulateQ_runLeft {α : Type} (x : OracleComp (oSpec + unifSpec) α) :
    simulateQ (runLeft (pSpec := pSpec)) x =
      liftCompLeft (extraSpec := [pSpec.Challenge]ₒ) x := by
  rw [← QueryImpl.simulateQ_add_liftComp_left _ (runRight (oSpec := oSpec) (pSpec := pSpec)) x,
    runLeft_add_runRight, simulateQ_id']
  rfl

/-- The compiled adversary runs the original adversary with private requests compiled. -/
theorem run_normalizePrivateCoins (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    (P.normalizePrivateCoins sampler).run = simulateQ (privateCoinsRunImpl sampler) P.run := by
  have hProver (stmt : Stmt) (aux : P.Aux) :
      (mapProverOracles (privateCoinsImpl sampler) P.prover).run stmt aux =
        simulateQ (privateCoinsRunImpl sampler) (P.prover.run stmt aux) := by
    have h := simulateQ_run_mapProverOracles (m := OracleComp RunSpec)
      (privateCoinsImpl (publicSpec := oSpec) sampler)
      (fun q => liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
        (privateCoinsImpl (publicSpec := oSpec) sampler q))
      runLeft runRight (fun _ => simulateQ_runLeft _) P.prover stmt aux
    rw [runLeft_add_runRight, simulateQ_id'] at h
    rw [h]
    rfl
  have hChoose :
      liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
          (OracleComp.normalizePrivateCoins sampler P.choose) =
        simulateQ (privateCoinsRunImpl sampler)
          (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ) P.choose) := by
    rw [OracleComp.normalizePrivateCoins, ← simulateQ_runLeft, ← QueryImpl.simulateQ_compose,
      privateCoinsRunImpl, liftCompLeft, QueryImpl.simulateQ_add_liftComp_left]
    congr 1
  simp only [liftCompLeft] at hChoose
  simp only [run, normalizePrivateCoins]
  rw [hChoose]
  simp only [simulateQ_bind, simulateQ_pure, hProver]

/-- Running a program rewritten by `privateCoinsRunImpl sampler` with uniform coins equals
running the original program with `sampler`. -/
theorem simulateQ_privateCoinsRunImpl {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (sampler : QueryImpl privateSpec ProbComp)
    (challenges : QueryImpl [pSpec.Challenge]ₒ (StateT σ ProbComp))
    (x : OracleComp ((oSpec + privateSpec) + [pSpec.Challenge]ₒ) α) :
    simulateQ ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) +
        challenges) (simulateQ (privateCoinsRunImpl sampler) x) =
      simulateQ ((impl.addLift sampler : QueryImpl _ (StateT σ ProbComp)) + challenges) x := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext q
  rcases q with q | q
  · have h := simulateQ_normalizePrivateCoins impl sampler
      (liftM ((oSpec + privateSpec).query q) : OracleComp (oSpec + privateSpec) _)
    simp only [OracleComp.normalizePrivateCoins, simulateQ_spec_query] at h
    have hLeft : ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) +
        challenges) ∘ₛ runLeft (pSpec := pSpec) =
        (impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) := by
      funext t
      rw [QueryImpl.apply_compose, runLeft, simulateQ_spec_query, QueryImpl.add_apply_inl]
    rw [QueryImpl.apply_compose]
    change simulateQ _ (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
      (privateCoinsImpl (publicSpec := oSpec) sampler q)) = _
    rw [← simulateQ_runLeft, ← QueryImpl.simulateQ_compose, hLeft, h]
    rfl
  · rw [QueryImpl.apply_compose]
    change simulateQ _ (liftM ((RunSpec).query (.inr q))) = _
    rw [simulateQ_spec_query, QueryImpl.add_apply_inr]
    rfl

/-- Compiling a custom sampler leaves the interpreted adversary run unchanged: running the
compiled adversary with uniform coins equals running the original with `sampler`. -/
theorem simulateQ_run_normalizePrivateCoins {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (sampler : QueryImpl privateSpec ProbComp)
    (challenges : QueryImpl [pSpec.Challenge]ₒ (StateT σ ProbComp))
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    simulateQ ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _ (StateT σ ProbComp)) +
        challenges) (P.normalizePrivateCoins sampler).run =
      simulateQ ((impl.addLift sampler : QueryImpl _ (StateT σ ProbComp)) + challenges)
        P.run := by
  rw [run_normalizePrivateCoins, simulateQ_privateCoinsRunImpl]

/-- Compiling a custom sampler keeps the adversary's log of `oSpec` queries: the compiled run
logs the same public queries as the original run. -/
theorem publicLog_withQueryLog_run_normalizePrivateCoins
    (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    (fun z => (z.1, z.2.fst.fst)) <$> (P.normalizePrivateCoins sampler).run.withQueryLog =
      simulateQ (privateCoinsRunImpl sampler)
        ((fun z => (z.1, z.2.fst.fst)) <$> P.run.withQueryLog) := by
  rw [run_normalizePrivateCoins]
  refine withQueryLog_simulateQ_project _ (fun l => l.fst.fst) (fun l => l.fst.fst) rfl rfl
    (fun _ _ => by simp only [QueryLog.fst_append])
    (fun _ _ => by simp only [QueryLog.fst_append]) ?_ P.run
  rintro ((q | q) | q)
  · change (fun z => (z.1, z.2.fst.fst)) <$>
        (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
          (liftM ((oSpec + unifSpec).query (.inl q)) :
            OracleComp (oSpec + unifSpec) _)).withQueryLog = _
    rw [← simulateQ_runLeft, simulateQ_spec_query]
    simp [runLeft, privateCoinsRunImpl, privateCoinsImpl, withQueryLog_query, QueryLog.fst]
    rfl
  · change (fun z => (z.1, z.2.fst.fst)) <$>
        (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
          (liftComp (sampler q) (oSpec + unifSpec))).withQueryLog = _
    rw [liftCompLeft, withQueryLog_liftComp_left]
    simp only [Functor.map_map, QueryLog.fst_inl]
    have h := congrArg (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ))
      (fst_withQueryLog_liftComp_right (publicSpec := oSpec) (sampler q))
    simp only [liftCompLeft, liftComp_map] at h
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · simp [privateCoinsRunImpl, privateCoinsImpl, QueryLog.fst, liftCompLeft]
  · change (fun z => (z.1, z.2.fst.fst)) <$>
        (liftM ((RunSpec).query (.inr q)) : OracleComp RunSpec _).withQueryLog = _
    simp [privateCoinsRunImpl, withQueryLog_query, QueryLog.fst]

/-- Compiling a custom sampler preserves every budget on selected public queries. -/
theorem IsQueryBound.normalizePrivateCoins (sampler : QueryImpl privateSpec ProbComp)
    (counts : ι → Prop) [DecidablePred counts]
    {P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec} {t : ℕ}
    (h : P.IsQueryBound (publicQuerySelector counts) t) :
    (P.normalizePrivateCoins sampler).IsQueryBound (publicQuerySelector counts) t := by
  unfold IsQueryBound at h ⊢
  rw [run_normalizePrivateCoins]
  apply h.simulateQ_of_step
  · intro q hq
    rcases q with (q | q) | q
    · change (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
        (liftM ((oSpec + unifSpec).query (.inl q)) : OracleComp (oSpec + unifSpec) _)).IsQueryBoundP
        _ 1
      rw [← simulateQ_runLeft, simulateQ_spec_query]
      simp [runLeft, publicQuerySelector, isQueryBoundP_query_iff]
    · exact hq.elim
    · exact hq.elim
  · intro q hq
    rcases q with (q | q) | q
    · change (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
        (liftM ((oSpec + unifSpec).query (.inl q)) : OracleComp (oSpec + unifSpec) _)).IsQueryBoundP
        _ 0
      rw [← simulateQ_runLeft, simulateQ_spec_query]
      simpa [runLeft, publicQuerySelector, isQueryBoundP_query_iff] using hq
    · change (liftCompLeft (extraSpec := [pSpec.Challenge]ₒ)
        (privateCoinsImpl (publicSpec := oSpec) sampler (.inr q))).IsQueryBoundP
        (publicQuerySelector (publicQuerySelector (κ := ℕ) counts)) 0
      rw [← simulateQ_runLeft]
      refine (isQueryBoundP_lift_private counts (sampler q)).simulateQ_of_step ?_ ?_ <;>
        intro u hu <;> rcases u with u | u <;>
        simp_all [runLeft, publicQuerySelector, isQueryBoundP_query_iff]
    · change (liftM ((RunSpec).query (.inr q)) : OracleComp RunSpec _).IsQueryBoundP _ 0
      simp [publicQuerySelector, isQueryBoundP_query_iff]

end AdaptiveProver

namespace Verifier

variable {ι κ σ Stmt Out WitOut : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- An adversary with a custom private sampler is a uniform-coin adversary: its compiled
form has the same soundness experiment, interpreted with `sampler`. -/
theorem adaptiveSoundnessExp_normalizePrivateCoins (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    V.adaptiveSoundnessExp init impl (P.normalizePrivateCoins sampler) =
      AdaptiveGame.run init (impl + sampler + challengeQueryImpl) P.run
        (fun (x, tr, _) => liftCompLeft (liftCompLeft (V.run x tr).run))
        (fun a out => out.map (a.1, ·)) := by
  have h := AdaptiveProver.simulateQ_run_normalizePrivateCoins impl sampler
    ((challengeQueryImpl (pSpec := pSpec)).liftTarget (StateT σ ProbComp)) P
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self] at h
  simp only [adaptiveSoundnessExp, AdaptiveGame.run, QueryImpl.add_lift_right,
    simulateQ_bind, simulateQ_pure, h, liftCompLeft, QueryImpl.simulateQ_add_liftComp_left]

/-- A query-bounded soundness guarantee for uniform-coin adversaries also bounds adversaries
that use any private sampler, with the same public-query budget. -/
theorem adaptiveSoundnessQueryBounded.apply_sampler {langIn : Set Stmt} {langOut : Set Out}
    {counts : ι → Prop} [DecidablePred counts] {t : ℕ} {error : ENNReal}
    (h : V.adaptiveSoundnessQueryBounded init impl langIn langOut counts t error)
    (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec)
    (hP : P.IsQueryBound (publicQuerySelector counts) t) :
    Pr{let out ← AdaptiveGame.run init (impl + sampler + challengeQueryImpl) P.run
        (fun (x, tr, _) => liftCompLeft (liftCompLeft (V.run x tr).run))
        (fun a out => out.map (a.1, ·))}[nargSoundFailEvent langIn langOut out] ≤ error := by
  rw [← adaptiveSoundnessExp_normalizePrivateCoins]
  exact h WitOut _ (AdaptiveProver.IsQueryBound.normalizePrivateCoins sampler counts hP)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem runWithExtractor_publicLog {κ' Wit : Type} {spec : OracleSpec κ'}
    (H : QueryImpl ((oSpec + spec) + [pSpec.Challenge]ₒ) (StateT σ ProbComp))
    (extractorImpl : QueryImpl (oSpec + unifSpec) (StateT σ ProbComp))
    (extract : Extractor.StraightlineWithCoins oSpec Stmt Wit WitOut pSpec)
    (Q : OracleComp ((oSpec + spec) + [pSpec.Challenge]ₒ) (Stmt × FullTranscript pSpec × WitOut))
    (verify : Stmt × FullTranscript pSpec × WitOut →
      OracleComp ((oSpec + spec) + [pSpec.Challenge]ₒ) (Option Out × QueryLog oSpec)) :
    AdaptiveGame.runWithExtractor init H extractorImpl Q.withQueryLog
      (fun a => verify a.1)
      (fun ((x, tr, wOut), logP) (_, logV) => extract x wOut tr logP.fst.publicQueries logV)
      (fun ((x, _, wOut), _) (out, _) wIn => (x, wIn, out, wOut)) =
    AdaptiveGame.runWithExtractor init H extractorImpl
      ((fun z => (z.1, z.2.fst.fst)) <$> Q.withQueryLog)
      (fun a => verify a.1)
      (fun ((x, tr, wOut), logP) (_, logV) => extract x wOut tr logP logV)
      (fun ((x, _, wOut), _) (out, _) wIn => (x, wIn, out, wOut)) := by
  simp only [AdaptiveGame.runWithExtractor, AdaptiveGame.execute, simulateQ_bind, simulateQ_pure,
    bind_assoc, pure_bind, bind_map_left]

/-- An adversary with a custom private sampler is a uniform-coin adversary for knowledge
soundness: its compiled form has the same extraction experiment, interpreted with `sampler`.
The extractor receives the same public query log. -/
theorem adaptiveKnowledgeSoundnessExp_normalizePrivateCoins {Wit : Type}
    (extract : Extractor.StraightlineWithCoins oSpec Stmt Wit WitOut pSpec)
    (sampler : QueryImpl privateSpec ProbComp)
    (P : AdaptiveProver (oSpec + privateSpec) Stmt Out WitOut pSpec) :
    V.adaptiveKnowledgeSoundnessExp init impl extract
        (P.normalizePrivateCoins sampler) =
      AdaptiveGame.runWithExtractor init (impl + sampler + challengeQueryImpl)
        (impl.addLift (QueryImpl.id' unifSpec))
        P.run.withQueryLog
        (fun ((x, tr, _), _) => liftCompLeft (liftCompLeft (V.run x tr).run.withQueryLog))
        (fun ((x, tr, wOut), logP) (_, logV) => extract x wOut tr logP.fst.publicQueries logV)
        (fun ((x, _, wOut), _) (out, _) wIn => (x, wIn, out, wOut)) := by
  have h : ∀ {α : Type} (x : OracleComp ((oSpec + privateSpec) + [pSpec.Challenge]ₒ) α), _ :=
    fun x => AdaptiveProver.simulateQ_privateCoinsRunImpl impl sampler
      ((challengeQueryImpl (pSpec := pSpec)).liftTarget (StateT σ ProbComp)) x
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self] at h
  unfold adaptiveKnowledgeSoundnessExp
  rw [runWithExtractor_publicLog (verify := fun a =>
      liftCompLeft (liftCompLeft (V.run a.1 a.2.1).run.withQueryLog)),
    runWithExtractor_publicLog (verify := fun a =>
      liftCompLeft (liftCompLeft (V.run a.1 a.2.1).run.withQueryLog)),
    AdaptiveProver.publicLog_withQueryLog_run_normalizePrivateCoins]
  simp only [AdaptiveGame.runWithExtractor, AdaptiveGame.execute, QueryImpl.add_lift_right,
    simulateQ_bind, simulateQ_pure, h, liftCompLeft, QueryImpl.simulateQ_add_liftComp_left]

end Verifier

end PrivateCoins

namespace Verifier

variable {ι σ Stmt Out : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- A constant chooser makes the same execution as the fixed-statement reduction game. -/
theorem adaptiveSoundnessExp_fixed {Aux WitOut : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover (oSpec + unifSpec) Stmt Aux Out WitOut pSpec) :
    V.adaptiveSoundnessExp init impl (AdaptiveProver.fixed stmt aux P) =
      (fun out : Option ((FullTranscript pSpec × Out × WitOut) × Out) =>
        out.map (fun result => (stmt, result.2))) <$>
        (do StateT.run' (simulateQ
          (impl + QueryImpl.id' unifSpec + challengeQueryImpl)
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
      V.adaptiveSoundness init impl langIn langOut
        (fun WitOut A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover oSpec Stmt Aux Out WitOut pSpec),
          A = AdaptiveProver.fixed stmt aux P) error := by
  let combined := impl + QueryImpl.id' unifSpec
  let challenges : QueryImpl [pSpec.Challenge]ₒ (StateT σ ProbComp) :=
    challengeQueryImpl.liftTarget _
  have hEvent (stmt : Stmt) {Aux WitOut : Type} (aux : Aux)
      (P : Prover oSpec Stmt Aux Out WitOut pSpec) :
      let A := AdaptiveProver.fixed stmt aux P
      Pr{let out ← V.adaptiveSoundnessExp (WitOut := WitOut) init impl A}[
        nargSoundFailEvent langIn langOut out] =
      Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
        StateT.run' (simulateQ (impl + challengeQueryImpl)
          ((Reduction.mk P V).run stmt aux).run) (← init)}[stmt ∉ langIn ∧ stmtOut ∈ langOut] := by
    dsimp only
    let fixed := AdaptiveProver.fixed stmt aux P
    let A : AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut pSpec := fixed
    let lifted : Prover (oSpec + unifSpec) Stmt Aux Out WitOut pSpec :=
      mapProverOracles (fun q => query (spec := oSpec + unifSpec) (.inl q)) P
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
    change Pr{let out ← V.adaptiveSoundnessExp init impl A}[
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

variable {ι σ Stmt Proof Out : Type} {oSpec : OracleSpec ι}
  [Inhabited Out]
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The one-message interactive game on an embedded NARG adversary is the NARG experiment. -/
theorem adaptiveSoundnessExp_ofNARG
    (P : OracleComp (oSpec + unifSpec) (Stmt × Proof)) :
    V.adaptiveSoundnessExp init impl (AdaptiveProver.ofNARG P) =
      adaptiveNARGSoundnessExp init impl V P := by
  simp only [adaptiveSoundnessExp, adaptiveNARGSoundnessExp, AdaptiveGame.run,
    AdaptiveProver.run_ofNARG, liftCompLeft, bind_map_left, simulateQ_bind, simulateQ_pure]
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self]
  simp only [QueryImpl.simulateQ_add_liftComp_left]

end Verifier

namespace Verifier

variable {ι σ Stmt Out Wit WitOut : Type} {oSpec : OracleSpec ι}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (V : Verifier oSpec Stmt Out pSpec)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Embed a public-oracle extractor into the combined legacy interface, exposing only public
queries from the legacy logs. -/
def _root_.Extractor.Straightline.forCombinedOracles
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec) :
    Extractor.Straightline (oSpec + unifSpec) Stmt Wit WitOut pSpec :=
  fun x wOut tr logP logV =>
    OptionT.mk (liftCompLeft (extract x wOut tr logP.publicQueries logV.publicQueries).run)

/-- For a fixed chooser, the named adaptive extractor has exactly the same failure probability
as the ordinary straightline extractor. -/
theorem adaptiveKnowledgeSoundness_fixed_probability
    (relIn : Set (Stmt × Wit)) (relOut : Set (Out × WitOut))
    (extract : Extractor.Straightline oSpec Stmt Wit WitOut pSpec)
    {Aux : Type} (stmt : Stmt) (aux : Aux)
    (P : Prover (oSpec + unifSpec) Stmt Aux Out WitOut pSpec) :
    Pr{let out ← (V.adaptiveKnowledgeSoundnessExp init impl extract.withCoins
      (AdaptiveProver.fixed stmt aux P))}[relationKSFailEvent relIn relOut out] =
    let pImpl := impl + QueryImpl.id' unifSpec + challengeQueryImpl (pSpec := pSpec)
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk P V.liftOracles).runWithLog stmt aux
      let wit ← OptionT.lift (liftCompLeft
        (Extractor.Straightline.forCombinedOracles extract stmt witOut transcript
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
        ((V.liftOracles (targetSpec := oSpec + unifSpec)).run stmt tr)).run =
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
      Extractor.Straightline.forCombinedOracles, OptionT.run_mk, QueryLog.publicQueries,
      QueryLog.fst_inl, Extractor.Straightline.simulateQ_withCoins,
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
    V.liftOracles.knowledgeSoundnessWith init (impl + QueryImpl.id' unifSpec) relIn relOut
      (Extractor.Straightline.forCombinedOracles extract) error ↔
      V.adaptiveKnowledgeSoundnessWithExtractor init impl relIn relOut extract.withCoins
        (fun A => ∃ (Aux : Type) (stmt : Stmt) (aux : Aux)
          (P : Prover (oSpec + unifSpec) Stmt Aux Out WitOut pSpec),
          A = AdaptiveProver.fixed stmt aux P)
        error := by
  constructor
  · intro h A hA
    obtain ⟨Aux, stmt, aux, P, rfl⟩ := hA
    refine (adaptiveKnowledgeSoundness_fixed_probability V init impl relIn relOut
      extract stmt aux P).le.trans ?_
    simpa only [← monadLift_liftM_OptionT, ← liftComp_eq_liftM, liftCompLeft,
      OptionT.run_bind, OptionT.run_monadLift, OptionT.lift, OptionT.run_mk,
      monadLift_self, map_eq_pure_bind, QueryImpl.addLift_def, QueryImpl.add_lift_right,
      QueryImpl.liftTarget_self] using h Aux stmt aux P
  · intro h Aux stmt aux P
    have hBound := (adaptiveKnowledgeSoundness_fixed_probability V init impl
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
variable {ι σ Stmt Proof Out WitOut : Type} {oSpec : OracleSpec ι}
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Flattening a one-message adversary leaves the soundness experiment unchanged. -/
theorem adaptiveSoundnessExp_toNARG
    (P : AdaptiveProver (oSpec + unifSpec) Stmt Out WitOut
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    adaptiveNARGSoundnessExp init impl V P.toNARG =
      V.adaptiveSoundnessExp init impl P := by
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
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl + (QueryImpl.id' unifSpec).liftTarget _)
    (QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1))))]
  simp only [liftComp_bind, liftComp_pure]
  rw [h]
  simp only [bind_map_left, heq]
  rfl
end Verifier

namespace Verifier
variable {ι σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι} [Inhabited Out]
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Use a NARG extractor on the single proof message, ignoring the trivial output witness. -/
def _root_.Extractor.StraightlineWithCoins.ofNARG
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) Wit) :
    Extractor.StraightlineWithCoins oSpec Stmt Wit Unit
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1) :=
  fun x _ tr => E x (tr 0)

/-- The embedded NARG experiment has the same logs and extraction result, with a unit witness. -/
theorem adaptiveKnowledgeSoundnessExp_ofNARG
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) Wit)
    (P : OracleComp (oSpec + unifSpec) (Stmt × Proof)) :
    V.adaptiveKnowledgeSoundnessExp init impl
      (Extractor.StraightlineWithCoins.ofNARG E) (AdaptiveProver.ofNARG P) =
      (fun a => (a.1, a.2.1, a.2.2, ())) <$>
        adaptiveNARGKnowledgeSoundnessExp init impl V E P := by
  simp only [adaptiveKnowledgeSoundnessExp, AdaptiveProver.run_ofNARG,
    withQueryLog_map, withQueryLog_liftComp_left, AdaptiveGame.runWithExtractor,
    AdaptiveGame.execute, adaptiveNARGKnowledgeSoundnessExp,
    map_bind, bind_map_left, simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc,
    Functor.map_map, StateT.run'_bind', StateT.run'_pure']
  simp only [QueryImpl.addLift_def, QueryImpl.add_lift_right, QueryImpl.liftTarget_self,
    QueryImpl.simulateQ_add_liftComp_left,
    Extractor.StraightlineWithCoins.ofNARG, QueryLog.fst_inl, Fin.cons_zero, Verifier.run]
  simp [runVerifierWithLog, liftCompLeft, QueryImpl.simulateQ_add_liftM_left,
    QueryLog.publicQueries]
end Verifier

namespace Verifier
variable {ι σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι}
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Flattening preserves the one-message knowledge experiment for the supplied extractor. -/
theorem adaptiveKnowledgeSoundnessExp_toNARG
    (E : Stmt → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp (oSpec + unifSpec)) Wit)
    (P : AdaptiveProver (oSpec + unifSpec) Stmt Out Unit
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)) :
    V.adaptiveKnowledgeSoundnessExp init impl
      (Extractor.StraightlineWithCoins.ofNARG E) P =
      (fun a => (a.1, a.2.1, a.2.2, ())) <$>
        adaptiveNARGKnowledgeSoundnessExp init impl V E P.toNARG := by
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
  rw [← QueryImpl.simulateQ_add_liftComp_left (impl + (QueryImpl.id' unifSpec).liftTarget _)
    (QueryImpl.liftTarget (StateT σ ProbComp) (challengeQueryImpl (pSpec :=
      (⟨!v[.P_to_V], !v[Proof]⟩ : ProtocolSpec 1)))) P.toNARG.withQueryLog]
  rw [AdaptiveProver.lift_toNARG_withQueryLog]
  simp [simulateQ_map, bind_map_left, runVerifierWithLog, liftCompLeft, heq,
    Extractor.StraightlineWithCoins.ofNARG,
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

/-! ## NARG security

Adaptive NARG soundness and knowledge soundness are the adaptive interactive predicates at the
one-message protocol `⟨!v[.P_to_V], !v[Proof]⟩`. The theorems `adaptiveNARGSoundness_iff` and
the others restate each predicate in the form of [CO25, Definitions 3.5 and 3.6]: the adversary
outputs a statement and a NARG string `(x, π)`, and the bound is on `adaptiveNARGSoundnessExp`
or `adaptiveNARGKnowledgeSoundnessExp`.

There are no separate definitions for families over a security parameter `λ` and an instance
bound `n`. A theorem quantifies over `λ`, `n`, and the query budget itself, and a statement-size
bound belongs in the failure event (see `nargSoundFailEvent`). -/

namespace Verifier
variable {ι σ Stmt Proof Out Wit : Type} {oSpec : OracleSpec ι}
  (V : NonInteractiveVerifier Proof oSpec Stmt Out)
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- **[CO25, Definition 3.5, adapted]** Adaptive NARG soundness against every adversary, with
private coins available. It is adaptive soundness of the one-message protocol;
`adaptiveNARGSoundness_iff` states it on `adaptiveNARGSoundnessExp`. -/
abbrev adaptiveNARGSoundness (langIn : Set Stmt) (langOut : Set Out) (error : ENNReal) : Prop :=
  V.adaptiveSoundness init impl langIn langOut (fun _ _ => True) error

/-- **[CO25, Definition 3.5]** Adaptive NARG soundness for a public-query selector and budget.
The budget excludes private draws; it does not truncate the experiment.
`adaptiveNARGSoundnessQueryBounded_iff` states it on `adaptiveNARGSoundnessExp`. -/
abbrev adaptiveNARGSoundnessQueryBounded (langIn : Set Stmt) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveSoundnessQueryBounded init impl langIn langOut counts t error

/-- **[CO25, Definition 3.6, adapted]** Adaptive NARG knowledge soundness for a named
straight-line extractor, without a query budget. The extractor runs after the verifier in the
same public-oracle state and receives both public logs, excluding private draws. -/
abbrev adaptiveNARGKnowledgeSoundnessWithExtractor
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (E : NARG.Extractor oSpec Stmt Wit Proof)
    (error : ENNReal) : Prop :=
  V.adaptiveKnowledgeSoundnessWithExtractor init impl relIn (langOut ×ˢ Set.univ)
    (Extractor.StraightlineWithCoins.ofNARG E) (fun _ => True) error

/-- **[CO25, Definition 3.6, adapted]** Adaptive NARG knowledge soundness for a named
straight-line extractor and a public-query budget. -/
abbrev adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (E : NARG.Extractor oSpec Stmt Wit Proof)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) : Prop :=
  V.adaptiveKnowledgeSoundnessQueryBoundedWithExtractor init impl relIn (langOut ×ˢ Set.univ)
    (Extractor.StraightlineWithCoins.ofNARG E) counts t error

/-- Adaptive knowledge soundness with one extractor for all provers.
The existential quantifier imposes no computability or resource bound. A classical witness
selector can ignore the logs and return a witness for any true statement. See
`Verifier.knowledgeSoundness_iff_relationSoundness` for the analogous equivalence for the
fixed-statement interactive game. -/
def adaptiveNARGKnowledgeSoundness
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (error : ENNReal) : Prop :=
  ∃ E, V.adaptiveNARGKnowledgeSoundnessWithExtractor init impl relIn langOut E error

/-- One straight-line extractor for all public-query budgets. The extractor is chosen before
both the budget and the prover. As in `adaptiveNARGKnowledgeSoundness`, the existential
extractor can select a witness by classical choice. -/
def adaptiveNARGKnowledgeSoundnessQueryBounded
    (relIn : Set (Stmt × Wit)) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (error : ℕ → ENNReal) : Prop :=
  ∃ E, ∀ t, V.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init impl
    relIn langOut E counts t (error t)

/-- With no output statement, the verifier never accepts, so false acceptance has
probability zero. -/
private theorem prEvent_nargSoundFailEvent_of_isEmpty [IsEmpty Out]
    (langIn : Set Stmt) (langOut : Set Out) (P : NARG.Prover oSpec Stmt Proof) :
    Pr{let out ← adaptiveNARGSoundnessExp init impl V P}[
      nargSoundFailEvent langIn langOut out] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ <| by
    rintro (_ | ⟨_, y⟩) _ h
    · exact h
    · exact isEmptyElim y

/-- With no output statement, the verifier never accepts, so extraction failure has
probability zero. -/
private theorem prEvent_nargKSFailEvent_of_isEmpty [IsEmpty Out]
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (E : NARG.Extractor oSpec Stmt Wit Proof)
    (P : NARG.Prover oSpec Stmt Proof) :
    Pr{let out ← adaptiveNARGKnowledgeSoundnessExp init impl V E P}[
      nargKSFailEvent relIn langOut out] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ <| by
    rintro ⟨_, w, _ | y⟩ _ h
    · cases w <;> exact h
    · exact isEmptyElim y

/-- **[CO25, Definition 3.5]** Adaptive NARG soundness in the paper's form: for every adversary
that outputs a statement and a NARG string, the verifier accepts a false statement with
probability at most `error`. -/
theorem adaptiveNARGSoundness_iff (langIn : Set Stmt) (langOut : Set Out) (error : ENNReal) :
    V.adaptiveNARGSoundness init impl langIn langOut error ↔
      ∀ P : NARG.Prover oSpec Stmt Proof,
        Pr{let out ← adaptiveNARGSoundnessExp init impl V P}[
          nargSoundFailEvent langIn langOut out] ≤ error := by
  constructor
  · intro h P
    rcases isEmpty_or_nonempty Out with hOut | hOut
    · exact (prEvent_nargSoundFailEvent_of_isEmpty V init impl langIn langOut P).trans_le
        zero_le
    · have := Classical.inhabited_of_nonempty hOut
      simpa only [adaptiveSoundnessExp_ofNARG] using h Unit (AdaptiveProver.ofNARG P) True.intro
  · intro h WitOut P _
    simpa only [adaptiveSoundnessExp_toNARG] using h P.toNARG

/-- **[CO25, Definition 3.5]** Query-bounded adaptive NARG soundness in the paper's form. -/
theorem adaptiveNARGSoundnessQueryBounded_iff (langIn : Set Stmt) (langOut : Set Out)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    V.adaptiveNARGSoundnessQueryBounded init impl langIn langOut counts t error ↔
      ∀ P : NARG.Prover oSpec Stmt Proof, P.IsQueryBoundP (publicQuerySelector counts) t →
        Pr{let out ← adaptiveNARGSoundnessExp init impl V P}[
          nargSoundFailEvent langIn langOut out] ≤ error := by
  constructor
  · intro h P hP
    rcases isEmpty_or_nonempty Out with hOut | hOut
    · exact (prEvent_nargSoundFailEvent_of_isEmpty V init impl langIn langOut P).trans_le
        zero_le
    · have := Classical.inhabited_of_nonempty hOut
      simpa only [adaptiveSoundnessExp_ofNARG] using
        h Unit (AdaptiveProver.ofNARG P) (AdaptiveProver.isQueryBound_ofNARG P _ _ hP)
  · intro h WitOut P hP
    simpa only [adaptiveSoundnessExp_toNARG] using h P.toNARG (P.isQueryBound_toNARG _ _ hP)

/-- **[CO25, Definition 3.6, adapted]** Adaptive NARG knowledge soundness in the paper's form:
for every adversary that outputs a statement and a NARG string, the verifier accepts while the
named extractor fails with probability at most `error`. -/
theorem adaptiveNARGKnowledgeSoundnessWithExtractor_iff
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (E : NARG.Extractor oSpec Stmt Wit Proof)
    (error : ENNReal) :
    V.adaptiveNARGKnowledgeSoundnessWithExtractor init impl relIn langOut E error ↔
      ∀ P : NARG.Prover oSpec Stmt Proof,
        Pr{let out ← adaptiveNARGKnowledgeSoundnessExp init impl V E P}[
          nargKSFailEvent relIn langOut out] ≤ error := by
  constructor
  · intro h P
    rcases isEmpty_or_nonempty Out with hOut | hOut
    · exact (prEvent_nargKSFailEvent_of_isEmpty V init impl relIn langOut E P).trans_le
        zero_le
    · have := Classical.inhabited_of_nonempty hOut
      simpa only [adaptiveKnowledgeSoundnessExp_ofNARG, prEvent_map, relationKSFailEvent_unit]
        using h (AdaptiveProver.ofNARG P) True.intro
  · intro h P _
    simpa only [adaptiveKnowledgeSoundnessExp_toNARG, prEvent_map, relationKSFailEvent_unit]
      using h P.toNARG

/-- **[CO25, Definition 3.6]** Query-bounded adaptive NARG knowledge soundness in the paper's
form. The budget restricts the adversary, not the extractor. -/
theorem adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor_iff
    (relIn : Set (Stmt × Wit)) (langOut : Set Out) (E : NARG.Extractor oSpec Stmt Wit Proof)
    (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    V.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init impl
        relIn langOut E counts t error ↔
      ∀ P : NARG.Prover oSpec Stmt Proof, P.IsQueryBoundP (publicQuerySelector counts) t →
        Pr{let out ← adaptiveNARGKnowledgeSoundnessExp init impl V E P}[
          nargKSFailEvent relIn langOut out] ≤ error := by
  constructor
  · intro h P hP
    rcases isEmpty_or_nonempty Out with hOut | hOut
    · exact (prEvent_nargKSFailEvent_of_isEmpty V init impl relIn langOut E P).trans_le
        zero_le
    · have := Classical.inhabited_of_nonempty hOut
      simpa only [adaptiveKnowledgeSoundnessExp_ofNARG, prEvent_map, relationKSFailEvent_unit]
        using h (AdaptiveProver.ofNARG P) (AdaptiveProver.isQueryBound_ofNARG P _ _ hP)
  · intro h P hP
    simpa only [adaptiveKnowledgeSoundnessExp_toNARG, prEvent_map, relationKSFailEvent_unit]
      using h P.toNARG (P.isQueryBound_toNARG _ _ hP)

end Verifier
