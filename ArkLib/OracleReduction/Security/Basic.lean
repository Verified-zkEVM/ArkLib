/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.Execution
public import ArkLib.OracleReduction.Security.AdaptiveGame
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Security Definitions for (Oracle) Reductions

This file defines basic security notions for (oracle) reductions:

- (Perfect) Completeness

- (Straightline) (Knowledge) Soundness

- Adaptive, query-bounded NARG soundness and knowledge soundness
- Simulator types for zero-knowledge

Security notions are predicates on reductions and verifiers. Adaptive NARG notions have
unbounded and query-bounded forms. Bounded knowledge soundness fixes an extractor before
quantifying over every natural-number budget.

See other files in the same directory for more refined soundness notions (i.e. state-restoration,
round-by-round, rewinding, etc.)

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  -- Note: `σ` may depend on the previous data, like `StmtIn`, `pSpec`, and so on
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-
TODO: the "right" factoring for the security definitions are the following:

- We have a two-layer interpretation approach: first, interpret the oracle queries into some monad
  `m` with native distribution semantics; then interpret the resulting computation
  as its measure `𝒟[·]`.

  This does not preclude `m` from being the same oracle computation type, but more interesting
  possibilities are possible, such as `m = ReaderT ρ` for lazy sampling of the shared oracle.

  Another possibility: given `OracleInterface OStmt`, we have an interpretation map

  `interpOStmt : OracleComp (oSpec + [OStmt]ₒ) →ᵐ ReaderT OStmt (OracleComp oSpec)`

- Relations should be `Stmt → Wit → m Prop`, with `m` being the intermediate monad. When `m` is the
  result of `interpOStmt` above, for instance, we get `Stmt → Wit → OStmt → Prop`, which is what we
  want. Same for when we interpret `oSpec` into `Reader (QueryImpl oSpec Id)`; we then have
  `Stmt → Wit → QueryImpl oSpec Id → Prop`, which allows us to define relations that rely
  on the (randomly sampled, at the beginning) values of the shared oracle.
-/

namespace Reduction

section Completeness

/-- A reduction satisfies **completeness** with regards to:
  - an initialization function `init : ProbComp σ` for some ambient state `σ`,
  - a stateful query implementation `impl` (in terms of `StateT σ ProbComp`)
  for the shared oracles `oSpec`,
  - an input relation `relIn` and output relation `relOut` (represented as sets), and
  - an error `completenessError ≥ 0`,

  if for all valid statement-witness pair `(stmtIn, witIn) ∈ relIn`, the execution between the
  honest prover and the honest verifier will result in a tuple `((prvStmtOut, witOut), stmtOut)`
  such that

  - `(stmtOut, witOut) ∈ relOut`, (the output statement-witness pair is valid) and
  - `prvStmtOut = stmtOut`, (the output statements are the same from both prover and verifier)

  except with probability `completenessError`.
-/
def completeness (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  (stmtIn, witIn) ∈ relIn →
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl challengeQueryImpl
    Pr{let ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ ← OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)}[
        (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut] ≥ 1 - completenessError

/-- A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`. -/
def perfectCompleteness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) : Prop :=
  completeness init impl relIn relOut reduction 0

/-- Type class for completeness for a reduction -/
class IsComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    where
  completenessError : ℝ≥0
  is_complete : completeness init impl relIn relOut reduction completenessError

/-- Type class for perfect completeness for a reduction -/
class IsPerfectComplete (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  is_perfect_complete : perfectCompleteness init impl relIn relOut reduction

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}

instance [reduction.IsPerfectComplete init impl relIn relOut] :
    IsComplete init impl relIn relOut reduction where
  completenessError := 0
  is_complete := IsPerfectComplete.is_perfect_complete

/-- If a reduction satisfies completeness with error `ε₁`, then it satisfies completeness with error
  `ε₂` for all `ε₂ ≥ ε₁`. -/
@[grind]
theorem completeness_error_mono {ε₁ ε₂ : ℝ≥0} (hε : ε₁ ≤ ε₂) :
    completeness init impl relIn relOut reduction ε₁ →
      completeness init impl relIn relOut reduction ε₂ := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hstmtIn
  have := h stmtIn witIn hstmtIn
  refine ge_trans this ?_
  exact tsub_le_tsub_left (by simp [hε]) 1

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relIn'` that is a subset of `relIn`. -/
@[simp, grind]
theorem completeness_relIn_mono {ε : ℝ≥0} {relIn' : Set (StmtIn × WitIn)}
    (hrelIn : relIn' ⊆ relIn) :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn' relOut reduction ε := by
  intro h
  dsimp [completeness] at h ⊢
  intro stmtIn witIn hStmtIn
  exact h stmtIn witIn (hrelIn hStmtIn)

/-- If a reduction satisfies completeness with error `ε` for some relation `relIn`, then it
  satisfies completeness with error `ε` for any relation `relOut'` that is a superset of `relOut`.
-/
theorem completeness_relOut_mono {ε : ℝ≥0} {relOut' : Set (StmtOut × WitOut)}
    (hrelOut : relOut ⊆ relOut') :
      completeness init impl relIn relOut reduction ε →
        completeness init impl relIn relOut' reduction ε := by
  intro h stmtIn witIn hIn
  exact ge_trans (prEvent_mono _ _ _ fun _ ⟨h1, h2⟩ ↦ ⟨hrelOut h1, h2⟩) (h _ _ hIn)

/-- Perfect completeness means that the probability of the reduction outputting a valid
  statement-witness pair is _exactly_ 1 (instead of at least `1 - 0`). -/
@[simp]
theorem perfectCompleteness_eq_prob_one :
    reduction.perfectCompleteness init impl relIn relOut ↔
    ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
        QueryImpl.addLift impl challengeQueryImpl
      Pr{let ⟨⟨_, (prvStmtOut, witOut)⟩, stmtOut⟩ ← OptionT.mk do
        (simulateQ pImpl (reduction.run stmtIn witIn)).run' (← init)}[
          (stmtOut, witOut) ∈ relOut ∧ prvStmtOut = stmtOut] = 1 := by
  simp only [perfectCompleteness, completeness, ENNReal.coe_zero, tsub_zero]
  exact forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    ⟨fun h => le_antisymm (prEvent_le_one _) (ge_iff_le.mp h),
     fun h => ge_of_eq h⟩

/-- Under a stateless handler, completeness is a support property of the interpreted run.
The supplied initialization is independent and has no effect on this property. -/
theorem perfectCompleteness_stateless_iff
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {spec : OracleSpec ι}
    {Stmt Wit Out OutWit σ : Type} [∀ i, SampleableType (pSpec.Challenge i)]
    (P : Reduction spec Stmt Wit Out OutWit pSpec)
    (init : ProbComp σ) (impl : QueryImpl spec ProbComp)
    (relation : Set (Stmt × Wit)) (relOut : Set (Out × OutWit)) :
    P.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relation relOut ↔
    ∀ stmt wit, (stmt, wit) ∈ relation →
      ∀ x ∈ support (simulateQ (impl + challengeQueryImpl) (P.run stmt wit).run),
        ∃ result, x = some result ∧
          (result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2 := by
  rw [Reduction.perfectCompleteness_eq_prob_one]
  have hi : QueryImpl.addLift (impl.liftTarget (StateT σ ProbComp))
      (challengeQueryImpl (pSpec := pSpec)) =
      (impl + challengeQueryImpl).liftTarget (StateT σ ProbComp) := by
    funext q
    cases q <;> rfl
  simp only [hi, simulateQ_liftTarget, StateT.run'_eq, StateT.run_monadLift,
    map_bind, map_pure, monadLift_self, bind_pure, OptionT.prEvent_mk_eq_one_iff,
    mem_support_bind_iff]
  constructor
  · intro h stmt wit hrel x hx
    obtain ⟨s, hs⟩ := support_nonempty init
    exact h stmt wit hrel x ⟨s, hs, hx⟩
  · intro h stmt wit hrel x hx
    obtain ⟨s, _hs, hx⟩ := hx
    exact h stmt wit hrel x hx

/-- **Support criterion for perfect completeness.** A reduction is perfectly complete as soon as
every element of the support of the *unsimulated* execution `(reduction.run stmtIn witIn).run` is
a successful result satisfying the completeness event.

This is the standard route to `perfectCompleteness` for protocols whose honest execution is
deterministic in the verifier messages: it discharges the probabilistic content once and for all,
leaving a purely support-level obligation about `Reduction.run`. No property of the verifier message
distribution is needed — only that `oSpec`'s queries are answered by `impl` and the initial state
is drawn from `init`, both of which the underlying VCVio lemma
`OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support` handles uniformly.

The triple to supply for each `x` in the support is: a result `result` with `x = some result`
(execution never fails), `(result.2, result.1.2.2) ∈ relOut` (the verifier's output statement
paired with the prover's output witness lies in the output relation), and
`result.1.2.1 = result.2` (the prover's and the verifier's output statements agree). -/
theorem perfectCompleteness_of_run_support
    (h : ∀ stmtIn witIn, (stmtIn, witIn) ∈ relIn →
      ∀ x ∈ support (reduction.run stmtIn witIn).run,
        ∃ result, x = some result ∧
          (result.2, result.1.2.2) ∈ relOut ∧ result.1.2.1 = result.2) :
    reduction.perfectCompleteness init impl relIn relOut := by
  rw [perfectCompleteness_eq_prob_one]
  intro stmtIn witIn hIn
  exact OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support init _ _ _
    (fun x hx => by
      obtain ⟨⟨⟨tr, prvStmtOut, witOut⟩, stmtOut⟩, hx, hrel, hstmt⟩ := h stmtIn witIn hIn x hx
      exact ⟨⟨⟨tr, prvStmtOut, witOut⟩, stmtOut⟩, hx, hrel, hstmt⟩)

end Completeness

end Reduction

section Soundness

/-! We define 3 variants each of soundness and knowledge soundness:

  1. (Plain) soundness
  2. Knowledge soundness

  These definitions fix the input statement before initializing the shared oracle. The adaptive
  interactive definitions in `Security/Adaptive.lean` allow an oracle-aided chooser.

  Note: all soundness definitions are really defined for the **verifier** only. The (honest)
prover does not feature into the definitions.
-/

namespace Extractor

/- We define different types of extractors here -/

variable (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)

/-- A straightline extractor takes in the input statement, the output witness, the IOR transcript,
  and the query logs from the prover and verifier, and returns a corresponding input witness.

  It runs once, after the execution, without rewinding the prover. It may query the shared oracles
  `oSpec` and may fail. The type bounds neither its running time nor its computability: a
  noncomputable function that picks a witness by classical choice is an extractor. A cost bound is
  a separate statement about a named extractor (see `Verifier.knowledgeSoundnessWith`).

  The extractor does not need the output statement, since re-running the verifier on the input
  statement, the transcript, and the verifier's query log recovers it.

  This form of extractor suffices for proving knowledge soundness of most hash-based IOPs.
-/
def Straightline :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- reduction transcript
  QueryLog oSpec → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp oSpec) WitIn -- input witness

end Extractor

namespace Verifier

/-- A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input
  language `langIn : Set StmtIn` and output language `langOut : Set StmtOut` if:
  - for all (malicious) provers with arbitrary types for `WitIn`, `WitOut`,
  - for all arbitrary `witIn`,
  - for all input statement `stmtIn ∉ langIn`,

  the execution between the prover and the honest verifier will result in an output statement
  `stmtOut` that is in `langOut` is at most `soundnessError`.

  (technical note: since execution may fail, this is _not_ equivalent to saying that
  `stmtOut ∉ langOut` with probability at least `1 - soundnessError`)
-/
def soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ stmtIn ∉ langIn,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    letI reduction := Reduction.mk prover verifier
    Pr{let ⟨_, stmtOut⟩ ← OptionT.mk do
      (simulateQ pImpl (reduction.run stmtIn witIn).run).run' (← init)}[
        stmtOut ∈ langOut] ≤ soundnessError

/-- Type class for soundness for a verifier -/
class IsSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  soundnessError : ℝ≥0
  is_sound : soundness init impl langIn langOut verifier soundnessError

-- How would one define a rewinding extractor? It should have oracle access to the prover's
-- functions (receive verifier messages and send messages), and be able to observe & simulate the
-- prover's oracle queries
/-- The straightline knowledge-soundness game for one specified extractor.

Unlike `knowledgeSoundness`, this predicate keeps the extractor's identity in its type. This is
the appropriate public contract when a caller needs to name, execute, or audit the exact
extractor certified by a theorem. The extractor is fixed before the arbitrary malicious prover,
which has its own private input of any type.

The predicate bounds only the error. Knowledge soundness in the cryptographic sense also needs a
bound on the cost of this extractor, stated separately for the same named extractor. -/
def knowledgeSoundnessWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  ∀ Aux : Type,
  ∀ stmtIn : StmtIn,
  ∀ aux : Aux,
  ∀ prover : Prover oSpec StmtIn Aux StmtOut WitOut pSpec,
    let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let exec := do
      let ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩
        ← (Reduction.mk prover verifier).runWithLog stmtIn aux
      let extractedWitIn? ←
        liftM (extractor stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run
      return (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr{let ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ ← OptionT.mk do
      (simulateQ pImpl exec.run).run' (← init)}[
        (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧
          (stmtOut, witOut) ∈ relOut] ≤ knowledgeError

/-- A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and
  with respect to input relation `relIn` and output relation `relOut` if:
  - there exists a straightline extractor `E`, such that
  - for every private input type `Aux`, input statement `stmtIn`, private input `aux : Aux`,
    and arbitrary malicious prover `prover` with that input type, chosen after the extractor,
  - if the execution with the honest verifier results in a pair `(stmtOut, witOut)`,

  then the probability that `(stmtOut, witOut)` is valid and yet the extractor fails to produce
  a witness `witIn'` such that `(stmtIn, witIn')` is valid is at most `knowledgeError`.

  Implementation note: the extractor returns an `OptionT` computation, so it may fail. We run
  this `OptionT` layer explicitly (via `.run`) and keep the resulting `Option WitIn` in the
  game's output, so that extractor failure counts as a "bad" event (the adversary wins).

  This is essential for the definition to be meaningful: if instead the extractor were bound
  inside the surrounding `OptionT` computation, its failure would contribute to the failure
  mass of the whole game, which `Pr{…}[…]` excludes (it only measures `some` outputs). The
  always-failing extractor `fun _ _ _ _ _ => failure` would then drive the game's event
  probability to `0`, vacuously discharging knowledge soundness (at error `0`!) for any
  verifier and any relations.

  In contrast, failures of the reduction execution itself (e.g. the verifier aborting) are
  still excluded from the event, matching the convention for (plain) soundness: a run in which
  the verifier does not accept imposes no obligation on the extractor.

  The extractor is unconstrained, so this contract carries no efficiency content. The classical
  witness selector `Extractor.Straightline.choose` makes it equivalent to
  `Verifier.relationSoundness` (`Verifier.knowledgeSoundness_iff_relationSoundness`). Extraction in
  the cryptographic sense needs a named extractor and a bound on its complete execution.
  `knowledgeSoundnessWith` fixes the extractor. `knowledgeSoundnessWithResources` in
  `Security/Resources.lean` additionally bounds the declared instruction counts of a measured
  program returning the same value, which does not bound the extractor's complete execution.
-/
def knowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
    verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError

/-- Existential knowledge soundness is exactly the existence of an extractor satisfying
`knowledgeSoundnessWith`. -/
theorem knowledgeSoundness_iff_exists_with
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError ↔
      ∃ extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec,
        verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError :=
  Iff.rfl

/-- Forget the identity of a specified extractor to obtain the existing existential contract. -/
theorem knowledgeSoundness_of_with
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {extractor : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec}
    {knowledgeError : ℝ≥0}
    (h : verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  (knowledgeSoundness_iff_exists_with init impl relIn relOut verifier knowledgeError).mpr
    ⟨extractor, h⟩

/-- Increasing the allowed error preserves knowledge soundness. -/
theorem knowledgeSoundness_error_mono
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {ε ε' : ℝ≥0}
    (hε : ε ≤ ε') (h : verifier.knowledgeSoundness init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut ε' := by
  obtain ⟨extractor, h⟩ := h
  refine ⟨extractor, fun Aux stmt aux prover => ?_⟩
  exact (h Aux stmt aux prover).trans (by exact_mod_cast hε)

/-- Type class for knowledge soundness for a verifier. Like `knowledgeSoundness`, it bounds no
extractor cost. -/
class IsKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  knowledgeError : ℝ≥0
  is_knowledge_sound : knowledgeSoundness init impl relIn relOut verifier knowledgeError

/-- An extractor is **monotone** if its success probability on a given query log is the same as
  the success probability on any extension of that query log. -/
class Extractor.Straightline.IsMonotone
    (relIn : Set (StmtIn × WitIn))
    (E : Extractor.Straightline oSpec StmtIn WitIn WitOut pSpec)
    [oSpec.UniformAnswerMeasure]
    where
  is_monotone : ∀ witOut stmtIn transcript, ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder probability for now, probably need to consider the whole game
    Pr{let witIn ← E stmtIn witOut transcript proveQueryLog₁ verifyQueryLog₁}[
      (stmtIn, witIn) ∈ relIn] ≤
    Pr{let witIn ← E stmtIn witOut transcript proveQueryLog₂ verifyQueryLog₂}[
      (stmtIn, witIn) ∈ relIn]

end Verifier

/-! ## Adaptive NARG security

The prover chooses a statement and NARG string, using public oracles and private randomness.
Each notion has one experiment. Unbounded and query-bounded predicates differ only in which
provers they quantify over; private draws are excluded from public-query budgets.

The KS extractor receives the statement, NARG string, and both public-query logs. Its
`extractorSpec` and handler specify its oracle permissions independently of the prover's
private sampler. A lifted `ProbComp` handler gives standalone extraction; an explicitly shared
handler can provide public-oracle access in the state left by verification. Neither the
extractor nor its handler receives a prover handle. No running-time bound is imposed here.
-/
section AdaptiveNARG

/-- **[CO25, Definition 3.5]** False-acceptance event on the NARG soundness experiment output
`Option (StmtIn × StmtOut)`: the prover output a false statement (`x ∉ langIn`) the verifier
accepted into `stmtOut ∈ langOut`. The unbounded and query-bounded predicates use the
same event. -/
def nargSoundFailEvent {StmtIn StmtOut : Type} (langIn : Set StmtIn) (langOut : Set StmtOut) :
    Option (StmtIn × StmtOut) → Prop
  | some (x, stmtOut) => x ∉ langIn ∧ stmtOut ∈ langOut
  | none => False

/-- Run a non-interactive verifier and record its base-oracle queries, including on rejection. -/
abbrev runVerifierWithLog {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn Proof StmtOut : Type}
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (x : StmtIn) (π : Proof) : OracleComp oSpec (Option StmtOut × QueryLog oSpec) :=
  withQueryLog (verifier.verify x (Fin.cons π (fun i => i.elim0))).run

/-- **[CO25, Definition 3.6]** Extraction-failure event on the NARG-KS experiment output
`StmtIn × Option WitIn × Option StmtOut`: the verifier accepted into `langOut` yet the extracted
input witness misses `relIn` (or none was produced). No output witness is supplied by the malicious
NARG prover: Definition 3.6 quantifies over the same adversaries producing only a statement and
NARG string `(x, π)` as Definition 3.5. -/
def nargKSFailEvent {StmtIn WitIn StmtOut : Type}
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut) :
    StmtIn × Option WitIn × Option StmtOut → Prop
  | (x, some witIn, some stmtOut) => stmtOut ∈ langOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut) => stmtOut ∈ langOut
  | _ => False

/-- Extraction-failure event for ArkLib's relation-valued reduction and state-restoration
interfaces. Unlike the paper's NARG event, these interfaces genuinely carry an output witness. -/
def relationKSFailEvent {StmtIn WitIn StmtOut WitOut : Type}
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut)) :
    StmtIn × Option WitIn × Option StmtOut × WitOut → Prop
  | (x, some witIn, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut ∧ (x, witIn) ∉ relIn
  | (_, none, some stmtOut, witOut) => (stmtOut, witOut) ∈ relOut
  | _ => False

/-- **[CO25, Definition 3.5]** Run the adaptive prover and verifier in one public-oracle state.
The private sampler serves only the prover. An absent verifier output produces `none`. The sampler
parameter supports internal reductions; the security predicates use standard `unifSpec`. -/
def adaptiveNARGSoundnessExp
    {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    ProbComp (Option (StmtIn × StmtOut)) :=
  AdaptiveGame.run init (impl.addLift privateImpl) P
    (fun a => liftComp (verifier.verify a.1 (Fin.cons a.2 (fun i => i.elim0))).run _)
    (fun a out => out.map (a.1, ·))

/-- The adaptive NARG soundness experiment in its optional-computation form. -/
theorem adaptiveNARGSoundnessExp_eq_option
    {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {σ StmtIn Proof StmtOut : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGSoundnessExp init impl privateImpl verifier P = (do
  (simulateQ (impl.addLift privateImpl : QueryImpl _ (StateT σ ProbComp)) (do
    let ⟨x, π⟩ ← P
    let stmtOut ← OptionT.mk (liftComp (verifier.verify x
      (Fin.cons π (fun i => i.elim0))).run (oSpec + privateSpec))
    return (x, stmtOut) : OptionT (OracleComp (oSpec + privateSpec))
      (StmtIn × StmtOut))).run' (← init)) := by
  exact AdaptiveGame.run_eq_runOption init (impl.addLift privateImpl) P
    (fun a => OptionT.mk (liftComp (verifier.verify a.1
      (Fin.cons a.2 (fun i => i.elim0))).run (oSpec + privateSpec)))
    (fun a out => (a.1, out))

/-- **[CO25, Definition 3.6, adapted]** Run the prover, verifier, and non-rewinding extractor.
The extractor receives separate public-query logs; private prover samples are excluded.
`extractorImpl` explicitly controls whether extraction can use the public-oracle state.
It does not receive the prover or its private samples. Extractor failure is retained as `none`. -/
def adaptiveNARGKnowledgeSoundnessExp
    {ι κ κE : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {extractorSpec : OracleSpec κE} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut) :=
  AdaptiveGame.runWithExtractor init (impl.addLift privateImpl) extractorImpl P.withQueryLog
    (fun a => liftComp (runVerifierWithLog verifier a.1.1 a.1.2) _)
    (fun a v => extractor a.1.1 a.1.2 a.2.publicQueries v.2)
    (fun a v wit => (a.1.1, wit, v.1))

/-- The adaptive NARG knowledge experiment in its logged prover/verifier form. -/
theorem adaptiveNARGKnowledgeSoundnessExp_eq
    {ι κ κE : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
    {extractorSpec : OracleSpec κE} {σ StmtIn Proof StmtOut WitIn : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (privateImpl : QueryImpl privateSpec ProbComp)
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (P : OracleComp (oSpec + privateSpec) (StmtIn × Proof)) :
    adaptiveNARGKnowledgeSoundnessExp init impl privateImpl extractorImpl verifier extractor P = (do
  StateT.run' (do
    let ⟨x, π, proverLog, stmtOut, trV⟩ ←
      simulateQ (impl.addLift privateImpl) (do
        let ⟨⟨x, π⟩, proverLog⟩ ← P.withQueryLog
        let ⟨stmtOut, trV⟩ ← liftComp (runVerifierWithLog verifier x π) _
        return (x, π, proverLog, stmtOut, trV))
    let trP := proverLog.publicQueries
    let witIn ← simulateQ extractorImpl (extractor x π trP trV).run
    return (x, witIn, stmtOut)) (← init)) := by
  simp only [adaptiveNARGKnowledgeSoundnessExp, AdaptiveGame.runWithExtractor,
    AdaptiveGame.execute, simulateQ_bind, simulateQ_pure, pure_bind, bind_assoc]

namespace Verifier

variable {ι κE : Type} {oSpec : OracleSpec ι} {extractorSpec : OracleSpec κE}
  {σ StmtIn Proof StmtOut WitIn : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
  (verifier : NonInteractiveVerifier Proof oSpec StmtIn StmtOut)

/-- **[CO25, Definition 3.5, adapted]** Adaptive soundness against every prover, with private
sampling available. The error is independent of any query budget. -/
def adaptiveNARGSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (error : ENNReal) : Prop :=
  ∀ P : OracleComp (oSpec + unifSpec) (StmtIn × Proof),
    Pr{let out ← adaptiveNARGSoundnessExp init impl (QueryImpl.id' unifSpec) verifier P}[
      nargSoundFailEvent langIn langOut out] ≤ error

/-- **[CO25, Definition 3.5]** Adaptive soundness for a public-query selector and budget.
The predicate excludes private draws from the budget; it does not truncate the experiment. -/
def adaptiveNARGSoundnessQueryBounded (langIn : Set StmtIn) (langOut : Set StmtOut)
    (queryBoundSelector : ι → Prop) [DecidablePred queryBoundSelector]
    (t : ℕ) (error : ENNReal) : Prop :=
  ∀ P : OracleComp (oSpec + unifSpec) (StmtIn × Proof),
    P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t →
      Pr{let out ← adaptiveNARGSoundnessExp init impl (QueryImpl.id' unifSpec) verifier P}[
        nargSoundFailEvent langIn langOut out] ≤ error

/-- Adaptive knowledge soundness for a supplied extractor, without a prover-query bound. -/
def adaptiveNARGKnowledgeSoundnessWithExtractor
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn) (error : ENNReal) : Prop :=
  ∀ P : OracleComp (oSpec + unifSpec) (StmtIn × Proof),
    Pr{let out ← adaptiveNARGKnowledgeSoundnessExp init impl (QueryImpl.id' unifSpec)
          extractorImpl verifier extractor P}[nargKSFailEvent relIn langOut out] ≤ error

/-- Adaptive knowledge soundness with one extractor for all provers. Extractor oracle permissions
are supplied through `extractorImpl`; private prover sampling does not grant additional access.
The existential quantifier imposes no computability or resource bound. A classical witness
selector can ignore the logs and return a witness for any true statement. See
`Verifier.knowledgeSoundness_iff_relationSoundness` for the analogous equivalence for the
fixed-statement interactive game. -/
def adaptiveNARGKnowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut) (error : ENNReal) : Prop :=
  ∃ extractor, adaptiveNARGKnowledgeSoundnessWithExtractor init impl extractorImpl verifier
    relIn langOut extractor error

/-- **[CO25, Definition 3.6, adapted]** Knowledge soundness for a supplied non-rewinding extractor
and a public-query budget. The extractor receives both public logs, excluding private draws. -/
def adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (extractor : StmtIn → Proof → QueryLog oSpec → QueryLog oSpec →
      OptionT (OracleComp extractorSpec) WitIn)
    (queryBoundSelector : ι → Prop) [DecidablePred queryBoundSelector]
    (t : ℕ) (error : ENNReal) : Prop :=
  ∀ P : OracleComp (oSpec + unifSpec) (StmtIn × Proof),
    P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t →
      Pr{let out ← adaptiveNARGKnowledgeSoundnessExp init impl (QueryImpl.id' unifSpec)
            extractorImpl verifier extractor P}[nargKSFailEvent relIn langOut out] ≤ error

/-- One non-rewinding extractor for all public-query budgets. The extractor is chosen before
both the budget and the prover; private sampling is available in every execution.
The budgets restrict the prover. As in `adaptiveNARGKnowledgeSoundness`, the existential
extractor can select a witness by classical choice. -/
def adaptiveNARGKnowledgeSoundnessQueryBounded
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (queryBoundSelector : ι → Prop) [DecidablePred queryBoundSelector]
    (error : ℕ → ENNReal) : Prop :=
  ∃ extractor, ∀ t, adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor
    init impl extractorImpl verifier relIn langOut extractor queryBoundSelector t (error t)

end Verifier
end AdaptiveNARG

end Soundness

namespace Reduction

section ZeroKnowledge

/-- A simulator for a reduction needs to produce the same transcript as the prover (but potentially
  all at once, instead of sequentially). We also grant the simulator the power to program the shared
  oracles `oSpec` -/
structure Simulator (oSpec : OracleSpec ι) (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  SimState : Type
  oracleSim : QueryImpl oSpec (StateT SimState (OracleComp oSpec))
  proverSim : StmtIn → StateT SimState (OracleComp oSpec) pSpec.FullTranscript

/- Public-coin honest-verifier and adaptive NARG zero-knowledge are defined in
`ArkLib.OracleReduction.Security.ZeroKnowledge`. -/

end ZeroKnowledge

end Reduction

/-! Completeness and soundness are the same as for non-oracle reductions. Only zero-knowledge is
  different (but we haven't defined it yet) -/

open Reduction

section OracleProtocol

variable [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleReduction

open Classical in
/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
def completeness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
    (completenessError : ℝ≥0) : Prop :=
  Reduction.completeness init impl relIn relOut oracleReduction.toReduction completenessError

open Classical in
/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
def perfectCompleteness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (oracleReduction : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) :
      Prop :=
  Reduction.perfectCompleteness init impl relIn relOut oracleReduction.toReduction

end OracleReduction

namespace OracleVerifier

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
def soundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.toVerifier.soundness init impl langIn langOut soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
def knowledgeSoundnessWith
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (extractor : Extractor.Straightline oSpec
      (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundnessWith
    init impl relIn relOut extractor knowledgeError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
def knowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.toVerifier.knowledgeSoundness init impl relIn relOut knowledgeError

/-- Forget a specified oracle-reduction extractor to obtain existential knowledge soundness. -/
theorem knowledgeSoundness_of_with
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {extractor : Extractor.Straightline oSpec
      (StmtIn × ∀ i, OStmtIn i) WitIn WitOut pSpec}
    {knowledgeError : ℝ≥0}
    (h : verifier.knowledgeSoundnessWith init impl relIn relOut extractor knowledgeError) :
    verifier.knowledgeSoundness init impl relIn relOut knowledgeError :=
  Verifier.knowledgeSoundness_of_with init impl h

/-- Increasing the allowed error preserves oracle knowledge soundness. -/
theorem knowledgeSoundness_error_mono
    {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
    {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}
    {verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec}
    {ε ε' : ℝ≥0} (hε : ε ≤ ε')
    (h : verifier.knowledgeSoundness init impl relIn relOut ε) :
    verifier.knowledgeSoundness init impl relIn relOut ε' :=
  Verifier.knowledgeSoundness_error_mono init impl hε h

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)] {Witness : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

/-! All security notions are inherited from `Reduction`, with the output relation specialized to the
  trivial accept/reject one: `fun accRej _ => accRej`. -/

open Reduction

@[reducible, simp]
def completeness (relation : Set (Statement × Witness)) (completenessError : ℝ≥0)
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.completeness init impl relation acceptRejectRel proof completenessError

@[reducible, simp]
def perfectCompleteness (relation : Set (Statement × Witness))
    (proof : Proof oSpec Statement Witness pSpec) : Prop :=
  Reduction.perfectCompleteness init impl relation acceptRejectRel proof

@[reducible, simp]
def soundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (soundnessError : ℝ≥0) : Prop :=
  verifier.soundness init impl langIn acceptRejectRel.language soundnessError

@[reducible, simp]
def knowledgeSoundness (relation : Set (Statement × Witness))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (knowledgeError : ℝ≥0) : Prop :=
  verifier.knowledgeSoundness init impl relation acceptRejectRel knowledgeError

/-- Under a stateless handler, completeness is a support property of the interpreted run.
The supplied initialization is independent and has no effect on this property. -/
theorem perfectCompleteness_stateless_iff
    {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {spec : OracleSpec ι}
    {Stmt Wit σ : Type} [∀ i, SampleableType (pSpec.Challenge i)]
    (P : Proof spec Stmt Wit pSpec) (init : ProbComp σ) (impl : QueryImpl spec ProbComp)
    (relation : Set (Stmt × Wit)) :
    P.perfectCompleteness init (impl.liftTarget (StateT σ ProbComp)) relation ↔
    ∀ stmt wit, (stmt, wit) ∈ relation →
      ∀ x ∈ support (simulateQ (impl + challengeQueryImpl) (P.run stmt wit).run),
        ∃ result, x = some result ∧
          (result.2, result.1.2.2) ∈ acceptRejectRel ∧ result.1.2.1 = result.2 :=
  Reduction.perfectCompleteness_stateless_iff P init impl relation acceptRejectRel

end Proof

namespace OracleProof

open OracleReduction

/-- Completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def completeness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec)
    (completenessError : ℝ≥0) : Prop := by
  exact OracleReduction.completeness (Oₛₒ := fun i => nomatch i) init impl
    relation acceptRejectOracleRel oracleProof completenessError

/-- Perfect completeness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def perfectCompleteness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (oracleProof : OracleProof oSpec Statement OStatement Witness pSpec) :
      Prop := by
  exact OracleReduction.perfectCompleteness (Oₛₒ := fun i => nomatch i)
    init impl relation acceptRejectOracleRel oracleProof

/-- Soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def soundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (soundnessError : ℝ≥0) : Prop := by
  exact (OracleVerifier.toVerifier (Oₛₒ := fun i => nomatch i) verifier).soundness init impl
    langIn acceptRejectOracleRel.language soundnessError

/-- Knowledge soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def knowledgeSoundness
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (knowledgeError : ℝ≥0) : Prop := by
  exact (OracleVerifier.toVerifier
    (Oₛₒ := fun i => nomatch i) verifier).knowledgeSoundness
      init impl relation acceptRejectOracleRel knowledgeError

end OracleProof

section Trivial

-- We show that the trivial (oracle) reduction is perfectly complete, sound, and knowledge sound.

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem Reduction.id_perfectCompleteness {rel : Set (StmtIn × WitIn)} :
    (Reduction.id : Reduction oSpec _ _ _ _ _).perfectCompleteness init impl rel rel := by
  apply perfectCompleteness_of_run_support init impl
  intro stmtIn witIn hIn x hx
  simp only [Reduction.id_run, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hx
  subst x
  exact ⟨((default, stmtIn, witIn), stmtIn), rfl, hIn, rfl⟩

private lemma Reduction.run_mk_verifier_id {WitIn WitOut : Type}
    (prover : Prover oSpec StmtIn WitIn StmtIn WitOut !p[])
    (stmtIn : StmtIn) (witIn : WitIn) :
    (Reduction.mk prover Verifier.id).run stmtIn witIn =
      (fun pr => (pr, stmtIn)) <$> prover.run stmtIn witIn := by
  simp only [Reduction.run, Verifier.run, Verifier.id, OptionT.run_pure,
    monadLift_bind, Function.comp_apply, monadLift_pure,
    pure_bind, Option.getM, map_eq_bind_pure_comp]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp]
theorem Verifier.id_soundness {lang : Set StmtIn} :
    (Verifier.id : Verifier oSpec _ _ _).soundness init impl lang lang 0 := by
  unfold soundness
  intro WitIn WitOut witIn prover stmtIn hstmtIn
  simp only [ENNReal.coe_zero, nonpos_iff_eq_zero, Reduction.run_mk_verifier_id,
    OptionT.prEvent_mk_eq_zero_iff]
  intro x hx hev
  apply hstmtIn
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
  obtain ⟨⟨a, s'⟩, ha, rfl⟩ := hx
  have hliftM : (liftM ((fun pr => (pr, stmtIn)) <$> Prover.run stmtIn witIn prover) :
      OptionT (OracleComp _) _).run =
      (fun pr => some (pr, stmtIn)) <$> Prover.run stmtIn witIn prover := by
    simp [Functor.map_map]
  rw [hliftM, simulateQ_map, StateT.run_map] at ha
  simp only [support_map, Set.mem_image, Prod.exists] at ha
  obtain ⟨pr, s'', ⟨b, _, _, heq⟩⟩ := ha
  -- `heq` identifies the sampled output with `(some (pr, stmtIn), _)`; peel it apart to read off
  -- that the output statement is literally `stmtIn`, contradicting `stmtIn ∉ lang` via `hev`.
  have hOption := (Prod.mk.inj heq).1
  have hPair := Option.some.inj hOption
  have hStmtOut := (Prod.mk.inj hPair).2
  rw [← hStmtOut] at hev
  exact hev

/-- The straightline extractor for the identity / trivial reduction, which just returns the input
  witness. -/
@[reducible]
def Extractor.Straightline.id : Extractor.Straightline oSpec StmtIn WitIn WitIn !p[] :=
  fun _ witOut _ _ _ => pure witOut

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp]
theorem Verifier.id_knowledgeSoundness {rel : Set (StmtIn × WitIn)} :
    (Verifier.id : Verifier oSpec _ _ _).knowledgeSoundness init impl rel rel 0 := by
  -- `Extractor.Straightline.id` returns the (adversarial) output witness. On the support of the
  -- game, the identity verifier outputs the input statement, so the bad event requires both
  -- `(stmtIn, witOut) ∉ rel` (extracted witness invalid) and `(stmtIn, witOut) ∈ rel`
  -- (output pair valid): a contradiction.
  refine ⟨Extractor.Straightline.id, fun Aux stmtIn aux prover => ?_⟩
  simp only [ENNReal.coe_zero, le_zero_iff]
  rw [OptionT.prEvent_mk_eq_zero_iff]
  intro x hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, _, hx⟩ := hx
  simp only [Reduction.runWithLog, Verifier.run, Verifier.id, Extractor.Straightline.id,
    OptionT.run_bind, OptionT.run_pure, Option.getM, Option.elimM,
    simulateQ_bind, StateT.run'_bind', support_bind, Set.mem_iUnion] at hx
  obtain ⟨⟨o, s'⟩, hi, hx2⟩ := hx
  cases o with
  | none =>
    simp only [Option.elim, simulateQ_pure, StateT.run'_pure', support_pure,
      Set.mem_singleton_iff] at hx2
    exact (Option.some_ne_none x hx2).elim
  | some x' =>
    -- From `hx2`: `x = (stmtIn, some witOut, x'.1.2, witOut)`
    simp only [Option.elim, simulateQ_pure, OptionT.run_pure, liftM_pure, pure_bind,
      StateT.run'_pure', support_pure, Set.mem_singleton_iff] at hx2
    -- From `hi`: the verifier is the identity, so `x'.1.2 = stmtIn`
    rw [show (pure stmtIn : OptionT (OracleComp oSpec) StmtIn) =
      (pure (some stmtIn) : OracleComp oSpec (Option StmtIn)) from rfl] at hi
    simp only [Option.elim, simulateQ_pure, OptionT.run_pure, WriterT.run_pure, liftM_pure,
      pure_bind, support_bind, Set.mem_iUnion, StateT.run_bind] at hi
    obtain ⟨⟨o2, s2⟩, _, hi2⟩ := hi
    cases o2 with
    | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hi2
      exact (Option.some_ne_none x' hi2.1).elim
    | some pr =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hi2
      obtain ⟨rfl, -⟩ := hi2
      simp only [Option.some.injEq] at hx2
      subst hx2
      rintro ⟨h1, h2⟩
      exact h1 _ rfl h2

/-- The identity / trivial reduction is perfectly complete. -/
@[simp]
theorem OracleReduction.id_perfectCompleteness
    {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleReduction.id : OracleReduction oSpec _ _ _ _ _ _ _).perfectCompleteness
      init impl rel rel := by
  unfold OracleReduction.perfectCompleteness
  simp only [OracleReduction.id_toReduction, Reduction.id_perfectCompleteness]

/-- The identity / trivial verifier is perfectly sound. -/
@[simp, grind .]
theorem OracleVerifier.id_soundness {lang : Set (StmtIn × ∀ i, OStmtIn i)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).soundness
      init impl lang lang 0 := by
  simp [OracleVerifier.soundness]

/-- The identity / trivial verifier is perfectly knowledge sound. -/
@[simp, grind .]
theorem OracleVerifier.id_knowledgeSoundness {rel : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)} :
    (OracleVerifier.id : OracleVerifier oSpec _ _ _ _ _).knowledgeSoundness
      init impl rel rel 0 := by
  simp [OracleVerifier.knowledgeSoundness]

end Trivial

end
