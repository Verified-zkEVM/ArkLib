/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Rewinding Knowledge Soundness (abstract notion)

  ArkLib's `Verifier.knowledgeSoundness` (in `Security.Basic`) quantifies over an
  `Extractor.Straightline`, which is fed the data of a *single* prover run (one transcript plus the
  prover/verifier query logs) and given no way to re-invoke the prover. Special-soundness-style
  arguments do **not** yield straightline extractors (cf. [AFK22]); they are inherently *rewinding*.

  This file introduces the rewinding knowledge-soundness notion they target. It is deliberately
  **abstract over the fork-oracle `F`** the extractor is allowed to query — the oracle whose
  answers are sibling runs of the prover (for CWSS, `CWSSStructure.forkOracle`). Because the
  parameter is an `OracleSpec F`, this notion mentions neither special-soundness nor
  coordinate-wise structure, and is reused by *both* implications in `Security.Implications`.

  The definition deliberately parallels the straightline `Verifier.knowledgeSoundness` of [PR #569]:

  * `Extractor.Rewinding` receives exactly the single-run data of an `Extractor.Straightline`
    (input statement, output witness, transcript, prover/verifier query logs) — its *central path* —
    but runs in `OracleComp (oSpec + F)`, so it may additionally fork via `F`. Black-box access is
    **enforced in the type**: the extractor receives no `Prover`, only the ability to query `F`.
  * The game is a **single coupled experiment**: one draw of the initial oracle state, the reduction
    run measured for acceptance *is* the central run handed to the extractor, and the ambient oracle
    state `σ` is threaded from the reduction run into the extractor run (so e.g. a random-oracle
    cache stays consistent across the fork queries). No independent re-run of the prover occurs at
    the level of the definition.
  * As in [PR #569], the extractor's `OptionT` is unwrapped (`.run`) *inside* the game, so its
    `Option` result is a data value: extractor failure counts as an adversary win. (Binding it in
    the surrounding `OptionT` instead would let an always-failing extractor drive the event
    probability to `0`, vacuously discharging knowledge soundness.)

  ## Quantitative form: extraction bounds instead of a constant error

  Strictly bounded extractors (every `OracleComp` makes finitely many queries) cannot achieve the
  linear knowledge error `ε - κ` of expected-time special-soundness extraction ([AFK22] / [FMN24]
  Fig. 11, a retry-until-accept loop): with single-shot forks the guarantee degrades with the
  prover's acceptance probability `ε` (forking-lemma-style, multiplicative losses). The notion is
  therefore parameterized by an **extraction bound** `extractBound : ℝ≥0∞ → ℝ≥0∞`: the probability
  that the measured run accepts *and* the extractor produces a valid witness is at least
  `extractBound ε`, where `ε` is the acceptance probability of the measured run. The classical
  constant-error form is the special case `extractBound := fun ε => ε - κ`
  (`knowledgeSoundnessRewindingWithError`), which remains the target for a future expected-time
  computation model.

  The fork oracle's *implementation* (`forkImpl`) is supplied by each concrete instantiation (for
  CWSS, `Verifier.cwssForkImpl`, which re-runs the prover with indexed replay of the parent run's
  challenges). `forkImpl` receives the prover's inputs `(stmtIn, witIn)` — re-running the prover
  requires them — while the extractor `E` sees neither: `witIn` enters the game only through the
  fork oracle's hidden implementation, preserving black-boxness. (Note this does not let a
  malicious `forkImpl` trivialize the notion by leaking `witIn`: the quantified `witIn` need not
  be a valid witness.)

  This file also defines the two *bridging hypotheses* that concrete implications need to relate
  realized (forked) runs to the probability-1 acceptance demanded by tree-based notions:

  * `QueryImpl.ReplayConsistent`: re-asking an already-answered `oSpec` query (from any state
    reachable by further queries) returns the same answer — i.e. `impl` behaves as a cache.
    Lazily-sampled random oracles qualify; for an empty `oSpec` it is vacuous. This makes a forked
    run's pre-fork prover messages coincide with its parent's.
  * `Verifier.DeterminateAcceptance`: if *some* execution of the verifier accepts a transcript,
    the verifier accepts it with certainty (probability 1 over a fresh initial state). Holds for
    deterministic, state-independent verifiers — in particular all standard special-soundness
    applications. This closes the gap between "this forked run accepted" and the
    `ChallengeTree.IsAccepting` condition consumed by `coordinateWiseSpecialSound`.

  ## References

  * [Attema, T., Fehr, S., and Klooß, M., *Fiat–Shamir Transformation of Multi-Round Interactive
      Proofs*][AFK22]
  * [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments: Towards
      Asymptotic and Concrete Efficiency*][FMN24]
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Extractor

/-- A **rewinding (black-box) extractor**, parameterized by the fork oracle `F` it may query.

  It receives exactly the single-run data of an `Extractor.Straightline` — the input statement, the
  output witness, the transcript, and the prover's and verifier's query logs of one (the *measured*)
  run, which serves as its central path — but runs in `OracleComp (oSpec + F)`, where `F` is the
  fork oracle (its answers are sibling runs of the prover). Black-box access is enforced *in the
  type*: the extractor receives no `Prover` and therefore cannot inspect one — it can only query
  `F`. It returns an input witness, probabilistically and possibly failing (`OptionT`). -/
def Rewinding {ι ιF : Type} (oSpec : OracleSpec ι) (F : OracleSpec ιF)
    (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) : Type :=
  StmtIn → -- input statement
  WitOut → -- output witness
  FullTranscript pSpec → -- transcript of the measured (central) run
  QueryLog oSpec → -- prover's query log of the measured run
  QueryLog oSpec → -- verifier's query log of the measured run
  OptionT (OracleComp (oSpec + F)) WitIn -- input witness

end Extractor

namespace QueryImpl

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- States reachable from `s` by answering some (possibly empty) sequence of queries through
  `impl`. -/
inductive Reachable (impl : QueryImpl oSpec (StateT σ ProbComp)) : σ → σ → Prop
  | refl (s : σ) : Reachable impl s s
  | step {s s' s'' : σ} {t : ι} {a : oSpec.Range t} :
      Reachable impl s s' → (a, s'') ∈ support ((impl t).run s') → Reachable impl s s''

/-- A query implementation is **replay-consistent** if re-asking an already-answered query — from
  any state reachable by answering further queries — surely returns the original answer. In other
  words, `impl` behaves as a cache: lazily-sampled random oracles qualify, as does any stateless
  deterministic implementation; for an empty `oSpec` the condition is vacuous.

  This is the hypothesis under which a forked run's pre-fork `oSpec` answers — and hence its
  pre-fork prover messages — coincide with its parent run's, so that the transcripts assembled
  into a `ChallengeTree` by a rewinding extractor are genuine protocol transcripts. -/
def ReplayConsistent (impl : QueryImpl oSpec (StateT σ ProbComp)) : Prop :=
  ∀ {t : ι} {s s₁ : σ} {a : oSpec.Range t}, (a, s₁) ∈ support ((impl t).run s) →
  ∀ {s₂ : σ}, impl.Reachable s₁ s₂ →
  ∀ {a' : oSpec.Range t} {s₃ : σ}, (a', s₃) ∈ support ((impl t).run s₂) → a' = a

end QueryImpl

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Acceptance of a verifier is **determinate** (w.r.t. `init`, `impl`, and an output language
  `langOut`) if, whenever *some* execution of the verifier on `(stmtIn, transcript)` — from some
  ambient oracle state — outputs a statement in `langOut`, then the verifier accepts that
  transcript with certainty: running it from a fresh initial state surely lands in `langOut`.

  This holds in particular when verification is a deterministic, state-independent function of the
  transcript (the standard setting for special soundness; e.g. Hachi's verifiers). It is the
  bridge between "this forked run was accepted in the realized execution" and the probability-1
  acceptance demanded by `ChallengeTree.IsAccepting`. -/
def DeterminateAcceptance (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (langOut : Set StmtOut) : Prop :=
  ∀ (stmtIn : StmtIn) (tr : FullTranscript pSpec),
    (∃ (s s' : σ) (stmtOut : StmtOut),
      (some stmtOut, s') ∈ support ((simulateQ impl (verifier.run stmtIn tr).run).run s) ∧
        stmtOut ∈ langOut) →
    Pr[(· ∈ langOut) |
      OptionT.mk do (simulateQ impl (verifier.run stmtIn tr)).run' (← init)] = 1

/-- A reduction satisfies **rewinding knowledge soundness** with extraction bound
  `extractBound : ℝ≥0∞ → ℝ≥0∞`, with respect to a fork oracle `F`, input relation `relIn`, and
  output relation `relOut`, if there is a rewinding extractor `E` (black-box, querying only `F`)
  such that, for every input statement, witness, and (malicious) prover, in the following
  **single coupled experiment**:

  1. draw the initial oracle state once and run the reduction with the honest verifier, logging
     queries (`runWithLog`), yielding a transcript, query logs, and a pair `(stmtOut, witOut)`;
  2. continue from the resulting oracle state and run `E` on that run's data (its central path),
     with the fork oracle interpreted by `forkImpl stmtIn witIn prover`, yielding
     `extractedWitIn?`;

  the probability that the measured run accepts (`(stmtOut, witOut) ∈ relOut`) *and* the extractor
  produces a valid input witness is at least `extractBound ε`, where `ε` is the probability that
  the measured run accepts. Equivalently (for `extractBound ε = ε - κ`): the probability that the
  measured run accepts while extraction fails is at most `κ` — the constant-error form
  `knowledgeSoundnessRewindingWithError`. As in [PR #569], the extractor's `Option` is data of the
  game, so extractor failure counts against the bound; failure of the reduction run itself (the
  verifier never accepted) is failure of the surrounding `OptionT` and is not counted.

  `forkImpl stmtIn witIn prover : QueryImpl F (StateT σ ProbComp)` is the fork oracle's
  implementation, supplied by each concrete instantiation (for CWSS, `Verifier.cwssForkImpl`); it
  shares the ambient oracle state `σ` with the measured run, so forked executions see a consistent
  oracle world. -/
def knowledgeSoundnessRewinding {ιF : Type} (F : OracleSpec ιF)
    (forkImpl : StmtIn → WitIn → Prover oSpec StmtIn WitIn StmtOut WitOut pSpec →
      QueryImpl F (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractBound : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∃ E : Extractor.Rewinding oSpec F StmtIn WitIn WitOut pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
    let redImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      impl.addLift challengeQueryImpl
    let extImpl : QueryImpl (oSpec + F) (StateT σ ProbComp) :=
      impl.addLift (forkImpl stmtIn witIn prover)
    let exec : ProbComp (Option (StmtIn × Option WitIn × StmtOut × WitOut)) := do
      let s₀ ← init
      -- the measured run, also serving as the extractor's central path
      let (red?, s₁) ←
        (simulateQ redImpl ((Reduction.mk prover verifier).runWithLog stmtIn witIn).run).run s₀
      match red? with
      | none => return none
      | some ⟨⟨⟨transcript, ⟨_, witOut⟩⟩, stmtOut⟩, proveQueryLog, verifyQueryLog⟩ =>
        -- the extractor continues in the same oracle world (state `s₁`), forking via `F`
        let extractedWitIn? ←
          (simulateQ extImpl
            (E stmtIn witOut transcript proveQueryLog.fst verifyQueryLog).run).run' s₁
        return some (stmtIn, extractedWitIn?, stmtOut, witOut)
    Pr[fun ⟨stmtIn, extractedWitIn?, stmtOut, witOut⟩ =>
        (∃ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∈ relIn) ∧
          (stmtOut, witOut) ∈ relOut
      | OptionT.mk exec] ≥
    extractBound
      Pr[fun ⟨_, _, stmtOut, witOut⟩ => (stmtOut, witOut) ∈ relOut | OptionT.mk exec]

/-- Rewinding knowledge soundness with a constant **knowledge error** `κ`: the extraction bound is
  `fun ε => ε - κ`, i.e. the probability that the measured run accepts while extraction fails is at
  most `κ`. This is the classical (expected-time) form of the guarantee ([AFK22] / [FMN24] Lemma
  2.31); strictly bounded (`OracleComp`) extractors generally only achieve weaker, forking-style
  bounds (see the module docstring), so implications proved in this library target
  `knowledgeSoundnessRewinding` with a non-linear bound instead. -/
def knowledgeSoundnessRewindingWithError {ιF : Type} (F : OracleSpec ιF)
    (forkImpl : StmtIn → WitIn → Prover oSpec StmtIn WitIn StmtOut WitOut pSpec →
      QueryImpl F (StateT σ ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (knowledgeError : ℝ≥0) : Prop :=
  knowledgeSoundnessRewinding init impl F forkImpl relIn relOut verifier
    (fun ε => ε - (knowledgeError : ℝ≥0∞))

end Verifier
