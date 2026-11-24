/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Alexander Hicks, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.InteractiveProof.Soundness
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.QueryTracking.QueryLog

/-!
# State-Restoration Security Definitions

This module uses the legacy `ProtocolSpec`, `Prover`, and `Verifier` representation.
Shared game execution is independent of that representation and lives in `ArkLib.Security`.

This file defines SR prover and extractor types, soundness experiments, and security predicates
adapted from [snarg-book, Definitions 13.2.1–13.2.3] and [CO25, Definitions 3.12–3.14]. Each notion
has an unbounded and a query-bounded form; `isSrChallengeMove` counts only queries
for verifier messages.
Query-bounded knowledge soundness fixes one extractor before all natural-number budgets.
The extractor may use randomness and both query logs and has no prover handle; no deterministic
or running-time claim is made. Each verifier-message query contains a salt chosen by the prover.
The prover's final output selects which salt is used in transcript reconstruction. The salt is
separate game data: verification and input relations use only the original statement.
This is the single-salt instance of the paper's salted state-restoration experiment.
The final lemmas preserve these bounds when custom or extra sampling interfaces are compiled
into the prover's private coins, without changing the extractor's public logs.

## References

* [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][snarg-book]
* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

variable {ι : Type}

namespace Prover

/-- An SR soundness prover returns `((𝕩, τ), α)`: the original statement, chosen salt,
and full prover-message tuple. It may request verifier messages `ρᵢ ← fᵢ((𝕩, τ), α[<i])`,
query the ambient oracles `oSpec`, and draw private uniform coins through `unifSpec`. -/
abbrev StateRestoration.Soundness (oSpec : OracleSpec ι) (StmtIn : Type) {Salt : Type} {n : ℕ}
    (pSpec : ProtocolSpec n) :=
  OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec)
    ((StmtIn × Salt) × pSpec.Messages)

/-- An SR knowledge-soundness prover returns `((𝕩, τ), α, w_out)`, adding an output witness
`w_out` to the soundness prover's output. It has the same oracle access: verifier-message
queries `ρᵢ ← fᵢ(qᵢ)`, ambient queries to `oSpec`, and private uniform coins. -/
abbrev StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι) (StmtIn WitOut : Type)
    {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec)
    ((StmtIn × Salt) × pSpec.Messages × WitOut)

end Prover

namespace Extractor

/-- A non-rewinding SR extractor computes `E(𝕩, τ, w_out, T, tr_P, tr_V)`, producing
an input witness `w_in` or failure `⊥`. Here `T` is the full transcript, `tr_P` records the
prover's ambient queries and SR moves, excluding its private coin queries. The log `tr_V`
records all verifier queries to `oSpec`.

The extractor may query `oSpec` and sample through `unifSpec`. Its interface supplies no
prover handle or direct access to the verifier-message oracles `fᵢ`. Failure on a valid
verifier output counts as extraction failure. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn WitIn WitOut : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → -- input statement
  Salt → -- salt context chosen by the prover
  WitOut → -- output witness
  pSpec.FullTranscript → -- transcript
  QueryLog (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp (oSpec + unifSpec)) WitIn -- private sampling and ambient queries

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- Run `((𝕩, τ), α) ← P`, reconstruct `T ← α.deriveTranscriptSR (𝕩, τ)`,
and return `(T, (𝕩, τ))`. Reconstruction queries each verifier-message oracle using the
chosen salt and prover-message prefix. The prover chooses `τ`; the enclosing
experiment answers its private coins uniformly. The IP verifier later receives only `𝕩` and
`T`. -/
def srSoundnessGame
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
    OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec)
      (pSpec.FullTranscript × (StmtIn × Salt)) := do
  let ⟨(stmtIn, salt), messages⟩ ← P
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (stmtIn, salt))
    ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec)
  return ⟨transcript, (stmtIn, salt)⟩

namespace Verifier

namespace StateRestoration

/-- Run the prover, reconstruct its selected transcript, and evaluate the verifier. The
initial oracle table is drawn from `init`. The prover's private coins are answered uniformly. -/
def soundnessExperiment
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
    ProbComp (StmtIn × Option StmtOut) :=
  AdaptiveGame.run init
    ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
      (QueryImpl.id' unifSpec)) srProver
    (fun ((x, salt), messages) => do
      let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (x, salt)) _
      liftComp (verifier.run x transcript) _)
    (fun result stmtOut => (result.1.1, stmtOut))

/-- False acceptance requires a false input statement and an accepted verifier output. -/
def soundnessFailureEvent (langIn : Set StmtIn) (langOut : Set StmtOut) :
    StmtIn × Option StmtOut → Prop
  | (stmtIn, some stmtOut) => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
  | _ => False

/-- The SR false-acceptance probability for a fixed prover:
`Pr[𝕩 ∉ langIn ∧ y ≠ ⊥ ∧ y ∈ langOut]`. -/
def soundnessFailureProb
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
    ENNReal :=
  Pr{let result ← soundnessExperiment init impl verifier srProver}[
    soundnessFailureEvent langIn langOut result]

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The shared adaptive soundness experiment runs the original SR game and verifier. -/
theorem soundnessFailureProb_eq
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
      soundnessFailureProb init impl langIn langOut verifier srProver =
  let experiment : ProbComp (StmtIn × Option StmtOut) := do
    StateT.run' (simulateQ
      (QueryImpl.addLift
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        (QueryImpl.id' unifSpec)) (do
      let ⟨transcript, (stmtIn, _salt)⟩ ← srSoundnessGame (Salt := Salt) srProver
      let stmtOut ← liftComp (verifier.run stmtIn transcript) _
      return (stmtIn, stmtOut))) (← init)
  Pr{let result ← experiment}[
    match result with
    | ⟨stmtIn, some stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn
    | _ => False] := by
  simp only [soundnessFailureProb, soundnessExperiment, AdaptiveGame.run, srSoundnessGame,
    bind_assoc, pure_bind]
  rfl

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Reconstruct the transcript, then log the verifier's ambient queries. Reconstruction
uses the same challenge table as the prover and takes place outside the log. -/
def reconstructAndVerifyWithLog {κ : Type} {privateSpec : OracleSpec κ}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (input : StmtIn × Salt) (messages : pSpec.Messages) :
    OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      (pSpec.FullTranscript × Option StmtOut × QueryLog oSpec) := do
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) input) _
  let (stmtOut, logV) ← liftComp (verifier.run input.1 transcript).run.withQueryLog _
  return (transcript, stmtOut, logV)

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Run the SR prover, reconstruct `T`, and compute `y ← verifier(𝕩, T)`, returning
`((𝕩, τ), w_out, T, tr_P, y, tr_V)`. The log `tr_P` contains the prover's ambient queries
and SR moves, excluding its `privateSpec` queries. The log `tr_V` records all verifier queries
to `oSpec`. Transcript-reconstruction queries are excluded from both logs. -/
def knowledgeSoundnessProverVerifierExp {κ : Type} {privateSpec : OracleSpec κ}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × pSpec.Messages × WitOut)) :
    OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × WitOut × pSpec.FullTranscript ×
        QueryLog (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) ×
        Option StmtOut × QueryLog oSpec) := do
  let ⟨⟨(stmtIn, salt), messages, witOut⟩, proverLog⟩ ← srProver.withQueryLog
  let tr := proverLog.publicQueries
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (stmtIn, salt))
    ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
  let ⟨stmtOut, tr_V⟩ ←
    liftComp (simulateQ loggingOracle (verifier.run stmtIn transcript).run).run _
  return ((stmtIn, salt), witOut, transcript, tr, stmtOut, tr_V)

/-- After the prover and verifier run, compute `w_in ← E(𝕩, τ, w_out, T, tr_P, tr_V)`.
The prover's and the extractor's private coins are answered uniformly. The extractor's public
handler exposes only the ambient oracles. -/
def knowledgeSoundnessExperiment
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec StmtIn WitOut pSpec (Salt := Salt)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) :=
  AdaptiveGame.runWithExtractor init
    ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
      (QueryImpl.id' unifSpec))
    (impl.addLift (QueryImpl.id' unifSpec))
    srProver.withQueryLog
    (fun ((input, messages, _), _) => reconstructAndVerifyWithLog verifier input messages)
    (fun (((x, salt), _, witOut), logP) (transcript, _, logV) =>
      srExtractor x salt witOut transcript logP.publicQueries logV)
    (fun ((input, _, witOut), _) (_, stmtOut, _) witIn => (input.1, witIn, stmtOut, witOut))

/-- The SR extraction-failure probability for a fixed prover and extractor:
`Pr[y ≠ ⊥ ∧ (y, w_out) ∈ relOut ∧ (w_in = ⊥ ∨ (𝕩, w_in) ∉ relIn)]`. -/
def knowledgeSoundnessFailureProb
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec StmtIn WitOut pSpec (Salt := Salt)) : ENNReal :=
  Pr{let result ← knowledgeSoundnessExperiment init impl srExtractor verifier srProver}[
    relationKSFailEvent relIn relOut result]

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The shared adaptive extraction experiment exposes the original SR verifier and logs. -/
theorem knowledgeSoundnessFailureProb_eq
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb init impl srExtractor relIn relOut verifier
      srProver =
  let experiment : ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) := do
    StateT.run' (do
      let ⟨(x, salt), witOut, transcript, tr, stmtOut, trV⟩ ←
        simulateQ (QueryImpl.addLift
          (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
          (QueryImpl.id' unifSpec))
          (knowledgeSoundnessProverVerifierExp (Salt := Salt) verifier srProver)
      let witIn ← simulateQ (impl.addLift (QueryImpl.id' unifSpec))
        (srExtractor x salt witOut transcript tr trV).run
      pure (x, witIn, stmtOut, witOut)) (← init)
  Pr{let result ← experiment}[relationKSFailEvent relIn relOut result] := by
  simp only [knowledgeSoundnessFailureProb, knowledgeSoundnessExperiment,
    AdaptiveGame.runWithExtractor, AdaptiveGame.execute,
    reconstructAndVerifyWithLog, knowledgeSoundnessProverVerifierExp, withQueryLog,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  rfl

/-- Select SR moves: `isSrChallengeMove (.inr (i, q)) = True`, while ambient queries
`.inl q` give `False`. The security predicates use `publicQuerySelector` to exclude
private draws. -/
def isSrChallengeMove : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop
  | .inl _ => False
  | .inr _ => True

/-- The SR move selector is decidable without equality on query inputs. -/
instance instDecidablePredSRChallengeMove :
    DecidablePred (isSrChallengeMove (Salt := Salt) (oSpec := oSpec)
      (StmtIn := StmtIn) (pSpec := pSpec)) := fun q =>
  match q with
  | .inl _ => isFalse id
  | .inr _ => isTrue True.intro

/-! ## State-restoration security predicates

Both unbounded and query-bounded predicates use the same experiments. A query bound restricts
the malicious prover; it does not truncate the game. Its selector applies only to ambient queries
and SR moves; private draws are always excluded from the bound.
-/

/-- SR soundness with error `ε`: every prover satisfies
`Pr[𝕩 ∉ langIn ∧ y ≠ ⊥ ∧ y ∈ langOut] ≤ ε`, with no query bound. -/
def soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt),
    soundnessFailureProb (Salt := Salt) init impl langIn langOut verifier P
      ≤ srSoundnessError

/-- SR soundness with error `error` for every prover making at most `t` queries selected by
`queryBoundSelector`. Set the selector to `isSrChallengeMove (Salt := Salt)` for a `t`-move
SR prover. Private samples are excluded from the budget. -/
def soundnessQueryBounded
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (queryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] (t : ℕ) (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t)
    (soundnessExperiment (Salt := Salt) init impl verifier)
    (soundnessFailureEvent langIn langOut) error

/-- For the fixed extractor `E`, every SR prover satisfies
`Pr[valid verifier output ∧ extraction failure] ≤ error`, with no query bound.
The event is the one defined by `knowledgeSoundnessFailureProb`. -/
def knowledgeSoundnessWithExtractor
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (error : ENNReal) : Prop :=
  ∀ P : Prover.StateRestoration.KnowledgeSoundness
    oSpec StmtIn WitOut pSpec (Salt := Salt),
    knowledgeSoundnessFailureProb (Salt := Salt) init impl extractor relIn relOut verifier P
      ≤ error

/-- SR knowledge soundness with error `ε`:
`∃ E, ∀ P, Pr[valid verifier output ∧ extraction failure] ≤ ε`, with no query bound.
The non-rewinding extractor `E` is fixed before the prover. Failure `w_in = ⊥` is included
in the event defined by `knowledgeSoundnessFailureProb`. The extractor is unrestricted:
classical choice can recover a witness from any true statement, ignoring the transcript and logs.
See `Verifier.knowledgeSoundness_iff_relationSoundness` for the analogous equivalence for
fixed-statement interaction. -/
def knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ extractor, knowledgeSoundnessWithExtractor (Salt := Salt) init impl relIn relOut verifier
    extractor
    srKnowledgeSoundnessError

/-- For the fixed extractor `E` and budget `t`, require
`Pr[valid verifier output ∧ extraction failure] ≤ error` for every prover making at most
`t` queries selected by `queryBoundSelector`. Private samples are excluded from the budget. -/
def knowledgeSoundnessQueryBoundedWithExtractor
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (extractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (queryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] (t : ℕ) (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t)
    (knowledgeSoundnessExperiment (Salt := Salt) init impl extractor verifier)
    (relationKSFailEvent relIn relOut) error

/-- One non-rewinding extractor for all query budgets:
`∃ E, ∀ t, ∀ P with ≤ t selected queries, Pr[valid output ∧ extraction failure] ≤ error t`.
The extractor is fixed before both the budget and prover; `queryBoundSelector` chooses which
non-private prover queries count. As in `knowledgeSoundness`, the extractor may use classical
choice to recover a witness from the input statement. -/
def knowledgeSoundnessQueryBounded
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (queryBoundSelector : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] (error : ℕ → ENNReal) : Prop :=
  ∃ extractor, ∀ t, knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn
    relOut verifier
    extractor queryBoundSelector t (error t)

end StateRestoration
end Verifier

end

open OracleComp OracleSpec

/-! ## State-restoration experiments -/

open OracleComp OracleSpec ProtocolSpec
namespace Verifier.StateRestoration
variable {ι κ : Type} {oSpec : OracleSpec ι} {privateSpec : OracleSpec κ}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
  (sampler : QueryImpl privateSpec ProbComp)

private theorem knowledgeSoundnessProverVerifierExp_eq_publicLog
    (V : Verifier oSpec StmtIn StmtOut pSpec) {κ' : Type} {spec : OracleSpec κ'}
    (Q : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + spec)
      ((StmtIn × Salt) × pSpec.Messages × WitOut)) :
    knowledgeSoundnessProverVerifierExp (Salt := Salt) V Q = (do
      let ⟨⟨x, messages, witOut⟩, tr⟩ ←
        (fun r : ((StmtIn × Salt) × pSpec.Messages × WitOut) ×
          QueryLog ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + spec) =>
            (r.1, r.2.publicQueries)) <$> Q.withQueryLog
      let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) x) _
      let ⟨stmtOut, trV⟩ ←
        liftComp (V.run x.1 transcript).run.withQueryLog _
      return (x, witOut, transcript, tr, stmtOut, trV)) := by
  simp only [knowledgeSoundnessProverVerifierExp, withQueryLog, bind_map_left]
  rfl

/-- An SR prover whose private coins come from `sampler` is a uniform-coin SR prover:
`normalizePrivateCoins sampler P` makes the same public queries and gives the same soundness
experiment. -/
theorem soundnessExperiment_normalizePrivateCoins (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × pSpec.Messages)) :
    soundnessExperiment (Salt := Salt) init impl V (normalizePrivateCoins sampler P) =
      AdaptiveGame.run init
        ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
          sampler) P
        (fun ((x, salt), messages) => do
          let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (x, salt)) _
          liftComp (V.run x transcript) _)
        (fun result stmtOut => (result.1.1, stmtOut)) := by
  simp only [soundnessExperiment, AdaptiveGame.run]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_add_liftComp_sum_left,
    simulateQ_add_add_liftComp_left, StateT.run'_bind', StateT.run'_pure']

private theorem runWithExtractor_eq_proverVerifierExp {κ' : Type} {spec : OracleSpec κ'}
    (H : QueryImpl ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + spec)
      (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (Q : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + spec)
      ((StmtIn × Salt) × pSpec.Messages × WitOut)) :
    AdaptiveGame.runWithExtractor init H (impl.addLift (QueryImpl.id' unifSpec))
      Q.withQueryLog
      (fun ((input, messages, _), _) => reconstructAndVerifyWithLog V input messages)
      (fun (((x, salt), _, witOut), logP) (transcript, _, logV) =>
        E x salt witOut transcript logP.publicQueries logV)
      (fun ((input, _, witOut), _) (_, stmtOut, _) witIn => (input.1, witIn, stmtOut, witOut)) =
    (do
      StateT.run' (do
        let ⟨(x, salt), witOut, transcript, tr, stmtOut, trV⟩ ←
          simulateQ H (knowledgeSoundnessProverVerifierExp (Salt := Salt) V Q)
        let witIn ← simulateQ (impl.addLift (QueryImpl.id' unifSpec))
          (E x salt witOut transcript tr trV).run
        pure (x, witIn, stmtOut, witOut)) (← init)) := by
  simp only [AdaptiveGame.runWithExtractor, AdaptiveGame.execute,
    reconstructAndVerifyWithLog, knowledgeSoundnessProverVerifierExp, withQueryLog,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  rfl

/-- An SR knowledge prover whose private coins come from `sampler` is a uniform-coin prover:
`normalizePrivateCoins sampler P` gives the same extraction experiment, including the public
query log that the extractor receives. -/
theorem knowledgeSoundnessExperiment_normalizePrivateCoins
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × pSpec.Messages × WitOut)) :
    knowledgeSoundnessExperiment (Salt := Salt) init impl E V (normalizePrivateCoins sampler P) =
      AdaptiveGame.runWithExtractor init
        ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
          sampler)
        (impl.addLift (QueryImpl.id' unifSpec))
        P.withQueryLog
        (fun ((input, messages, _), _) => reconstructAndVerifyWithLog V input messages)
        (fun (((x, salt), _, witOut), logP) (transcript, _, logV) =>
          E x salt witOut transcript logP.publicQueries logV)
        (fun ((input, _, witOut), _) (_, stmtOut, _) witIn =>
          (input.1, witIn, stmtOut, witOut)) := by
  simp only [knowledgeSoundnessExperiment]
  rw [runWithExtractor_eq_proverVerifierExp, runWithExtractor_eq_proverVerifierExp]
  rw [knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt),
    knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt)]
  rw [publicQueries_withQueryLog_normalizePrivateCoins]
  simp only [simulateQ_bind, simulateQ_pure]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_map,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left, bind_map_left, bind_assoc,
    pure_bind, StateT.run'_bind', StateT.run'_pure']

/-- A move-bounded SR soundness bound for uniform-coin provers covers provers whose private
coins come from any sampler. -/
theorem soundnessQueryBounded_apply_sampler
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t error)
    (P : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × pSpec.Messages))
    (hP : P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t) :
    Pr{let result ← AdaptiveGame.run init
        ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
          sampler) P
        (fun ((x, salt), messages) => do
          let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (x, salt)) _
          liftComp (V.run x transcript) _)
        (fun result stmtOut => (result.1.1, stmtOut))}[
      soundnessFailureEvent langIn langOut result] ≤ error := by
  classical
  rw [← soundnessExperiment_normalizePrivateCoins (Salt := Salt) init impl sampler]
  exact h _ (hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt)))

/-- An SR extractor for uniform-coin provers also extracts from provers whose private coins
come from any sampler, with the same move bound and error. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_apply_sampler
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn relOut V E
      (isSrChallengeMove (Salt := Salt)) t error)
    (P : OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × pSpec.Messages × WitOut))
    (hP : P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t) :
    Pr{let result ← AdaptiveGame.runWithExtractor init
        ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
          sampler)
        (impl.addLift (QueryImpl.id' unifSpec))
        P.withQueryLog
        (fun ((input, messages, _), _) => reconstructAndVerifyWithLog V input messages)
        (fun (((x, salt), _, witOut), logP) (transcript, _, logV) =>
          E x salt witOut transcript logP.publicQueries logV)
        (fun ((input, _, witOut), _) (_, stmtOut, _) witIn =>
          (input.1, witIn, stmtOut, witOut))}[
      relationKSFailEvent relIn relOut result] ≤ error := by
  classical
  rw [← knowledgeSoundnessExperiment_normalizePrivateCoins (Salt := Salt) init impl sampler]
  exact h _ (hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt)))

end Verifier.StateRestoration

namespace Verifier.StateRestoration

section AmbientSampling

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut Salt : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Adding a sampling slot to the ambient interface does not strengthen an SR prover:
its samples can all be routed through the private interface. -/
theorem soundnessFailureProb_mergePrivateCoins
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness (oSpec + unifSpec)
      StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      langIn langOut (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    soundnessFailureProb (Salt := Salt) init impl langIn langOut V P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp)) +
        challenge)
      (impl + challenge) (fun _ => rfl) x messages
  have hmerge := simulateQ_mergeRight impl challenge ((QueryImpl.id' unifSpec).liftTarget _) P
  simp only [soundnessFailureProb_eq, srSoundnessGame]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left]
  simp only [Verifier.liftOracles, Verifier.run]
  rw [hmerge]
  simp only [challenge,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self] at htr
  simp only [htr, OptionT.mk, QueryImpl.simulateQ_add_liftComp_left]
  rfl

/-- A move-bounded SR soundness premise remains valid when private sampling is carried
through an extra ambient slot. The verifier continues to use only its original oracles. -/
theorem soundnessQueryBounded_addPrivateCoins
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (ε : ENNReal)
    (hSR : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t ε) :
    soundnessQueryBounded (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec)) langIn langOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) (isSrChallengeMove (Salt := Salt)) t ε := by
  intro P hP
  change soundnessFailureProb init _ langIn langOut _ P ≤ ε
  rw [soundnessFailureProb_mergePrivateCoins (Salt := Salt)]
  apply hSR P.mergeRight
  apply hP.simulateQ_of_step <;> intro q hq <;>
    rcases q with ((q | q) | q) | q <;>
      simp_all [QueryImpl.mergeRight, publicQuerySelector, isSrChallengeMove]

/-- Lift an SR extractor to the temporary ambient sampling interface. Its supplied logs
are projected back to the original public oracles and SR moves. -/
def addPrivateCoinsExtractor
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt)) :
    Extractor.StateRestoration (oSpec + unifSpec) StmtIn WitIn WitOut pSpec (Salt := Salt) :=
  fun x salt w tr log logV => OptionT.mk
    (liftCompLeft (E x salt w tr log.eraseMiddle logV.fst).run)

/-- Merging the prover's two sampling slots preserves the SR extraction-failure probability.
The adapter removes entries from the extra sampling slot before passing the logs to `E`. -/
theorem knowledgeSoundnessFailureProb_mergePrivateCoins
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.KnowledgeSoundness (oSpec + unifSpec)
      StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      (addPrivateCoinsExtractor (Salt := Salt) E) relIn relOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    knowledgeSoundnessFailureProb (Salt := Salt) init impl E relIn relOut V P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp)) +
        challenge)
      (impl + challenge) (fun _ => rfl) x messages
  have hlog (x : StmtIn) (tr : pSpec.FullTranscript) :
      (simulateQ loggingOracle
        ((V.liftOracles (targetSpec := oSpec + unifSpec)).run x tr).run).run =
        liftCompLeft (V.run x tr).run.withQueryLog >>= fun z =>
          pure (z.1, QueryLog.inl z.2) :=
    withQueryLog_liftComp_left_of_query (oSpec := oSpec) (spec₂ := unifSpec) (fun _ => rfl)
      (V.run x tr).run
  simp only [knowledgeSoundnessFailureProb_eq]
  rw [knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt) V,
    fst_withQueryLog_mergeRight]
  unfold knowledgeSoundnessProverVerifierExp
  simp only [simulateQ_bind, simulateQ_pure,
    hlog, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left, bind_assoc, pure_bind]
  rw [simulateQ_mergeRight]
  simp only [simulateQ_map, bind_map_left]
  simp only [addPrivateCoinsExtractor, OptionT.run_mk, liftCompLeft,
    QueryImpl.simulateQ_add_liftComp_left]
  simp only [challenge,
    QueryImpl.addLift_def, QueryImpl.liftTarget_self] at htr
  simp only [htr, QueryLog.fst_inl]

/-- The same SR extractor works after routing temporary ambient sampling privately. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_addPrivateCoins
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (ε : ENNReal)
    (hSR : knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn relOut V E
      (isSrChallengeMove (Salt := Salt)) t ε) :
    knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init (impl.addLift (QueryImpl.id'
      unifSpec))
      relIn relOut (V.liftOracles (targetSpec := oSpec + unifSpec))
      (addPrivateCoinsExtractor (Salt := Salt) E) (isSrChallengeMove (Salt := Salt)) t ε := by
  intro P hP
  change knowledgeSoundnessFailureProb init _ _ relIn relOut _ P ≤ ε
  rw [knowledgeSoundnessFailureProb_mergePrivateCoins (Salt := Salt)]
  apply hSR P.mergeRight
  apply hP.simulateQ_of_step <;> intro q hq <;>
    rcases q with ((q | q) | q) | q <;>
      simp_all [QueryImpl.mergeRight, publicQuerySelector, isSrChallengeMove]

end AmbientSampling
end Verifier.StateRestoration

/-! ## Derived NARG specializations -/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

private theorem withQueryLog_map {ι α β : Type} {spec : OracleSpec ι}
    (f : α → β) (p : OracleComp spec α) :
    (f <$> p).withQueryLog = (fun a => (f a.1, a.2)) <$> p.withQueryLog := by
  simp [withQueryLog, simulateQ_map, WriterT.run_map]

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- The derived NARG verifier reconstructs the transcript using the statement and salt,
then runs the original verifier. The proof consists of the prover messages. -/
def toNARGVerifier (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier pSpec.Messages (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec)
      (StmtIn × Salt) StmtOut where
  verify x tr := OptionT.mk do
    let transcript ← (tr 0).deriveTranscriptSR (oSpec := oSpec) x
    liftComp (V.run x.1 transcript).run _

variable (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- The derived NARG experiment preserves the accepted statement and verifier output. -/
theorem soundnessExperiment_toNARG
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
    (fun a => a.2.map (a.1, ·)) <$> soundnessExperiment init impl V P =
    Option.map (fun a => (a.1.1, a.2)) <$>
      adaptiveNARGSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        (toNARGVerifier V) P := by
  simp only [soundnessExperiment, adaptiveNARGSoundnessExp, toNARGVerifier,
    AdaptiveGame.run, Fin.cons_zero, OptionT.run_mk, liftComp_bind,
    simulateQ_bind, simulateQ_pure, map_bind, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left]
  simp [StateT.run'_eq, map_bind,
    QueryImpl.simulateQ_add_liftM_left, Verifier.run]
  rfl

/-- Forgetting the salt in the failure event gives exactly the SR soundness error. -/
theorem soundnessFailureProb_toNARG
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb init impl langIn langOut V P =
      Pr{let out ← (adaptiveNARGSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        (toNARGVerifier V) P)}[nargSoundFailEvent (Prod.fst ⁻¹' langIn) langOut out] := by
  have h := congrArg (fun p => Pr{let out ← p}[nargSoundFailEvent langIn langOut out])
    (soundnessExperiment_toNARG init impl V P)
  simp only [prEvent_map] at h
  convert h using 1
  · unfold soundnessFailureProb
    congr 2
    funext a
    rcases a with ⟨x, out⟩
    cases out <;> simp [soundnessFailureEvent, nargSoundFailEvent, and_comm]
  · congr 3
    funext out
    cases out <;> simp [nargSoundFailEvent]

/-- The derived NARG verifier has the same bounded soundness contract and query selector. -/
theorem soundnessQueryBounded_iff_adaptiveNARGSoundnessQueryBounded
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (counts : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    soundnessQueryBounded init impl langIn langOut V counts t error ↔
    (toNARGVerifier V).adaptiveNARGSoundnessQueryBounded init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (Prod.fst ⁻¹' langIn) langOut counts t error := by
  rw [Verifier.adaptiveNARGSoundnessQueryBounded_iff]
  unfold soundnessQueryBounded AdaptiveGame.Bounded
  simp only [← soundnessFailureProb_toNARG, soundnessFailureProb]
end Verifier.StateRestoration

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Include the output witness in the NARG string and return it alongside the verifier output.
This turns the SR output relation into the NARG output language. -/
def toNARGKnowledgeVerifier (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (pSpec.Messages × WitOut)
      (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec)
      (StmtIn × Salt) (StmtOut × WitOut) where
  verify x tr := (fun y => (y, (tr 0).2)) <$>
    (toNARGVerifier V).verify x (Fin.cons (tr 0).1 (fun i => i.elim0))

variable [DecidableEq StmtIn] [DecidableEq Salt]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Inhabited (pSpec.Challenge i)]

/-- Recover the transcript from the verifier's challenge log, without issuing queries.
Only the ambient verifier log is passed to the original named SR extractor. The NARG extractor
may also query the verifier-message oracles, but this one never does. -/
def toNARGExtractor
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt)) :
    (StmtIn × Salt) → (pSpec.Messages × WitOut) →
      QueryLog (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) →
      OptionT (OracleComp ((oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec) + unifSpec))
        WitIn :=
  fun x proof logP logV => OptionT.mk <| liftPublicLeft (E x.1 x.2 proof.2
    (FullTranscript.ofMessagesChallenges proof.1 (proof.1.challengesOfLog x logV.snd))
    logP logV.fst).run

omit [DecidableEq StmtIn] [DecidableEq Salt] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, Inhabited (pSpec.Challenge i)] in
private theorem runVerifierWithLog_toNARGKnowledgeVerifier
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn × Salt)
    (proof : pSpec.Messages × WitOut) :
    runVerifierWithLog (toNARGKnowledgeVerifier V) x proof =
      (do
        let cs ← chalTupleUpTo (oSpec := oSpec) x proof.1 ⟨n, Nat.lt_succ_self n⟩
        let tr := FullTranscript.ofMessagesChallenges proof.1 (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)
        let result ← liftComp (V.run x.1 tr).run.withQueryLog
          (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec)
        return (result.1.map (·, proof.2),
          QueryLog.inr (canonChalLog x proof.1 ⟨n, Nat.lt_succ_self n⟩ cs) ++
            QueryLog.inl result.2)) := by
  have hLog : (proof.1.deriveTranscriptSR (oSpec := oSpec) x).withQueryLog =
      (do
        let cs ← chalTupleUpTo (oSpec := oSpec) x proof.1 ⟨n, Nat.lt_succ_self n⟩
        pure (show pSpec.FullTranscript from
          FullTranscript.ofMessagesChallenges proof.1 (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩),
          QueryLog.inr (canonChalLog x proof.1 ⟨n, Nat.lt_succ_self n⟩ cs))) :=
    logged_deriveTranscriptSRAux_eq (oSpec := oSpec) x proof.1 ⟨n, Nat.lt_succ_self n⟩
  simp only [runVerifierWithLog, toNARGKnowledgeVerifier, toNARGVerifier,
    Fin.cons_zero, OptionT.run_map, OptionT.run_mk, withQueryLog_map, withQueryLog_bind,
    hLog, withQueryLog_liftComp_left, map_bind, Functor.map_map]
  simp only [bind_assoc, pure_bind, map_eq_pure_bind, Prod.map, id_eq]
end Verifier.StateRestoration

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [DecidableEq StmtIn] [DecidableEq Salt]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Inhabited (pSpec.Challenge i)]

private theorem toNARGExtractor_canonLog
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (x : StmtIn × Salt) (proof : pSpec.Messages × WitOut)
    (cs : pSpec.ChallengesUpTo ⟨n, Nat.lt_succ_self n⟩)
    (logP : QueryLog (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec))
    (logV : QueryLog oSpec) :
    (toNARGExtractor E x proof logP
      (QueryLog.inr (canonChalLog x proof.1 ⟨n, Nat.lt_succ_self n⟩ cs) ++
        QueryLog.inl logV)).run =
      liftPublicLeft (E x.1 x.2 proof.2
        (FullTranscript.ofMessagesChallenges proof.1
          (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)) logP logV).run := by
  simp [toNARGExtractor, QueryLog.snd_append, QueryLog.fst_append,
    Messages.challengesOfLog_canonChalLog]

variable (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- The derived NARG experiment preserves extraction and the accepted output-witness pair. -/
theorem knowledgeSoundnessExperiment_toNARG
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec StmtIn WitOut pSpec (Salt := Salt)) :
    (fun a => (a.1, a.2.1, a.2.2.1.map (·, a.2.2.2))) <$>
      knowledgeSoundnessExperiment init impl E V P =
    (fun a => (a.1.1, a.2)) <$>
      adaptiveNARGKnowledgeSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        (toNARGKnowledgeVerifier V) (toNARGExtractor E) P := by
  have hDerive (x : StmtIn × Salt) (messages : pSpec.Messages) :
      messages.deriveTranscriptSR (oSpec := oSpec) x = (do
        let cs ← chalTupleUpTo (oSpec := oSpec) x messages ⟨n, Nat.lt_succ_self n⟩
        pure (show pSpec.FullTranscript from
          FullTranscript.ofMessagesChallenges messages (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩))) :=
    Messages.deriveTranscriptSR_eq_chalTupleUpTo x messages
  simp only [knowledgeSoundnessExperiment, adaptiveNARGKnowledgeSoundnessExp,
    runVerifierWithLog_toNARGKnowledgeVerifier, AdaptiveGame.runWithExtractor,
    AdaptiveGame.execute, reconstructAndVerifyWithLog,
    liftComp_bind, liftComp_pure,
    bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure,
    toNARGExtractor_canonLog, map_bind, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left,
    simulateQ_liftPublicLeft]
  simp [hDerive, QueryImpl.simulateQ_add_liftM_left,
    StateT.run'_eq, map_bind]
end Verifier.StateRestoration

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [DecidableEq StmtIn] [DecidableEq Salt]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Inhabited (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- SR extraction failure is the derived NARG failure event, with exactly the same named
extractor execution. Reconstruction uses only the logged answers. -/
theorem knowledgeSoundnessFailureProb_toNARG
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb init impl E relIn relOut V P =
    Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (toNARGKnowledgeVerifier V) (toNARGExtractor E) P)}[
        nargKSFailEvent {a | (a.1.1, a.2) ∈ relIn} relOut out] := by
  have h := congrArg (fun p => Pr{let out ← p}[nargKSFailEvent relIn relOut out])
    (knowledgeSoundnessExperiment_toNARG init impl V E P)
  simp only [prEvent_map] at h
  have hSR (a : StmtIn × Option WitIn × Option StmtOut × WitOut) :
      nargKSFailEvent relIn relOut (a.1, a.2.1, a.2.2.1.map (·, a.2.2.2)) =
      relationKSFailEvent relIn relOut a := by
    rcases a with ⟨x, wit, out, w⟩
    cases wit <;> cases out <;> rfl
  have hNARG (a : (StmtIn × Salt) × Option WitIn × Option (StmtOut × WitOut)) :
      nargKSFailEvent relIn relOut (a.1.1, a.2) =
      nargKSFailEvent {a | (a.1.1, a.2) ∈ relIn} relOut a := by
    rcases a with ⟨x, wit, out⟩
    cases wit <;> cases out <;> rfl
  simpa only [knowledgeSoundnessFailureProb, hSR, hNARG] using h

/-- The bounded SR knowledge contract is the derived NARG contract. The adapter retains the
extractor's ambient-oracle access and hides reconstruction queries from its original logs. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_iff_adaptiveNARGKnowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (counts : (oSpec + srVerifierMessageOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    knowledgeSoundnessQueryBoundedWithExtractor init impl relIn relOut V E counts t error ↔
    (toNARGKnowledgeVerifier V).adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      {a | (a.1.1, a.2) ∈ relIn} relOut
      (toNARGExtractor E) counts t error := by
  rw [Verifier.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor_iff]
  unfold knowledgeSoundnessQueryBoundedWithExtractor AdaptiveGame.Bounded
  simp only [← knowledgeSoundnessFailureProb_toNARG, knowledgeSoundnessFailureProb]

/-- The same derived NARG characterization holds for unbounded SR adversaries. -/
theorem knowledgeSoundnessWithExtractor_iff_adaptiveNARGKnowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (error : ENNReal) :
    knowledgeSoundnessWithExtractor init impl relIn relOut V E error ↔
    (toNARGKnowledgeVerifier V).adaptiveNARGKnowledgeSoundnessWithExtractor init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      {a | (a.1.1, a.2) ∈ relIn} relOut
      (toNARGExtractor E) error := by
  rw [Verifier.adaptiveNARGKnowledgeSoundnessWithExtractor_iff]
  unfold knowledgeSoundnessWithExtractor
  simp only [knowledgeSoundnessFailureProb_toNARG]
end Verifier.StateRestoration

namespace Verifier.StateRestoration

/-- SR soundness without a query bound is soundness of the same derived NARG verifier. -/
theorem soundness_iff_adaptiveNARGSoundness
    {ι StmtIn StmtOut Salt : Type} {oSpec : OracleSpec ι}
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (init : ProbComp (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srVerifierMessageOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (error : ENNReal) :
    soundness init impl langIn langOut V error ↔
    (toNARGVerifier V).adaptiveNARGSoundness init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (Prod.fst ⁻¹' langIn) langOut error := by
  rw [Verifier.adaptiveNARGSoundness_iff]
  unfold soundness
  simp only [soundnessFailureProb_toNARG]

end Verifier.StateRestoration

/-! ## Ordinary public-coin state restoration -/

namespace IP

/-- An ordinary public-coin verifier's statement and full transcript determine its final
decision. Both `none` and `some false` mean rejection. -/
abbrev Verifier (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  _root_.Verifier []ₒ Statement Bool pSpec

/-- The empty interface has a unique handler, with no state effects. -/
def emptyImpl {σ : Type} : QueryImpl []ₒ (StateT σ ProbComp) := fun q => nomatch q

/-- An SR adversary returns `((𝕩, τ), α)`: the statement, chosen salt, and prover messages.
It queries the single-salt challenge oracles and uses private coins. The empty summand is
only the generic backend's interface adapter. -/
abbrev SRProver (Statement : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover.StateRestoration.Soundness []ₒ Statement pSpec (Salt := Salt)

/-- An ordinary non-rewinding SR extractor computes `E(𝕩, τ, T, tr_sr)` from the original
statement, chosen salt, final transcript, and SR move-response trace. It may use private coins
and may fail; it receives no prover handle or private sampling log. -/
abbrev SRExtractor (Statement Witness : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Statement → Salt → pSpec.FullTranscript →
    QueryLog (srVerifierMessageOracle (Statement × Salt) pSpec) →
    OptionT ProbComp Witness

/-- Run an ordinary SR adversary and reconstruct its final transcript using the same
verifier-message functions queried during its moves. -/
def srGame {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    OracleComp (([]ₒ + srVerifierMessageOracle (Statement × Salt) pSpec) + unifSpec)
      (pSpec.FullTranscript × (Statement × Salt)) :=
  srSoundnessGame (Salt := Salt) P

/-- The internal reduction output relation for Boolean acceptance has a dummy witness. -/
def acceptRelation : Set (Bool × Unit) := {result | result.1 ∈ ({true} : Set Bool)}

/-- Add the unique dummy witness required by the generic reduction game. -/
def SRProver.toReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    Prover.StateRestoration.KnowledgeSoundness []ₒ Statement Unit pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2, ())) <$> P

/-- Erase the generic game's dummy witness. This does not change any query. -/
def SRProver.ofReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ Statement Unit pSpec (Salt := Salt)) :
    SRProver Statement pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2.1)) <$> P

/-- The dummy output witness carries no information. -/
theorem SRProver.toReduction_ofReduction {Statement Salt : Type} {n : ℕ}
    {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ Statement Unit pSpec (Salt := Salt)) :
    (SRProver.ofReduction P).toReduction = P := by
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  simp only [SRProver.toReduction, SRProver.ofReduction, Functor.map_map]
  have h : (fun result : (Statement × Salt) × pSpec.Messages × Unit =>
      (result.1, result.2.1, ())) = id := by
    funext ⟨x, messages, u⟩
    cases u
    rfl
  rw [h, id_map]

/-- Adapt the ordinary extractor to the general reduction interface. Pass it the statement,
salt, transcript, and SR move-response log, discarding the empty ambient logs and dummy witness. -/
def SRExtractor.toReduction {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) :
    Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt) :=
  fun x salt _ transcript log _ => OptionT.mk
    (liftComp (E x salt transcript log.snd).run ([]ₒ + unifSpec))

section

variable {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srVerifierMessageOracle (Statement × Salt) pSpec) Id))

/-- Extraction failure for an ordinary SR adversary. The dummy witness is introduced only
inside the general backend; the adversary and extractor interfaces do not expose it. -/
noncomputable def srKnowledgeSoundnessFailureProb (relation : Set (Statement × Witness))
    (V : Verifier Statement pSpec) (E : SRExtractor Statement Witness pSpec (Salt := Salt))
    (P : SRProver Statement pSpec (Salt := Salt)) : ENNReal :=
  _root_.Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt) init emptyImpl
    E.toReduction relation acceptRelation V P.toReduction

omit [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The same named ordinary extractor works in the general dummy-witness game. -/
theorem srKnowledgeSoundnessQueryBoundedWithExtractor_to_generic
    (relation : Set (Statement × Witness)) (V : Verifier Statement pSpec)
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) (t : ℕ) (error : ENNReal)
    (h : ∀ P : SRProver Statement pSpec (Salt := Salt),
      P.IsQueryBoundP (publicQuerySelector
        (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt) (oSpec := []ₒ))) t →
      srKnowledgeSoundnessFailureProb (Salt := Salt) init relation V E P ≤ error) :
    _root_.Verifier.StateRestoration.knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt)
      init emptyImpl relation acceptRelation V E.toReduction
      (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)) t error := by
  intro P hP
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  have hBound : (SRProver.ofReduction P).IsQueryBoundP
      (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t := by
    simpa only [SRProver.ofReduction, isQueryBoundP_map_iff] using hP
  have hResult := h (SRProver.ofReduction P) hBound
  unfold srKnowledgeSoundnessFailureProb at hResult
  simp only [SRProver.toReduction_ofReduction] at hResult
  exact hResult

end

section Families

variable {Statement Witness : Type} {Salt : ℕ → ℕ → Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ s n, ProtocolSpec (rounds s n)}
  [∀ s n i, SampleableType ((pSpec s n).Challenge i)]
  [DecidableEq Statement] [∀ s n i, DecidableEq ((pSpec s n).Message i)]
  [∀ s n i, DecidableEq ((pSpec s n).Challenge i)]
  (init : ∀ s n, ProbComp
    (QueryImpl (srVerifierMessageOracle (Statement × Salt s n) (pSpec s n)) Id))
  (V : ∀ s n, Verifier Statement (pSpec s n))

/-- **[snarg-book, state-restoration soundness]** SR soundness for every public salt-size
parameter `s`, instance-size bound `n`, and move budget `t`. The salt carrier and challenge
sampler may depend on `s,n`. Guarding the final decision implements the joint event
`size x ≤ n ∧ x ∉ language ∧ accepted`; it does not condition or truncate the game. -/
def srSoundness (language : Set Statement) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ s n t, _root_.Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt s n)
    (init s n) emptyImpl language {true} ((V s n).restrictSize size n)
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n)) t (error s n t)

/-- The state-restoration bound for a supplied non-rewinding extractor family, for every
salt-size parameter `s`, instance-size bound `n`, move budget, and adversary. The family may
depend on `s` and `n`; no efficiency guarantee is imposed. -/
def srKnowledgeSoundnessWithExtractor (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (E : ∀ s n, SRExtractor Statement Witness (pSpec s n) (Salt := Salt s n))
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ s n t (P : SRProver Statement (pSpec s n) (Salt := Salt s n)),
    P.IsQueryBoundP (publicQuerySelector
      (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n) (oSpec := []ₒ))) t →
    srKnowledgeSoundnessFailureProb (init s n) relation ((V s n).restrictSize size n)
      (E s n) P ≤ error s n t

/-- **[snarg-book, state-restoration knowledge soundness]** One non-rewinding extractor
family satisfies `srKnowledgeSoundnessWithExtractor`. With no resource bound on the
extractor, classical witness selection gives an extractor from soundness for the relation's
language. See `Verifier.knowledgeSoundness_iff_relationSoundness` for this argument in the
ordinary interactive game. -/
def srKnowledgeSoundness (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∃ E, srKnowledgeSoundnessWithExtractor init V relation size E error

end Families

end IP
