/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Alexander Hicks, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.QueryTracking.QueryLog
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript

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
query the ambient oracles `oSpec`, and draw private samples through `privateSpec`.
The security predicates instantiate `privateSpec` with `unifSpec`. -/
abbrev StateRestoration.Soundness {κ : Type} (oSpec : OracleSpec ι)
    (privateSpec : OracleSpec κ) (StmtIn : Type) {Salt : Type} {n : ℕ}
    (pSpec : ProtocolSpec n) :=
  OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
    ((StmtIn × Salt) × pSpec.Messages)

/-- An SR knowledge-soundness prover returns `((𝕩, τ), α, w_out)`, adding an output witness
`w_out` to the soundness prover's output. It has the same oracle access: verifier-message
queries `ρᵢ ← fᵢ(qᵢ)`, ambient queries to `oSpec`, and private samples through `privateSpec`. -/
abbrev StateRestoration.KnowledgeSoundness {κ : Type} (oSpec : OracleSpec ι)
    (privateSpec : OracleSpec κ) (StmtIn WitOut : Type) {Salt : Type} {n : ℕ}
    (pSpec : ProtocolSpec n) :=
  OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
    ((StmtIn × Salt) × pSpec.Messages × WitOut)

end Prover

namespace Extractor

/-- A non-rewinding SR extractor computes `E(𝕩, τ, w_out, T, tr_P, tr_V)`, producing
an input witness `w_in` or failure `⊥`. Here `T` is the full transcript, `tr_P` records the
prover's ambient queries and SR moves, excluding its `privateSpec` queries. The log `tr_V`
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
  QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp (oSpec + unifSpec)) WitIn -- private sampling and ambient queries

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- Run `((𝕩, τ), α) ← P`, reconstruct `T ← α.deriveTranscriptSR (𝕩, τ)`,
and return `(T, (𝕩, τ))`. Reconstruction queries each verifier-message oracle using the
chosen salt and prover-message prefix. The prover chooses `τ`; the enclosing
experiment interprets its private sampler. The IP verifier later receives only `𝕩` and `T`. -/
def srSoundnessGame {κ : Type} {privateSpec : OracleSpec κ}
    (P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (pSpec.FullTranscript × (StmtIn × Salt)) := do
  let ⟨(stmtIn, salt), messages⟩ ← P
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (stmtIn, salt))
    ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
  return ⟨transcript, (stmtIn, salt)⟩

namespace Verifier

namespace StateRestoration

/-- Run the prover, reconstruct its selected transcript, and evaluate the verifier. The
initial oracle table is drawn from `init`. The prover uses `privateImpl` for private samples. -/
def soundnessExperiment {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    ProbComp (StmtIn × Option StmtOut) :=
  AdaptiveGame.run init
    ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
      privateImpl) srProver
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
def soundnessFailureProb {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    ENNReal :=
  Pr{let result ← soundnessExperiment init impl privateImpl verifier srProver}[
    soundnessFailureEvent langIn langOut result]

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The shared adaptive soundness experiment runs the original SR game and verifier. -/
theorem soundnessFailureProb_eq {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
      soundnessFailureProb init impl privateImpl langIn langOut verifier srProver =
  let experiment : ProbComp (StmtIn × Option StmtOut) := do
    StateT.run' (simulateQ
      (QueryImpl.addLift
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        privateImpl) (do
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

omit [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Reconstruct the transcript, then log the verifier's ambient queries. Reconstruction
uses the same challenge table as the prover and takes place outside the log. -/
def reconstructAndVerifyWithLog {κ : Type} {privateSpec : OracleSpec κ}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (input : StmtIn × Salt) (messages : pSpec.Messages) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (pSpec.FullTranscript × Option StmtOut × QueryLog oSpec) := do
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) input) _
  let (stmtOut, logV) ← liftComp (verifier.run input.1 transcript).run.withQueryLog _
  return (transcript, stmtOut, logV)

omit [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
    [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Run the SR prover, reconstruct `T`, and compute `y ← verifier(𝕩, T)`, returning
`((𝕩, τ), w_out, T, tr_P, y, tr_V)`. The log `tr_P` contains the prover's ambient queries
and SR moves, excluding its `privateSpec` queries. The log `tr_V` records all verifier queries
to `oSpec`. Transcript-reconstruction queries are excluded from both logs. -/
def knowledgeSoundnessProverVerifierExp {κ : Type} {privateSpec : OracleSpec κ}
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    OracleComp ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      ((StmtIn × Salt) × WitOut × pSpec.FullTranscript ×
        QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) ×
        Option StmtOut × QueryLog oSpec) := do
  let ⟨⟨(stmtIn, salt), messages, witOut⟩, proverLog⟩ ← srProver.withQueryLog
  let tr := proverLog.publicQueries
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) (stmtIn, salt))
    ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
  let ⟨stmtOut, tr_V⟩ ←
    liftComp (simulateQ loggingOracle (verifier.run stmtIn transcript).run).run _
  return ((stmtIn, salt), witOut, transcript, tr, stmtOut, tr_V)

/-- After the prover and verifier run, compute `w_in ← E(𝕩, τ, w_out, T, tr_P, tr_V)`.
The prover samples through `privateSpec` with handler `privateImpl`, and the extractor samples
through `unifSpec`. The extractor's public handler exposes only the ambient oracles. -/
def knowledgeSoundnessExperiment {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) :=
  AdaptiveGame.runWithExtractor init
    ((impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)).addLift
      privateImpl)
    (impl.addLift (QueryImpl.id' unifSpec))
    srProver.withQueryLog
    (fun ((input, messages, _), _) => reconstructAndVerifyWithLog verifier input messages)
    (fun (((x, salt), _, witOut), logP) (transcript, _, logV) =>
      srExtractor x salt witOut transcript logP.publicQueries logV)
    (fun ((input, _, witOut), _) (_, stmtOut, _) witIn => (input.1, witIn, stmtOut, witOut))

/-- The SR extraction-failure probability for a fixed prover and extractor:
`Pr[y ≠ ⊥ ∧ (y, w_out) ∈ relOut ∧ (w_in = ⊥ ∨ (𝕩, w_in) ∉ relIn)]`. -/
def knowledgeSoundnessFailureProb {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) : ENNReal :=
  Pr{let result ← knowledgeSoundnessExperiment init impl privateImpl srExtractor verifier srProver}[
    relationKSFailEvent relIn relOut result]

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The shared adaptive extraction experiment exposes the original SR verifier and logs. -/
theorem knowledgeSoundnessFailureProb_eq {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb init impl privateImpl srExtractor relIn relOut verifier
      srProver =
  let experiment : ProbComp (StmtIn × Option WitIn × Option StmtOut × WitOut) := do
    StateT.run' (do
      let ⟨(x, salt), witOut, transcript, tr, stmtOut, trV⟩ ←
        simulateQ (QueryImpl.addLift
          (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
          privateImpl)
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
def isSrChallengeMove : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop
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
  ∀ P : Prover.StateRestoration.Soundness oSpec unifSpec StmtIn pSpec (Salt := Salt),
    soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut verifier P
      ≤ srSoundnessError

/-- SR soundness with error `error` for every prover making at most `t` queries selected by
`queryBoundSelector`. Set the selector to `isSrChallengeMove (Salt := Salt)` for a `t`-move
SR prover. Private samples are excluded from the budget. -/
def soundnessQueryBounded
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (queryBoundSelector : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] (t : ℕ) (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t)
    (soundnessExperiment (Salt := Salt) init impl (QueryImpl.id' unifSpec) verifier)
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
    oSpec unifSpec StmtIn WitOut pSpec (Salt := Salt),
    knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) extractor
      relIn relOut verifier P
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
    (queryBoundSelector : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] (t : ℕ) (error : ENNReal) : Prop :=
  AdaptiveGame.Bounded
    (fun P => P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t)
    (knowledgeSoundnessExperiment (Salt := Salt) init impl (QueryImpl.id' unifSpec)
      extractor verifier)
    (relationKSFailEvent relIn relOut) error

/-- One non-rewinding extractor for all query budgets:
`∃ E, ∀ t, ∀ P with ≤ t selected queries, Pr[valid output ∧ extraction failure] ≤ error t`.
The extractor is fixed before both the budget and prover; `queryBoundSelector` chooses which
non-private prover queries count. As in `knowledgeSoundness`, the extractor may use classical
choice to recover a witness from the input statement. -/
def knowledgeSoundnessQueryBounded
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (queryBoundSelector : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
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
  [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
  (sampler : QueryImpl privateSpec ProbComp)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
private theorem knowledgeSoundnessProverVerifierExp_eq_publicLog
    (V : Verifier oSpec StmtIn StmtOut pSpec) {κ' : Type} {spec : OracleSpec κ'}
    (Q : Prover.StateRestoration.KnowledgeSoundness oSpec spec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessProverVerifierExp (Salt := Salt) V Q = (do
      let ⟨⟨x, messages, witOut⟩, tr⟩ ←
        (fun r : ((StmtIn × Salt) × pSpec.Messages × WitOut) ×
          QueryLog ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + spec) =>
            (r.1, r.2.publicQueries)) <$> Q.withQueryLog
      let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) x) _
      let ⟨stmtOut, trV⟩ ←
        liftComp (V.run x.1 transcript).run.withQueryLog _
      return (x, witOut, transcript, tr, stmtOut, trV)) := by
  simp only [knowledgeSoundnessProverVerifierExp, withQueryLog, bind_map_left]
  rfl

/-- Compiling a custom sampler preserves the SR soundness experiment. -/
theorem soundnessFailureProb_normalizePrivateCoins (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut V
      (normalizePrivateCoins sampler P) =
    soundnessFailureProb (Salt := Salt) init impl sampler langIn langOut V P := by
  simp only [soundnessFailureProb_eq, srSoundnessGame]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_add_liftComp_sum_left,
    simulateQ_add_add_liftComp_left, StateT.run'_bind', StateT.run'_pure', map_bind, map_pure]

/-- Compiling a custom sampler preserves SR extraction, including its public-query log. -/
theorem knowledgeSoundnessFailureProb_normalizePrivateCoins
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) E relIn relOut V
      (normalizePrivateCoins sampler P) =
    knowledgeSoundnessFailureProb (Salt := Salt) init impl sampler E relIn relOut V P := by
  simp only [knowledgeSoundnessFailureProb_eq]
  rw [knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt),
    knowledgeSoundnessProverVerifierExp_eq_publicLog (Salt := Salt)]
  rw [publicQueries_withQueryLog_normalizePrivateCoins]
  simp only [simulateQ_bind, simulateQ_pure]
  simp only [simulateQ_normalizePrivateCoins]
  simp only [QueryImpl.addLift_def, QueryImpl.liftTarget_self, simulateQ_map,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left, bind_map_left, bind_assoc,
    pure_bind, StateT.run'_bind', StateT.run'_pure', map_bind, map_pure]

/-- A standard-coin SR soundness premise covers any private sampler with the same move bound. -/
theorem soundnessQueryBounded_apply_sampler
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t error) :
    ∀ P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt),
      P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t →
      soundnessFailureProb (Salt := Salt) init impl sampler langIn langOut V P ≤ error := by
  classical
  intro P hP
  rw [← soundnessFailureProb_normalizePrivateCoins (Salt := Salt) init impl sampler]
  apply h
  exact hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt))

/-- The same SR extractor works after compilation of any custom private prover sampler. -/
theorem knowledgeSoundnessQueryBoundedWithExtractor_apply_sampler
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (error : ENNReal)
    (h : knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt) init impl relIn relOut V E
      (isSrChallengeMove (Salt := Salt)) t error) :
    ∀ P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt),
      P.IsQueryBoundP
      (publicQuerySelector (isSrChallengeMove (Salt := Salt) (oSpec := oSpec))) t →
      knowledgeSoundnessFailureProb (Salt := Salt) init impl sampler E
        relIn relOut V P ≤ error := by
  classical
  intro P hP
  rw [← knowledgeSoundnessFailureProb_normalizePrivateCoins (Salt := Salt) init impl sampler]
  apply h
  exact hP.normalizePrivateCoins sampler (isSrChallengeMove (Salt := Salt))

end Verifier.StateRestoration

namespace Verifier.StateRestoration

section AmbientSampling

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut Salt : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]

/-- Adding a sampling slot to the ambient interface does not strengthen an SR prover:
its samples can all be routed through the private interface. -/
theorem soundnessFailureProb_mergePrivateCoins
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness (oSpec + unifSpec) unifSpec
      StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      (QueryImpl.id' unifSpec)
      langIn langOut (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut V
      P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) + challenge)
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
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (t : ℕ) (ε : ENNReal)
    (hSR : soundnessQueryBounded (Salt := Salt) init impl langIn langOut V (isSrChallengeMove
      (Salt := Salt)) t ε) :
    soundnessQueryBounded (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec)) langIn langOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) (isSrChallengeMove (Salt := Salt)) t ε := by
  intro P hP
  change soundnessFailureProb init _ _ langIn langOut _ P ≤ ε
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
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.KnowledgeSoundness (oSpec + unifSpec) unifSpec
      StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb (Salt := Salt) init (impl.addLift (QueryImpl.id' unifSpec))
      (QueryImpl.id' unifSpec) (addPrivateCoinsExtractor (Salt := Salt) E) relIn relOut
      (V.liftOracles (targetSpec := oSpec + unifSpec)) P =
    knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) E relIn relOut V
      P.mergeRight := by
  let challenge := srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)
  have htr (x : StmtIn × Salt) (messages : pSpec.Messages) :=
    simulateQ_deriveTranscriptSR_eq
      ((impl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
        (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) + challenge)
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
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
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
  change knowledgeSoundnessFailureProb init _ _ _ relIn relOut _ P ≤ ε
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
    NonInteractiveVerifier pSpec.Messages (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (StmtIn × Salt) StmtOut where
  verify x tr := OptionT.mk do
    let transcript ← (tr 0).deriveTranscriptSR (oSpec := oSpec) x
    liftComp (V.run x.1 transcript).run _

variable [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- The derived NARG experiment preserves the accepted statement and verifier output. -/
theorem soundnessExperiment_toNARG {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    (fun a => a.2.map (a.1, ·)) <$> soundnessExperiment init impl privateImpl V P =
    Option.map (fun a => (a.1.1, a.2)) <$>
      adaptiveNARGSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) privateImpl
        (toNARGVerifier V) P := by
  simp only [soundnessExperiment, adaptiveNARGSoundnessExp, toNARGVerifier,
    AdaptiveGame.run, Fin.cons_zero, OptionT.run_mk, liftComp_bind,
    simulateQ_bind, simulateQ_pure, map_bind, QueryImpl.addLift_def, QueryImpl.liftTarget_self,
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left]
  simp [StateT.run'_eq, map_bind,
    QueryImpl.simulateQ_add_liftM_left, Verifier.run]
  rfl

/-- Forgetting the salt in the failure event gives exactly the SR soundness error. -/
theorem soundnessFailureProb_toNARG {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
    soundnessFailureProb init impl privateImpl langIn langOut V P =
      Pr{let out ← (adaptiveNARGSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) privateImpl
        (toNARGVerifier V) P)}[nargSoundFailEvent (Prod.fst ⁻¹' langIn) langOut out] := by
  have h := congrArg (fun p => Pr{let out ← p}[nargSoundFailEvent langIn langOut out])
    (soundnessExperiment_toNARG init impl privateImpl V P)
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
    (counts : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    soundnessQueryBounded init impl langIn langOut V counts t error ↔
    (toNARGVerifier V).adaptiveNARGSoundnessQueryBounded init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (Prod.fst ⁻¹' langIn) langOut counts t error := by
  unfold soundnessQueryBounded Verifier.adaptiveNARGSoundnessQueryBounded AdaptiveGame.Bounded
  simp only [← soundnessFailureProb_toNARG, soundnessFailureProb]
end Verifier.StateRestoration

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- Include the output witness in the NARG string and return it alongside the verifier output.
This turns the SR output relation into the NARG output language. -/
def toNARGKnowledgeVerifier (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (pSpec.Messages × WitOut)
      (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) (StmtIn × Salt) (StmtOut × WitOut) where
  verify x tr := (fun y => (y, (tr 0).2)) <$>
    (toNARGVerifier V).verify x (Fin.cons (tr 0).1 (fun i => i.elim0))

variable [DecidableEq StmtIn] [DecidableEq Salt]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Inhabited (pSpec.Challenge i)]

/-- Recover the transcript from the verifier's challenge log, without issuing queries.
Only the ambient verifier log is passed to the original named SR extractor. -/
def toNARGExtractor
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt)) :
    (StmtIn × Salt) → (pSpec.Messages × WitOut) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) →
      OptionT (OracleComp (oSpec + unifSpec)) WitIn :=
  fun x proof logP logV => E x.1 x.2 proof.2
    (FullTranscript.ofMessagesChallenges proof.1 (proof.1.challengesOfLog x logV.snd))
    logP logV.fst

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
          (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
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
    (logP : QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
    (logV : QueryLog oSpec) :
    toNARGExtractor E x proof logP
      (QueryLog.inr (canonChalLog x proof.1 ⟨n, Nat.lt_succ_self n⟩ cs) ++ QueryLog.inl logV) =
      E x.1 x.2 proof.2
        (FullTranscript.ofMessagesChallenges proof.1
          (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)) logP logV := by
  simp [toNARGExtractor, QueryLog.snd_append, QueryLog.fst_append,
    Messages.challengesOfLog_canonChalLog]

variable [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- The derived NARG experiment preserves extraction and the accepted output-witness pair. -/
theorem knowledgeSoundnessExperiment_toNARG {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    (fun a => (a.1, a.2.1, a.2.2.1.map (·, a.2.2.2))) <$>
      knowledgeSoundnessExperiment init impl privateImpl E V P =
    (fun a => (a.1.1, a.2)) <$>
      adaptiveNARGKnowledgeSoundnessExp init
        (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
        privateImpl (impl.addLift (QueryImpl.id' unifSpec))
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
    simulateQ_add_liftComp_sum_left, simulateQ_add_add_liftComp_left]
  simp [hDerive, QueryImpl.simulateQ_add_liftM_left,
    StateT.run'_eq, map_bind]
end Verifier.StateRestoration

namespace Verifier.StateRestoration
variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [DecidableEq StmtIn] [DecidableEq Salt]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Inhabited (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
  (impl : QueryImpl oSpec (StateT
    (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))

/-- SR extraction failure is the derived NARG failure event, with exactly the same named
extractor execution. Reconstruction uses only the logged answers. -/
theorem knowledgeSoundnessFailureProb_toNARG {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) :
    knowledgeSoundnessFailureProb init impl privateImpl E relIn relOut V P =
    Pr{let out ← (adaptiveNARGKnowledgeSoundnessExp init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      privateImpl (impl.addLift (QueryImpl.id' unifSpec))
      (toNARGKnowledgeVerifier V) (toNARGExtractor E) P)}[
        nargKSFailEvent {a | (a.1.1, a.2) ∈ relIn} relOut out] := by
  have h := congrArg (fun p => Pr{let out ← p}[nargKSFailEvent relIn relOut out])
    (knowledgeSoundnessExperiment_toNARG init impl privateImpl V E P)
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
    (counts : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred counts] (t : ℕ) (error : ENNReal) :
    knowledgeSoundnessQueryBoundedWithExtractor init impl relIn relOut V E counts t error ↔
    (toNARGKnowledgeVerifier V).adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (impl.addLift (QueryImpl.id' unifSpec)) {a | (a.1.1, a.2) ∈ relIn} relOut
      (toNARGExtractor E) counts t error := by
  unfold knowledgeSoundnessQueryBoundedWithExtractor
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBoundedWithExtractor AdaptiveGame.Bounded
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
      (impl.addLift (QueryImpl.id' unifSpec)) {a | (a.1.1, a.2) ∈ relIn} relOut
      (toNARGExtractor E) error := by
  unfold knowledgeSoundnessWithExtractor Verifier.adaptiveNARGKnowledgeSoundnessWithExtractor
  simp only [knowledgeSoundnessFailureProb_toNARG]
end Verifier.StateRestoration

namespace Verifier.StateRestoration

/-- SR soundness without a query bound is soundness of the same derived NARG verifier. -/
theorem soundness_iff_adaptiveNARGSoundness
    {ι StmtIn StmtOut Salt : Type} {oSpec : OracleSpec ι}
    {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
    (init : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (impl : QueryImpl oSpec (StateT
      (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (V : Verifier oSpec StmtIn StmtOut pSpec) (error : ENNReal) :
    soundness init impl langIn langOut V error ↔
    (toNARGVerifier V).adaptiveNARGSoundness init
      (impl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      (Prod.fst ⁻¹' langIn) langOut error := by
  unfold soundness Verifier.adaptiveNARGSoundness
  simp only [soundnessFailureProb_toNARG]

end Verifier.StateRestoration
