/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Alexander Hicks, Michele Orrù, Yuxi Zheng
-/
module

public import ArkLib.OracleReduction.Security.Basic

/-!
# State-Restoration Security Definitions

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

/-- The SR false-acceptance probability for a fixed prover:
`Pr[𝕩 ∉ langIn ∧ y ≠ ⊥ ∧ y ∈ langOut]`.
Run the prover, reconstruct its selected transcript `T`, and evaluate `y ← verifier(𝕩, T)`.
The verifier uses `oSpec`; the prover additionally uses the verifier-message oracles and
`privateSpec`, whose sampler is `privateImpl`. The initial oracle table is drawn from `init`. -/
def soundnessFailureProb {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt)) :
      ENNReal :=
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
    | _ => False]

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

/-- The SR extraction-failure probability for a fixed prover and extractor:
`Pr[y ≠ ⊥ ∧ (y, w_out) ∈ relOut ∧ (w_in = ⊥ ∨ (𝕩, w_in) ∉ relIn)]`.
After the prover and verifier run, compute `w_in ← E(𝕩, τ, w_out, T, tr_P, tr_V)`.
The prover samples through `privateSpec` with handler `privateImpl`; the extractor samples
through `unifSpec`. Both may query `oSpec`, but only the prover and transcript reconstruction
directly query the verifier-message oracles. -/
def knowledgeSoundnessFailureProb {κ : Type} {privateSpec : OracleSpec κ}
    (privateImpl : QueryImpl privateSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec (Salt := Salt))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn WitOut pSpec (Salt := Salt)) : ENNReal :=
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
  Pr{let result ← experiment}[relationKSFailEvent relIn relOut result]

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
  ∀ P : Prover.StateRestoration.Soundness oSpec unifSpec StmtIn pSpec (Salt := Salt),
    P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t →
      soundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) langIn langOut
        verifier P ≤ error

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
  ∀ P : Prover.StateRestoration.KnowledgeSoundness
    oSpec unifSpec StmtIn WitOut pSpec (Salt := Salt),
    P.IsQueryBoundP (publicQuerySelector queryBoundSelector) t →
      knowledgeSoundnessFailureProb (Salt := Salt) init impl (QueryImpl.id' unifSpec) extractor
      relIn relOut verifier P
        ≤ error

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
