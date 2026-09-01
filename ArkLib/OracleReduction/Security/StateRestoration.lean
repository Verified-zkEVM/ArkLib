/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen, Alexander Hicks
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # State-Restoration Security Definitions

  This file defines state-restoration security notions for (oracle) reductions.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type}

namespace Prover

/-- The type for the **state-restoration** prover in the soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, and a full transcript of interaction.

This is different from the state-restoration prover type in the knowledge soundness game, which
additionally needs to output an output witness. -/
def StateRestoration.Soundness (oSpec : OracleSpec ι) (StmtIn : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec + (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages)

/-- The type for the **state-restoration** prover in the knowledge soundness game.

Such a prover has query access to challenge oracles that can return the `i`-th challenge, for all
`i : pSpec.ChallengeIdx`, given the input statement and the transcript up to that point.
It returns an input statement, a full transcript of interaction, and an output witness.

Note that the output witness is an addition compared to the state-restoration soundness prover
type. -/
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι) (StmtIn WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) :=
  OracleComp (oSpec + (srChallengeOracle StmtIn pSpec)) (StmtIn × pSpec.Messages × WitOut)

/-- **Coin-bearing** state-restoration soundness prover.

`Prover.StateRestoration.Soundness` is deterministic given its oracle answers. A *compiled* prover —
e.g. DSFS's `D2SAlgo^f`, which samples during lookahead/backtrack — needs **private coins**.
We model those by appending an extra oracle `auxSpec` after the SR interface `oSpec + chal`,
giving the
**Option A** order `(oSpec + srChallengeOracle …) + auxSpec`.  This is exactly the natural ambient
of a compiled prover `D2SAlgo^f` (`oSpec`, then the challenge oracle, then its sampled coins),
so the coins are answered at game time by a sampler `auxImpl` appended to the standard SR
handler (see
`coinSRExperimentProb`); the verifier never sees `auxSpec`.  Taking `auxSpec := []ₒ` recovers
`Soundness` up to `+ []ₒ`. -/
abbrev StateRestoration.SoundnessWithCoins (oSpec : OracleSpec ι) (StmtIn : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) {κ : Type} (auxSpec : OracleSpec κ) :=
  OracleComp ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec) (StmtIn × pSpec.Messages)

/-- **Coin-bearing** state-restoration knowledge-soundness prover — the KS analog of
`SoundnessWithCoins`, additionally outputting a witness.  Same **Option A** ambient
`(oSpec + srChallengeOracle …) + auxSpec`. -/
abbrev StateRestoration.KnowledgeSoundnessWithCoins (oSpec : OracleSpec ι) (StmtIn WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) {κ : Type} (auxSpec : OracleSpec κ) :=
  OracleComp ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec) (StmtIn × pSpec.Messages × WitOut)

end Prover

namespace OracleProver

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the soundness
  game.

This is a wrapper around the state-restoration prover type in the soundness game for the associated
reduction. -/
@[reducible]
def StateRestoration.Soundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.Soundness oSpec (StmtIn × (∀ i, OStmtIn i)) pSpec

/-- The type for the **state-restoration** oracle prover (in an oracle reduction) in the knowledge
  soundness game.

This is a wrapper around the state-restoration prover type in the knowledge soundness game for the
associated reduction. -/
@[reducible]
def StateRestoration.KnowledgeSoundness (oSpec : OracleSpec ι)
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitOut : Type)
    {n : ℕ} {pSpec : ProtocolSpec n} :=
  Prover.StateRestoration.KnowledgeSoundness oSpec (StmtIn × (∀ i, OStmtIn i)) WitOut pSpec

end OracleProver

namespace Extractor

/-- A straightline extractor for state-restoration.

The extractor is partial: failure to output a witness must count as extraction failure in the
knowledge-soundness game whenever the prover convinces the verifier. -/
def StateRestoration (oSpec : OracleSpec ι)
    (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  StmtIn → -- input statement
  WitOut → -- output witness
  pSpec.FullTranscript → -- transcript
  QueryLog (oSpec + (srChallengeOracle StmtIn pSpec)) → -- prover's query log
  QueryLog oSpec → -- verifier's query log
  OptionT (OracleComp oSpec) WitIn -- an oracle computation that outputs an input witness

end Extractor

variable {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
  (impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))

/-- The state-restoration game for soundness. Basically a wrapper around the state-restoration
  prover to derive the full transcript from the messages output by the prover, with the challenges
  computed from the state-restoration oracle. -/
def srSoundnessGame (P : Prover.StateRestoration.Soundness oSpec StmtIn pSpec) :
    OracleComp (oSpec + (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn) := do
  let ⟨stmtIn, messages⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn⟩

/-- The state-restoration soundness game for a **coin-bearing** prover (Option A ambient
`(oSpec + chal) + auxSpec`). Identical to `srSoundnessGame`, but the prover may sample private coins
`auxSpec`; the transcript derivation (over `oSpec + chal`) is lifted into the coin-extended spec. -/
def srSoundnessGameWithCoins {κ : Type} {auxSpec : OracleSpec κ}
    (P : Prover.StateRestoration.SoundnessWithCoins oSpec StmtIn pSpec auxSpec) :
    OracleComp ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec)
      (pSpec.FullTranscript × StmtIn) := do
  let ⟨stmtIn, messages⟩ ← P
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
    ((oSpec + fsChallengeOracle StmtIn pSpec) + auxSpec)
  return ⟨transcript, stmtIn⟩

/-- The state-restoration game for knowledge soundness. Basically a wrapper around the
    state-restoration prover (for knowledge soundness) to derive the full transcript from the
    messages output by the prover, with the challenges computed from the state-restoration oracle.
-/
def srKnowledgeSoundnessGame
    (P : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec) :
    OracleComp (oSpec + (srChallengeOracle StmtIn pSpec))
      (pSpec.FullTranscript × StmtIn × WitOut) := do
  let ⟨stmtIn, messages, witOut⟩ ← P
  let transcript ← messages.deriveTranscriptSR stmtIn
  return ⟨transcript, stmtIn, witOut⟩

/-- The state-restoration knowledge-soundness game for a **coin-bearing** prover (Option A ambient
`(oSpec + chal) + auxSpec`).  KS analog of `srSoundnessGameWithCoins`. -/
def srKnowledgeSoundnessGameWithCoins {κ : Type} {auxSpec : OracleSpec κ}
    (P : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec auxSpec) :
    OracleComp ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec)
      (pSpec.FullTranscript × StmtIn × WitOut) := do
  let ⟨stmtIn, messages, witOut⟩ ← P
  let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
    ((oSpec + fsChallengeOracle StmtIn pSpec) + auxSpec)
  return ⟨transcript, stmtIn, witOut⟩

namespace Verifier

namespace StateRestoration

/-- State-restoration soundness -/
def soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec,
  Pr[ fun | ⟨stmtIn, some stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn | _ => False
    | do (simulateQ (impl.addLift srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
        <| (do
    let ⟨transcript, stmtIn⟩ ← srSoundnessGame srProver
    let stmtOut ← liftComp (verifier.run stmtIn transcript) _
    return (stmtIn, stmtOut))).run' (← init)
  ] ≤ srSoundnessError

/-- The false-acceptance probability of the coin-bearing SR experiment (Option A) for a *fixed*
prover `srProver`.  The handler is the standard SR handler `impl.addLift srChallengeQueryImpl'` with
the coin sampler appended on the outside (`… .addLift auxImpl`) — answering `oSpec` by `impl`, the
pre-sampled challenge oracle by `srChallengeQueryImpl'`, the prover's private coins `auxSpec` by
`auxImpl`.  The IP verifier lives over base `oSpec` and is lifted into the game spec (it never sees
the coins).  Taking `auxSpec := []ₒ` recovers `srExperimentProb` up to `+ []ₒ`. -/
def coinSRExperimentProb {κ : Type} {auxSpec : OracleSpec κ}
    (auxImpl : QueryImpl auxSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.SoundnessWithCoins oSpec StmtIn pSpec auxSpec) : ENNReal :=
  let gameImpl : QueryImpl ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec)
      (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp) :=
    (impl.addLift srChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)).addLift auxImpl
  Pr[ fun | ⟨stmtIn, some stmtOut⟩ => stmtOut ∈ langOut ∧ stmtIn ∉ langIn | _ => False
    | do (simulateQ gameImpl <| (do
      let ⟨transcript, stmtIn⟩ ← srSoundnessGameWithCoins srProver
      let stmtOut ← liftComp (verifier.run stmtIn transcript) _
      return (stmtIn, stmtOut))).run' (← init)
  ]

/-- **Coin-bearing** state-restoration soundness: identical to `soundness`, but the prover may use
private coins `auxSpec` (answered at game time by the sampler `auxImpl`). The challenge oracle is
still answered by `srChallengeQueryImpl'` (the pre-sampled function in `init`), the IP's shared
oracle by `impl`. Taking `auxSpec := []ₒ` recovers `soundness`. -/
def soundnessWithCoins {κ : Type} (auxSpec : OracleSpec κ)
    (auxImpl : QueryImpl auxSpec ProbComp)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srSoundnessError : ENNReal) : Prop :=
  ∀ srProver : Prover.StateRestoration.SoundnessWithCoins oSpec StmtIn pSpec auxSpec,
    coinSRExperimentProb (init := init) (impl := impl) auxImpl langIn langOut verifier srProver
      ≤ srSoundnessError

/-- State-restoration knowledge soundness (w/ straightline extractor).

The state-restoration extractor returns an `OptionT` computation, so it may fail. We run this
`OptionT` layer explicitly and keep the resulting `Option WitIn` in the game output. Thus,
extractor failure counts as a bad event whenever the state-restoration prover convinces the
verifier, matching the standard knowledge-soundness experiment where the extractor is required
to produce a valid witness on accepting executions.
-/
def knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundness oSpec StmtIn WitOut pSpec,
    Pr[ fun
      | ⟨stmtIn, extractedWitIn?, some stmtOut, witOut⟩ =>
          (∀ extractedWitIn ∈ extractedWitIn?, (stmtIn, extractedWitIn) ∉ relIn) ∧
            (stmtOut, witOut) ∈ relOut
      | _ => False
    | do
      (simulateQ (impl.addLift srChallengeQueryImpl' : QueryImpl _ (StateT _ ProbComp))
          <| (do
            let ⟨transcript, stmtIn, witOut⟩ ← srKnowledgeSoundnessGame srProver
            let stmtOut ← liftComp (verifier.run stmtIn transcript) _
            let extractedWitIn? ← liftM (srExtractor stmtIn witOut transcript default default).run
            return (stmtIn, extractedWitIn?, stmtOut, witOut))).run' (← init)
    ] ≤ srKnowledgeSoundnessError

/-- Coin-bearing SR knowledge-soundness experiment (Option A) for a *fixed* extractor + coin-prover.
The prover lives over the Option-A ambient `(oSpec + chal) + auxSpec` (coins answered by `auxImpl`,
appended to the standard SR handler), but the *straightline* extractor and the verifier live over
**base** `oSpec` (they make no coin queries) and are `liftComp`-ed into the game spec.
This keeps the extractor a base-`oSpec` object — exactly what a downstream FS extractor (DSFS
Construction 6.3) consumes. -/
def coinKSExperimentProb {κ : Type} {auxSpec : OracleSpec κ}
    (auxImpl : QueryImpl auxSpec ProbComp)
    (srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srProver : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec
      auxSpec) : ENNReal :=
  let gameImpl : QueryImpl ((oSpec + srChallengeOracle StmtIn pSpec) + auxSpec)
      (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp) :=
    (impl.addLift srChallengeQueryImpl' :
      QueryImpl (oSpec + srChallengeOracle StmtIn pSpec)
        (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)).addLift auxImpl
  Pr[ relationKSFailEvent relIn relOut
    | do (simulateQ gameImpl <| (do
          let ⟨transcript, stmtIn, witOut⟩ ← srKnowledgeSoundnessGameWithCoins srProver
          let stmtOut ← liftComp (verifier.run stmtIn transcript) _
          let witInOpt ← liftComp (srExtractor stmtIn witOut transcript default default).run _
          return (stmtIn, witInOpt, stmtOut, witOut))).run' (← init)
    ]

/-- **Coin-bearing** SR knowledge soundness (KS analog of `soundnessWithCoins`): there is a
*straightline* (base-`oSpec`) extractor such that every coin-bearing SR-KS prover (over
`oSpec + auxSpec`) has extraction-failure probability ≤ the error.  Taking `auxSpec := []ₒ` recovers
`knowledgeSoundness`. -/
def knowledgeSoundnessWithCoins {κ : Type} (auxSpec : OracleSpec κ)
    (auxImpl : QueryImpl auxSpec ProbComp)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srKnowledgeSoundnessError : ENNReal) : Prop :=
  ∃ srExtractor : Extractor.StateRestoration oSpec StmtIn WitIn WitOut pSpec,
  ∀ srProver : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec StmtIn WitOut pSpec
      auxSpec,
    coinKSExperimentProb (init := init) (impl := impl) auxImpl srExtractor relIn relOut verifier
      srProver ≤ srKnowledgeSoundnessError

end StateRestoration

end Verifier

namespace OracleVerifier



end OracleVerifier

end
