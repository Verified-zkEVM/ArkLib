/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orru
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration

/-!
  # The Single-Salt Fiat-Shamir Transformation (CO25 Construction 3.17)

  This file defines the *single-salt* Fiat-Shamir transformation. This is a generic transformation
  on a (public-coin) interactive reduction (IR) `R` that:

  - Has the prover sample a public salt `τ : Salt` once at the start of the protocol.
  - Includes `τ` in the non-interactive proof.
  - Prefixes every Fiat-Shamir oracle query with `τ` by augmenting the statement type to
    `StmtIn × Salt`. Concretely, the salted oracle is
    `fsChallengeOracle (StmtIn × Salt) pSpec`.

  Here `Salt` is an abstract pre-encoded salt type. In the paper, salts live in `{0,1}^{δ★}`
  (the binary-string side). The duplex-sponge instantiation (CO25 Construction 4.3) connects an
  on-sponge `Vector U δ` salt to this `Salt` via an injective encoding (`SaltCodec` in
  `FiatShamir/DuplexSponge/Defs.lean`).

  This is the generic (oracle-style) analog of CO25 Construction 4.3, which instantiates the
  generic salted construction via a duplex sponge. The duplex-sponge variant lives in
  `FiatShamir/DuplexSponge/Defs.lean` (see `Reduction.duplexSpongeFiatShamirSalted`).

  The unsalted basic version is in `FiatShamir/Basic.lean` (see `Reduction.fiatShamir`).
-/

open ProtocolSpec OracleComp OracleSpec

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/--
Salted single-salt Fiat-Shamir proof: pair of a public salt and the prover's messages.
-/
abbrev FSSaltedProof (pSpec : ProtocolSpec n) (Salt : Type) :=
  Salt × pSpec.Messages

/-- Paper-faithful type of the FS-standard salted verifier `𝒱_std^f`
(`\mathcal{V}_{\mathsf{std}}^f`), per CO25 Construction 3.17.

`𝒱_std^f` consumes salted proofs `(τ, π) : FSSaltedProof pSpec Salt` and queries a single
**Fiat-Shamir challenge oracle** `f := fsChallengeOracle (StmtIn × Salt) pSpec` keyed at the
augmented statement `(stmtIn, τ)`. The salt `τ : Salt` is paper-side `{0,1}^{δ★}` — the
abstract pre-encoded salt type bridged from on-sponge `Vector U δ` via `SaltCodec.encode = bin`
at the DS→FS boundary.

Constructed from a base interactive `Verifier` via `Verifier.singleSaltFiatShamir`. Used in
Lemma 5.1 (`KeyLemma.lean`) and §5.8 hybrids `Hyb_0 .. Hyb_4` as the FS-standard reference
verifier whose query trace `tr_𝒱` is mapped to/from the DSFS trace via `D2STrace`
(line 4 trace map). -/
abbrev FSStdSaltedVerifier {n : ℕ} {ι : Type} (oSpec : OracleSpec ι) (pSpec : ProtocolSpec n)
    (StmtIn StmtOut Salt : Type) :=
  NonInteractiveVerifier (FSSaltedProof pSpec Salt)
    (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
    StmtIn StmtOut

/--
Prover's per-round step for the single-salt Fiat-Shamir transformation.

This is the salted analog of `Prover.processRoundFS`: each Fiat-Shamir query is keyed by the
augmented statement `(stmtIn, salt)` instead of just `stmtIn`. The inner prover state is threaded
through unchanged.
-/
@[inline, specialize]
def Prover.processRoundFSSalted {Salt : Type} [VCVCompatible Salt] (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      (pSpec.MessagesUpTo j.castSucc ×
        (StmtIn × Salt) × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
        (pSpec.MessagesUpTo j.succ ×
          (StmtIn × Salt) × prover.PrvState j.succ) := do
  let ⟨messages, augStmt, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsChallengeOracle (StmtIn × Salt) pSpec)
                      ⟨⟨j, hDir⟩, ⟨augStmt, messages⟩⟩
    return ⟨messages.extend hDir, augStmt, f challenge⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, augStmt, newState⟩

/--
Run the prover up to round `i` under the single-salt Fiat-Shamir transformation, given an
explicit salt `τ`.
-/
@[inline, specialize]
def Prover.runToRoundFSSalted {Salt : Type} [VCVCompatible Salt]
    (salt : Salt) (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
          (pSpec.MessagesUpTo i × (StmtIn × Salt) × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, ⟨stmt, salt⟩, state⟩)
    prover.processRoundFSSalted
    i

/--
Single-salt Fiat-Shamir transformation for the prover (CO25 Construction 3.17 prover surface).

The prover samples a salt `τ ← sampleSalt stmtIn state`, then runs the underlying interactive
prover with all FS queries keyed by the augmented statement `(τ, stmtIn)`, and packages the salt
together with the produced messages as the non-interactive proof.
-/
def Prover.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → P.PrvState 0 →
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
        Salt) :
    NonInteractiveProver (FSSaltedProof pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let salt ← sampleSalt stmtIn state
    let ⟨messages, _, state⟩ ←
      P.runToRoundFSSalted (salt := salt) (Fin.last n) stmtIn state
    return ⟨(salt, messages), state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/--
Single-salt Fiat-Shamir transformation for the verifier (CO25 Construction 3.17 verifier
surface).

The verifier reads the salt `τ` and messages from the proof, then derives the transcript by
querying the FS oracle keyed at the augmented statement `(τ, stmtIn)`.
-/
def Verifier.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    FSStdSaltedVerifier oSpec pSpec StmtIn StmtOut Salt where
  verify := fun stmtIn proof => do
    let saltedProof : FSSaltedProof pSpec Salt := proof 0
    let salt : Salt := saltedProof.1
    let messages : pSpec.Messages := saltedProof.2
    let transcript ←
      messages.deriveTranscriptFS (oSpec := oSpec) (StmtIn := StmtIn × Salt)
        (stmtIn, salt)
    Option.getM (← (V.verify stmtIn transcript).run)

/--
Single-salt Fiat-Shamir transformation for an (interactive) reduction (CO25 Construction 3.17),
combining the salted prover and verifier surfaces.
-/
def Reduction.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → R.prover.PrvState 0 →
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
        Salt) :
    NonInteractiveReduction (FSSaltedProof pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.singleSaltFiatShamir sampleSalt
  verifier := R.verifier.singleSaltFiatShamir

/-!
## Security theorems for the single-salt Fiat-Shamir transformation (CO25 §3.5)

Theorems 3.18 and 3.19 are the **FS-transform lifting theorems** (Seam #2 in the DSFS proof
chain). They show that SR soundness/KS of the IP `saltedIPVerifier V` implies basic
soundness/KS of `Verifier.singleSaltFiatShamir V` in the random-oracle model.

The FS ROM state is `σ = QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id` — a
pre-sampled oracle function (note: `srChallengeOracle = fsChallengeOracle` by alias).
The full FS impl decomposes as `fsImpl.addLift srChallengeQueryImpl'`, where `fsImpl` handles
base `oSpec` queries and `srChallengeQueryImpl'` reads FS-oracle responses from state.
-/

section SingleSaltSecurity

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]

/-- Lift the IP verifier `V` to accept `StmtIn × Salt` by ignoring the salt component.

The SR challenge oracle for this lifted verifier is `srChallengeOracle (StmtIn × Salt) pSpec`,
which equals `fsChallengeOracle (StmtIn × Salt) pSpec` by alias. -/
def saltedIPVerifier {Salt : Type} (V : Verifier oSpec StmtIn StmtOut pSpec) :
    Verifier oSpec (StmtIn × Salt) StmtOut pSpec where
  -- NOTE: once the salt are used in oracle queries (`StmtIn × Salt` is the input statement) to
  -- generate the transcript, the IP/IOP verifier's `verify` method doesn't need it anymore,
  -- the salt's role is to randomize the oracle queries to add zero-knowledge and the verifier
  -- isn't necessarily aware of zero-knowledge
  verify := fun ⟨stmtIn, _⟩ transcript => V.verify stmtIn transcript

/-- Lift a soundness language `langIn : Set StmtIn` to `Set (StmtIn × Salt)`,
ignoring the salt. -/
def langInSalted {Salt : Type} (langIn : Set StmtIn) : Set (StmtIn × Salt) :=
  {p | p.1 ∈ langIn}

/-- Lift an input relation `relIn : Set (StmtIn × WitIn)` to
`Set ((StmtIn × Salt) × WitIn)`, ignoring the salt. -/
def relInSalted {Salt : Type} (relIn : Set (StmtIn × WitIn)) : Set ((StmtIn × Salt) × WitIn) :=
  {p | ⟨p.1.1, p.2⟩ ∈ relIn}

set_option linter.unusedDecidableInType false

/-- The single-salt FS verifier run as a NARG `verify` (CO25 `V_std^f(x,·)`): build the
single-message transcript from the FS proof and run `Verifier.singleSaltFiatShamir V`.  Shared by
the FS NARG soundness/KS statements (Thm 3.18/3.19) and the DSFS `Hyb₄` game-match so they refer to
the *same* verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → FSSaltedProof pSpec Salt →
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) StmtOut :=
  fun stmtIn proof =>
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify stmtIn
      (Fin.cons proof (fun i => i.elim0))

/-- `Verifier.singleSaltFiatShamir`'s `verify` on the length-1 transcript `Fin.cons π 0` is, by
definition, the bare FS-NARG `verify` map `fsSaltedVerify V x π`.  Bridges the NIV-shaped
`adaptiveNARG*Exp init impl (Verifier.singleSaltFiatShamir V)` experiments back to the
`fsSaltedVerify`-shaped §6.1/§6.2 game-match proofs (`simp only [fsSaltedNIV_verify]` after unfolding
the experiment restores the `fsSaltedVerify`-form goal). -/
theorem fsSaltedNIV_verify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify x (Fin.cons π (fun i => i.elim0))
      = fsSaltedVerify V x π :=
  rfl

/-- The SR prover induced by a coin-bearing single-salt FS prover: it only repackages the
statement, salt, and message tuple. -/
def srInducedProver {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Prover.StateRestoration.SoundnessWithCoins oSpec (StmtIn × Salt) pSpec auxSpec := do
  let ⟨x, proof⟩ ← P
  return ⟨(x, proof.1), proof.2⟩

/-- The induced SR prover is a pure map of its source prover. -/
lemma srInducedProver_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    srInducedProver (Salt := Salt) P = (fun p => ((p.1, p.2.1), p.2.2)) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- CO25 Theorem 3.18 — Single-salt FS soundness from IP SR-soundness.

If `saltedIPVerifier V` has state-restoration soundness (for `langInSalted langIn`) with error
`ε`, then `Verifier.singleSaltFiatShamir V` has basic soundness in the ROM with error `ε`.

**Proof sketch**: each FS malicious prover is converted to an SR prover by replacing its
`fsChallengeOracle` queries with SR oracle queries against the same pre-sampled function.
The FS verifier's `deriveTranscriptFS` call and the SR game's `deriveTranscriptSR` call are
identical (same oracle, same keys: `srChallengeOracle = fsChallengeOracle` by alias).
**Open seam**: body is `sorry` — used as Seam #2 in `Soundness.lean` (Theorem 6.1). -/
theorem theorem_3_18_soundness
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (auxSpec : OracleSpec κ) (auxImpl : QueryImpl auxSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (srBound : Prover.StateRestoration.SoundnessWithCoins oSpec (StmtIn × Salt) pSpec
      auxSpec → Prop)
    (bound : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt) → Prop)
    (hBound : ∀ P, bound P → srBound (srInducedProver P))
    (ε : ENNReal)
    -- Coin-bearing SR soundness of the salted IP (the compiled FS prover may use private coins).
    (h_sr : Verifier.StateRestoration.soundnessWithCoins fsInit fsImpl auxSpec auxImpl
        (langInSalted (Salt := Salt) langIn) langOut (saltedIPVerifier (Salt := Salt) V)
        srBound ε) :
    -- CO25 Def 3.5 (adaptive, coin-bearing NARG soundness) of the single-salt FS argument,
    -- phrased as a property of the NARG verifier `Verifier.singleSaltFiatShamir V`.
    Verifier.adaptiveNARGSoundnessWithCoins
      (init := fsInit) (impl := fsImpl.addLift srChallengeQueryImpl')
      auxImpl
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      langIn langOut (bound := bound) ε := by
  -- FS↔SR crosswalk: salted FS NARG game ≡ IP SR game (`fsChallengeOracle = srChallengeOracle`,
  -- `deriveTranscriptFS = deriveTranscriptSR`) up to prover-spec regroup; coins carry through.
  sorry

/-- The SR-KS prover induced by a coin-bearing single-salt FS KS prover: it only repackages its
output statement, salt, messages, and claimed output witness. -/
def srInducedProverKS {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt × WitOut)) :
    Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) WitOut pSpec
      auxSpec := do
  let ⟨x, proof, witOut⟩ ← P
  return ⟨(x, proof.1), proof.2, witOut⟩

/-- The induced SR-KS prover is a pure map of its source prover. -/
lemma srInducedProverKS_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt × WitOut)) :
    srInducedProverKS (Salt := Salt) P
      = (fun p => ((p.1, p.2.1.1), p.2.1.2, p.2.2)) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- CO25 Theorem 3.19 — Single-salt FS straightline KS from IP SR-KS.

If `saltedIPVerifier V` has state-restoration knowledge soundness (for `relInSalted relIn`)
with error `ε`, then `Verifier.singleSaltFiatShamir V` has straightline KS in the ROM with
error `ε`.

**Proof sketch**: given the SR extractor `E_SR` from `h_sr_ks`, the FS straightline extractor
(1) extracts `(τ, messages)` from the FS proof, (2) filters the FS query log to reconstruct
the IP SR query log, and (3) calls `E_SR (stmtIn, τ) witOut ip_transcript ip_log`.
**Open seam**: body is `sorry` — used as Seam #2 in `Soundness.lean` (Theorem 6.2). -/
theorem theorem_3_19_straightline_ks
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (auxSpec : OracleSpec κ) (auxImpl : QueryImpl auxSpec ProbComp)
    -- The extractor's own helper/sampler oracle (`P`-independent), generic so the caller picks it
    -- (DSFS passes `(Unit →ₒ U)` for Construction 6.3's D2STrace; the bare FS extractor ignores it).
    {κE : Type} (auxSpecE : OracleSpec κE) (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (srBound : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) WitOut
      pSpec auxSpec → Prop)
    (bound : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt × WitOut) → Prop)
    (hBound : ∀ P, bound P → srBound (srInducedProverKS P))
    (ε : ENNReal)
    -- Coin-bearing SR knowledge soundness of the salted IP.
    (h_sr_ks : Verifier.StateRestoration.knowledgeSoundnessWithCoins fsInit fsImpl auxSpec auxImpl
        (relInSalted (Salt := Salt) relIn) relOut (saltedIPVerifier (Salt := Salt) V)
        srBound ε) :
    -- CO25 Def 3.6 (adaptive, coin-bearing straightline KS) of the single-salt FS argument,
    -- phrased as a property of the NARG verifier `Verifier.singleSaltFiatShamir V`.
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins (WitIn := WitIn) (WitOut := WitOut)
      (init := fsInit) (impl := fsImpl.addLift srChallengeQueryImpl')
      auxImpl auxImplE
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      relIn relOut (bound := bound) ε := by
  -- FS↔SR crosswalk for KS: SR straightline extractor ⇒ FS straightline extractor (Construction
  -- 3.19); transcripts coincide by alias; coins carry through.
  sorry

end SingleSaltSecurity
