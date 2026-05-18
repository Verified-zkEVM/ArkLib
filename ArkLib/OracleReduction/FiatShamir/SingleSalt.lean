/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic

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
