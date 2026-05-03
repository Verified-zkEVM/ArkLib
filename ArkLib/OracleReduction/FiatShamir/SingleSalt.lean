/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.Basic

/-!
  # The Single-Salt Fiat-Shamir Transformation (CO25 Construction 3.17)

  This file defines the *single-salt* Fiat-Shamir transformation. This is a generic transformation
  on a (public-coin) interactive reduction (IR) `R` that:

  - Has the prover sample a public salt `τ ∈ Salt^δ` once at the start of the protocol.
  - Includes `τ` in the non-interactive proof.
  - Prefixes every Fiat-Shamir oracle query with `τ` by augmenting the statement type to
    `Vector Salt δ × StmtIn`. Concretely, the salted oracle is
    `fsChallengeOracle (Vector Salt δ × StmtIn) pSpec`.

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
Salted single-salt Fiat-Shamir proof: pair of a public salt vector and the prover's messages.
-/
abbrev FSSaltedProof (pSpec : ProtocolSpec n) (Salt : Type) (δ : Nat) :=
  Vector Salt δ × (∀ i, pSpec.Message i)

/--
Prover's per-round step for the single-salt Fiat-Shamir transformation.

This is the salted analog of `Prover.processRoundFS`: each Fiat-Shamir query is keyed by the
augmented statement `(salt, stmtIn)` instead of just `stmtIn`. The inner prover state is threaded
through unchanged.
-/
@[inline, specialize]
def Prover.processRoundFSSalted {Salt : Type} [VCVCompatible Salt] {δ : Nat} (j : Fin n)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (currentResult : OracleComp (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
      (pSpec.MessagesUpTo j.castSucc ×
        (Vector Salt δ × StmtIn) × prover.PrvState j.castSucc)) :
      OracleComp (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
        (pSpec.MessagesUpTo j.succ ×
          (Vector Salt δ × StmtIn) × prover.PrvState j.succ) := do
  let ⟨messages, augStmt, state⟩ ← currentResult
  match hDir : pSpec.dir j with
  | .V_to_P => do
    let f ← prover.receiveChallenge ⟨j, hDir⟩ state
    let challenge ← query (spec := fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
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
def Prover.runToRoundFSSalted {Salt : Type} [VCVCompatible Salt] {δ : Nat}
    (salt : Vector Salt δ) (i : Fin (n + 1))
    (stmt : StmtIn) (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (state : prover.PrvState 0) :
        OracleComp (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
          (pSpec.MessagesUpTo i × (Vector Salt δ × StmtIn) × prover.PrvState i) :=
  Fin.induction
    (pure ⟨default, ⟨salt, stmt⟩, state⟩)
    prover.processRoundFSSalted
    i

/--
Single-salt Fiat-Shamir transformation for the prover (CO25 Construction 3.17 prover surface).

The prover samples a salt `τ ← sampleSalt stmtIn state`, then runs the underlying interactive
prover with all FS queries keyed by the augmented statement `(τ, stmtIn)`, and packages the salt
together with the produced messages as the non-interactive proof.
-/
def Prover.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt] (δ : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → P.PrvState 0 →
      OracleComp (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
        (Vector Salt δ)) :
    NonInteractiveProver (FSSaltedProof pSpec Salt δ)
      (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
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
def Verifier.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt] (δ : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (FSSaltedProof pSpec Salt δ)
      (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
      StmtIn StmtOut where
  verify := fun stmtIn proof => do
    let saltedProof : FSSaltedProof pSpec Salt δ := proof 0
    let salt : Vector Salt δ := saltedProof.1
    let messages : pSpec.Messages := saltedProof.2
    let transcript ←
      messages.deriveTranscriptFS (oSpec := oSpec) (StmtIn := Vector Salt δ × StmtIn)
        (salt, stmtIn)
    Option.getM (← (V.verify stmtIn transcript).run)

/--
Single-salt Fiat-Shamir transformation for an (interactive) reduction (CO25 Construction 3.17),
combining the salted prover and verifier surfaces.
-/
def Reduction.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt] (δ : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : (stmt : StmtIn) → R.prover.PrvState 0 →
      OracleComp (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
        (Vector Salt δ)) :
    NonInteractiveReduction (FSSaltedProof pSpec Salt δ)
      (oSpec + fsChallengeOracle (Vector Salt δ × StmtIn) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.singleSaltFiatShamir (δ := δ) sampleSalt
  verifier := R.verifier.singleSaltFiatShamir (δ := δ)
