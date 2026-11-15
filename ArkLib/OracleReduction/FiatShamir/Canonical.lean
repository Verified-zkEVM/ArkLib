/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Quang Dao
-/
module

public import ArkLib.OracleReduction.FiatShamir.Basic
public import ArkLib.InteractiveProof.StateRestorationSoundness
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
public import VCVio.OracleComp.Coercions.SubSpec.Routing
public import ToMathlib.Control.OptionT

/-!
# Canonical Fiat-Shamir with one fixed-length salt ([CO25, Construction 3.17])

This file defines the canonical Fiat-Shamir transformation, parameterized by salt length. This is
a generic transformation
on a (public-coin) interactive reduction (IR) `R` that:

- Has the prover sample a public salt `τ : Salt` once at the start of the protocol.
- Includes `τ` in the NARG string.
- Prefixes every Fiat-Shamir oracle query with separate salt context `(stmtIn, τ)`. Concretely,
  the salted oracle is
  `fsChallengeOracle (StmtIn × Salt) pSpec`.

The public `fiatShamirSalted` constructors use `Vector U saltLength`. The abstract `Salt` compiler
is an internal encoding adapter used by security proofs; its application statement types stay
unchanged. Here `Salt` is an abstract pre-encoded salt type. In the paper, salts live in
`{0,1}^{δ★}`
(the binary-string side). The duplex-sponge instantiation ([CO25, Construction 4.4]) connects an
on-sponge `Vector U δ` salt to this `Salt` via an injective encoding (`SaltCodec` in
`FiatShamir/DuplexSponge/Defs.lean`).

This is the generic (oracle-style) analog of [CO25, Construction 4.4], which instantiates the
generic salted construction via a duplex sponge. The duplex-sponge variant lives in
`FiatShamir/DuplexSponge/Defs.lean` (see `Reduction.duplexSpongeFiatShamir`).

Length zero is the empty-salt instance of this same canonical transformation.
`FiatShamir/Basic.lean` contains shared state-restoration execution helpers only.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open ProtocolSpec OracleComp OracleSpec OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]

/--
Canonical Fiat-Shamir NARG string: pair of a public salt and the prover's messages.
-/
abbrev FSSaltedNARGString (pSpec : ProtocolSpec n) (Salt : Type) :=
  Salt × pSpec.Messages

/--
Prover's per-round step for the canonical Fiat-Shamir transformation.

This is the salted analog of `Prover.processRoundFS`: each Fiat-Shamir query is keyed by the
context `(stmtIn, salt)` instead of just `stmtIn`. The inner prover state is threaded through
unchanged.
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
    let verifierMessage ← query (spec := fsChallengeOracle (StmtIn × Salt) pSpec)
                      ⟨⟨j, hDir⟩, ⟨augStmt, messages⟩⟩
    return ⟨messages.extend hDir, augStmt, f verifierMessage⟩
  | .P_to_V => do
    let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
    return ⟨messages.concat hDir msg, augStmt, newState⟩

/--
Run the prover up to round `i` under the canonical Fiat-Shamir transformation, given an
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
Canonical Fiat-Shamir transformation for the prover ([CO25, Construction 3.17] prover surface).

The prover samples a salt `τ ← sampleSalt` using only the ambient oracle `oSpec`, then runs the
underlying interactive prover with all FS queries keyed by the context `(stmtIn, τ)`,
and packages the salt together with the produced messages as the NARG string. The sampler
cannot inspect the statement, witness-bearing prover state, or Fiat–Shamir table.

Adapted from **[snarg-book, Construction 14.1.1]**, which salts every round; here a single salt
is sampled once and keys all rounds.
-/
def Prover.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveProver (Message := FSSaltedNARGString pSpec Salt)
      (oSpec := oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => match i with
    | 0 => StmtIn × P.PrvState 0
    | _ => P.PrvState (Fin.last n)
  input := fun ctx => ⟨ctx.1, P.input ctx⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmtIn, state⟩ => do
    let salt ← sampleSalt
    let ⟨messages, _, state⟩ ←
      P.runToRoundFSSalted (salt := salt) (Fin.last n) stmtIn state
    return ⟨(salt, messages), state⟩
  -- This function is never invoked so we apply the elimination principle
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun st => (P.output st).liftComp _

/--
Canonical Fiat-Shamir transformation for the verifier ([CO25, Construction 3.17] verifier
surface).

The verifier reads the salt `τ` and messages from the NARG string, then derives the transcript by
querying the FS oracle keyed at the context `(stmtIn, τ)`.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Verifier.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (FSSaltedNARGString pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) StmtIn StmtOut where
  verify := fun stmtIn nargString => do
    let saltedNARGString : FSSaltedNARGString pSpec Salt := nargString 0
    let salt : Salt := saltedNARGString.1
    let messages : pSpec.Messages := saltedNARGString.2
    let transcript ←
      messages.deriveTranscriptFS (oSpec := oSpec) (StmtIn := StmtIn × Salt)
        (stmtIn, salt)
    Option.getM (← (V.verify stmtIn transcript).run)

/--
Canonical Fiat-Shamir transformation for an (interactive) reduction ([CO25, Construction 3.17]),
combining the salted prover and verifier surfaces.
Adapted from **[snarg-book, Construction 14.1.1]** (single salt instead of per-round salts).
-/
def Reduction.compileFiatShamir {Salt : Type} [VCVCompatible Salt]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveReduction (FSSaltedNARGString pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.compileFiatShamir sampleSalt
  verifier := R.verifier.compileFiatShamir

/-- The single-salt FS verifier run as a NARG `verify` (CO25 `V_std^f(x,·)`): build the
single-message transcript from the FS NARG string and run `Verifier.compileFiatShamir V`. Used by
the DSFS Section 5 `Hyb₄`/basic-FS game so both games refer to the same verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → FSSaltedNARGString pSpec Salt →
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) StmtOut :=
  fun stmtIn nargString =>
    (Verifier.compileFiatShamir (Salt := Salt) V).verify stmtIn
      (Fin.cons nargString (fun i => i.elim0))

/-- Canonical Fiat-Shamir NARG metadata: one fixed-length salt and the unchanged message family.
The salt is not part of the application statement, witness, relation, or interactive messages. -/
abbrev FiatShamirNARGString (pSpec : ProtocolSpec n) (U : Type) (saltLength : Nat) :=
  FSSaltedNARGString pSpec (Vector U saltLength)

/-- Canonical FS keys use separate salt context. The paired context here is a random-oracle key,
not an augmented application statement or relation. -/
abbrev ProtocolSpec.canonicalFSOracle (StmtIn : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (U : Type) (saltLength : Nat) :=
  fsChallengeOracle (StmtIn × Vector U saltLength) pSpec

/-- Canonical Fiat-Shamir prover. Sample one salt of the configured length using only the ambient
oracle, then reuse it in every verifier-message query. Fresh uniform private salt randomness is
required by the ZK experiment. Length zero uses the same construction with an empty salt. -/
def Prover.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveProver (FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  P.compileFiatShamir sampleSalt

/-- Canonical Fiat-Shamir verifier, taking salt metadata separately from the original messages. -/
def Verifier.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    NonInteractiveVerifier (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn StmtOut :=
  V.compileFiatShamir

/-- Canonical Fiat-Shamir transformation with one salt of fixed length per NARG string.
The abstract-salt compiler below is an internal encoding adapter for the security reductions,
not another application-facing transformation. -/
def Reduction.fiatShamirSalted {U : Type} [VCVCompatible U] (saltLength : Nat)
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveReduction (Message := FiatShamirNARGString pSpec U saltLength)
      (oSpec + canonicalFSOracle StmtIn pSpec U saltLength) StmtIn WitIn StmtOut WitOut :=
  R.compileFiatShamir sampleSalt
