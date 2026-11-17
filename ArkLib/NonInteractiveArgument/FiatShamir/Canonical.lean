/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù, Quang Dao
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Basic
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

## Main results

- `canonicalFiatShamir_soundness`: **[CO25, Theorem 3.18]**,
  soundness from SR soundness.
- `canonicalFiatShamir_knowledgeSoundness`: **[CO25, Theorem 3.19], adapted to
  extractors with both query logs and oracle access**, one extractor for the entire budget family.
  This does not establish the deterministic, prover-trace-only contract of Definition 3.6.

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

namespace CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- `Verifier.compileFiatShamir`'s `verify` on the length-1 transcript `Fin.cons π 0` is, by
definition, the bare FS-NARG `verify` map `fsSaltedVerify V x π`.  Bridges the NIV-shaped
`adaptiveNARG*Exp init impl (Verifier.compileFiatShamir V)` experiments back to the
`fsSaltedVerify`-shaped §6.1/§6.2 game-match proofs (`simp only [fsSaltedNIV_verify]` after
unfolding the experiment restores the `fsSaltedVerify`-form goal). -/
theorem fsSaltedNIV_verify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (Verifier.compileFiatShamir (Salt := Salt) V).verify x (Fin.cons π (fun i => i.elim0))
      = fsSaltedVerify V x π :=
  rfl

/-- Induce an SR prover from an adaptive FS prover:
`(𝕩, (τ, α)) ← P; return ((𝕩, τ), α)`.
The statement `𝕩`, chosen salt `τ`, and full prover-message tuple `α` are repackaged without
adding queries. The FS and single-salt SR query types coincide, so the original oracle calls,
including private sampling through `privateSpec`, are retained. -/
def srInducedProver {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt) := do
  let ⟨x, nargString⟩ ← P
  return ⟨(x, nargString.1), nargString.2⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The induced SR prover is `P` followed by a pure repackaging of its output — in particular it
makes *exactly* the queries `P` makes. -/
lemma srInducedProver_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    srInducedProver (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2)) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- Induce an SR knowledge-soundness prover from an adaptive FS prover:
`(𝕩, (τ, α)) ← P; return ((𝕩, τ), α, ())`.
The unit value `()` supplies the generic SR interface's output witness. As with
`srInducedProver`, the oracle calls and their order are unchanged. -/
def srInducedProverKS {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn Unit pSpec (Salt := Salt) := do
  let ⟨x, nargString⟩ ← P
  return ⟨(x, nargString.1), nargString.2, ()⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The induced SR-KS prover is `P` followed by a pure repackaging of its output — in particular
it makes *exactly* the queries `P` makes. -/
lemma srInducedProverKS_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    srInducedProverKS (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2, ())) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

/-- Delegate FS extraction to the non-rewinding SR extractor `E`. Given `π = (τ, α)`, compute
`ρ := Messages.challengesOfLog (𝕩, τ) α tr_V.snd` and assemble the transcript `T = (α, ρ)`
in protocol order, then return `E 𝕩 τ () T tr_P tr_V.fst`.

The log `tr_V.snd` contains verifier queries for FS messages, while `tr_V.fst` contains its
ambient queries to `oSpec`. The prover log `tr_P` contains both kinds of query and is passed
intact. The value `()` supplies the SR output witness. Subsequent extractor calls use
`oSpec + unifSpec`.

Reconstruction rescans `tr_V.snd` for each verifier-message position. With `k` such positions
and `N` log entries, this uses up to `O(k * N)` entry inspections, plus transcript assembly
and one invocation of `E`. -/
def fsSRDelegatingExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp (oSpec + unifSpec)) WitIn :=
  E x π.1 ()
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 tr_V.snd))
    tr_P tr_V.fst

/-- Embed the delegated base-oracle computation into the NARG extractor interface.
The verifier message and helper slots are available in the ambient type but are not used here. -/
def fsSRDelegatingNARGExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    OptionT (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)) WitIn :=
  OptionT.mk (liftComp (fsSRDelegatingExtractor E x π tr_P tr_V).run
    ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec))

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Canonical verifier logs reconstruct the SR inputs exactly. This is equality of entire
oracle computations, not just of pure witness values, so subsequent extractor queries are
preserved under any common interpretation. -/
lemma fsSRDelegatingExtractor_canonical {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (x : StmtIn) (π : FSSaltedNARGString pSpec Salt)
    (tr_P : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
    (tr_V : QueryLog oSpec)
    (cs : pSpec.ChallengesUpTo ⟨n, Nat.lt_succ_self n⟩) :
    fsSRDelegatingExtractor E x π tr_P
      (QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
        ++ QueryLog.inl tr_V) =
      E x π.1 ()
        (FullTranscript.ofMessagesChallenges π.2
          (fun r => cs ⟨⟨r.1.1, r.1.2⟩, r.2⟩)) tr_P tr_V := by
  unfold fsSRDelegatingExtractor
  rw [QueryLog.snd_append, QueryLog.snd_inr, QueryLog.snd_inl, List.append_nil]
  rw [QueryLog.fst_append, QueryLog.fst_inr, QueryLog.fst_inl, List.nil_append]
  rw [Messages.challengesOfLog_canonChalLog]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The FS verifier reconstructs the same transcript as the SR game, then runs the IP verifier.
This equality retains all queries and their order, including queries made by the IP verifier. -/
private lemma fsSaltedVerify_eq_deriveTranscriptSR {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (fsSaltedVerify V x π).run =
      (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 : OracleComp _ _) >>=
        fun t => liftComp (V.verify x t).run (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) := by
  dsimp only [fsSaltedVerify, Verifier.compileFiatShamir,
    ProtocolSpec.Messages.deriveTranscriptFS]
  simp only [OptionT.liftM_def, OptionT.run_bind, Option.elimM, OptionT.run_lift, bind_assoc,
    pure_bind, Option.elim_some]
  simp only [Fin.cons_zero]
  refine bind_congr fun t => ?_
  rw [show (liftM (V.verify x t).run :
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
        (Option StmtOut)) =
    OptionT.lift (liftM (V.verify x t).run :
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) (Option StmtOut)) from
    (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [OptionT.run_lift, bind_assoc, pure_bind, Option.elim_some,
    OracleComp.liftComp_eq_liftM]
  trans (liftM (V.verify x t).run : OracleComp _ _) >>= pure
  · apply bind_congr
    intro result
    cases result <;> rfl
  · exact bind_pure _

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Canonical form of the logged single-salt FS verifier run: query the verifier message tuple, run
the (logged) base verifier on the assembled transcript, and read out the decision together with
the canonical verifier message log followed by the (left-embedded) base-verifier log. -/
private lemma logged_fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedNARGString pSpec Salt) :
    (simulateQ loggingOracle ((fsSaltedVerify (Salt := Salt) V x π).run)).run
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        (liftComp ((simulateQ loggingOracle
            ((V.verify x (Transcript.ofMessagesChallenges
              (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
          (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun q =>
          pure (q.1, QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
            ++ QueryLog.inl q.2) := by
  rw [fsSaltedVerify_eq_deriveTranscriptSR]
  refine Eq.trans (OracleComp.withQueryLog_bind _ _) ?_
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 :
      OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) _).withQueryLog
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs,
          QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs))
    from logged_deriveTranscriptSRAux_eq (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩]
  refine Eq.trans (bind_assoc _ _ _) ?_
  refine bind_congr fun cs => ?_
  change ((Prod.map id
      fun l => (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs).inr ++ l) <$>
    ((V.verify x (Transcript.ofMessagesChallenges (Messages.take ⟨n, Nat.lt_succ_self n⟩ π.2)
      cs)).run.liftComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)).withQueryLog) = _
  rw [show ((liftComp ((V.verify x (Transcript.ofMessagesChallenges
        (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)
        (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))).withQueryLog
    = (liftComp ((simulateQ loggingOracle ((V.verify x (Transcript.ofMessagesChallenges
          (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
        (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun p =>
        pure (p.1, QueryLog.inl p.2)
    from withQueryLog_liftComp_left_of_query (fun t => rfl) _]
  refine Eq.trans (map_bind _ _ _) ?_
  refine bind_congr fun q => ?_
  refine Eq.trans (map_pure _ _) ?_
  rfl

omit [VCVCompatible StmtIn] [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **FS↔SR KS crosswalk (the core of [CO25, Theorem 3.19])**: with the Construction-3.19
delegating extractor, the coin-bearing NARG KS experiment for the single-salt FS
verifier is the original-statement marginal of the coin-bearing SR-KS experiment for the induced
SR prover — with the *same* SR extractor `E` receiving the same transcript and the same
(projected) query logs. -/
private lemma fsKSExtractionSetup_eq_map_srKSExtractionSetup {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ}
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    (do
      let ⟨⟨x, π⟩, tr⟩ ← (simulateQ loggingOracle P).run
      (fun a => (x, fsSRDelegatingExtractor E x π tr.fst a.2, a.1)) <$>
        liftComp (simulateQ loggingOracle (fsSaltedVerify V x π).run).run
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
          (h := instMonadLiftTOfMonadLift
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
            (OracleQuery ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec))))
    = (fun out : (StmtIn × Salt) × OptionT (OracleComp (oSpec + unifSpec)) WitIn ×
        Option StmtOut × Unit =>
        (out.1.1, out.2.1, out.2.2.1)) <$>
      (do
        let ⟨⟨stmtIn, messages, _unit⟩, tr⟩ ←
          (simulateQ loggingOracle (srInducedProverKS P)).run
        let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
        let ⟨stmtOut, tr_V⟩ ←
          liftComp (simulateQ loggingOracle
            (V.run stmtIn.1 transcript).run).run _
        return (stmtIn, E stmtIn.1 stmtIn.2 () transcript tr.fst tr_V,
          stmtOut, ())) := by
  classical
  -- Align the prover stage: the induced SR prover is `P` with a pure repackaging, so its logged
  -- run is the logged run of `P` with the same log.
  simp only [srInducedProverKS_eq_map, simulateQ_map, WriterT.run_map,
    bind_map_left, map_bind]
  refine bind_congr fun p => ?_
  -- Verify stage: canonical form of the logged FS verifier, and the explicit form of the SR
  -- transcript derivation.
  rw [logged_fsSaltedVerify]
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 :
      OracleComp _ _)
    = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) (p.1.1, p.1.2.1) p.1.2.2
        ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (p.1.2.2.take ⟨n, Nat.lt_succ_self n⟩) cs)
    from Messages.deriveTranscriptSR_eq_chalTupleUpTo _ _]
  -- Push the lifts through both sides and align stage by stage.
  simp only [liftComp_bind, liftComp_pure, map_bind, map_pure]
  conv_rhs =>
    enter [1]
    erw [liftComp_bind (h := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))]
  simp only [bind_assoc]
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))
    (fun t => by rcases t with t | t <;> rfl)
    (chalTupleUpTo (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 ⟨n, Nat.lt_succ_self n⟩)]
  refine bind_congr fun cs => ?_
  refine OracleComp.bind_congr' ?_ fun q => ?_
  · refine liftComp_liftComp ?_ _
    intro t
    rfl
  · -- The delegated extractor receives the reconstructed transcript and the
    -- projected logs, which coincide with the SR experiment's transcript and logs.
    refine congrArg pure ?_
    refine congrArg (fun w => (p.1.1, w, q.1)) ?_
    rw [fsSRDelegatingExtractor_canonical]
    rfl

omit [VCVCompatible StmtIn] in
/-- Delegating extraction preserves the SR failure probability, including the extractor's
private sampling and its ambient queries in the final verifier state. -/
private lemma fsKSShared_failure_eq {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {privateSpec : OracleSpec κ} (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt)) :
    Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
          (Verifier.compileFiatShamir (Salt := Salt) V)
          (fsSRDelegatingNARGExtractor E) P}[nargKSFailEvent relIn langOut out] =
      Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
        fsInit fsImpl privateImpl E
        relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
        V (srInducedProverKS P) := by
  let publicImpl : QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp) :=
    fsImpl.addLift (srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
  have hbase : (publicImpl.addLift (QueryImpl.id' unifSpec) : QueryImpl _
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)) ∘ₛ
      (fun q => liftM (OracleSpec.query q) : QueryImpl (oSpec + unifSpec)
        (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec))) =
      fsImpl.addLift (QueryImpl.id' unifSpec) := by
    funext q
    cases q with
    | inl q =>
      change simulateQ _ (liftM
        (((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec).query
          (.inl (.inl q)))) = _
      rw [simulateQ_spec_query]
      rfl
    | inr q =>
      change simulateQ _ (liftM
        (((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec).query
          (.inr q))) = _
      rw [simulateQ_spec_query]
      rfl
  dsimp only [publicImpl] at hbase
  have h := congrArg (fun computation =>
    StateT.run' (σ := QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id)
      (m := ProbComp) (do
      let out ← simulateQ (publicImpl.addLift privateImpl) computation
      let w ← simulateQ (fsImpl.addLift (QueryImpl.id' unifSpec)) out.2.1.run
      pure (out.1, w, out.2.2))) (fsKSExtractionSetup_eq_map_srKSExtractionSetup V E P)
  have h' := congrArg (fun computation =>
    Pr{let out ← do computation (← fsInit)}[nargKSFailEvent relIn langOut out]) h
  simp only [adaptiveNARGKnowledgeSoundnessExp_eq,
    Verifier.StateRestoration.knowledgeSoundnessFailureProb_eq]
  unfold fsSRDelegatingNARGExtractor Verifier.StateRestoration.knowledgeSoundnessProverVerifierExp
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_map, bind_map_left,
    OptionT.run_mk, liftComp_def, ← QueryImpl.simulateQ_compose, hbase,
    bind_assoc, pure_bind, runVerifierWithLog, withQueryLog] at h' ⊢
  convert h' using 1
  · apply congrArg prEvent
    simp only [map_bind, publicImpl, fsSaltedVerify]
    rfl
  · apply congrArg prEvent
    simp only [map_bind, map_pure, StateT.run'_bind', StateT.run'_pure']
    refine bind_congr (m := ProbComp) fun s => ?_
    refine bind_congr fun p => ?_
    refine bind_congr fun tr => ?_
    refine bind_congr fun v => ?_
    cases p.1.1.2.2
    refine bind_congr fun w => ?_
    cases w.1 <;> cases v.1.1 <;> rfl

omit [VCVCompatible StmtIn] in
/-- Transport a supplied SR extractor, without choosing it after the query budget.
The conclusion uses the NARG extractor interface documented above. Repackaging preserves all
queries, and the selector implication transfers the same `IsQueryBoundP` budget.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem canonicalFiatShamir_knowledgeSoundness_of_fixedExtractor
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    (h_sr_ks : ∀ P : Prover.StateRestoration.KnowledgeSoundness
      oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
        fsInit fsImpl privateImpl E
        relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
        V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
          (Verifier.compileFiatShamir (Salt := Salt) V)
          (fsSRDelegatingNARGExtractor E) P}[nargKSFailEvent relIn langOut out] ≤ ε := by
  intro P hP
  rw [fsKSShared_failure_eq privateImpl V E fsInit fsImpl relIn langOut P]
  apply h_sr_ks (srInducedProverKS P)
  rw [srInducedProverKS_eq_map, OracleComp.isQueryBoundP_map_iff]
  exact OracleComp.IsQueryBoundP.of_imp hCount hP

end CanonicalFS

section CanonicalSecurity

open CanonicalFS

variable [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  in
/-- **[CO25, Theorem 3.18]** Single-salt FS soundness from IP SR-soundness.

If `V` has state-restoration soundness for `langIn` in the game with salt space `Salt`, with error
`ε`, then `Verifier.compileFiatShamir V` has adaptive NARG soundness in the ROM with error `ε`.

**Proof**: repackage the FS prover's output as the original statement, salt context, and
prover messages.
The SR game reconstructs the same transcript and runs the same verifier, so its
false-acceptance probability equals that of the FS experiment. Apply SR soundness directly.

The premise and conclusion use `IsQueryBoundP` with the same natural-number budget `t`.
The selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`: every query counted in the
SR premise is also counted in the FS conclusion. For the paper-facing formulation, choose
`srQueryBoundSelector = publicQuerySelector Verifier.StateRestoration.isSrChallengeMove` and
`queryBoundSelector = nargPublicQuery`.
To count only queries for verifier messages, choose the move selector on both sides. Repackaging
preserves queries exactly, so neither choice increases the budget or the soundness error.
Adapted from **[snarg-book, Theorem 14.3.1]** to the single-salt construction. -/
theorem canonicalFiatShamir_soundness_withSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : ∀ P : Prover.StateRestoration.Soundness oSpec privateSpec StmtIn pSpec (Salt := Salt),
      P.IsQueryBoundP srQueryBoundSelector t →
      Verifier.StateRestoration.soundnessFailureProb (Salt := Salt) fsInit fsImpl privateImpl
        langIn langOut V P ≤ ε) :
    ∀ P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
      (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
      Pr{let out ← adaptiveNARGSoundnessExp fsInit (fsImpl.addLift srChallengeQueryImpl')
          privateImpl (Verifier.compileFiatShamir (Salt := Salt) V) P}[
            nargSoundFailEvent langIn langOut out] ≤ ε := by
  intro P hP
  have hBound : (srInducedProver P).IsQueryBoundP srQueryBoundSelector t := by
    rw [srInducedProver_eq_map, OracleComp.isQueryBoundP_map_iff]
    exact OracleComp.IsQueryBoundP.of_imp hCount hP
  have hSound := h_sr (srInducedProver P) hBound
  suffices hSame :
      Pr{let out ← adaptiveNARGSoundnessExp fsInit
          (fsImpl.addLift srChallengeQueryImpl') privateImpl
          (Verifier.compileFiatShamir (Salt := Salt) V) P}[
          nargSoundFailEvent langIn langOut out] =
      Verifier.StateRestoration.soundnessFailureProb (Salt := Salt) fsInit fsImpl privateImpl
        langIn langOut V (srInducedProver P) by
    exact hSame.trans_le hSound
  simp only [adaptiveNARGSoundnessExp_eq_option, Verifier.StateRestoration.soundnessFailureProb_eq,
    srSoundnessGame]
  rw [prEvent_def, prEvent_def]
  refine congrArg (fun computation : ProbComp Prop => 𝒟[computation] {True}) ?_
  simp only [map_bind]
  refine bind_congr (m := ProbComp) fun state => ?_
  rw [← StateT.run'_map', ← StateT.run'_map', ← simulateQ_map, ← simulateQ_map]
  apply congrArg (fun computation :
    StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp Prop =>
      computation.run' state)
  apply congrArg (simulateQ _)
  rw [show (liftM P : OptionT
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec))
      (StmtIn × FSSaltedNARGString pSpec Salt)) = OptionT.lift P from rfl]
  simp only [srInducedProver_eq_map, fsSaltedNIV_verify,
    fsSaltedVerify_eq_deriveTranscriptSR, Verifier.run,
    OptionT.monad_bind_eq_bind, OptionT.bind, OptionT.monad_pure_eq_pure, OptionT.pure,
    OptionT.lift, OptionT.mk, bind_assoc, pure_bind, bind_map_left, map_bind, map_pure,
    liftComp_bind]
  refine bind_congr fun p => ?_
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery ((oSpec + srChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + privateSpec)))
      (OracleQuery ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)))
    (fun q => by cases q <;> rfl)
    (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1, p.2.1) p.2.2)]
  refine bind_congr (m := OracleComp
    ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)) fun transcript => ?_
  refine OracleComp.bind_congr' ?_ fun out => ?_
  · refine liftComp_liftComp ?_ (V.verify p.1 transcript).run
    intro q
    rfl
  · cases out <;> simp only [map_pure, nargSoundFailEvent, and_comm]

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- **[CO25, Theorem 3.19]** — One SR extractor yields
one NARG extractor for every natural-number query budget, with the same error function.
The query selectors satisfy `srQueryBoundSelector q → queryBoundSelector q`, as in the
soundness theorem.
The NARG extractor interface permits randomness and both logs; it does not establish the
deterministic, prover-trace-only contract of Definition 3.6.
Adapted from the straightline case of **[snarg-book, Theorem 14.4.1]**. -/
theorem canonicalFiatShamir_knowledgeSoundness_withSampler
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (privateSpec : OracleSpec κ) (privateImpl : QueryImpl privateSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector srQueryBoundSelector :
      ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : ∃ E : Extractor.StateRestoration oSpec StmtIn WitIn Unit pSpec (Salt := Salt),
      ∀ t, ∀ P : Prover.StateRestoration.KnowledgeSoundness
        oSpec privateSpec StmtIn Unit pSpec (Salt := Salt),
        P.IsQueryBoundP srQueryBoundSelector t →
        Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt)
          fsInit fsImpl privateImpl E
          relIn {yu : StmtOut × Unit | yu.1 ∈ langOut}
          V P ≤ ε t) :
    ∃ extractor : StmtIn → FSSaltedNARGString pSpec Salt →
      QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) →
      QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) →
      OptionT (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)) WitIn,
      ∀ t, ∀ P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + privateSpec)
        (StmtIn × FSSaltedNARGString pSpec Salt), P.IsQueryBoundP queryBoundSelector t →
        Pr{let out ← adaptiveNARGKnowledgeSoundnessExp fsInit
            (fsImpl.addLift srChallengeQueryImpl') privateImpl
            ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
            (Verifier.compileFiatShamir (Salt := Salt) V) extractor P}[
              nargKSFailEvent relIn langOut out] ≤ ε t := by
  classical
  let _ : DecidableEq StmtIn := Classical.decEq _
  let _ (i : pSpec.MessageIdx) : DecidableEq (pSpec.Message i) := Classical.decEq _
  obtain ⟨E, hE⟩ := hSR
  refine ⟨fsSRDelegatingNARGExtractor E, ?_⟩
  intro t
  exact canonicalFiatShamir_knowledgeSoundness_of_fixedExtractor
    privateSpec privateImpl V relIn langOut fsInit fsImpl E
    queryBoundSelector srQueryBoundSelector hCount t (ε t) (hE t)

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS soundness with standard private randomness. -/
theorem canonicalFiatShamir_soundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (Verifier.compileFiatShamir (Salt := Salt) V) langIn langOut queryBoundSelector t ε := by
  exact canonicalFiatShamir_soundness_withSampler
    unifSpec (QueryImpl.id' unifSpec) V langIn langOut
    fsInit fsImpl (publicQuerySelector queryBoundSelector)
    (publicQuerySelector srQueryBoundSelector)
    (by intro q h; cases q with
        | inl q => exact hCount q h
        | inr _ => exact h.elim) t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Single-salt FS knowledge soundness with standard private randomness. -/
theorem canonicalFiatShamir_knowledgeSoundness
    {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    (srQueryBoundSelector : (oSpec + srChallengeOracle (StmtIn × Salt) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Salt)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Salt) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (Verifier.compileFiatShamir (Salt := Salt) V) relIn langOut queryBoundSelector ε := by
  exact canonicalFiatShamir_knowledgeSoundness_withSampler
    unifSpec (QueryImpl.id' unifSpec) V relIn langOut
    fsInit fsImpl (publicQuerySelector queryBoundSelector)
    (publicQuerySelector srQueryBoundSelector)
    (by intro q h; cases q with
        | inl q => exact hCount q h
        | inr _ => exact h.elim) ε hSR

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem fiatShamir_soundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Vector U saltLength) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsChallengeOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srChallengeOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (t : ℕ) (ε : ENNReal)
    -- SR soundness of the original IP in the game with the same salt context.
    (h_sr : Verifier.StateRestoration.soundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl langIn langOut V
      srQueryBoundSelector t ε) :
    Verifier.adaptiveNARGSoundnessQueryBounded
      fsInit (fsImpl.addLift srChallengeQueryImpl')
      (V.fiatShamirSalted (U := U) saltLength) langIn langOut queryBoundSelector t ε := by
  exact canonicalFiatShamir_soundness (Salt := Vector U saltLength)
    V langIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount t ε h_sr

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- Knowledge soundness of canonical Fiat-Shamir for every salt length, including zero.
The SR game carries salt separately from the original statement and input relation. -/
theorem fiatShamir_knowledgeSoundness
    {U : Type} [VCVCompatible U] (saltLength : ℕ)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Vector U saltLength) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Vector U saltLength) pSpec) Id) ProbComp))
    (queryBoundSelector :
      (oSpec + fsChallengeOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    (srQueryBoundSelector :
      (oSpec + srChallengeOracle (StmtIn × Vector U saltLength) pSpec).Domain → Prop)
    [DecidablePred queryBoundSelector] [DecidablePred srQueryBoundSelector]
    (hCount : ∀ q, srQueryBoundSelector q → queryBoundSelector q)
    (ε : ℕ → ENNReal)
    (hSR : Verifier.StateRestoration.knowledgeSoundnessQueryBounded (Salt := Vector U saltLength)
      fsInit fsImpl relIn
      {yu : StmtOut × Unit | yu.1 ∈ langOut}
      V srQueryBoundSelector ε) :
    Verifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      fsInit (fsImpl.addLift (srChallengeQueryImpl' (pSpec := pSpec)))
      ((fsImpl.addLift (srChallengeQueryImpl'
          (Statement := StmtIn × Vector U saltLength) (pSpec := pSpec)) : QueryImpl _
            (StateT (QueryImpl
              (srChallengeOracle (StmtIn × Vector U saltLength) pSpec) Id) ProbComp)).addLift
          (QueryImpl.id' unifSpec))
      (V.fiatShamirSalted (U := U) saltLength) relIn langOut queryBoundSelector ε := by
  exact canonicalFiatShamir_knowledgeSoundness (Salt := Vector U saltLength)
    V relIn langOut fsInit fsImpl
    queryBoundSelector srQueryBoundSelector hCount ε hSR


end CanonicalSecurity
