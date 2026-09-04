/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Michele Orrù
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
import ArkLib.ToVCVio.Tactic.VCVNorm

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

open ProtocolSpec OracleComp OracleSpec OracleReduction

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

The prover samples a salt `τ ← sampleSalt` using only the ambient oracle `oSpec`, then runs the
underlying interactive prover with all FS queries keyed by the augmented statement `(stmtIn, τ)`,
and packages the salt together with the produced messages as the non-interactive proof. The sampler
cannot inspect the statement, witness-bearing prover state, or Fiat–Shamir table.
-/
def Prover.singleSaltFiatShamir {Salt : Type} [VCVCompatible Salt]
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveProver (FSSaltedProof pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
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
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveReduction (FSSaltedProof pSpec Salt)
      (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)
      StmtIn WitIn StmtOut WitOut where
  prover := R.prover.singleSaltFiatShamir sampleSalt
  verifier := R.verifier.singleSaltFiatShamir

/-- The single-salt FS verifier run as a NARG `verify` (CO25 `V_std^f(x,·)`): build the
single-message transcript from the FS proof and run `Verifier.singleSaltFiatShamir V`. Used by
the DSFS Section 5 `Hyb₄`/basic-FS game so both games refer to the same verifier. -/
def fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    StmtIn → FSSaltedProof pSpec Salt →
      OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) StmtOut :=
  fun stmtIn proof =>
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify stmtIn
      (Fin.cons proof (fun i => i.elim0))

section Security

noncomputable section

open scoped NNReal

variable [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Completeness statement for single-salt Fiat-Shamir with a fresh uniformly sampled salt,
matching CO25 Construction 3.17. The sampler's `OracleComp oSpec Salt` type prevents access to the
statement, witness-bearing prover state, and Fiat–Shamir table. `sampleSalt_uniform` additionally
says that evaluating it has the joint distribution of a fresh uniform draw and the unchanged
ambient state. The proof is intentionally deferred. -/
theorem singleSaltFiatShamir_completeness
    {Salt : Type} [VCVCompatible Salt]
    [SampleableType Salt]
    [SampleableType (OracleFamily (srChallengeOracle (StmtIn × Salt) pSpec))]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (sampleSalt : OracleComp oSpec Salt)
    (sampleSalt_uniform : sampleSalt.IsFreshUniformSampler impl)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (completenessError : ℝ≥0) :
  R.completeness init impl relIn relOut completenessError →
    (R.singleSaltFiatShamir sampleSalt).completeness
      (init := do
        let challengeSpec := srChallengeOracle (StmtIn × Salt) pSpec
        let f ← (OracleDistribution.uniform challengeSpec).sample
        let challengeImpl : QueryImpl challengeSpec Id := fun q => f q
        return (← init, challengeImpl))
      (impl := (impl.addLift fsChallengeQueryImpl' :
        QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
          (StateT (σ × QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)))
      relIn relOut completenessError := by
  sorry

end

end Security
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
  verify := fun ⟨stmtIn, _⟩ transcript => V.verify stmtIn transcript

/-- Lift a soundness language `langIn : Set StmtIn` to `Set (StmtIn × Salt)`,
ignoring the salt. -/
def langInSalted {Salt : Type} (langIn : Set StmtIn) : Set (StmtIn × Salt) :=
  {p | p.1 ∈ langIn}

/-- Lift an input relation `relIn : Set (StmtIn × WitIn)` to
`Set ((StmtIn × Salt) × WitIn)`, ignoring the salt. -/
def relInSalted {Salt : Type} (relIn : Set (StmtIn × WitIn)) : Set ((StmtIn × Salt) × WitIn) :=
  {p | ⟨p.1.1, p.2⟩ ∈ relIn}

/-- View an accepting-output set as the relation-valued interface expected by ArkLib's generic
state-restoration definitions. The `Unit` component carries no adversarial claim. -/
def unitOutputRelation (langOut : Set StmtOut) : Set (StmtOut × Unit) :=
  {p | p.1 ∈ langOut}

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- `Verifier.singleSaltFiatShamir`'s `verify` on the length-1 transcript `Fin.cons π 0` is, by
definition, the bare FS-NARG `verify` map `fsSaltedVerify V x π`.  Bridges the NIV-shaped
`adaptiveNARG*Exp init impl (Verifier.singleSaltFiatShamir V)` experiments back to the
`fsSaltedVerify`-shaped §6.1/§6.2 game-match proofs (`simp only [fsSaltedNIV_verify]` after
unfolding the experiment restores the `fsSaltedVerify`-form goal). -/
theorem fsSaltedNIV_verify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    (Verifier.singleSaltFiatShamir (Salt := Salt) V).verify x (Fin.cons π (fun i => i.elim0))
      = fsSaltedVerify V x π :=
  rfl

/-- The coin-bearing SR prover induced by an adaptive FS NARG prover (CO25 Construction 3.18's
`𝒫_SR`): run `P` for `(𝕩, (τ, m))` and output the salted statement `(𝕩, τ)` together with
messages `m`.

`P`'s ambient spec `(oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec` *is* the SR
ambient (`fsChallengeOracle = srChallengeOracle` by alias), so no query routing is needed: the
paper's "forward each well-formed FS query as an SR move" simulation is rendered trivial by the
typed challenge oracle (there are no malformed queries to lazily answer, either). -/
def srInducedProver {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Prover.StateRestoration.SoundnessWithCoins oSpec (StmtIn × Salt) pSpec auxSpec := do
  let ⟨x, proof⟩ ← P
  return ⟨(x, proof.1), proof.2⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The induced SR prover is `P` followed by a pure repackaging of its output — in particular it
makes *exactly* the queries `P` makes. -/
lemma srInducedProver_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    srInducedProver (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2)) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- **Query-budget preservation (Construction 3.18)**: the induced SR prover satisfies exactly
the query bounds `P` does, for any VCVio budget discipline `(b, canQuery, cost)`. -/
lemma isQueryBound_srInducedProver_iff {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ} {B : Type}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt))
    (b : B) (canQuery : _ → B → Prop) (cost : _ → B → B) :
    (srInducedProver (Salt := Salt) P).IsQueryBound b canQuery cost
      ↔ P.IsQueryBound b canQuery cost := by
  rw [srInducedProver_eq_map, OracleComp.isQueryBound_map_iff]

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- **FS↔SR game crosswalk (the core of CO25 Theorem 3.18).** The coin-bearing Def-3.5 NARG
soundness experiment for the single-salt FS verifier is the
`(salted statement, accept-readout)`-marginal of the coin-bearing SR soundness experiment of the
induced SR prover: both run `P`, derive the transcript by the *same* computation
(`deriveTranscriptFS = deriveTranscriptSR` by alias, keyed at the same salted statement against
the same pre-sampled challenge function), and run the same base verifier `V`; they differ only in
the shape of the read-out (`OptionT`-abort vs an in-band `Option`). -/
theorem fsNARGSoundnessExp_eq_srExp {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ} (auxImpl : QueryImpl auxSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    adaptiveNARGSoundnessExpWithCoins fsInit (fsImpl.addLift srChallengeQueryImpl') auxImpl
      (Verifier.singleSaltFiatShamir (Salt := Salt) V) P
    = (fun out : (StmtIn × Salt) × Option StmtOut =>
        Option.map (fun stmtOut => (out.1.1, stmtOut)) out.2) <$>
      (do (simulateQ (((fsImpl.addLift srChallengeQueryImpl' :
            QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
              auxImpl) :
          QueryImpl _ (StateT _ ProbComp)) <| (do
        let ⟨transcript, stmtIn⟩ ← srSoundnessGameWithCoins (srInducedProver P)
        let stmtOut ← liftComp ((saltedIPVerifier (Salt := Salt) V).run stmtIn transcript) _
        return (stmtIn, stmtOut))).run' (← fsInit)) := by
  classical
  unfold adaptiveNARGSoundnessExpWithCoins
  simp only [fsSaltedNIV_verify]
  rw [map_bind]
  refine bind_congr fun s => ?_
  rw [← StateT.run'_map', ← simulateQ_map]
  refine congrArg (fun c => StateT.run' c s) ?_
  dsimp only [srSoundnessGameWithCoins, srInducedProver, fsSaltedVerify,
    Verifier.singleSaltFiatShamir, saltedIPVerifier, Verifier.run,
    ProtocolSpec.Messages.deriveTranscriptFS]
  delta fsChallengeOracle fsChallengeQueryImpl'
  vcv_norm
  simp only [Fin.cons_zero]
  apply OptionT.ext (m := StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)
  simp only [OptionT.run_bind, Option.elimM, pure_bind, bind_assoc]
  simp only [OptionT.run]
  change (simulateQ _ (P >>= fun a => pure (some a)) >>= _) = _
  rw [simulateQ_bind]
  simp only [simulateQ_pure, bind_assoc, pure_bind, Option.elim_some]
  refine bind_congr fun p => ?_
  change simulateQ
      (_ : QueryImpl _ (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
      (((_ : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)
            pSpec.FullTranscript) >>= _ :
        OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)
          (Option StmtOut)))
    >>= (_ : Option StmtOut →
        StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp
          (Option (StmtIn × StmtOut))) = _
  simp only [simulateQ_bind, bind_assoc]
  vcv_norm
  have hroute {α : Type}
      (X : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec) α) :
      simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec) +
            QueryImpl.liftTarget
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)
              auxImpl)
          (liftComp X (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)) =
        simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec)) X := by
    rw [liftComp_inst_irrel
      (i₂ := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
      (fun t => by rcases t with t | t <;> rfl) X]
    exact QueryImpl.simulateQ_add_liftComp_left _ _ X
  have hrouteBase {α : Type} (X : OracleComp oSpec α) :
      simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec) +
            QueryImpl.liftTarget
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)
              auxImpl)
          (liftComp X (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)) =
        simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
          (liftComp X (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) := by
    rw [← hroute]
    exact congrArg _ (Eq.symm (liftComp_liftComp
      (spec₁ := oSpec)
      (spec₂ := oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (spec₃ := oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)
      (fun _ => rfl) X))
  have hrouteChallenge {α : Type} (X : OracleComp oSpec α) :
      simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
          (liftComp X (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) =
        simulateQ fsImpl X := by
    rw [liftComp_inst_irrel
      (i₂ := instMonadLiftTOfMonadLift
        (OracleQuery oSpec) (OracleQuery oSpec)
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)))
      (fun _ => rfl) X]
    exact QueryImpl.simulateQ_add_liftComp_left _ _ X
  rw [hroute]
  refine bind_congr fun tr => ?_
  rw [hrouteBase]
  vcv_norm
  have hsimVerifier :
      simulateQ
          (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
          ((liftM (V.verify p.1 tr).run : OptionT
              (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
              (Option StmtOut)) :
            OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (Option (Option StmtOut))) =
        some <$> simulateQ fsImpl (V.verify p.1 tr).run := by
    rw [← OracleComp.monadLift_liftM_OptionT]
    exact QueryImpl.simulateQ_optionT_liftM_run_eq_of_query _ _
      (fun t => by
        simpa only [OracleComp.liftComp_eq_liftM, simulateQ_spec_query] using
          hrouteChallenge
            (liftM (oSpec.query t) : OracleComp oSpec (oSpec.Range t)))
      (V.verify p.1 tr).run
  conv_lhs =>
    enter [1]
    change simulateQ
      (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec))
      ((liftM (V.verify p.1 tr).run : OptionT
          (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (Option StmtOut)) :
        OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
          (Option (Option StmtOut)))
    rw [hsimVerifier]
  vcv_norm
  conv_rhs =>
    enter [1]
    change simulateQ fsImpl (V.verify p.1 tr).run
  refine bind_congr fun o => ?_
  rcases o with _ | out
  · simp only [Option.elim_none, Option.map_none]
  · simp only [Option.elim_some, Option.map_some]
    change simulateQ
        (fsImpl + srChallengeQueryImpl' (Statement := StmtIn × Salt) (pSpec := pSpec) +
          QueryImpl.liftTarget
            (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)
            auxImpl)
        ((pure (p.1, out) : OptionT
          (OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))
          (StmtIn × StmtOut)).run) = pure (some (p.1, out))
    vcv_norm


omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- CO25 Theorem 3.18 — Single-salt FS soundness from IP SR-soundness.

If `saltedIPVerifier V` has state-restoration soundness (for `langInSalted langIn`) with error
`ε`, then `Verifier.singleSaltFiatShamir V` has basic soundness in the ROM with error `ε`.

**Proof**: the FS malicious prover `P` *is* already an SR prover up to repackaging its output
(`srInducedProver`), since its ambient spec is the SR ambient and the typed challenge oracle
leaves no malformed queries to route.  The NARG experiment is then the accept-readout marginal of
the SR experiment (`fsNARGSoundnessExp_eq_srExp`), and the events agree on that marginal.

The theorem is parametric in the prover classes: SR soundness against `srBound`-provers lifts to
NARG soundness against any FS prover class `bound` whose induced SR provers land in `srBound`
(`hBound`).  Taking `bound = srBound = fun _ => True` recovers the unbounded statement.  Since
`srInducedProver P` makes exactly `P`'s queries, query budgets transfer on the nose: for the
CO25 query-budget form, instantiate both classes with `fun P => P.IsQueryBound b canQuery cost`
and discharge `hBound` with `(isQueryBound_srInducedProver_iff ..).mpr`. -/
theorem single_salt_fiat_shamir_soundness
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
  intro P hP
  refine le_trans (le_of_eq ?_) (h_sr (srInducedProver P) (hBound P hP))
  unfold Verifier.StateRestoration.coinSRExperimentProb
  rw [fsNARGSoundnessExp_eq_srExp auxImpl V fsInit fsImpl P, probEvent_map]
  congr 1
  funext out
  rcases out with ⟨⟨x, salt⟩, _ | stmtOut⟩ <;> simp [langInSalted, and_comm]

/-- The coin-bearing SR knowledge-soundness prover induced by an adaptive FS NARG KS prover
(the KS analog of `srInducedProver`): run `P` for `(𝕩, (τ, m))` and output the salted statement
`(𝕩, τ)`, the messages `m`, and the canonical unit required by the generic SR interface. -/
def srInducedProverKS {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) Unit pSpec
      auxSpec := do
  let ⟨x, proof⟩ ← P
  return ⟨(x, proof.1), proof.2, ()⟩

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The induced SR-KS prover is `P` followed by a pure repackaging of its output — in particular
it makes *exactly* the queries `P` makes. -/
lemma srInducedProverKS_eq_map {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    srInducedProverKS (Salt := Salt) P
      = (fun p => ((p.1, p.2.1), p.2.2, ())) <$> P := by
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun p => rfl

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- **Query-budget preservation (Construction 3.19)**: the induced SR-KS prover satisfies exactly
the query bounds `P` does, for any VCVio budget discipline `(b, canQuery, cost)`. -/
lemma isQueryBound_srInducedProverKS_iff {Salt : Type} [VCVCompatible Salt]
    {κ : Type} {auxSpec : OracleSpec κ} {B : Type}
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt))
    (b : B) (canQuery : _ → B → Prop) (cost : _ → B → B) :
    (srInducedProverKS (Salt := Salt) P).IsQueryBound b canQuery cost
      ↔ P.IsQueryBound b canQuery cost := by
  rw [srInducedProverKS_eq_map, OracleComp.isQueryBound_map_iff]

/-- **CO25 Construction 3.19 extractor (pure, trace-based, computable)**: parse the salted proof
`π = (τ, m)`, rebuild the IP transcript from `m` and the verifier's logged challenge queries
(`Messages.challengesOfLog` on the challenge part of `tr_V`), and run the SR extractor `E` on
the salted statement `(𝕩, τ)` with the canonical unit required only by ArkLib's generic SR
interface, the prover's query log (the SR move-response trace — `fsChallengeOracle =
srChallengeOracle` by alias, so the paper's `FSToSR` trace map is the identity), and the verifier's
`oSpec`-query log.

This is the paper's explicitly *efficient* extractor — a single pass over the verifier's trace
(`Messages.challengesOfLog`) followed by one invocation of `E` — not a classical witness
choice: the extraction work beyond `E` is linear in the trace. -/
def fsSRDelegatingExtractor {Salt : Type} [VCVCompatible Salt]
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (x : StmtIn) (π : FSSaltedProof pSpec Salt)
    (tr_P tr_V : QueryLog (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) :
    Option WitIn :=
  E (x, π.1) ()
    (FullTranscript.ofMessagesChallenges π.2
      (Messages.challengesOfLog (x, π.1) π.2 tr_V.snd))
    tr_P tr_V.fst

omit [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- Canonical form of the logged single-salt FS verifier run: query the challenge tuple, run
the (logged) base verifier on the assembled transcript, and read out the decision together with
the canonical challenge log followed by the (left-embedded) base-verifier log. -/
private lemma logged_fsSaltedVerify {Salt : Type} [VCVCompatible Salt]
    (V : Verifier oSpec StmtIn StmtOut pSpec) (x : StmtIn) (π : FSSaltedProof pSpec Salt) :
    (simulateQ loggingOracle ((fsSaltedVerify (Salt := Salt) V x π).run)).run
    = chalTupleUpTo (oSpec := oSpec) (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        (liftComp ((simulateQ loggingOracle
            ((V.verify x (Transcript.ofMessagesChallenges
              (π.2.take ⟨n, Nat.lt_succ_self n⟩) cs)).run)).run)
          (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec)) >>= fun q =>
          pure (q.1, QueryLog.inr (canonChalLog (x, π.1) π.2 ⟨n, Nat.lt_succ_self n⟩ cs)
            ++ QueryLog.inl q.2) := by
  have hrun : (fsSaltedVerify (Salt := Salt) V x π).run
      = (Messages.deriveTranscriptSR (oSpec := oSpec) (x, π.1) π.2 : OracleComp _ _)
          >>= fun t => liftComp ((V.verify x t).run)
            (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) := by
    dsimp only [fsSaltedVerify, Verifier.singleSaltFiatShamir,
      ProtocolSpec.Messages.deriveTranscriptFS]
    vcv_norm
    simp only [Fin.cons_zero]
    refine bind_congr fun t => ?_
    rw [show (liftM (V.verify x t).run :
        OptionT (OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
          (Option StmtOut)) =
      OptionT.lift (liftM (V.verify x t).run :
        OracleComp (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) (Option StmtOut)) from
      (OracleComp.monadLift_liftM_OptionT _).symm]
    simp only [OptionT.run_lift, bind_assoc, pure_bind, Option.elim_some,
      bind_pure, OracleComp.liftComp_eq_liftM]
  rw [hrun]
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
    from withQueryLog_liftComp_inl (fun t => rfl) _]
  refine Eq.trans (map_bind _ _ _) ?_
  refine bind_congr fun q => ?_
  refine Eq.trans (map_pure _ _) ?_
  rfl

omit [VCVCompatible StmtIn] in
/-- **FS↔SR KS crosswalk (the core of CO25 Theorem 3.19)**: with the Construction-3.19
delegating extractor, the coin-bearing Def-3.6 NARG KS experiment for the single-salt FS
verifier is the salted-statement marginal of the coin-bearing SR-KS experiment for the induced
SR prover — with the *same* SR extractor `E` receiving the same transcript and the same
(projected) query logs. -/
private lemma fsKSExp_eq_map_srKSExp {Salt : Type} [VCVCompatible Salt]
    {κ κE : Type} {auxSpec : OracleSpec κ} (auxImpl : QueryImpl auxSpec ProbComp)
    {auxSpecE : OracleSpec κE} (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (E : Extractor.StateRestoration oSpec (StmtIn × Salt) WitIn Unit pSpec)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (P : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt)) :
    adaptiveNARGKnowledgeSoundnessExpWithCoins fsInit (fsImpl.addLift srChallengeQueryImpl')
      auxImpl auxImplE (Verifier.singleSaltFiatShamir (Salt := Salt) V)
      (fun x π tr_P tr_V =>
        OptionT.mk (pure (fsSRDelegatingExtractor E x π tr_P tr_V))) P
    = (fun out : (StmtIn × Salt) × Option WitIn × Option StmtOut × Unit =>
        (out.1.1, out.2.1, out.2.2.1)) <$>
      (do (simulateQ (((fsImpl.addLift srChallengeQueryImpl' :
            QueryImpl (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
              (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp)).addLift
            auxImpl) :
          QueryImpl _ (StateT _ ProbComp)) <| (do
        let ⟨⟨stmtIn, messages, _unit⟩, tr⟩ ←
          (simulateQ loggingOracle (srInducedProverKS P)).run
        let transcript ← liftComp (messages.deriveTranscriptSR (oSpec := oSpec) stmtIn)
          ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
        let ⟨stmtOut, tr_V⟩ ←
          liftComp (simulateQ loggingOracle
            ((saltedIPVerifier (Salt := Salt) V).run stmtIn transcript).run).run _
        return (stmtIn, E stmtIn () transcript tr.fst tr_V,
          stmtOut, ()))).run' (← fsInit)) := by
  classical
  unfold adaptiveNARGKnowledgeSoundnessExpWithCoins
  simp only [OptionT.run_mk, simulateQ_pure, bind_pure_comp]
  simp only [fsSaltedNIV_verify]
  rw [map_bind]
  refine bind_congr fun s => ?_
  simp only [map_pure]
  rw [bind_pure_comp]
  rw [← StateT.run'_map', ← simulateQ_map]
  conv_rhs => rw [← StateT.run'_map', ← simulateQ_map]
  refine congrArg (fun c => StateT.run' (simulateQ _ c) s) ?_
  -- Align the prover stage: the induced SR prover is `P` with a pure repackaging, so its logged
  -- run is the logged run of `P` with the same log.
  refine Eq.trans ?_ (Eq.symm (congrArg (fun z => _ <$> z)
    (Eq.trans (congrArg (· >>= _) (show (simulateQ loggingOracle
        (srInducedProverKS (Salt := Salt) P)).run
      = (simulateQ loggingOracle P).run >>= fun p =>
          pure (((p.1.1, p.1.2.1), p.1.2.2, ()), p.2) from by
        refine Eq.trans (OracleComp.withQueryLog_bind _ _) (bind_congr fun p => ?_)
        simp only [OracleComp.withQueryLog_pure, map_pure, Prod.map, id, List.append_nil]))
      (Eq.trans (bind_assoc _ _ _) (bind_congr fun p => pure_bind _ _)))))
  simp only [map_bind, Functor.map_map]
  refine bind_congr fun p => ?_
  -- Verify stage: canonical form of the logged FS verifier, and the explicit form of the SR
  -- transcript derivation.
  refine Eq.trans (congrArg (fun z : OracleComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)
      (Option StmtOut × QueryLog (oSpec + srChallengeOracle (StmtIn × Salt) pSpec)) =>
    (fun a => (p.1.1, fsSRDelegatingExtractor E p.1.1 p.1.2 p.2.fst a.2, a.1)) <$>
      z.liftComp (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)
        (h := instMonadLiftTOfMonadLift
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))))
    (logged_fsSaltedVerify V p.1.1 p.1.2)) ?_
  rw [show (Messages.deriveTranscriptSR (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 :
      OracleComp _ _)
    = chalTupleUpTo (oSpec := oSpec) (pSpec := pSpec) (p.1.1, p.1.2.1) p.1.2.2
        ⟨n, Nat.lt_succ_self n⟩ >>= fun cs =>
        pure (Transcript.ofMessagesChallenges (p.1.2.2.take ⟨n, Nat.lt_succ_self n⟩) cs)
    from Messages.deriveTranscriptSR_eq_chalTupleUpTo _ _]
  -- Push the lifts through both sides and align stage by stage.
  refine Eq.trans (congrArg (fun z => _ <$> z)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _)) ?_
  refine Eq.trans (map_bind _ _ _) ?_
  refine Eq.trans ?_ (Eq.symm (Eq.trans (congrArg (· >>= _)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
        (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _))
    (Eq.trans (bind_assoc _ _ _) (bind_congr fun cs =>
      Eq.trans (congrArg (· >>= _) (OracleComp.liftComp_pure _ _)) (pure_bind _ _)))))
  rw [liftComp_inst_irrel
    (i₁ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
    (i₂ := instMonadLiftTOfMonadLift
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleQuery (oSpec + (fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
      (OracleQuery (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec + auxSpec)))
    (fun t => by rcases t with t | t <;> rfl)
    (chalTupleUpTo (oSpec := oSpec) (p.1.1, p.1.2.1) p.1.2.2 ⟨n, Nat.lt_succ_self n⟩)]
  refine bind_congr fun cs => ?_
  refine Eq.trans (congrArg (fun z => _ <$> z)
    (OracleComp.liftComp_bind
      (h := instMonadLiftTOfMonadLift
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
        (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _ _)) ?_
  refine Eq.trans (map_bind _ _ _) ?_
  refine Eq.trans (bind_congr fun q => Eq.trans
    (congrArg (fun z => _ <$> z)
      (OracleComp.liftComp_pure
        (h := instMonadLiftTOfMonadLift
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec))
          (OracleQuery (oSpec + srChallengeOracle (StmtIn × Salt) pSpec + auxSpec))) _ _))
    (map_pure _ _)) ?_
  refine Eq.trans ?_ (Eq.symm (map_eq_bind_pure_comp _ _ _))
  refine liftComp_liftComp_bind_congr ?_ _ _ _ fun q => ?_
  case _ => intro t; rfl
  -- Read-out equality: the delegated extractor receives the reconstructed transcript and the
  -- projected logs, which coincide with the SR experiment's transcript and logs.
  have hchal := Messages.challengesOfLog_canonChalLog
    (p.1.1, p.1.2.1) p.1.2.2 cs
  refine congrArg pure ?_
  refine congrArg (fun w => (p.1.1, w, q.1)) ?_
  change fsSRDelegatingExtractor E p.1.1 p.1.2 p.2.fst
      (QueryLog.inr (canonChalLog (p.1.1, p.1.2.1) p.1.2.2 ⟨n, Nat.lt_succ_self n⟩ cs)
        ++ QueryLog.inl q.2) = _
  unfold fsSRDelegatingExtractor
  rw [QueryLog.snd_append, QueryLog.snd_inr, QueryLog.snd_inl, List.append_nil]
  rw [QueryLog.fst_append, QueryLog.fst_inr, QueryLog.fst_inl, List.nil_append]
  rw [hchal]
  rfl

omit [VCVCompatible StmtIn] [DecidableEq StmtIn]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- CO25 Theorem 3.19 — Single-salt FS straightline KS from IP SR-KS.

If `saltedIPVerifier V` has state-restoration knowledge soundness (for `relInSalted relIn`)
with error `ε`, then `Verifier.singleSaltFiatShamir V` has straightline KS in the ROM with
error `ε`.

**Proof**: the FS extractor is CO25 Construction 3.19 (`fsSRDelegatingExtractor`) — parse the
salted proof `π = (τ, m)`, rebuild the IP transcript from `m` and the verifier's logged
challenge queries (`Messages.challengesOfLog`; the reconstruction is exact by
`Messages.challengesOfLog_canonChalLog`), and run the SR extractor `E` on the salted statement
`(𝕩, τ)` with the canonical unit required only by ArkLib's generic SR interface, the prover's
query log (the SR move-response trace — the paper's
`FSToSR` trace map is the identity here since `fsChallengeOracle = srChallengeOracle` by
alias), and the verifier's `oSpec`-query log.  The FS-KS experiment is then *equal* to the
salted-statement marginal of the SR-KS experiment with the same extractor
(`fsKSExp_eq_map_srKSExp`), and the SR hypothesis closes the bound.
Used as Seam #2 in `KnowledgeSoundness.lean` (Theorem 6.2).

The theorem is parametric in the prover classes: SR-KS against `srBound`-provers lifts to NARG
straightline KS against any FS prover class `bound` whose induced SR provers land in `srBound`
(`hBound`).  Taking `bound = srBound = fun _ => True` recovers the unbounded statement.  Since
`srInducedProverKS P` makes exactly `P`'s queries, query budgets transfer on the nose: for the
CO25 query-budget form, instantiate both classes with `fun P => P.IsQueryBound b canQuery cost`
and discharge `hBound` with `(isQueryBound_srInducedProverKS_iff ..).mpr`. -/
theorem single_salt_fiat_shamir_straightline_knowledge_soundness
    {Salt : Type} [VCVCompatible Salt]
    {κ : Type} (auxSpec : OracleSpec κ) (auxImpl : QueryImpl auxSpec ProbComp)
    -- The extractor's own helper/sampler oracle (`P`-independent), generic so the caller picks it
    -- (DSFS passes `(Unit →ₒ U)` for Construction 6.3's D2STrace; the bare FS extractor ignores
    -- it).
    {κE : Type} (auxSpecE : OracleSpec κE) (auxImplE : QueryImpl auxSpecE ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (relIn : Set (StmtIn × WitIn)) (langOut : Set StmtOut)
    (fsInit : ProbComp (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id))
    (fsImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle (StmtIn × Salt) pSpec) Id) ProbComp))
    (srBound : Prover.StateRestoration.KnowledgeSoundnessWithCoins oSpec (StmtIn × Salt) Unit
      pSpec auxSpec → Prop)
    (bound : OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + auxSpec)
      (StmtIn × FSSaltedProof pSpec Salt) → Prop)
    (hBound : ∀ P, bound P → srBound (srInducedProverKS P))
    (ε : ENNReal)
    -- Coin-bearing SR knowledge soundness of the salted IP.
    (h_sr_ks : Verifier.StateRestoration.knowledgeSoundnessWithCoins fsInit fsImpl auxSpec auxImpl
        (relInSalted (Salt := Salt) relIn) (unitOutputRelation langOut)
        (saltedIPVerifier (Salt := Salt) V)
        srBound ε) :
    -- CO25 Def 3.6 (adaptive, coin-bearing straightline KS) of the single-salt FS argument,
    -- phrased as a property of the NARG verifier `Verifier.singleSaltFiatShamir V`.
    Verifier.adaptiveNARGKnowledgeSoundnessWithCoins (WitIn := WitIn)
      (init := fsInit) (impl := fsImpl.addLift srChallengeQueryImpl')
      auxImpl auxImplE
      (verifier := Verifier.singleSaltFiatShamir (Salt := Salt) V)
      relIn langOut (bound := bound) ε := by
  classical
  let _ : DecidableEq StmtIn := Classical.decEq _
  let _ (i : pSpec.MessageIdx) : DecidableEq (pSpec.Message i) := Classical.decEq _
  let _ (i : pSpec.ChallengeIdx) : DecidableEq (pSpec.Challenge i) := Classical.decEq _
  obtain ⟨E, hE⟩ := h_sr_ks
  -- CO25 Construction 3.19: delegate to the SR extractor `E`.
  refine ⟨fun x π tr_P tr_V =>
    OptionT.mk (pure (fsSRDelegatingExtractor E x π tr_P tr_V)), ?_⟩
  intro P hP
  refine le_trans (le_of_eq ?_) (hE (srInducedProverKS P) (hBound P hP))
  rw [fsKSExp_eq_map_srKSExp auxImpl auxImplE V E fsInit fsImpl P, probEvent_map]
  refine probEvent_ext fun out _ => ?_
  rcases out with ⟨⟨x, τ⟩, wi?, so?, u⟩
  rcases u with ⟨⟩
  rcases wi? with _ | w <;> rcases so? with _ | so <;> exact Iff.rfl

end SingleSaltSecurity
