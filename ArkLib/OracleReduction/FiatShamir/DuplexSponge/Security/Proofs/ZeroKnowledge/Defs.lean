/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.Execution
public import VCVio.OracleComp.Constructions.RandomPermutation.Conditioning
public import VCVio.OracleComp.Constructions.UniformPreimage
public import ArkLib.InteractiveProof.ZeroKnowledge
public import ArkLib.NonInteractiveArgument.Legacy
public import VCVio.OracleComp.EvalDist.DiscreteTVDistFintype
public import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Definitions and experiments for duplex-sponge Fiat--Shamir zero knowledge

This file defines the duplex-sponge objects shared by the zero-knowledge hybrid proof in
[CO25, §§7.2--7.3].

## Paper correspondence

* `programBlocks` implements the `ProgramBlocks` procedure inside Construction 7.5.
* `dsfsZKSimulator` implements Construction 7.5, and `referenceZKProver` is Figure 5's Hybrid 0
  prover.
* With the native DSFS sampler and query handlers, `hyb0Exp`, `hyb1Exp`, `hyb2Exp`,
  the two Hybrid 3
  presentations, and `hyb4Exp` are plan-first Lean presentations of the five experiments in
  Figure 5.

`SimulationReduction.lean` proves the Hybrid 1--4 bounds. `Security/Proofs/ZeroKnowledge.lean`
combines them with the Hybrid 0--1 estimate; `Security/ZeroKnowledge.lean` transports that bound
to the canonical prover and states Theorem 7.1.
The Section 5 soundness hybrids are different games; only their codec, sponge, and
oracle-distribution infrastructure is reused here.

## Lean representation

A `PermutationProgram` stores only forward edges; inverse entries are induced by installing those
edges into a genuine permutation. The quantitative Hybrid 0--1 analysis is developed in the
`ZeroKnowledge/` submodules, separately from these shared experiment definitions.

Hybrids 1--3 sample a complete verifier message plan before replaying the prover.  This matches
Definition
7.2's single random choice of verifier randomness and its public-coin tuple presentation.

All declarations are pointwise at a fixed `ProtocolSpec`, alphabet, sponge size, and `Codec`.
Thus `Codec.decodingBias i` is the per-round total-variation bound from Definition 4.1;
size aggregation is supplied at the final theorem.

## References

* [Chiesa, A. and Orrù, M., *A Fiat--Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ZeroKnowledge

variable {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]

/-! ## Canonical decoder-preimage sampling ([CO25, Lemma 3.2 and Claim 7.9]) -/

omit [SpongeUnit U] [SpongeSize] in
/-- Executable `ProbComp` form of the codec's exact per-round TV-distance guarantee. -/
theorem codec_round_probComp_tvDist_le_bias
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (i : pSpec.ChallengeIdx) :
    discreteTVDist
      (uniformSample (pSpec.Challenge i) (h := VCVCompatible.toSampleableType))
      (codec.decode i <$> (uniformSample
        (EncodedVerifierMessage (pSpec := pSpec) (U := U) i)
        (h := VCVCompatible.toSampleableType)))
      ≤ (codec.decodingBias i : ℝ) :=
  @Codec.decode_isBiased _ _ _ codec i VCVCompatible.toSampleableType
    VCVCompatible.toSampleableType

/-! ## Complete verifier message plans for Hybrids 1--3 -/

/-- All encoded verifier messages in one protocol execution. -/
abbrev EncodedVerifierMessages :=
  (i : pSpec.ChallengeIdx) → EncodedVerifierMessage (pSpec := pSpec) (U := U) i

/-- Explicit canonical sampler for a complete dependent tuple of encoded verifier messages. -/
@[reducible] noncomputable def sampleableEncodedVerifierMessages
    [VCVCompatible U] :
    SampleableType (EncodedVerifierMessages (pSpec := pSpec) (U := U)) := by
  letI : Nonempty (EncodedVerifierMessages (pSpec := pSpec) (U := U)) :=
    ⟨fun _ => default⟩
  exact SampleableType.ofFintype _

/-- Explicit canonical sampler for a complete dependent tuple of protocol verifier messages. -/
@[reducible] noncomputable def sampleableVerifierMessages
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    SampleableType pSpec.Challenges := by
  letI : Nonempty pSpec.Challenges := ⟨fun _ => default⟩
  exact SampleableType.ofFintype _

/-- The coordinatewise decoder on a complete encoded verifier message plan. -/
def decodeVerifierMessages
    (encoded : EncodedVerifierMessages (pSpec := pSpec) (U := U)) : pSpec.Challenges :=
  fun i => codec.decode i (encoded i)

omit [SpongeUnit U] [SpongeSize] in
/-- Surjectivity of the complete decoder follows pointwise from `Codec.decode_surjective`. -/
theorem decodeVerifierMessages_surjective :
    Function.Surjective (decodeVerifierMessages (pSpec := pSpec) (U := U)) := by
  exact Function.Surjective.piMap codec.decode_surjective

/-- A complete verifier message plan together with the encoded values programmed into the
sponge. -/
abbrev VerifierMessagePlan :=
  pSpec.Challenges × EncodedVerifierMessages (pSpec := pSpec) (U := U)

/-- The prover messages and exact encoded verifier messages consumed by the common DSFS compiler
for Hybrids 1--4. -/
abbrev PlannedVerifierView :=
  pSpec.Messages × EncodedVerifierMessages (pSpec := pSpec) (U := U)

/-- Exact uniform sampling from a fiber of the complete coordinatewise decoder.  Treating the
whole plan as one finite map lets [CO25, Lemma 3.2] lift to every verifier round in one step. -/
def sampleEncodedVerifierMessagesPreimage
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (verifierMessages : pSpec.Challenges) :
    ProbComp (EncodedVerifierMessages (pSpec := pSpec) (U := U)) := by
  classical
  let ψ := decodeVerifierMessages (pSpec := pSpec) (U := U)
  exact OracleComp.UniformPreimage.sampleUniformPreimage ψ verifierMessages
    (OracleComp.UniformPreimage.preimage_nonempty ψ
      (decodeVerifierMessages_surjective (pSpec := pSpec) (U := U)) verifierMessages)

/-- Hybrid 1's complete verifier message plan: sample all encoded verifier messages uniformly and
decode them coordinatewise. -/
def hyb1VerifierMessagePlan
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ProbComp (VerifierMessagePlan (pSpec := pSpec) (U := U)) := do
  let encoded ← uniformSample _ (h := sampleableEncodedVerifierMessages)
  pure (decodeVerifierMessages (pSpec := pSpec) (U := U) encoded, encoded)

/-- Hybrid 2's complete verifier message plan: decode one uniform encoded plan, then resample
uniformly inside the fiber of the resulting verifier message tuple. -/
def hyb2VerifierMessagePlan
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ProbComp (VerifierMessagePlan (pSpec := pSpec) (U := U)) := do
  let encoded' ← uniformSample _ (h := sampleableEncodedVerifierMessages)
  let verifierMessages := decodeVerifierMessages (pSpec := pSpec) (U := U) encoded'
  let encoded ←
    sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) verifierMessages
  pure (decodeVerifierMessages (pSpec := pSpec) (U := U) encoded, encoded)

/-- Hybrid 3's complete verifier message plan: sample honest-verifier messages uniformly, followed
by an exact uniform encoded preimage. -/
def hyb3VerifierMessagePlan
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    ProbComp (VerifierMessagePlan (pSpec := pSpec) (U := U)) := do
  let verifierMessages ← uniformSample _ (h := sampleableVerifierMessages)
  let encoded ←
    sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) verifierMessages
  pure (verifierMessages, encoded)

omit [SpongeUnit U] [SpongeSize] in
/-- Complete-plan form of Lemma 3.2: decoding and uniformly resampling a whole fiber preserves the
uniform distribution on encoded verifier message plans. -/
theorem evalDist_resampleEncodedVerifierMessages
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    (letI : MeasurableSpace (EncodedVerifierMessages (pSpec := pSpec) (U := U)) := ⊤
    𝒟[do
      let encoded' ← uniformSample _ (h := sampleableEncodedVerifierMessages)
      sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U)
        (decodeVerifierMessages (pSpec := pSpec) (U := U) encoded')] =
      𝒟[uniformSample _ (h := sampleableEncodedVerifierMessages)]) := by
  let : MeasurableSpace (EncodedVerifierMessages (pSpec := pSpec) (U := U)) := ⊤
  let := sampleableEncodedVerifierMessages (pSpec := pSpec) (U := U)
  simp_rw [sampleEncodedVerifierMessagesPreimage]
  exact OracleComp.UniformPreimage.bind_sampleUniformPreimage_eq_uniform
    (decodeVerifierMessages (pSpec := pSpec) (U := U))

omit [SpongeUnit U] [SpongeSize] in
/-- **[CO25, Claim 7.9]** verifier message-plan core.

The theorem proves that `hyb1VerifierMessagePlan` and `hyb2VerifierMessagePlan` are identically
distributed by uniform fiber resampling (Lemma 3.2).  The first sentence of the paper's proof says
“Hybrid 2 and Hybrid 3,” but the claim statement and calculation concern Hybrid 1 and Hybrid 2. -/
theorem evalDist_hyb1VerifierMessagePlan_eq_hyb2VerifierMessagePlan
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    (letI : MeasurableSpace (VerifierMessagePlan (pSpec := pSpec) (U := U)) := ⊤
    𝒟[hyb1VerifierMessagePlan (pSpec := pSpec) (U := U)] =
      𝒟[hyb2VerifierMessagePlan (pSpec := pSpec) (U := U)]) := by
  let : MeasurableSpace (VerifierMessagePlan (pSpec := pSpec) (U := U)) := ⊤
  have h := ((evalDistEq_iff_evalDist_eq.mpr
    (evalDist_resampleEncodedVerifierMessages (pSpec := pSpec) (U := U))).bind_left
    (fun encoded => (pure (decodeVerifierMessages (pSpec := pSpec) (U := U) encoded, encoded) :
      ProbComp (VerifierMessagePlan (pSpec := pSpec) (U := U))))).evalDist_eq
  simpa only [hyb1VerifierMessagePlan, hyb2VerifierMessagePlan, bind_assoc] using h.symm

/-! ## Materializing complete verifier message plans with the honest prover -/

/-- Run the prover on the verifier message component of a plan and retain the plan's exact encoded
verifier messages for the common DSFS compiler. -/
def materializeVerifierMessagePlan
    {WitIn StmtOut WitOut : Type}
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (plan : VerifierMessagePlan (pSpec := pSpec) (U := U)) :
    ProbComp (PlannedVerifierView (pSpec := pSpec) (U := U)) := do
  let messages ← Reduction.runProverWithChallenges coinImpl prover stmt wit plan.1
  pure (messages, plan.2)

/-- Sample the exact encoded verifier messages associated with one complete public-coin view. -/
def planVerifierView
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (view : Reduction.IPVerifierView StmtIn pSpec) :
    ProbComp (PlannedVerifierView (pSpec := pSpec) (U := U)) := do
  let encoded ← sampleEncodedVerifierMessagesPreimage
    (pSpec := pSpec) (U := U) view.2.challenges
  pure (view.2.messages, encoded)

omit [SpongeUnit U] [SpongeSize] in
/-- Recover the message tuple from the `FullTranscript` constructor used for Definition 7.2. -/
@[simp]
theorem fullTranscript_messages_ofMessagesChallenges
    (messages : pSpec.Messages) (verifierMessages : pSpec.Challenges) :
    (FullTranscript.ofMessagesChallenges messages verifierMessages).messages = messages := by
  exact congrArg Prod.fst (FullTranscript.equivMessagesChallenges.apply_symm_apply
    (messages, verifierMessages))

omit [SpongeUnit U] [SpongeSize] in
/-- Recover the verifier message tuple from the `FullTranscript` constructor used for Definition
7.2. -/
@[simp]
theorem fullTranscript_challenges_ofMessagesChallenges
    (messages : pSpec.Messages) (verifierMessages : pSpec.Challenges) :
    (FullTranscript.ofMessagesChallenges messages verifierMessages).challenges =
      verifierMessages := by
  exact congrArg Prod.snd (FullTranscript.equivMessagesChallenges.apply_symm_apply
    (messages, verifierMessages))

/-- Hybrid 1 through the honest prover, before the shared DSFS compiler. -/
def hyb1PlannedView
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    ProbComp (PlannedVerifierView (pSpec := pSpec) (U := U)) := do
  let plan ← hyb1VerifierMessagePlan (pSpec := pSpec) (U := U)
  materializeVerifierMessagePlan (U := U) coinImpl prover stmt wit plan

/-- Hybrid 2 through the honest prover, before the shared DSFS compiler. -/
def hyb2PlannedView
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    ProbComp (PlannedVerifierView (pSpec := pSpec) (U := U)) := do
  let plan ← hyb2VerifierMessagePlan (pSpec := pSpec) (U := U)
  materializeVerifierMessagePlan (U := U) coinImpl prover stmt wit plan

/-- Hybrid 3 through the honest prover, before normalization to an honest verifier view followed
by Construction 7.5. -/
def hyb3PlannedView
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    ProbComp (PlannedVerifierView (pSpec := pSpec) (U := U)) := do
  let plan ← hyb3VerifierMessagePlan (pSpec := pSpec) (U := U)
  materializeVerifierMessagePlan (U := U) coinImpl prover stmt wit plan

omit [SpongeUnit U] [SpongeSize] in
/-- Normalization of Hybrid 3: sampling the decoder preimage before running the prover is
distributionally identical to first producing the complete honest verifier view and then sampling
the same preimage. -/
theorem evalDist_hyb3PlannedView_eq_honestVerifierView_bind_planVerifierView
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (letI : MeasurableSpace (PlannedVerifierView (pSpec := pSpec) (U := U)) := ⊤
    𝒟[hyb3PlannedView (U := U) coinImpl prover stmt wit] =
      𝒟[do
        let view ← Reduction.honestVerifierView coinImpl prover stmt wit
        planVerifierView (U := U) view]) := by
  let : MeasurableSpace (PlannedVerifierView (pSpec := pSpec) (U := U)) := ⊤
  simp only [hyb3PlannedView, hyb3VerifierMessagePlan, materializeVerifierMessagePlan,
    Reduction.honestVerifierView, Reduction.runProverWithChallenges, planVerifierView]
  rw [bind_assoc, bind_assoc]
  refine evalDist_bind_congr _ _ _ fun verifierMessages => ?_
  rw [bind_assoc, bind_assoc]
  simp only [pure_bind, fullTranscript_messages_ofMessagesChallenges,
    fullTranscript_challenges_ofMessagesChallenges]
  exact OracleComp.evalDist_bind_bind_swap
    (sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) verifierMessages)
    (Reduction.runProverWithChallenges coinImpl prover stmt wit verifierMessages)
    (fun encoded messages => pure (messages, encoded))

omit [SpongeUnit U] [SpongeSize] in
/-- **[CO25, Claim 7.9]** Prover-view form.

Running the same honest prover against the two identically distributed verifier message plans
preserves the equality between Hybrid 1 and Hybrid 2. -/
theorem evalDist_hyb1PlannedView_eq_hyb2PlannedView
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    (letI : MeasurableSpace (PlannedVerifierView (pSpec := pSpec) (U := U)) := ⊤
    𝒟[hyb1PlannedView (U := U) coinImpl prover stmt wit] =
      𝒟[hyb2PlannedView (U := U) coinImpl prover stmt wit]) := by
  let : MeasurableSpace (PlannedVerifierView (pSpec := pSpec) (U := U)) := ⊤
  exact ((evalDistEq_iff_evalDist_eq.mpr
    (evalDist_hyb1VerifierMessagePlan_eq_hyb2VerifierMessagePlan (pSpec := pSpec) (U :=
      U))).bind_left
    (materializeVerifierMessagePlan (U := U) coinImpl prover stmt wit)).evalDist_eq

/-- A finite DSFS permutation program.  Storing forward edges only makes the intended inverse
program structurally paired with it. -/
abbrev PermutationProgram (U : Type) [SpongeUnit U] :=
  List (CanonicalSpongeState U × CanonicalSpongeState U)

/-- Install a DSFS permutation program into one sampled ideal-oracle realization.

The hash table is retained verbatim, while sequential swaps give every edge list deterministic
total semantics as a permutation. -/
def programmedDuplexSpongeOracle
    [DecidableEq U]
    (realization : DuplexSpongeOracleFamily StmtIn U)
    (program : PermutationProgram U) : DuplexSpongeOracleFamily StmtIn U :=
  (realization.1, PermutationConditioning.install realization.2 program)

/-- Answer queries after installing a permutation program into the sampled DSFS oracle.
The original hash table is preserved, and inverse answers use the installed permutation. -/
def dsfsProgrammedQueryImpl [DecidableEq U]
    (realization : DuplexSpongeOracleFamily StmtIn U) (program : PermutationProgram U) :
    QueryImpl (duplexSpongeOracle StmtIn U) ProbComp :=
  duplexSpongeOracleQueryImpl (programmedDuplexSpongeOracle realization program)

/-! ## `ProgramBlocks` -/

/-- The cursor position after squeezing a positive number `len` of rate elements.  Unlike a bare
`len % r`, this returns `r` (not `0`) when the last rate block is exactly exhausted, matching the
executable `DuplexSponge.squeeze` semantics. -/
def squeezePosAfterPositive (len : ℕ) (_hlen : 0 < len) : Fin (SpongeSize.R + 1) :=
  ⟨(len - 1) % SpongeSize.R + 1, by
    have hmod := Nat.mod_lt (len - 1) SpongeSize.R_pos
    omega⟩

/-- Output of one `ProgramBlocks` call. -/
structure ProgramBlocksOutput (U : Type) [SpongeUnit U] [SpongeSize] where
  sponge : CanonicalDuplexSponge U
  program : PermutationProgram U

/-- Select the final sampled state, retaining `start` in the zero-block edge case. -/
def lastStateOr (start : CanonicalSpongeState U) :
    {m : ℕ} → Vector (CanonicalSpongeState U) m → CanonicalSpongeState U
  | 0, _ => start
  | k + 1, states => states.get (Fin.last k)

/-- Deterministic core of `ProgramBlocks`, after rate blocks and capacity segments have been
sampled. -/
def programBlocksFromSamples {m len : ℕ}
    (sponge : CanonicalDuplexSponge U)
    (rateBlocks : Vector (Vector U SpongeSize.R) m)
    (capacities : Vector (Vector U SpongeSize.C) m) :
    ProgramBlocksOutput U :=
  let states : Vector (CanonicalSpongeState U) m :=
    Vector.ofFn fun j =>
      (Vector.append (rateBlocks.get j) (capacities.get j)).cast
        (by simp [SpongeSize.R_plus_C_eq_N])
  let finalState := lastStateOr sponge.state states
  let finalSponge : CanonicalDuplexSponge U :=
    if hlen : len = 0 then sponge
    else
      { state := finalState
        absorbPos := 0
        squeezePos := squeezePosAfterPositive len (Nat.pos_of_ne_zero hlen) }
  { sponge := finalSponge
    program := List.zip (sponge.state :: states.toList) states.toList }

/-- Split the supplied units into exactly `m` rate blocks, sampling uniform padding for a final
partial block.  `m` is instantiated with `L_V(i)` by `programBlocks`. -/
def rateBlocksFromUnitsM [VCVCompatible U] :
    (m : ℕ) → List U →
      ProbComp {blocks : List (Vector U SpongeSize.R) // blocks.length = m}
  | 0, _ => pure ⟨[], rfl⟩
  | m + 1, units => do
      let headUnits := units.take SpongeSize.R
      let restUnits := units.drop SpongeSize.R
      let block ←
        if hFull : headUnits.length = SpongeSize.R then
          pure <| Vector.ofFn fun j => headUnits.get ⟨j.1, by rw [hFull]; exact j.2⟩
        else do
          let padLen := SpongeSize.R - headUnits.length
          let pad ← uniformSample (Vector U padLen) (h := VCVCompatible.toSampleableType)
          let blockList := headUnits ++ pad.toList
          have hTake : headUnits.length ≤ SpongeSize.R := by
            exact List.length_take_le SpongeSize.R units
          have hLen : blockList.length = SpongeSize.R := by
            simp [blockList, padLen, Nat.add_sub_of_le hTake]
          pure <| Vector.ofFn fun j => blockList.get ⟨j.1, by rw [hLen]; exact j.2⟩
      let ⟨tail, hTail⟩ ← rateBlocksFromUnitsM m restUnits
      pure ⟨block :: tail, by simp [hTail]⟩

/-- **[CO25, Construction 7.5]** The `ProgramBlocks` procedure.

The encoded verifier message is split into exactly $L_V(i)=\lceil \ell_V(i)/r\rceil$ rate blocks,
with padding only for a partial final block.  One independent capacity segment is sampled per block,
and the result contains the forward-edge representation of the paired
$(\mu_{p,i},\mu_{p^{-1},i})$ lists and the post-squeeze sponge state.  Inverse entries are derived
during installation.

As in the paper's prover-message/verifier-message round structure, the construction represents a
squeeze that starts at `sponge.squeezePos = r`. -/
def programBlocks
    [VCVCompatible U] (i : pSpec.ChallengeIdx)
    (sponge : CanonicalDuplexSponge U)
    (encoded : EncodedVerifierMessage (pSpec := pSpec) (U := U) i) :
    ProbComp (ProgramBlocksOutput U) := do
  let ⟨blocks, hBlocks⟩ ←
    rateBlocksFromUnitsM (U := U) (pSpec.Lᵥᵢ i) encoded.toList
  let rateBlocks : Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ i) :=
    ⟨blocks.toArray, by simpa using hBlocks⟩
  let capacities ← uniformSample (Vector (Vector U SpongeSize.C) (pSpec.Lᵥᵢ i))
    (h := VCVCompatible.toSampleableType)
  pure (programBlocksFromSamples
    (len := verifierMessageSize (pSpec := pSpec) i) sponge rateBlocks capacities)

/-- **[CO25, Definition 7.4]** The aggregate public-oracle query condition.  It counts every
hash, permutation, and inverse-permutation query made across both adversarial stages. -/
def HasPublicQueryBound
    {WitIn Proof Output : Type} {admissible : StmtIn → WitIn → Prop}
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn Proof Output admissible)
    (t : ℕ) : Prop :=
  adversary.HasAggregateQueryBound (fun _ => True) t

/-! ## Construction 7.5 and Hybrid 4 -/

/-- **[CO25, Figure 5]** Message computation for Hybrid 0.

Sample the salt and observe the full runner's messages through the argument interface of
Definition 7.4. This hybrid computation does not construct a compiled prover or run its output. -/
def referenceZKProver
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec) :
    Reduction.NARGZKProver
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :=
  fun stmt wit => OracleComp.swapOracles do
    let salt ← uniformSample (Vector U δ) (h := VCVCompatible.toSampleableType)
    let result ← prover.referenceRunDSFSSalted salt (Fin.last n) stmt (prover.input (stmt, wit))
    pure (salt, result.1)

/-- The canonical [CO25, Construction 4.4] prover, with uniform salt, through the NARG interface.
Terminal sponge work is omitted and the reduction output is fixed to acceptance. -/
def dsfsZKProver
    {WitIn : Type} [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (prover : Prover unifSpec StmtIn WitIn Bool Unit pSpec) :
    Reduction.NARGZKProver (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) :=
  Reduction.NonInteractiveProver.toNARGZKProver
    (prover.duplexSpongeFiatShamir δ
      (uniformSample (Vector U δ) (h := VCVCompatible.toSampleableType)))

/-- **[CO25, Figure 5]** One round of the common compiler (lines 8--11).

Prover messages are encoded and absorbed.  For verifier rounds, the exact encoded verifier message
is passed to the `ProgramBlocks` operation from Construction 7.5, step 5(d). -/
def compilePlannedViewRound [VCVCompatible U] (messages : pSpec.Messages)
    (encodedVerifierMessages : ∀ i, EncodedVerifierMessage (pSpec := pSpec) (U := U) i)
    (i : Fin n)
    (previous : OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec)
      (CanonicalDuplexSponge U × PermutationProgram U)) :
    OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec)
      (CanonicalDuplexSponge U × PermutationProgram U) := do
  let ⟨currentSponge, program⟩ ← previous
  match hDir : pSpec.dir i with
  | .P_to_V =>
      let idx : pSpec.MessageIdx := ⟨i, hDir⟩
      let nextSponge ←
        liftM (m := OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec))
          (DuplexSponge.absorb currentSponge (codec.encode idx (messages idx)).toList)
      pure (nextSponge, program)
  | .V_to_P =>
      let idx : pSpec.ChallengeIdx := ⟨i, hDir⟩
      let programmed ← programBlocks (pSpec := pSpec) (U := U) idx currentSponge
        (encodedVerifierMessages idx)
      pure (programmed.sponge, program ++ programmed.program)

/-- **[CO25, Figure 5]** Common compiler for Hybrids 1--4.

It implements Construction 7.5, steps 2--10, after the interactive view and exact encoded
verifier messages have been supplied.  Its randomness is precisely the salt, partial-block padding,
and
capacity segments.  The output is the salted NARG string and the forward-edge representation of the
paired permutation program. -/
def compilePlannedView
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (stmt : StmtIn)
    (view : PlannedVerifierView (pSpec := pSpec) (U := U)) :
    OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ × PermutationProgram U) := do
  let salt ← uniformSample (Vector U δ) (h := VCVCompatible.toSampleableType)
  let sponge0 : CanonicalDuplexSponge U ←
    liftM (m := OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec))
      (DuplexSponge.start (U := U) (C := CanonicalSpongeState U) stmt)
  let sponge ← simulateQ
    (fun q => query (spec := duplexSpongeForwardOracle StmtIn U + unifSpec) (.inl (.inr q)))
    (DuplexSponge.absorb sponge0 salt.toList)
  let result ← Fin.induction
    (motive := fun _ => OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec)
      (CanonicalDuplexSponge U × PermutationProgram U))
    (pure (sponge, []))
    (compilePlannedViewRound (StmtIn := StmtIn) view.1 view.2)
    (Fin.last n)
  pure ((salt, view.1), result.2)

/-- Canonical inclusion of private coins into the forward oracle. -/
@[reducible]
def uniformToForwardSubSpec :
    unifSpec ⊂ₒ (duplexSpongeForwardOracle StmtIn U + unifSpec) :=
  OracleQuery.subSpec_add_right

/-- Canonical embedding of private randomness into the forward-only DSFS compiler oracle.  Naming
the inclusion avoids typeclass search choosing a longer, extensionally equal sub-spec path. -/
def liftUniformToForward {A : Type} (oa : ProbComp A) :
    OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec) A :=
  @OracleComp.liftComp _ _ _ _ oa _
    (@instMonadLiftTOfMonadLift _ _ _
      (uniformToForwardSubSpec (StmtIn := StmtIn) (U := U)).toMonadLift
      (instMonadLiftT _))

/-- Canonical inclusion of the forward oracle into the full oracle. -/
@[reducible]
def forwardToFullSubSpec :
    (duplexSpongeForwardOracle StmtIn U + unifSpec) ⊂ₒ
      (duplexSpongeOracle StmtIn U + unifSpec) := by
  let hPermutation :
      forwardPermutationOracle (CanonicalSpongeState U) ⊂ₒ
        permutationOracle (CanonicalSpongeState U) :=
    OracleQuery.subSpec_add_left
  let hDuplex :
      duplexSpongeForwardOracle StmtIn U ⊂ₒ
        duplexSpongeOracle StmtIn U :=
    OracleQuery.subSpec_right_add_right_add_of_subSpec (h := hPermutation)
  exact OracleQuery.subSpec_left_add_left_add_of_subSpec (h := hDuplex)

/-- Canonical embedding of the forward-only compiler into the full DSFS oracle.  In particular,
permutation queries are mapped to `p`, never to the response-compatible `p⁻¹` slot. -/
def liftForwardToFull {A : Type}
    (oa : OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec) A) :
    OracleComp (duplexSpongeOracle StmtIn U + unifSpec) A :=
  @OracleComp.liftComp _ _ _ _ oa _
    (@instMonadLiftTOfMonadLift _ _ _
      (forwardToFullSubSpec (StmtIn := StmtIn) (U := U)).toMonadLift
      (instMonadLiftT _))

/-- `liftForwardToFull` commutes with monadic bind. -/
@[simp]
theorem liftForwardToFull_bind {A B : Type}
    (oa : OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec) A)
    (ob : A → OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec) B) :
    liftForwardToFull (StmtIn := StmtIn) (U := U) (oa >>= ob) =
      liftForwardToFull (StmtIn := StmtIn) (U := U) oa >>= fun x =>
        liftForwardToFull (StmtIn := StmtIn) (U := U) (ob x) := by
  simp only [liftForwardToFull, OracleComp.liftComp_bind]

/-- Compile one complete public-coin view by first sampling an exact uniform preimage of its full
verifier message tuple, then invoking the common exact-plan compiler. -/
def compileSimulatedView
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (view : Reduction.IPVerifierView StmtIn pSpec) :
    OracleComp (duplexSpongeForwardOracle StmtIn U + unifSpec)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ × PermutationProgram U) := do
  let encodedVerifierMessages ← liftUniformToForward
    (StmtIn := StmtIn) (U := U)
    (sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) view.2.challenges)
  compilePlannedView (pSpec := pSpec) (U := U) δ view.1
    (view.2.messages, encodedVerifierMessages)

/-- Shared exact-plan compiler for Hybrids 1--3. -/
def dsfsPlannedViewCompiler
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) :
    Reduction.NARGZKViewCompiler
      (duplexSpongeOracle StmtIn U)
      StmtIn (PlannedVerifierView (pSpec := pSpec) (U := U))
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) (PermutationProgram U) :=
  fun stmt view =>
    liftForwardToFull (StmtIn := StmtIn) (U := U)
      (compilePlannedView (pSpec := pSpec) (U := U) δ stmt view)

/-- **[CO25, Figure 5]** Common randomized compiler for Hybrids 3 and 4.

It samples exact decoder preimages and then invokes `compilePlannedView`.  The statement selected
by the NARG adversary is authoritative; the redundant first component carried by the supplied
view is deliberately ignored. -/
def dsfsViewCompiler
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) :
    Reduction.NARGZKViewCompiler
      (duplexSpongeOracle StmtIn U)
      StmtIn (Reduction.IPVerifierView StmtIn pSpec)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) (PermutationProgram U) :=
  fun stmt view =>
    liftForwardToFull (StmtIn := StmtIn) (U := U)
      (compileSimulatedView (pSpec := pSpec) (U := U) δ (stmt, view.2))

/-- **[CO25, Construction 7.5]** Simulator, steps 1--11.

`viewSimulator` supplies the simulated public-coin view in step 1.  `dsfsViewCompiler` samples the
salt and encoded verifier-message preimages, runs `ProgramBlocks` in every verifier round, and
returns the NARG string and program.  The paper's hash program is empty; Lean therefore stores only
the permutation edges, with inverse entries derived during installation. -/
def dsfsZKSimulator
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (stmt : StmtIn) :
    OracleComp (duplexSpongeOracle StmtIn U + unifSpec)
      (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ × PermutationProgram U) := do
  let simulatedView ← liftForwardToFull (StmtIn := StmtIn) (U := U)
    (liftUniformToForward (StmtIn := StmtIn) (U := U) (viewSimulator stmt))
  dsfsViewCompiler (pSpec := pSpec) (U := U) δ stmt simulatedView

/-! ## Full adaptive Hybrids 0--4 -/

/-- **[CO25, Figure 5]** Hybrid 0: the real adaptive experiment with the honest salted DSFS prover.

With `D_𝔖.sample` and `duplexSpongeOracleQueryImpl`, this is the left endpoint of Claim 7.6. -/
def hyb0Exp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKRealExp sampleOracle oracleImpl
    (referenceZKProver (pSpec := pSpec) (U := U) δ prover) adversary

/-- **[CO25, Figure 5]** Plan-first Lean presentation of Hybrid 1.

The experiment samples encoded verifier messages uniformly in line 11, decodes them for the honest
prover, programs the corresponding permutation states, and runs the second adversarial stage
against the programmed oracle. -/
def hyb1Exp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (hyb1PlannedView (pSpec :=
    pSpec) (U := U) coinImpl prover)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary

/-- **[CO25, Figure 5]** Plan-first Lean presentation of Hybrid 2.

Relative to Hybrid 1, line 11 decodes a uniform encoded verifier message and then resamples an exact
uniform member of the same decoder fiber. -/
def hyb2Exp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (hyb2PlannedView (pSpec :=
    pSpec) (U := U) coinImpl prover)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary

/-- **[CO25, Figure 5]** Plan-first presentation of Hybrid 3.

Line 11 first samples an honest verifier message and then an exact uniform encoded preimage.
`evalDist_hyb3Exp_eq_hyb3NormalizedPlanExp` identifies this with `hyb3NormalizedPlanExp`, where the
honest-verifier view is factored out for Claim 7.11. -/
def hyb3Exp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (hyb3PlannedView (pSpec :=
    pSpec) (U := U) coinImpl prover)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary

/-- Hybrid 3 normalized through an honest public-coin verifier view. The source view includes
the encoded preimage samples, and the DSFS compiler uses standard uniform private coins. -/
def hyb3NormalizedPlanExp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (fun stmt wit => do
      let view ← Reduction.honestVerifierView coinImpl prover stmt wit
      planVerifierView (U := U) view)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary

/-- The plan-first and honest-view presentations of the complete Hybrid 3 experiment are
distributionally identical. -/
theorem evalDist_hyb3Exp_eq_hyb3NormalizedPlanExp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    (letI : MeasurableSpace Output := ⊤
    𝒟[hyb3Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl prover
      adversary] =
      𝒟[hyb3NormalizedPlanExp
        (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
        coinImpl prover adversary]) := by
  exact Reduction.evalDist_adaptiveNARGZKViewExp_congr
    sampleOracle oracleImpl programImpl (hyb3PlannedView (pSpec := pSpec) (U := U) coinImpl prover)
    (fun stmt wit => do
      let view ← Reduction.honestVerifierView coinImpl prover stmt wit
      planVerifierView (U := U) view)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary
    (fun stmt wit _ =>
      evalDist_hyb3PlannedView_eq_honestVerifierView_bind_planVerifierView
        (U := U) coinImpl prover stmt wit)

/-- **[CO25, Claim 7.9]** For the complete adaptive experiment:
Hybrid 1 and Hybrid 2 are identically distributed.

The result holds for any common sampler, interpreter and programming function. Instantiating
them with `D_𝔖.sample`, `duplexSpongeOracleQueryImpl` and `dsfsProgrammedQueryImpl` gives
the Figure 5 experiments. -/
theorem evalDist_hyb1Exp_eq_hyb2Exp
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    (letI : MeasurableSpace Output := ⊤
    𝒟[hyb1Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl prover
      adversary] =
      𝒟[hyb2Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl prover
        adversary]) := by
  exact Reduction.evalDist_adaptiveNARGZKViewExp_congr
    sampleOracle oracleImpl programImpl (hyb1PlannedView (pSpec := pSpec) (U := U) coinImpl prover)
    (hyb2PlannedView (pSpec := pSpec) (U := U) coinImpl prover)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary
    (fun stmt wit _ =>
      evalDist_hyb1PlannedView_eq_hyb2PlannedView
        (U := U) coinImpl prover stmt wit)

/-- **[CO25, Figure 5]** Hybrid 4.

The honest interactive view in Hybrid 3 is replaced by the statement-only simulator from
Definition 7.3; the exact-preimage compiler and adaptive continuation are unchanged. -/
def hyb4Exp
    {WitIn Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    ProbComp Output :=
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (fun stmt _ =>
    viewSimulator stmt)
    (dsfsViewCompiler (pSpec := pSpec) (U := U) δ) adversary

end DuplexSpongeFS.ZeroKnowledge
