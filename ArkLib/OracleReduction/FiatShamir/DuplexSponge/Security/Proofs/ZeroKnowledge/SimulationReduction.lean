/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ZeroKnowledge.Defs
public import VCVio.OracleComp.EvalDist.DiscreteTVDistPi

/-!
# Zero knowledge of duplex-sponge Fiat–Shamir (Theorem 7.1)

This file formalizes the suffix from Hybrid 1 to the simulator in [CO25, Figure 5] and isolates the
Hybrid 0–1 estimate needed for Theorem 7.1.

## Paper correspondence

* `evalDist_hyb1Exp_eq_hyb2Exp` proves Claim 7.9, identifying Hybrids 1 and 2.
* `discreteTVDist_hyb2Exp_hyb3Exp_le` proves Claim 7.10 directly from the
  codec total-variation contract:
  `Δ(Hyb₂, Hyb₃) ≤ ∑ i, codec.decodingBias i`.
* `discreteTVDist_hyb3Exp_hyb4Exp_le` exposes Claim 7.11 for the complete adaptive experiments,
  using `discreteTVDist_hyb3NormalizedPlanExp_hyb4PlanExp_le` for the view comparison:
  `Δ(Hyb₃, Hyb₄) ≤ zIP`.
* `hyb4Exp_eq_adaptiveNARGZKSimExp` identifies Hybrid 4 with Definition 7.4's simulated
  experiment instantiated by Construction 7.5.
* `reference_adaptiveNARG_zeroKnowledgeWithSimulator_of_hybrid_bound` composes these results
  with a supplied Hybrid 0–1 error bound.

## Formalization boundary

The composition takes a Hybrid 0–1 bound (Claim 7.6) as a hypothesis, which the public
theorems discharge with the proved first-transition estimates. Its codec term is Claim 7.10's
sum.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ZeroKnowledge

variable {n : ℕ} {pSpec : ProtocolSpec n}
  {StmtIn U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U]

/- Keep the samplers used by the Section 7 notation canonical and local. The underlying
definitions are explicit so this file does not restore the global sampling diamonds removed by
the Section 5 cleanup. -/
local instance sampleableEncodedVerifierMessagesInst [VCVCompatible U] :
    SampleableType (EncodedVerifierMessages (pSpec := pSpec) (U := U)) :=
  sampleableEncodedVerifierMessages

local instance sampleableVerifierMessagesInst
    [∀ i, VCVCompatible (pSpec.Challenge i)] :
    SampleableType pSpec.Challenges :=
  sampleableVerifierMessages

local instance sampleableVerifierMessageInst
    [∀ i, VCVCompatible (pSpec.Challenge i)] (i : pSpec.ChallengeIdx) :
    SampleableType (pSpec.Challenge i) :=
  VCVCompatible.toSampleableType

local instance sampleableEncodedVerifierMessageInst
    [VCVCompatible U] (i : pSpec.ChallengeIdx) :
    SampleableType (EncodedVerifierMessage (pSpec := pSpec) (U := U) i) :=
  VCVCompatible.toSampleableType

omit [SpongeUnit U] [SpongeSize] in
/-- The full dependent verifier message tuple inherits the sum of the exact per-round TV bounds. -/
theorem discreteTVDist_decodeVerifierMessages_uniform_le_sum
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    discreteTVDist
        (decodeVerifierMessages (pSpec := pSpec) (U := U) <$>
          ($ᵗ (EncodedVerifierMessages (pSpec := pSpec) (U := U))))
        ($ᵗ pSpec.Challenges) ≤
      ∑ i, (codec.decodingBias i : ℝ) := by
  convert
    (OracleComp.discreteTVDist_map_uniform_pi_le_sum
      (A := fun i : pSpec.ChallengeIdx => pSpec.Challenge i)
      (B := fun i : pSpec.ChallengeIdx =>
        EncodedVerifierMessage (pSpec := pSpec) (U := U) i)
      (fun i => codec.decode i)
      (fun i => (codec.decodingBias i : ℝ))
      (fun i => by
        rw [discreteTVDist.comm]
        exact codec_round_probComp_tvDist_le_bias
          (pSpec := pSpec) (U := U) i)) using 1
  rfl

private def verifierMessagePlanPreimagePair
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (verifierMessages : pSpec.Challenges) :
    ProbComp (VerifierMessagePlan (pSpec := pSpec) (U := U)) := do
  let encoded ←
    sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) verifierMessages
  pure (verifierMessages, encoded)

omit [SpongeUnit U] [SpongeSize] in
/-- Resampling a decoded fiber records the same decoded verifier message tuple. -/
private theorem hyb2VerifierMessagePlan_eq_bind
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    hyb2VerifierMessagePlan (pSpec := pSpec) (U := U) =
      ((decodeVerifierMessages (pSpec := pSpec) (U := U) <$>
          ($ᵗ (EncodedVerifierMessages (pSpec := pSpec) (U := U)))) >>=
        verifierMessagePlanPreimagePair (pSpec := pSpec) (U := U)) := by
  rw [hyb2VerifierMessagePlan, bind_map_left]
  refine bind_congr fun encoded' => ?_
  simp_rw [verifierMessagePlanPreimagePair,
    sampleEncodedVerifierMessagesPreimage, bind_pure_comp]
  exact OracleComp.UniformPreimage.map_sampleUniformPreimage_decode_pair
    (decodeVerifierMessages (pSpec := pSpec) (U := U))
    (decodeVerifierMessages (pSpec := pSpec) (U := U) encoded')
    (OracleComp.UniformPreimage.preimage_apply_nonempty
      (decodeVerifierMessages (pSpec := pSpec) (U := U)) encoded')

omit [SpongeUnit U] [SpongeSize] in
/-- **[CO25, Claim 7.10]** verifier message-plan reduction used in the proof.

It bounds the distance between the Hybrid 2 and Hybrid 3 verifier message plans by the sum of the
per-round codec TV bounds. -/
theorem discreteTVDist_hyb2VerifierMessagePlan_hyb3VerifierMessagePlan_le
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)] :
    discreteTVDist
        (hyb2VerifierMessagePlan (pSpec := pSpec) (U := U))
        (hyb3VerifierMessagePlan (pSpec := pSpec) (U := U)) ≤
      ∑ i, (codec.decodingBias i : ℝ) := by
  rw [hyb2VerifierMessagePlan_eq_bind]
  exact (discreteTVDist.bind_le _ _
    (verifierMessagePlanPreimagePair (pSpec := pSpec) (U := U))).trans
      (discreteTVDist_decodeVerifierMessages_uniform_le_sum (pSpec := pSpec) (U := U))

omit [SpongeUnit U] [SpongeSize] in
/-- **[CO25, Claim 7.10]** Prover-view reduction used in the proof.

Applying the same prover to the two verifier message plans preserves the summed TV bound. -/
theorem discreteTVDist_hyb2PlannedView_hyb3PlannedView_le
    {StmtIn WitIn StmtOut WitOut : Type}
    [VCVCompatible U] [∀ i, VCVCompatible (pSpec.Challenge i)]
    (coinImpl : QueryImpl unifSpec ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) :
    discreteTVDist
        (hyb2PlannedView (U := U) coinImpl prover stmt wit)
        (hyb3PlannedView (U := U) coinImpl prover stmt wit) ≤
      ∑ i, (codec.decodingBias i : ℝ) := by
  exact (discreteTVDist.bind_le _ _
    (materializeVerifierMessagePlan (U := U) coinImpl prover stmt wit)).trans
      (discreteTVDist_hyb2VerifierMessagePlan_hyb3VerifierMessagePlan_le (pSpec := pSpec) (U := U))

/-- **[CO25, Claim 7.10]** For the full adaptive experiments, the per-round TV bounds stored in
`Codec.decodingBias` give `Δ(Hyb₂, Hyb₃) ≤ ∑ i, codec.decodingBias i`.

The paper writes the arguments as `(Hyb₃, Hyb₂)`; Lean uses the symmetric order shown in the
theorem statement.  Both adversarial stages, oracle programming, and the common compiler are
included. -/
theorem discreteTVDist_hyb2Exp_hyb3Exp_le
    {StmtIn WitIn StmtOut WitOut Output : Type}
    {admissible : StmtIn → WitIn → Prop}
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
    discreteTVDist
        (hyb2Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl prover
          adversary)
        (hyb3Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl
          prover adversary) ≤
      ∑ i, (codec.decodingBias i : ℝ) := by
  exact Reduction.discreteTVDist_adaptiveNARGZKViewExp_le
    sampleOracle oracleImpl programImpl (hyb2PlannedView (pSpec := pSpec) (U := U) coinImpl prover)
    (hyb3PlannedView (pSpec := pSpec) (U := U) coinImpl prover)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ)
    adversary
    (∑ i, (codec.decodingBias i : ℝ))
    (Finset.sum_nonneg fun i _ => NNReal.coe_nonneg _)
    (fun stmt wit _ =>
      discreteTVDist_hyb2PlannedView_hyb3PlannedView_le
        (pSpec := pSpec) (U := U) coinImpl prover stmt wit)

/-- **[CO25, Figure 5]** Planned-view presentation of Hybrid 4.

The simulator's view is postprocessed by the same exact-preimage sampler and DSFS compiler as the
normalized presentation of Hybrid 3. -/
def hyb4PlanExp
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
  Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (fun stmt _ => do
      let view ← viewSimulator stmt
      planVerifierView (pSpec := pSpec) (U := U) view)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary

/-- **[CO25, Claim 7.11]** Planned-view form:
`Δ(Hyb₃, Hyb₄) ≤ zIP`.

Lean compares normalized Hybrid 3 with planned Hybrid 4 in the symmetric order.  Definition 7.3's
HVZK bound is preserved by the common exact-preimage sampler, DSFS compiler, oracle programming,
and adaptive continuation. -/
theorem discreteTVDist_hyb3NormalizedPlanExp_hyb4PlanExp_le
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
    (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible)
    (zIP : ℝ) (hzIP : 0 ≤ zIP)
    (hHVZK : ∀ stmt wit, admissible stmt wit →
      discreteTVDist (Reduction.honestVerifierView coinImpl prover stmt wit)
        (viewSimulator stmt) ≤ zIP) :
    discreteTVDist
      (hyb3NormalizedPlanExp
        (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl coinImpl prover adversary)
      (hyb4PlanExp
        (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl  viewSimulator
          adversary) ≤ zIP := by
  exact Reduction.discreteTVDist_adaptiveNARGZKViewExp_le
    sampleOracle oracleImpl programImpl (fun stmt wit => do
      let view ← Reduction.honestVerifierView coinImpl prover stmt wit
      planVerifierView (pSpec := pSpec) (U := U) view)
    (fun stmt _ => do
      let view ← viewSimulator stmt
      planVerifierView (pSpec := pSpec) (U := U) view)
    (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary zIP hzIP
    (fun stmt wit hAdmissible =>
      (discreteTVDist.bind_le
        (Reduction.honestVerifierView coinImpl prover stmt wit)
        (viewSimulator stmt)
        (planVerifierView (pSpec := pSpec) (U := U))).trans
          (hHVZK stmt wit hAdmissible))

/-! ## Fusion with [CO25, Figure 5]'s view-compiler presentation -/

private theorem simulate_nested_lift_probComp
    {A : Type}
    (publicImpl : QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (oa : ProbComp A) :
    simulateQ (publicImpl + QueryImpl.id' unifSpec)
      (liftForwardToFull (StmtIn := StmtIn) (U := U)
        (liftUniformToForward (StmtIn := StmtIn) (U := U) oa)) = oa := by
  simp only [liftForwardToFull, liftUniformToForward, OracleComp.liftComp_def]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  trans simulateQ (QueryImpl.id' unifSpec) oa
  · congr 1
  · exact simulateQ_id' oa

private theorem simulateQ_dsfsZKSimulator
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ) (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (publicImpl : QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (stmt : StmtIn) :
    simulateQ (publicImpl + QueryImpl.id' unifSpec)
        (dsfsZKSimulator (pSpec := pSpec) (U := U) δ viewSimulator stmt) =
      (viewSimulator stmt >>= fun view =>
        simulateQ (publicImpl + QueryImpl.id' unifSpec)
          (dsfsViewCompiler (pSpec := pSpec) (U := U) δ stmt view)) := by
  simp only [dsfsZKSimulator, simulateQ_bind]
  rw [simulate_nested_lift_probComp]

/-- Compiler-level fusion, before the programmed-oracle adversarial continuation is attached. -/
private theorem simulateQ_dsfsViewCompiler_eq_plan
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    (publicImpl : QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (stmt : StmtIn) (view : Reduction.IPVerifierView StmtIn pSpec) :
    simulateQ (publicImpl + QueryImpl.id' unifSpec)
        (dsfsViewCompiler (pSpec := pSpec) (U := U) δ stmt view) =
      (planVerifierView (pSpec := pSpec) (U := U) view >>= fun plan =>
        simulateQ (publicImpl + QueryImpl.id' unifSpec)
          (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ stmt plan)) := by
  simp only [dsfsViewCompiler, compileSimulatedView, dsfsPlannedViewCompiler,
    planVerifierView, liftForwardToFull_bind, simulateQ_bind]
  simp only [bind_assoc, pure_bind]
  rw [simulate_nested_lift_probComp (StmtIn := StmtIn) (U := U) publicImpl
    (sampleEncodedVerifierMessagesPreimage (pSpec := pSpec) (U := U) view.2.challenges)]

/-- Fusion after installing the compiler's program and running the second adversarial stage. -/
private theorem adaptiveNARGZKViewPostprocess_plan_eq_view
    {WitIn Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type}
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible)
    (realization : Carrier) (state : adversary.State)
    (stmt : StmtIn) (view : Reduction.IPVerifierView StmtIn pSpec) :
    (planVerifierView (pSpec := pSpec) (U := U) view >>= fun plan =>
      Reduction.adaptiveNARGZKViewPostprocess oracleImpl programImpl (dsfsPlannedViewCompiler
        (pSpec := pSpec) (U := U) δ) adversary
        realization state stmt plan) =
      Reduction.adaptiveNARGZKViewPostprocess oracleImpl programImpl (dsfsViewCompiler (pSpec :=
        pSpec) (U := U) δ) adversary
        realization state stmt view := by
  simp only [Reduction.adaptiveNARGZKViewPostprocess]
  rw [simulateQ_dsfsViewCompiler_eq_plan
    (pSpec := pSpec) (U := U) δ (oracleImpl realization) stmt view]
  simp only [bind_assoc]

/-- With the canonical uniform-coin handler, sampling the encoded plan in the source view is
distributionally identical to sampling it inside the DSFS view compiler.  The restriction on the
handler is essential: an arbitrary handler may change the distribution of lifted coin queries. -/
theorem evalDist_planViewCompiler_fusion
    {WitIn Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (viewSource : StmtIn → WitIn →
      ProbComp (Reduction.IPVerifierView StmtIn pSpec))
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible) :
    (letI : MeasurableSpace Output := ⊤
    𝒟[Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl (fun stmt wit => do
        let view ← viewSource stmt wit
        planVerifierView (pSpec := pSpec) (U := U) view)
      (dsfsPlannedViewCompiler (pSpec := pSpec) (U := U) δ) adversary] =
    𝒟[Reduction.adaptiveNARGZKViewExp sampleOracle oracleImpl programImpl viewSource
      (dsfsViewCompiler (pSpec := pSpec) (U := U) δ) adversary]) := by
  congr 1
  simp only [Reduction.adaptiveNARGZKViewExp]
  refine bind_congr fun ⟨realization, xw, state⟩ => ?_
  rw [bind_assoc]
  refine bind_congr fun view => ?_
  exact adaptiveNARGZKViewPostprocess_plan_eq_view
    (pSpec := pSpec) (U := U) δ oracleImpl programImpl adversary
    realization state (xw : StmtIn × WitIn).1 view

/-- For canonical uniform coins, planned Hybrid 4 is distributionally equal to the
[CO25, Figure 5] compiler-based Hybrid 4. -/
theorem evalDist_hyb4PlanExp_eq_hyb4Exp
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
    (letI : MeasurableSpace Output := ⊤
    𝒟[hyb4PlanExp (pSpec := pSpec) (U := U)
      δ sampleOracle oracleImpl programImpl  viewSimulator adversary] =
    𝒟[hyb4Exp (pSpec := pSpec) (U := U)
      δ sampleOracle oracleImpl programImpl  viewSimulator adversary]) := by
  exact evalDist_planViewCompiler_fusion (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl
    programImpl
    (fun stmt _ => viewSimulator stmt) adversary

/-- With canonical uniform coins, full Hybrid 4 is exactly [CO25, Definition 7.4]'s simulated
experiment instantiated with the simulator from Construction 7.5. -/
theorem hyb4Exp_eq_adaptiveNARGZKSimExp
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
    hyb4Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
        viewSimulator adversary =
      Reduction.adaptiveNARGZKSimExp sampleOracle oracleImpl programImpl
        (dsfsZKSimulator (pSpec := pSpec) (U := U) δ viewSimulator) adversary := by
  simp only [hyb4Exp, Reduction.adaptiveNARGZKViewExp,
    Reduction.adaptiveNARGZKPrefix, Reduction.adaptiveNARGZKViewPostprocess,
    Reduction.adaptiveNARGZKSimExp]
  simp only [bind_assoc]
  congr 1
  funext realization
  congr 1
  funext choice
  rw [simulateQ_dsfsZKSimulator
    (pSpec := pSpec) (U := U) δ viewSimulator (oracleImpl realization)
    (choice.1 : StmtIn × WitIn).1]
  simp only [bind_assoc, pure_bind]

/-- The complete adaptive Hybrid 3–4 transition has statistical distance at most `zIP`
when the honest-verifier view error is bounded by `zIP` on every admissible input.
The common compiler and adversarial continuation preserve this bound. -/
theorem discreteTVDist_hyb3Exp_hyb4Exp_le
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible)
    (zIP : ℝ) (hzIP : 0 ≤ zIP)
    (hHVZK : ∀ stmt wit, admissible stmt wit →
      discreteTVDist
        (Reduction.honestVerifierView (QueryImpl.id' unifSpec) prover stmt wit)
        (viewSimulator stmt) ≤ zIP) :
    discreteTVDist
      (hyb3Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
        (QueryImpl.id' unifSpec) prover adversary)
      (hyb4Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
         viewSimulator adversary) ≤ zIP := by
  rw [discreteTVDist.congr_evalDistEq
    (evalDistEq_iff_evalDist_eq.mpr (evalDist_hyb3Exp_eq_hyb3NormalizedPlanExp
      (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
      (QueryImpl.id' unifSpec) prover adversary))
    (evalDistEq_iff_evalDist_eq.mpr (evalDist_hyb4PlanExp_eq_hyb4Exp
      (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
      viewSimulator adversary).symm)]
  exact discreteTVDist_hyb3NormalizedPlanExp_hyb4PlanExp_le (pSpec := pSpec) (U := U)
    δ sampleOracle oracleImpl programImpl (QueryImpl.id' unifSpec)
    prover viewSimulator adversary zIP hzIP hHVZK

/-- Supporting lemma for **[CO25, Theorem 7.1]**. The complete verified Hybrid 1–4 suffix.

The distance from Hybrid 1 to Definition 7.4's simulated experiment instantiated by
Construction 7.5 is at most
`(∑ i, codec.decodingBias i) + zIP`. -/
theorem discreteTVDist_hyb1Exp_adaptiveNARGZKSimExp_le_sum
    {WitIn StmtOut WitOut Output : Type} {admissible : StmtIn → WitIn → Prop}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (δ : ℕ)
    {Carrier : Type} (sampleOracle : ProbComp Carrier)
    (oracleImpl : Carrier → QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (programImpl : Carrier → PermutationProgram U →
      QueryImpl (duplexSpongeOracle StmtIn U) ProbComp)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (adversary : Reduction.NARGZKAdversary
      (duplexSpongeOracle StmtIn U)
      StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) δ) Output admissible)
    (zIP : ℝ) (hzIP : 0 ≤ zIP)
    (hHVZK : ∀ stmt wit, admissible stmt wit →
      discreteTVDist
        (Reduction.honestVerifierView (QueryImpl.id' unifSpec) prover stmt wit)
        (viewSimulator stmt) ≤ zIP) :
    discreteTVDist
      (hyb1Exp (pSpec := pSpec) (U := U)
        δ sampleOracle oracleImpl programImpl (QueryImpl.id' unifSpec) prover adversary)
      (Reduction.adaptiveNARGZKSimExp sampleOracle oracleImpl programImpl
        (dsfsZKSimulator (pSpec := pSpec) (U := U) δ viewSimulator) adversary) ≤
      (∑ i, (codec.decodingBias i : ℝ)) + zIP := by
  rw [← hyb4Exp_eq_adaptiveNARGZKSimExp
    (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl viewSimulator adversary]
  rw [discreteTVDist.congr_evalDistEq
    (evalDistEq_iff_evalDist_eq.mpr (evalDist_hyb1Exp_eq_hyb2Exp (pSpec := pSpec) (U := U)
      δ sampleOracle oracleImpl programImpl
      (QueryImpl.id' unifSpec) prover adversary))
    (evalDistEq_iff_evalDist_eq.mpr (evalDist_hyb4PlanExp_eq_hyb4Exp
      (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl viewSimulator
        adversary).symm)]
  have h₃₄ : discreteTVDist
      (hyb3Exp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
        (QueryImpl.id' unifSpec) prover adversary)
      (hyb4PlanExp (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
         viewSimulator adversary) ≤ zIP := by
    rw [discreteTVDist.congr_evalDistEq .rfl
      (evalDistEq_iff_evalDist_eq.mpr (evalDist_hyb4PlanExp_eq_hyb4Exp
        (pSpec := pSpec) (U := U) δ sampleOracle oracleImpl programImpl
        viewSimulator adversary))]
    exact discreteTVDist_hyb3Exp_hyb4Exp_le (pSpec := pSpec) (U := U)
      δ sampleOracle oracleImpl programImpl prover viewSimulator adversary
      zIP hzIP hHVZK
  exact (discreteTVDist.triangle _ _ _).trans (add_le_add
    (discreteTVDist_hyb2Exp_hyb3Exp_le (pSpec := pSpec) (U := U)
      δ sampleOracle oracleImpl programImpl (QueryImpl.id' unifSpec) prover adversary) h₃₄)

/-! ## Theorem 7.1 reduction boundary -/

/-- Error bound for the verified hybrid reduction.

`hyb0Hyb1Error` is the supplied Hybrid 0–1 error.  The other terms are Definition 7.3's
honest-view error and Claim 7.10's sum of exact codec TV bounds. -/
def simulationReductionBound (c : Codec pSpec U)
    (zIP hyb0Hyb1Error : ℝ) : ℝ :=
  zIP + hyb0Hyb1Error + ∑ i, (c.decodingBias i : ℝ)

/-- **[CO25, Construction 7.5]** Named-simulator reduction for Theorem 7.1, assuming a Hybrid 0–1
bound: if `viewSimulator` is a uniform-error honest-verifier simulator for the IP, then
`dsfsZKSimulator delta viewSimulator` simulates the DSFS argument for the public-query budget `t`
with error `zIP + hyb0Hyb1Error t + ∑ εᵢ`. -/
theorem reference_adaptiveNARG_zeroKnowledgeWithSimulator_of_hybrid_bound
    {WitIn StmtOut WitOut : Type}
    [VCVCompatible StmtIn] [VCVCompatible U]
    [∀ i, VCVCompatible (pSpec.Challenge i)]
    (delta : ℕ)
    (prover : Prover unifSpec StmtIn WitIn StmtOut WitOut pSpec)
    (relation : Set (StmtIn × WitIn))
    (zIP : ℝ) (hyb0Hyb1Error : ℕ → ℝ) (hzIP : 0 ≤ zIP)
    (viewSimulator : Reduction.HonestVerifierSimulator StmtIn pSpec)
    (hHVZK : ∀ stmt wit, (stmt, wit) ∈ relation →
      discreteTVDist
        (Reduction.honestVerifierView (QueryImpl.id' unifSpec) prover stmt wit)
        (viewSimulator stmt) ≤ zIP)
    (hHybridZeroOne : ∀ (t : ℕ) (Output : Type)
      (adversary : Reduction.NARGZKAdversary
        (duplexSpongeOracle StmtIn U)
        StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) delta) Output
          (fun stmt wit => (stmt, wit) ∈ relation)),
      HasPublicQueryBound adversary t →
        discreteTVDist
          (hyb0Exp (pSpec := pSpec) (U := U) delta
            (D_𝔖.sample StmtIn U) duplexSpongeOracleQueryImpl
             prover adversary)
          (hyb1Exp (pSpec := pSpec) (U := U) delta
            (D_𝔖.sample StmtIn U) duplexSpongeOracleQueryImpl dsfsProgrammedQueryImpl
            (QueryImpl.id' unifSpec) prover adversary) ≤ hyb0Hyb1Error t)
    (t : ℕ) :
    ∀ (Output : Type)
      (adversary : Reduction.NARGZKAdversary (duplexSpongeOracle StmtIn U)
        StmtIn WitIn (DSFSTypedNARGString (pSpec := pSpec) (U := U) delta) Output
        (fun stmt wit => (stmt, wit) ∈ relation)),
      adversary.HasAggregateQueryBound (fun _ => True) t →
        discreteTVDist
          (Reduction.adaptiveNARGZKRealExp (D_𝔖.sample StmtIn U) duplexSpongeOracleQueryImpl
            (referenceZKProver (U := U) delta prover) adversary)
          (Reduction.adaptiveNARGZKSimExp (D_𝔖.sample StmtIn U) duplexSpongeOracleQueryImpl
            dsfsProgrammedQueryImpl (dsfsZKSimulator (U := U) delta viewSimulator) adversary) ≤
          simulationReductionBound (pSpec := pSpec) (U := U) codec zIP (hyb0Hyb1Error t) := by
  intro Output adversary hBounds
  have h₀₁ := hHybridZeroOne t Output adversary hBounds
  have h₁sim := discreteTVDist_hyb1Exp_adaptiveNARGZKSimExp_le_sum
    (pSpec := pSpec) (U := U) delta
    (D_𝔖.sample StmtIn U) duplexSpongeOracleQueryImpl dsfsProgrammedQueryImpl
    prover viewSimulator adversary zIP hzIP hHVZK
  calc
    _ ≤ hyb0Hyb1Error t + ((∑ i, (codec.decodingBias i : ℝ)) + zIP) :=
      (discreteTVDist.triangle _ _ _).trans (add_le_add h₀₁ h₁sim)
    _ = _ := by unfold simulationReductionBound; ring

end DuplexSpongeFS.ZeroKnowledge
