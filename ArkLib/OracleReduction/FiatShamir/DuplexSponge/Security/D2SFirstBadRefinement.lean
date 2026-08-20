/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.RevisedHybridGame
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadArithmetic

/-!
# Exact adaptive refinement for the revised Hyb₁ verifier

The first-bad runner is deliberately fuel-bounded and retains its verifier residual.  The live
Hyb₁ D2F interpreter instead executes that residual directly under `StateT` and `ExceptT`.
This file proves the lossless bridge between those two presentations.  It is separate from the
probability arithmetic: the bridge preserves the complete value/state/stop result, while the
first-bad theorem subsequently charges only its monitor-stop face.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.KeyLemma

open DuplexSpongeFS.ProverTransform DuplexSpongeFS.DSTraceStorage

variable {n : ℕ} {pSpec : ProtocolSpec n} {StmtIn StmtOut : Type}
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, VCVCompatible (pSpec.Message i)] [codec : CodecCore pSpec U]
  {δ : ℕ} [DecidableEq StmtIn] [DecidableEq U]
  {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- The three paper budgets on a Lemma-5.8 malicious prover give an ordinary all-request bound
on its empty-lifted `DS` program.  This is the exact normalization needed to run the prover
through the stateful first-bad runner: because the ambient oracle is `[]ₒ`, every possible query
is a right-summand D2S request. -/
lemma maliciousProver_isQueryBound_all
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    IsQueryBoundP maliciousProver (fun _ => True) (tₕ + tₚ + tₚᵢ) := by
  have hRight : IsQueryBoundP maliciousProver (fun point => point.isRight = true)
      (tₕ + tₚ + tₚᵢ) :=
    BadEventDS.isQueryBoundP_isRight_of_classes hBound.1 hBound.2.1 hBound.2.2
  rw [isQueryBoundP_congr_pred (p' := fun _ => True)] at hRight
  · exact hRight
  · rintro (impossible | query)
    · exact PEmpty.elim impossible
    · simp

/-- The same paper event bound for a state-threaded adaptive kernel.  This is the reusable
bridge for a live hybrid controller whose state contains an eager challenge table and a residual
program: the terminal trace is bad exactly at its retained monitor stop. -/
lemma d2sQueryRunRevisedAdaptiveWithStep_terminalBad_le_badEventBound
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (contract : D2SAdaptiveKernelFirstBadContract kernel)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (fuel : ℕ) (controlState : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (j : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j) :
    Pr[ fun result => BadEventDS.E result.terminalTrace |
      d2sQueryRunRevisedAdaptiveWithStep kernel control fuel controlState normal] ≤
      ENNReal.ofReal (Statement.badEventBound U (j + fuel)) := by
  rw [show (fun result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S =>
      BadEventDS.E result.terminalTrace) = fun result => result.isMonitorStop by
    funext result
    exact propext (D2SAdaptiveRunResult.isMonitorStop_iff_badEvent_terminalTrace result).symm]
  exact (d2sQueryRunRevisedAdaptiveWithStep_monitorStop_le
    kernel contract control fuel controlState normal j hCoherent hBaseLength).trans
      (Statement.adaptiveD2SCharge_div_le_badEventBoundENN (U := U) j fuel)

/-- Every successful terminal state of a finite adaptive execution inherits the concrete
`RateOnlyCacheCoherent` invariant and gains at most one base-trace occurrence per reached D2S
request.  This is the deterministic prover-to-verifier boundary used by the revised Lemma 5.8
argument: it concerns only successful continuations, so a monitor stop never manufactures a
reusable successor state. -/
lemma d2sQueryRunRevisedAdaptiveWithStep_complete_invariant
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (contract : D2SAdaptiveKernelFirstBadContract kernel)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (fuel : ℕ) (controlState : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (j : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (finalState : S)
    (finalNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hTerminal : .complete finalState finalNormal ∈ support
      (d2sQueryRunRevisedAdaptiveWithStep kernel control fuel controlState normal)) :
    RateOnlyCacheCoherent finalNormal ∧
      (getBaseTrace finalNormal.state.trace).length ≤ j + fuel := by
  induction fuel generalizing controlState normal j finalState finalNormal with
  | zero =>
      cases hNext : control.next controlState normal with
      | done =>
          rw [d2sQueryRunRevisedAdaptiveWithStep, hNext, mem_support_pure_iff] at hTerminal
          injection hTerminal with hState hNormal
          subst finalState
          subst finalNormal
          exact ⟨hCoherent, by simpa using hBaseLength⟩
      | query q advance =>
          rw [d2sQueryRunRevisedAdaptiveWithStep, hNext, mem_support_pure_iff] at hTerminal
          cases hTerminal
  | succ fuel ih =>
      cases hNext : control.next controlState normal with
      | done =>
          rw [d2sQueryRunRevisedAdaptiveWithStep, hNext, mem_support_pure_iff] at hTerminal
          injection hTerminal with hState hNormal
          subst finalState
          subst finalNormal
          exact ⟨hCoherent, by omega⟩
      | query q advance =>
          rw [d2sQueryRunRevisedAdaptiveWithStep, hNext, mem_support_bind_iff] at hTerminal
          obtain ⟨stepResult, hStep, hTerminal⟩ := hTerminal
          cases stepResult with
          | «continue» answer state' normal' =>
              have hInvariant := contract.continueInvariant controlState normal q j hCoherent
                hBaseLength answer state' normal' hStep
              have hFinal := ih (advance state' answer normal') normal' (j + 1)
                hInvariant.1 hInvariant.2 finalState finalNormal hTerminal
              refine ⟨hFinal.1, ?_⟩
              omega
          | stopped stoppedNormal record =>
              rw [mem_support_pure_iff] at hTerminal
              cases hTerminal
          | underlyingAbort =>
              rw [mem_support_pure_iff] at hTerminal
              cases hTerminal

/-- Extract a successful value and its returned normal state from an empty-lifted adaptive
terminal result.  All stopped, search-aborting, fuel-exhausted, and nonterminal residual faces
map to `none`, exactly matching the absorbing-stop convention of the revised Figure-4 game. -/
def d2sAdaptiveRunResultCompletedValue?
    {α : Type}
    (terminal : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)) :
    Option (α × D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :=
  match terminal with
  | .complete (.pure value) normal => some (value, normal)
  | _ => none

/-- Every successful value exposed by `completedValue?` inherits the exact stateful replay
invariant.  This turns the support of the adaptive prover distribution into the pointwise
hypothesis of `hyb1LiveDirect_monitorStop_bind_le_Dcap`, with no manual cache reconstruction. -/
lemma d2sQueryRunRevisedAdaptiveWithStep_completedValue_support_invariant
    {α : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α))
    (contract : D2SAdaptiveKernelFirstBadContract kernel)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α))
    (fuel : ℕ)
    (controlState : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (j : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (terminal : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α))
    (hTerminal : terminal ∈ support
      (d2sQueryRunRevisedAdaptiveWithStep kernel control fuel controlState normal))
    (value : α)
    (finalNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hValue : d2sAdaptiveRunResultCompletedValue? terminal = some (value, finalNormal)) :
    RateOnlyCacheCoherent finalNormal ∧
      (getBaseTrace finalNormal.state.trace).length ≤ j + fuel := by
  cases terminal with
  | complete finalResidual completedNormal =>
      cases finalResidual with
      | pure output =>
          simp only [d2sAdaptiveRunResultCompletedValue?] at hValue
          have hPair : (output, completedNormal) = (value, finalNormal) :=
            Option.some.inj hValue
          have hOutput : output = value := congrArg Prod.fst hPair
          have hNormal : completedNormal = finalNormal := congrArg Prod.snd hPair
          subst value
          subst finalNormal
          exact d2sQueryRunRevisedAdaptiveWithStep_complete_invariant
            kernel contract control fuel controlState normal j hCoherent hBaseLength
            (pure output) completedNormal hTerminal
      | queryBind query continuation =>
          simp [d2sAdaptiveRunResultCompletedValue?] at hValue
  | stopped control stoppedNormal record =>
      simp [d2sAdaptiveRunResultCompletedValue?] at hValue
  | underlyingAbort control abortedNormal =>
      simp [d2sAdaptiveRunResultCompletedValue?] at hValue
  | fuelExhausted control exhaustedNormal =>
      simp [d2sAdaptiveRunResultCompletedValue?] at hValue

/-- Interpret a terminal adaptive verifier result as the exact result shape of the direct
lossless D2F executor.  The two syntactically impossible faces are deliberately classified as
underlying aborts: `complete` can arise only from a pure residual, and `fuelExhausted` is excluded
on support when this one-step fact is lifted to a whole-run refinement using a query-fuel bound. -/
def hyb1AdaptiveTerminalToStopping
    (terminal : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut)) :
    Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit) :=
  match terminal with
  | .complete (_, .pure value) normal => .ok ((value, normal), PUnit.unit)
  | .complete (_, .queryBind _ _) normal => .error (.underlyingAbort normal)
  | .stopped _ normal record => .error (.monitorStop normal record)
  | .underlyingAbort _ normal => .error (.underlyingAbort normal)
  | .fuelExhausted _ normal => .error (.underlyingAbort normal)

/-- Forget the control payload of one adaptive Hyb₁ step while retaining exactly the direct
stopping interpreter's value/state/stop outcome. -/
def hyb1AdaptiveStepToStopping
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    {q : (duplexSpongeChallengeOracle StmtIn U).Domain}
    (result : D2SAdaptiveStepResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut) q) :
    Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((((duplexSpongeChallengeOracle StmtIn U).Range q ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) :=
  match result with
  | .continue answer _ normal' => .ok ((answer, normal'), PUnit.unit)
  | .stopped normal' record => .error (.monitorStop normal' record)
  | .underlyingAbort => .error (.underlyingAbort normal)

/-- The structurally recursive first-bad presentation of a pure-Hyb₁ verifier residual.  It uses
the same one-query revised dispatcher as the live D2F interpreter, but exposes the residual's
ordinary `pure`/`queryBind` structure.  The theorem below identifies it exactly with the
fuel-bounded adaptive runner; the already-proved live-executor refinement remains in
`RevisedHybridGame` and is composed at the experiment boundary. -/
noncomputable def hyb1DirectResidualRun
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut)) :
    D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      ProbComp
        (Except
          (D2SRevisedStoppingReason
            (δ := δ) (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
          ((Option StmtOut ×
            D2SNormalState
              (δ := δ) (T_H := T_H) (T_P := T_P)
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) :=
  OracleComp.recOn residual
    (fun value normal => pure (.ok ((value, normal), PUnit.unit)))
    (fun request _continuation ih normal =>
      match request with
      | .inl impossible => PEmpty.elim impossible
      | .inr query => do
          let result ← simulateQ
            ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
              (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
            (d2sQueryStepRevised normal query)
          match result with
          | .continue answer normal' => ih answer normal'
          | .stopped normal' record => pure (.error (.monitorStop normal' record))
          | .underlyingAbort => pure (.error (.underlyingAbort normal)))

omit [(i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i)] in
/-- The fuel-bounded adaptive first-bad run has the same complete terminal distribution as the
structural direct residual runner whenever the fuel bounds the residual's D2S requests.  The
only purpose of the bound is to exclude the adaptive runner's synthetic `fuelExhausted` result;
it is not a probabilistic estimate. -/
lemma hyb1AdaptiveRun_to_directResidual_eq_of_bound
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (fuel : ℕ)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hBound : IsQueryBoundP residual (fun _ => True) fuel) :
    hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) <$>
        d2sQueryRunRevisedAdaptiveWithStep
          (hyb1VerifierStepKernel
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
          (hyb1VerifierControl
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
          fuel (kSigma, residual) normal =
      hyb1DirectResidualRun (T_H := T_H) (T_P := T_P) kSigma residual normal := by
  induction fuel generalizing residual normal with
  | zero =>
      cases residual with
      | pure value =>
          rfl
      | queryBind query continuation =>
          change IsQueryBoundP (liftM (OracleSpec.query query) >>= continuation)
            (fun _ => True) 0 at hBound
          rw [isQueryBoundP_query_bind_iff] at hBound
          rcases hBound.1 with hFalse | hPositive
          · exact False.elim (hFalse trivial)
          · omega
  | succ fuel ih =>
      cases residual with
      | pure value =>
          rfl
      | queryBind request continuation =>
          change IsQueryBoundP (liftM (OracleSpec.query request) >>= continuation)
            (fun _ => True) (fuel + 1) at hBound
          cases request with
          | inl impossible => exact PEmpty.elim impossible
          | inr request =>
              rw [isQueryBoundP_query_bind_iff] at hBound
              rw [hyb1VerifierControl, D2SAdaptiveControl.ofEmptyLiftedOracleComp,
                d2sQueryRunRevisedAdaptiveWithStep, hyb1DirectResidualRun,
                hyb1VerifierStepKernel]
              simp only [map_eq_pure_bind, bind_assoc]
              apply bind_congr
              intro result
              cases result with
              | «continue» answer normal' =>
                  have hRest : IsQueryBoundP (continuation answer) (fun _ => True) fuel := by
                    simpa using hBound.2 answer
                  simpa [D2SAdaptiveStepResult.ofRevised, hyb1AdaptiveTerminalToStopping,
                    hyb1DirectResidualRun] using
                    ih (continuation answer) normal' hRest
              | stopped stoppedNormal record =>
                  rfl
              | underlyingAbort =>
                  rfl

omit [DecidableEq StmtIn] [DecidableEq U] in
/-- The concrete forward verifier residual has sufficient adaptive fuel at the exact stateful
schedule count: one initial `DS.Start` hash request plus `N_𝒱` forward permutation calls.  This
is a request bound, not a claim that every response-dependent execution makes exactly that many
D2S requests. -/
lemma runForwardVerifierWide_isQueryBound_at_verifierPermCallCount_succ
    {StmtOut : Type}
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ) :
    IsQueryBoundP (runForwardVerifierWide δ V stmtIn proof) (fun _ => True)
      (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) := by
  classical
  have hClasses := BadEventDS.isQueryBoundP_isRight_of_classes
    (BadEventDS.runForwardVerifierWide_hash_bound V stmtIn proof)
    (BadEventDS.runForwardVerifierWide_fwd_bound_exact V stmtIn proof)
    (BadEventDS.runForwardVerifierWide_bwd_bound V stmtIn proof)
  rw [isQueryBoundP_congr_pred (p' := fun _ => True)] at hClasses
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hClasses
  · rintro (impossible | query)
    · exact PEmpty.elim impossible
    · simp

/-- The one continuous pure-Hyb₁ residual: the malicious prover first returns its salted
proof and the real forward verifier then consumes that exact pair.  It is deliberately not a
concatenation of two fresh D2S executions.  The remaining phase-fusion theorem must identify its
adaptive replay with the inherited-state two-phase Figure-4 executor. -/
noncomputable def hyb1FullResidual
    {StmtOut : Type}
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut) :=
  maliciousProver >>= fun output =>
    runForwardVerifierWide δ V output.1 output.2

/-- The continuous Hyb₁ residual is exactly the two Figure-4 phases with inherited state.  A
prover stop is absorbing; on success, the forward verifier receives the prover's returned
statement, salted proof, normal D2S state, and `gᵢ` memo.  Thus this is an equality of complete
lossless executions, not a statistical coupling or a union bound. -/
lemma hyb1FullResidual_stopping_eq_phased
    {StmtOut : Type}
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
      (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
      (hyb1FullResidual V maliciousProver) normal PUnit.unit =
      d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        maliciousProver normal PUnit.unit >>= fun result =>
          match result with
          | Except.error reason => pure (Except.error reason)
          | Except.ok ((output, normal'), memo') =>
              d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
                (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
                (runForwardVerifierWide δ V output.1 output.2) normal' memo' := by
  unfold hyb1FullResidual
  rw [d2fRawRevisedStoppingFrom_bind
    (gImpl := hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
    (first := maliciousProver)
    (next := fun output => runForwardVerifierWide δ V output.1 output.2)
    (normal := normal) (memo := PUnit.unit)]
  apply bind_congr
  rintro (reason | ⟨⟨output, normal'⟩, memo'⟩) <;> rfl

/-- The first-bad predicate on the lossless result of the continuous Hyb₁ residual.  A successful
result has no monitor stop; an error is charged precisely when it is the structured post-occurrence
monitor stop, rather than an underlying search or ambient-oracle abort. -/
def hyb1FullStoppingResultIsMonitorStop
    {StmtOut : Type}
    (result : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) : Prop :=
  match result with
  | Except.error reason => reason.isMonitorStop
  | Except.ok _ => False

/-- At the fresh initial state, the continuous residual and the actual two-phase Figure-4 game
have exactly the same first-bad indicator.  This packages the phase-fusion equality at the event
level needed by Lemma 5.8: it preserves a prover-side and a verifier-side `Monitor` stop, while
leaving all other stops uncharged on both sides. -/
lemma hyb1FullResidual_monitorStop_eq_game
    {StmtOut : Type}
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) <$>
      d2fRawRevisedStoppingFrom (T_H := T_H) (T_P := T_P)
        (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
        (hyb1FullResidual V maliciousProver)
        (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) PUnit.unit =
      (fun result => result.monitorStop? ≠ none) <$>
        hybridGameRevisedResult (T_H := T_H) (T_P := T_P)
          (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
          V maliciousProver := by
  rw [hyb1FullResidual_stopping_eq_phased]
  unfold hybridGameRevisedResult d2fRawRevisedStopping
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro proverResult
  cases proverResult with
  | error reason =>
      cases reason <;> simp [hyb1FullStoppingResultIsMonitorStop,
        HybridGameRevisedResult.monitorStop?, D2SRevisedStoppingReason.isMonitorStop]
  | ok proverRun =>
      simp only [bind_assoc]
      apply bind_congr
      intro verifierResult
      cases verifierResult with
      | error reason =>
          cases reason <;> simp [hyb1FullStoppingResultIsMonitorStop,
            HybridGameRevisedResult.monitorStop?, D2SRevisedStoppingReason.isMonitorStop]
      | ok verifierRun =>
          simp [hyb1FullStoppingResultIsMonitorStop, HybridGameRevisedResult.monitorStop?]

/-- The named stateful first-bad runner for the entire Hyb₁ prover--verifier residual.  It uses
one normal state, one eager challenge table, and one fuel counter across both phases. -/
noncomputable def hyb1FullAdaptiveRun
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fuel : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) StmtOut)) :=
  d2sQueryRunRevisedAdaptiveWithStep
    (hyb1VerifierStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
    (hyb1VerifierControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
    fuel (kSigma, hyb1FullResidual V maliciousProver) normal

/-- Lemma 5.8a for the full stateful Hyb₁ residual.  This is the generic first-bad calculation
instantiated with the one continuous prover--verifier control program; it charges the concrete
event on the retained terminal trace, not an auxiliary abort flag. -/
lemma hyb1FullAdaptiveRun_terminalBad_le_badEventBound
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fuel j : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j) :
    Pr[ fun result => BadEventDS.E result.terminalTrace |
      hyb1FullAdaptiveRun (T_H := T_H) (T_P := T_P)
        kSigma V maliciousProver fuel normal] ≤
      ENNReal.ofReal (Statement.badEventBound U (j + fuel)) := by
  unfold hyb1FullAdaptiveRun
  apply d2sQueryRunRevisedAdaptiveWithStep_terminalBad_le_badEventBound
  · exact hyb1VerifierStepKernelFirstBadContract
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut)
  · exact hCoherent
  · exact hBaseLength

/-- The paper's prover budget plus the exact stateful verifier schedule bounds the one
continuous Hyb₁ residual.  The final `+1` is the verifier's initial `DS.Start` hash request;
`verifierPermCallCount` itself counts only forward permutation calls. -/
lemma hyb1FullResidual_isQueryBound
    {StmtOut : Type}
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    IsQueryBoundP (hyb1FullResidual V maliciousProver) (fun _ => True)
      (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) := by
  unfold hyb1FullResidual
  refine (isQueryBoundP_bind
    (n := tₕ + tₚ + tₚᵢ)
    (m := verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)
    (maliciousProver_isQueryBound_all maliciousProver tₕ tₚ tₚᵢ hBound)
    (fun output _ => runForwardVerifierWide_isQueryBound_at_verifierPermCallCount_succ
      V output.1 output.2)).mono (by omega)

/-- The full prover→verifier residual has the same lossless adaptive presentation as its direct
fixed-table interpreter.  The separate phase-fusion theorem will connect this one-program view to
the inherited-state two-phase Figure-4 executor. -/
lemma hyb1FullResidualAdaptiveRun_to_directResidual_eq
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) <$>
        d2sQueryRunRevisedAdaptiveWithStep
          (hyb1VerifierStepKernel
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
          (hyb1VerifierControl
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
            (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut))
          (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)
          (kSigma, hyb1FullResidual V maliciousProver) normal =
      hyb1DirectResidualRun (T_H := T_H) (T_P := T_P) kSigma
        (hyb1FullResidual V maliciousProver) normal := by
  exact hyb1AdaptiveRun_to_directResidual_eq_of_bound
    (T_H := T_H) (T_P := T_P) kSigma
    (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)
    (hyb1FullResidual V maliciousProver) normal
    (hyb1FullResidual_isQueryBound V maliciousProver tₕ tₚ tₚᵢ hBound)

omit [(i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i)] in
/-- The generic adaptive-to-first-bad equality specialized to the verifier residual occurring in
pure Hyb₁.  This is the proof-facing form: its residual is the actual `runForwardVerifierWide`
program, while its fuel hypothesis is supplied by the exact stateful schedule accounting. -/
lemma hyb1PureVerifierAdaptiveRun_to_directResidual_eq_of_bound
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (fuel : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hBound : IsQueryBoundP (runForwardVerifierWide δ V stmtIn proof) (fun _ => True) fuel) :
    hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) <$>
        hyb1PureVerifierAdaptiveRun (T_H := T_H) (T_P := T_P)
          kSigma V stmtIn proof fuel normal =
      hyb1DirectResidualRun (T_H := T_H) (T_P := T_P)
        kSigma (runForwardVerifierWide δ V stmtIn proof) normal := by
  simpa [hyb1PureVerifierAdaptiveRun] using
    hyb1AdaptiveRun_to_directResidual_eq_of_bound
      (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut)
      kSigma fuel (runForwardVerifierWide δ V stmtIn proof) normal hBound

/-- The exact-stateful-count instance of the pure-Hyb₁ adaptive/direct first-bad refinement. -/
lemma hyb1PureVerifierAdaptiveRun_to_directResidual_eq_at_verifierPermCallCount_succ
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) <$>
        hyb1PureVerifierAdaptiveRun (T_H := T_H) (T_P := T_P)
          kSigma V stmtIn proof
          (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal =
      hyb1DirectResidualRun (T_H := T_H) (T_P := T_P)
        kSigma (runForwardVerifierWide δ V stmtIn proof) normal :=
  hyb1PureVerifierAdaptiveRun_to_directResidual_eq_of_bound
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
    (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal
    (runForwardVerifierWide_isQueryBound_at_verifierPermCallCount_succ V stmtIn proof)

omit [(i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i)] in
/-- The structural residual replay is definitionally the live fixed-table stopping executor.
This is the residual-program induction which composes the adaptive first-bad runner with the
actual Hyb₁ D2F execution; it preserves the complete return/state/stopping result. -/
lemma hyb1DirectResidualRun_eq_liveDirect
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (residual : OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut))
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1DirectResidualRun (T_H := T_H) (T_P := T_P) kSigma residual normal =
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        residual).run normal).run PUnit.unit).run := by
  induction residual using OracleComp.recOn generalizing normal with
  | pure value =>
      rfl
  | queryBind request continuation ih =>
      cases request with
      | inl impossible => exact PEmpty.elim impossible
      | inr request =>
          rw [hyb1DirectResidualRun]
          simp only [OracleComp.recOn, simulateQ, PFunctor.FreeM.mapM,
            StateT.run_bind, ExceptT.run_bind]
          have hStep' :
              @ExceptT.run
                (D2SRevisedStoppingReason (δ := δ) (T_H := T_H) (T_P := T_P)
                  (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) ProbComp
                ((([]ₒ + duplexSpongeChallengeOracle StmtIn U).toPFunctor.B (.inr request) ×
                  D2SNormalState (δ := δ) (T_H := T_H) (T_P := T_P)
                    (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)
                (((hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma
                  (.inr request)).run normal).run PUnit.unit) =
                hyb1D2SStepToStopping normal <$>
                  simulateQ
                    ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                      (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                    (d2sQueryStepRevised normal request) := by
            rw [hyb1D2FStoppingDirectImpl]
            change ExceptT.run ((do
              let result ← simulateQ
                (hyb1StoppingD2SDirect (T_H := T_H) (T_P := T_P) kSigma)
                (d2sQueryStepRevised normal request)
              StateT.mk fun memo => ExceptT.mk
                (pure (d2sRevisedStepPost normal result memo))).run PUnit.unit) = _
            simp only [StateT.run_bind, ExceptT.run_bind]
            conv_lhs =>
              enter [1]
              rw [hyb1StoppingD2SDirect_step_run (T_H := T_H) (T_P := T_P)
                kSigma normal request]
            rw [bind_map_left, map_eq_pure_bind]
            apply bind_congr
            intro result
            cases result <;> rfl
          have hRhs :
              (do
                let x ← (((hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma
                  (.inr request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
              (do
                let result ← simulateQ
                  ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                    (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                  (d2sQueryStepRevised normal request)
                match result with
                | .continue answer normal' =>
                    hyb1DirectResidualRun (T_H := T_H) (T_P := T_P)
                      kSigma (continuation answer) normal'
                | .stopped normal' record => pure (.error (.monitorStop normal' record))
                | .underlyingAbort => pure (.error (.underlyingAbort normal))) := by
            calc
              (do
                let x ← (((hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma
                  (.inr request)).run normal).run PUnit.unit).run
                match x with
                | .ok x =>
                    (((PFunctor.FreeM.mapM
                      (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                      (continuation x.1.1)).run x.1.2).run x.2).run
                | .error e => pure (.error e)) =
                (do
                  let x ← hyb1D2SStepToStopping normal <$>
                    simulateQ
                      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma +
                        (d2sUnitSampleImpl (U := U) + QueryImpl.id' unifSpec))
                      (d2sQueryStepRevised normal request)
                  match x with
                  | .ok x =>
                      (((PFunctor.FreeM.mapM
                        (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                        (continuation x.1.1)).run x.1.2).run x.2).run
                  | .error e => pure (.error e)) := by
                    exact congrArg (fun z => z >>= fun x =>
                      match x with
                      | .ok x =>
                          (((PFunctor.FreeM.mapM
                            (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                            (continuation x.1.1)).run x.1.2).run x.2).run
                      | .error e => pure (.error e)) hStep'
              _ = _ := by
                simp only [map_eq_pure_bind, bind_assoc]
                apply bind_congr
                intro result
                cases result with
                | «continue» answer normal' =>
                    simp only [hyb1D2SStepToStopping]
                    simpa [simulateQ] using (ih answer normal').symm
                | stopped normal' record => rfl
                | underlyingAbort => rfl
          convert hRhs.symm using 2
          funext x
          cases x <;> rfl

/-- The exact stateful first-bad bound for a fixed outer permutation sample in the live Hyb₁
stopping interpreter.  The proof is purely lossless: the direct residual is first identified with
the adaptive runner, and the direct stop predicate is then identified with `E` on its terminal
trace.  Consequently, the coefficient is the paper's exact `B(tₕ + tₚ + tₚᵢ + N_𝒱 + 1)`, with
no extra union bound for the prover/verifier phase boundary. -/
lemma hyb1FullDirect_monitorStop_le_badEventBound
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    Pr[hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) |
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        (hyb1FullResidual V maliciousProver)).run
          (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run PUnit.unit).run] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) := by
  rw [← hyb1DirectResidualRun_eq_liveDirect (T_H := T_H) (T_P := T_P)
    kSigma (hyb1FullResidual V maliciousProver)
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))]
  rw [← hyb1FullResidualAdaptiveRun_to_directResidual_eq (T_H := T_H) (T_P := T_P)
    kSigma V maliciousProver tₕ tₚ tₚᵢ
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) hBound]
  rw [probEvent_map]
  have hPredicate :
      (fun terminal : D2SAdaptiveRunResult
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
        (T_H := T_H) (T_P := T_P)
        (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) StmtOut) =>
        hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
          (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) terminal)) =
      fun terminal => BadEventDS.E terminal.terminalTrace := by
    funext terminal
    apply propext
    have hStop :
        hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
          (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) terminal) ↔
          terminal.isMonitorStop := by
      cases terminal with
      | complete control normal =>
          rcases control with ⟨sampledTable, residual⟩
          cases residual <;> rfl
      | stopped control normal record => rfl
      | underlyingAbort control normal => rfl
      | fuelExhausted control normal => rfl
    exact hStop.trans terminal.isMonitorStop_iff_badEvent_terminalTrace
  change Pr[(fun terminal =>
    hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
      (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) terminal)) |
      hyb1FullAdaptiveRun (T_H := T_H) (T_P := T_P)
        kSigma V maliciousProver
        (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)
        (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U))] ≤ _
  rw [hPredicate]
  simpa only [zero_add] using
    (hyb1FullAdaptiveRun_terminalBad_le_badEventBound
      (T_H := T_H) (T_P := T_P) (kSigma := kSigma) (V := V)
      (maliciousProver := maliciousProver)
      (fuel := tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)
      (j := 0)
      (normal := D2SNormalState.initial (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      RateOnlyCacheCoherent.initial (by
        change (getBaseTrace ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))).length ≤ 0
        simp [getBaseTrace, getBaseTraceAux]))

/-- Installing a fixed eager `D_Σ` table outside the complete Figure-4 execution preserves the
monitor-stop event exactly.  This is the lossless bridge from the continuous direct residual to
the actual two-phase H1 game under its outer oracle interpreter. -/
lemma hyb1FullDirect_monitorStop_eq_outerGame
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ) :
    hyb1FullStoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) <$>
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        (hyb1FullResidual V maliciousProver)).run
          (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
            (StmtIn := StmtIn) (pSpec := pSpec) (U := U))).run PUnit.unit).run =
      (fun result => result.monitorStop? ≠ none) <$>
        simulateQ
          (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (δ := δ) kSigma)
          (hybridGameRevisedResult (T_H := T_H) (T_P := T_P)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
            V maliciousProver) := by
  rw [← hyb1D2fRawRevisedStopping_hyb1_eq_direct (T_H := T_H) (T_P := T_P)
    kSigma (hyb1FullResidual V maliciousProver)
    (D2SNormalState.initial (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))]
  rw [← simulateQ_map, ← simulateQ_map]
  exact congrArg (simulateQ
    (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) kSigma))
    (hyb1FullResidual_monitorStop_eq_game (T_H := T_H) (T_P := T_P) V maliciousProver)

/-- The same bound stated at the genuine sampled Figure-4 H1 boundary.  This transports only the
Boolean monitor observation through the proved lossless outer-interpreter equality; it does not
assume an independence relation between the sampled table and the adversarial prover. -/
lemma hyb1FullSampledOuterGame_monitorStop_le_badEventBound
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    Pr[fun result => result.monitorStop? ≠ none |
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).sample >>= fun kSigma =>
        simulateQ
          (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (δ := δ) kSigma)
          (hybridGameRevisedResult (T_H := T_H) (T_P := T_P)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
            V maliciousProver))] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) := by
  apply probEvent_bind_le_of_forall_le
  intro kSigma _
  have mapEvent {α : Type} (g : α → Prop) (mx : ProbComp α) :
      Pr[g | mx] = Pr[id | g <$> mx] := by
    rw [probEvent_map, Function.id_comp]
  rw [mapEvent]
  rw [← hyb1FullDirect_monitorStop_eq_outerGame (T_H := T_H) (T_P := T_P)
    kSigma V maliciousProver]
  rw [probEvent_map, Function.id_comp]
  exact hyb1FullDirect_monitorStop_le_badEventBound (T_H := T_H) (T_P := T_P)
    kSigma V maliciousProver tₕ tₚ tₚᵢ hBound

/-- The sampled revised Hyb₁ endpoint in the paper's literal event form.  The lossless result
retains its terminal D2S trace, and `Monitor` stopping is equivalent to `E` on that trace. -/
lemma hyb1FullSampledOuterGame_terminalBad_le_badEventBound
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (tₕ tₚ tₚᵢ : ℕ)
    (hBound : BadEventDS.IsLemma5_8QueryBound
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ)
      maliciousProver tₕ tₚ tₚᵢ) :
    Pr[ fun result => BadEventDS.E result.baseTrace |
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).sample >>= fun kSigma =>
        simulateQ
          (hyb1VerifierOuterImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
            (δ := δ) kSigma)
          (hybridGameRevisedResult (T_H := T_H) (T_P := T_P)
            (hyb1GImpl (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))
            V maliciousProver))] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (tₕ + tₚ + tₚᵢ + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) := by
  apply HybridGameRevisedResult.probBadEvent_le_of_monitorStop
  exact hyb1FullSampledOuterGame_monitorStop_le_badEventBound
    (T_H := T_H) (T_P := T_P) V maliciousProver tₕ tₚ tₚᵢ hBound

/-- The monitor-stop predicate on the live lossless executor.  Successful verifier returns and
all non-monitor exceptions are deliberately uncharged. -/
def hyb1StoppingResultIsMonitorStop
    (result : Except
      (D2SRevisedStoppingReason
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      ((Option StmtOut ×
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) × PUnit)) : Prop :=
  match result with
  | .ok _ => False
  | .error reason => reason.isMonitorStop

omit [(i : pSpec.ChallengeIdx) → VCVCompatible (pSpec.Challenge i)]
  [(i : pSpec.MessageIdx) → VCVCompatible (pSpec.Message i)] in
/-- Projecting an adaptive terminal result into the live stopping executor preserves exactly the
event charged by the first-bad argument. -/
lemma hyb1AdaptiveTerminalToStopping_isMonitorStop_iff
    (terminal : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut)) :
    hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
      (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) terminal) ↔
      terminal.isMonitorStop := by
  cases terminal with
  | complete control normal =>
      rcases control with ⟨kSigma, residual⟩
      cases residual <;> rfl
  | stopped control normal record => rfl
  | underlyingAbort control normal => rfl
  | fuelExhausted control normal => rfl

/-- The exact stateful adaptive first-bad execution is the real fixed-table lossless Hyb₁ D2F
execution after terminal projection.  This is the missing semantic bridge from the local
first-bad charge to the live verifier experiment. -/
lemma hyb1PureVerifierAdaptiveRun_to_liveDirect_eq_at_verifierPermCallCount_succ
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) <$>
        hyb1PureVerifierAdaptiveRun (T_H := T_H) (T_P := T_P)
          kSigma V stmtIn proof
          (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal =
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        (runForwardVerifierWide δ V stmtIn proof)).run normal).run PUnit.unit).run := by
  rw [hyb1PureVerifierAdaptiveRun_to_directResidual_eq_at_verifierPermCallCount_succ
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof normal]
  exact hyb1DirectResidualRun_eq_liveDirect (T_H := T_H) (T_P := T_P)
    kSigma (runForwardVerifierWide δ V stmtIn proof) normal

/-- The paper's stopped-verifier envelope `D(T,N_𝒱)` bounds the monitor-stop event of the
*live* fixed-table Hyb₁ D2F execution, not merely its auxiliary adaptive presentation. -/
lemma hyb1LiveDirect_monitorStop_le_Dcap
    [Nonempty U] [Section5Nonempty pSpec]
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (T : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ T) :
    Pr[ hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) |
      (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
        (runForwardVerifierWide δ V stmtIn proof)).run normal).run PUnit.unit).run] ≤
      ENNReal.ofReal (Statement.Dcap U T
        (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := by
  rw [← hyb1PureVerifierAdaptiveRun_to_liveDirect_eq_at_verifierPermCallCount_succ
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof normal]
  rw [probEvent_map]
  have hPredicate :
      (fun terminal : D2SAdaptiveRunResult
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
          (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut) =>
        hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
        (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut)
          terminal)) =
        fun terminal => terminal.isMonitorStop := by
    funext terminal
    exact propext (hyb1AdaptiveTerminalToStopping_isMonitorStop_iff
      (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) terminal)
  change Pr[ (fun terminal => hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P)
    (hyb1AdaptiveTerminalToStopping (T_H := T_H) (T_P := T_P) (StmtOut := StmtOut) terminal)) |
    hyb1PureVerifierAdaptiveRun (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
      (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal] ≤ _
  rw [hPredicate]
  exact Statement.hyb1PureVerifierAdaptiveRun_monitorStop_le_Dcap
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof normal T hCoherent hBaseLength

/-- The stopped-verifier bound applies directly after a stateful adaptive prover replay.  Only
terminals exposing an actual prover value invoke the verifier; every other terminal is absorbed
into an uncharged successful placeholder.  Hence the proof uses the completed-value support
invariant pointwise and does not condition on, or resample after, the prover run. -/
lemma hyb1LiveDirect_monitorStop_after_adaptiveProver_le_Dcap
    [Nonempty U] [Section5Nonempty pSpec]
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fuel j T : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hFinalLength : j + fuel ≤ T) :
    Pr[ hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) |
      d2sQueryRunRevisedAdaptiveWithStep
        (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P)
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
          (S := MaliciousProver []ₒ pSpec StmtIn U δ))
        (D2SAdaptiveControl.ofEmptyLiftedOracleComp
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
        fuel maliciousProver normal >>= fun terminal =>
          match d2sAdaptiveRunResultCompletedValue? terminal with
          | none => pure (.ok ((none, normal), PUnit.unit))
          | some ((stmtIn, proof), finalNormal) =>
              (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                (runForwardVerifierWide δ V stmtIn proof)).run finalNormal).run PUnit.unit).run] ≤
      ENNReal.ofReal (Statement.Dcap U T
        (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := by
  apply probEvent_bind_le_of_forall_le
  intro terminal hTerminal
  cases hValue : d2sAdaptiveRunResultCompletedValue? terminal with
  | none =>
      calc
        Pr[ hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) |
          pure (.ok ((none, normal), PUnit.unit)) ] = 0 := by
            apply probEvent_eq_zero
            intro result hResult
            rw [mem_support_pure_iff] at hResult
            subst result
            simp [hyb1StoppingResultIsMonitorStop]
        _ ≤ ENNReal.ofReal (Statement.Dcap U T
          (verifierPermCallCount (pSpec := pSpec) (δ := δ))) := bot_le
  | some pair =>
      rcases pair with ⟨output, finalNormal⟩
      rcases output with ⟨stmtIn, proof⟩
      have hInvariant := d2sQueryRunRevisedAdaptiveWithStep_completedValue_support_invariant
        (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P)
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
          (S := MaliciousProver []ₒ pSpec StmtIn U δ))
        (d2sQueryStepRevisedKernelFirstBadContract (T_H := T_H) (T_P := T_P)
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma))
        (D2SAdaptiveControl.ofEmptyLiftedOracleComp
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
        fuel maliciousProver normal j hCoherent hBaseLength terminal hTerminal
        (stmtIn, proof) finalNormal hValue
      simpa [hValue] using
        hyb1LiveDirect_monitorStop_le_Dcap (T_H := T_H) (T_P := T_P)
          kSigma V stmtIn proof finalNormal T hInvariant.1
          (Nat.le_trans hInvariant.2 hFinalLength)

/-- The complete stateful Hyb₁ execution—an adaptive prover prefix followed by the exact
verifier schedule—has one common Lemma-5.8 first-stop budget.  This is the full-run version of
`hyb1LiveDirect_monitorStop_le_badEventBound`; it is intentionally stated after the prover
distribution has been bound, so it can be used directly by the eventual H₀/H₁ coupling without
introducing a conditional-independence assumption. -/
lemma hyb1LiveDirect_monitorStop_after_adaptiveProver_le_badEventBound
    [Nonempty U] [Section5Nonempty pSpec]
    {StmtOut : Type}
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (maliciousProver : MaliciousProver []ₒ pSpec StmtIn U δ)
    (fuel j T : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j)
    (hFinalLength : j + fuel ≤ T) :
    Pr[ hyb1StoppingResultIsMonitorStop (T_H := T_H) (T_P := T_P) |
      d2sQueryRunRevisedAdaptiveWithStep
        (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P)
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl kSigma)
          (S := MaliciousProver []ₒ pSpec StmtIn U δ))
        (D2SAdaptiveControl.ofEmptyLiftedOracleComp
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn × DSSaltedProof (pSpec := pSpec) (U := U) δ))
        fuel maliciousProver normal >>= fun terminal =>
          match d2sAdaptiveRunResultCompletedValue? terminal with
          | none => pure (.ok ((none, normal), PUnit.unit))
          | some ((stmtIn, proof), finalNormal) =>
              (((simulateQ (hyb1D2FStoppingDirectImpl (T_H := T_H) (T_P := T_P) kSigma)
                (runForwardVerifierWide δ V stmtIn proof)).run finalNormal).run PUnit.unit).run] ≤
      ENNReal.ofReal (Statement.badEventBound U
        (T + verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) := by
  exact (hyb1LiveDirect_monitorStop_after_adaptiveProver_le_Dcap
    (T_H := T_H) (T_P := T_P) kSigma V maliciousProver fuel j T normal hCoherent
    hBaseLength hFinalLength).trans
      (ENNReal.ofReal_le_ofReal
        (Statement.Dcap_le_badEventBound (U := U) T
          (verifierPermCallCount (pSpec := pSpec) (δ := δ))))

end DuplexSpongeFS.KeyLemma
