/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadProbability
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadHistory
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule

/-!
# Adaptive first-bad runner for revised D2SQuery

The finite-list runner is useful for a fixed suffix, but a real verifier may choose its next
duplex query from the normal state and from answers already received.  This module supplies the
small, executable adaptive core needed by the endpoint refinement: it is fuel-bounded, chooses a
new query after every successful step, and is absorbing at a monitor stop or underlying abort.

The control state `S` is deliberately opaque.  It can carry an outer verifier state, a memo table,
or a pre-sampled random tape.  The probability theorem is uniform in it, so the later live-endpoint
refinement need only show that its next-query mechanism is represented by this control; it does
not reopen any D2SQuery branch or introduce an independence assumption.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize] [VCVCompatible U]
  [codec : CodecCore pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U] [SampleableType U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- One exact outer-control decision.  A `query` packages both the chosen D2S request and the
only continuation permitted after it: the continuation receives that request's dependent answer
and the successor normal state.  Consequently there is no operation for advancing a control with
a mismatched query. -/
inductive D2SAdaptiveNext (S : Type)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) where
  | done : D2SAdaptiveNext S normal
  | query (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
      (advance : S → (duplexSpongeChallengeOracle StmtIn U).Range q →
        D2SNormalState
          (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) → S) :
      D2SAdaptiveNext S normal

/-- The optional request exposed by an adaptive decision.  The runner itself eliminates the
decision directly to obtain the certified continuation; this projection is solely a lightweight
interface for completion lemmas. -/
def D2SAdaptiveNext.request?
    {S : Type}
    {normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)} :
    D2SAdaptiveNext S normal → Option (duplexSpongeChallengeOracle StmtIn U).Domain
  | .done => none
  | .query q _ => some q

/-- The outer control for a finite adaptive revised-D2SQuery run.  `next` may inspect the current
normal state and arbitrary carried state.  On a query, it returns the exact dependent continuation
to run after the answer.  This representation makes an impossible “advance with some other
query” unrepresentable. -/
structure D2SAdaptiveControl (S : Type) where
  next :
    ∀ (_ : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
      D2SAdaptiveNext S normal

/-- The lossless terminal result of an adaptive revised-D2SQuery execution.  Unlike the older
`D2SRevisedStepResult Unit` summary, this retains the controller state at **every** terminal
face.  Thus an outer verifier/hybrid refinement can reconstruct its public observation after a
normal completion, a monitored first-bad stop, or an underlying search failure without treating
the controller state as an untyped side condition.

The `stopped`, `underlyingAbort`, and `fuelExhausted` constructors retain the exact control and
normal states immediately before the terminal query.  In particular, a stop still has no reusable
successor: its `record` owns the one post-occurrence bad trace, while `normal` owns the
pre-occurrence reusable table/cache. -/
inductive D2SAdaptiveRunResult (S : Type) where
  | complete (control : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SAdaptiveRunResult S
  | stopped (control : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
      D2SAdaptiveRunResult S
  | underlyingAbort (control : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SAdaptiveRunResult S
  | fuelExhausted (control : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SAdaptiveRunResult S

/-- Forget only the controller payload of an adaptive result.  This projects exactly to the
three-way public result used by the existing first-bad theorem; it never turns a monitored stop
into an underlying abort or exposes a successor after a stop. -/
def D2SAdaptiveRunResult.toStepResult
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit :=
  match result with
  | .complete _ normal => .continue () normal
  | .stopped _ normal record => .stopped normal record
  | .underlyingAbort _ _ => .underlyingAbort
  | .fuelExhausted _ normal => .continue () normal

/-- The monitor-stop event for a lossless adaptive result. -/
def D2SAdaptiveRunResult.isMonitorStop
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) : Prop :=
  match result with
  | .complete _ _ => False
  | .stopped _ _ _ => True
  | .underlyingAbort _ _ => False
  | .fuelExhausted _ _ => False

/-- Whether a bounded adaptive run ended only because its supplied fuel was exhausted.  This is
kept distinct from both monitor stops and underlying aborts: the verifier-refinement proof must
rule this face out from the real query bound, rather than silently treating it as either event. -/
def D2SAdaptiveRunResult.isFuelExhausted
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) : Prop :=
  match result with
  | .complete _ _ => False
  | .stopped _ _ _ => False
  | .underlyingAbort _ _ => False
  | .fuelExhausted _ _ => True

/-- One state-threaded D2S step for the adaptive runner.  A successful branch returns its
post-step outer state together with the normal successor.  In contrast, a monitored stop retains
only the pre-step controller state at the runner boundary: the stop record already owns the
post-occurrence trace but deliberately exposes no reusable state. -/
inductive D2SAdaptiveStepResult (S : Type)
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain) where
  | continue (answer : (duplexSpongeChallengeOracle StmtIn U).Range q)
      (state : S)
      (normal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
      D2SAdaptiveStepResult S q
  | stopped (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) normal) :
      D2SAdaptiveStepResult S q
  | underlyingAbort : D2SAdaptiveStepResult S q

/-- The only chargeable terminal face of a state-threaded step. -/
def D2SAdaptiveStepResult.isMonitorStop
    {S : Type} {q : (duplexSpongeChallengeOracle StmtIn U).Domain}
    (result : D2SAdaptiveStepResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S q) :
    Prop :=
  match result with
  | .continue _ _ _ => False
  | .stopped _ _ => True
  | .underlyingAbort => False

/-- Embed one direct revised-D2S result into a state-threaded result by preserving the caller's
outer state on its only continuing face. -/
def D2SAdaptiveStepResult.ofRevised
    {S : Type} (state : S)
    {q : (duplexSpongeChallengeOracle StmtIn U).Domain} :
    D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      ((duplexSpongeChallengeOracle StmtIn U).Range q) →
      D2SAdaptiveStepResult
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (δ := δ) (T_H := T_H) (T_P := T_P) S q
  | .continue answer normal => .continue answer state normal
  | .stopped normal record => .stopped normal record
  | .underlyingAbort => .underlyingAbort

omit [VCVCompatible U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveStepResult.ofRevised_isMonitorStop
    {S : Type} (state : S)
    {q : (duplexSpongeChallengeOracle StmtIn U).Domain}
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      ((duplexSpongeChallengeOracle StmtIn U).Range q)) :
    (D2SAdaptiveStepResult.ofRevised state result).isMonitorStop ↔ result.isMonitorStop := by
  cases result <;> rfl

/-- A fully interpreted state-threaded D2S step.  The actual verifier/hybrid instantiation can
put its memo and lazy-sampling tables in `S`; unlike the older direct runner, this interface does
not assume that interpreting a D2S request leaves outer state unchanged. -/
structure D2SAdaptiveStepKernel (S : Type) where
  step : ∀ (_ : S)
    (_ : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain),
    ProbComp (D2SAdaptiveStepResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S q)

omit [VCVCompatible U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveRunResult.toStepResult_isMonitorStop
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    result.toStepResult.isMonitorStop ↔ result.isMonitorStop := by
  cases result <;> rfl

/-- Run at most `fuel` revised D2SQuery calls under an adaptive controller.  A controller that
returns `none` finishes normally.  A monitored stop or underlying abort is terminal, so neither
`advance` nor any suffix query is evaluated in those branches. -/
noncomputable def d2sQueryRunRevisedAdaptive
    {S : Type}
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    (fuel : ℕ) → S →
      D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      ProbComp (D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit)
  | 0, _, normal => pure (.continue () normal)
  | fuel + 1, controlState, normal =>
      match control.next controlState normal with
      | .done => pure (.continue () normal)
      | .query q advance => do
          let result ← simulateQ
            (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
            (d2sQueryStepRevised normal q)
          match result with
          | .continue answer normal' =>
              d2sQueryRunRevisedAdaptive gImpl control fuel
                (advance controlState answer normal') normal'
          | .stopped normal' record => pure (.stopped normal' record)
          | .underlyingAbort => pure .underlyingAbort

/-- The lossless adaptive runner.  It has the same query schedule and absorbing behaviour as
`d2sQueryRunRevisedAdaptive`, but retains the final controller state so a concrete outer endpoint
can be defined by post-processing this run rather than by carrying an unrelated sampler.

This runner is deliberately fuel-bounded.  The future verifier-refinement theorem must establish
the particular fuel bound for the observed endpoint; this declaration does not identify the
number of D2S oracle requests with the distinct schedule count `N_𝒱`. -/
noncomputable def d2sQueryRunRevisedAdaptiveWithControl
    {S : Type}
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    (fuel : ℕ) → S →
      D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      ProbComp (D2SAdaptiveRunResult
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
  | 0, controlState, normal =>
      match control.next controlState normal with
      | .done => pure (.complete controlState normal)
      | .query _ _ => pure (.fuelExhausted controlState normal)
  | fuel + 1, controlState, normal =>
      match control.next controlState normal with
      | .done => pure (.complete controlState normal)
      | .query q advance => do
          let result ← simulateQ
            (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
            (d2sQueryStepRevised normal q)
          match result with
          | .continue answer normal' =>
              d2sQueryRunRevisedAdaptiveWithControl gImpl control fuel
                (advance controlState answer normal') normal'
          | .stopped normal' record => pure (.stopped controlState normal' record)
          | .underlyingAbort => pure (.underlyingAbort controlState normal)

/-- The state-threaded form of the lossless adaptive runner.  It has the same absorbing terminal
semantics as `d2sQueryRunRevisedAdaptiveWithControl`, but obtains each D2S transition from an
explicit kernel that may update the outer memo/table state.  This is the exact execution shape
needed by the live revised Hyb₁--Hyb₄ interpreters.

The direct `gImpl : gSpec → ProbComp` runner is recovered below as the kernel that preserves its
outer state.  Thus this is a generalization of the established first-bad runner, not a competing
query semantics. -/
noncomputable def d2sQueryRunRevisedAdaptiveWithStep
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    (fuel : ℕ) → S →
      D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) →
      ProbComp (D2SAdaptiveRunResult
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
  | 0, controlState, normal =>
      match control.next controlState normal with
      | .done => pure (.complete controlState normal)
      | .query _ _ => pure (.fuelExhausted controlState normal)
  | fuel + 1, controlState, normal =>
      match control.next controlState normal with
      | .done => pure (.complete controlState normal)
      | .query q advance => do
          let result ← kernel.step controlState normal q
          match result with
          | .continue answer state' normal' =>
              d2sQueryRunRevisedAdaptiveWithStep kernel control fuel
                (advance state' answer normal') normal'
          | .stopped normal' record => pure (.stopped controlState normal' record)
          | .underlyingAbort => pure (.underlyingAbort controlState normal)

/-- The existing direct D2S dispatcher as a state-preserving state-threaded kernel. -/
noncomputable def d2sQueryStepRevisedKernel
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    {S : Type} :
    D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S where
  step state normal q := do
    D2SAdaptiveStepResult.ofRevised state <$> simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)

/-- The two local facts needed to aggregate a first-bad bound through a state-threaded kernel.
They are deliberately phrased over the kernel's real `ProbComp` support: no caller may assert an
arbitrary successor relation or silently turn an underlying abort into a continuation.

The direct dispatcher already proves these two facts.  A live Hyb kernel must prove the same
facts for its memo/table interpreter once, after which the aggregate proof below is unchanged. -/
structure D2SAdaptiveKernelFirstBadContract
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) where
  monitorStop_le : ∀ (state : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (j : ℕ),
    RateOnlyCacheCoherent normal →
    (getBaseTrace normal.state.trace).length ≤ j →
    Pr[ fun result => result.isMonitorStop | kernel.step state normal q] ≤
      ((2 * j + 1 : ℕ) : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U)
  continueInvariant : ∀ (state : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (j : ℕ),
    RateOnlyCacheCoherent normal →
    (getBaseTrace normal.state.trace).length ≤ j →
    ∀ (answer : (duplexSpongeChallengeOracle StmtIn U).Range q)
      (state' : S)
      (normal' : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
      .continue answer state' normal' ∈ support (kernel.step state normal q) →
        RateOnlyCacheCoherent normal' ∧
          (getBaseTrace normal'.state.trace).length ≤ j + 1

/-- A trace-extension relation for the raw, insertion-ordered D2S log.  It is deliberately an
explicit suffix equation rather than a length inequality: later prover→verifier refinements need
the inherited prefix itself to expose cross-phase collision witnesses. -/
def D2STraceExtends
    (initial final : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ tail, final = initial ++ tail

omit [VCVCompatible U] [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U]
  [SampleableType U] in
@[refl] lemma D2STraceExtends.refl
    (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    D2STraceExtends trace trace := ⟨[], by simp⟩

omit [VCVCompatible U] [DecidableEq StmtIn] [DecidableEq U] [Fintype U] [Nonempty U]
  [SampleableType U] in
lemma D2STraceExtends.trans
    {trace₀ trace₁ trace₂ : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h₀₁ : D2STraceExtends trace₀ trace₁)
    (h₁₂ : D2STraceExtends trace₁ trace₂) :
    D2STraceExtends trace₀ trace₂ := by
  rcases h₀₁ with ⟨tail₀₁, h₀₁⟩
  rcases h₁₂ with ⟨tail₁₂, h₁₂⟩
  refine ⟨tail₀₁ ++ tail₁₂, ?_⟩
  rw [h₁₂, h₀₁, List.append_assoc]

/-- The one deterministic history fact needed in addition to the first-bad probability
contract.  Every supported continuation appends its concrete query-answer pair, while stopped
and aborting faces are handled structurally by the runner. -/
structure D2SAdaptiveKernelTraceContract
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) where
  continue_append_one : ∀ (state : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (answer : (duplexSpongeChallengeOracle StmtIn U).Range q)
    (state' : S)
    (normal' : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
    .continue answer state' normal' ∈ support (kernel.step state normal q) →
      ∃ occurrence : Sigma (duplexSpongeChallengeOracle StmtIn U),
        normal'.state.trace = normal.state.trace ++ [occurrence]

/-- The full history contract for a state-threaded D2S interpreter.  In addition to exact
continuations, a monitor stop must expose a terminal record whose **own terminal trace** extends
the input normal state.  This is the exact downstream observable: the terminal result exposes
`record.trace`, not the record's pre-stop normal state.  The field is essential rather than
automatic, since an arbitrary kernel can manufacture a stop record over an unrelated history. -/
structure D2SAdaptiveKernelHistoryContract
    {S : Type}
    (kernel : D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    extends D2SAdaptiveKernelTraceContract kernel where
  monitorStop_prefix : ∀ (state : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (stoppedNormal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (record : D2SPostOccurrenceStopRecord
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stoppedNormal),
    .stopped stoppedNormal record ∈ support (kernel.step state normal q) →
      D2STraceExtends normal.state.trace record.trace

/-- The terminal raw trace of a lossless adaptive execution.  A monitored stop exposes the
post-occurrence trace owned by its record; every other terminal face exposes its carried normal
state. -/
def D2SAdaptiveRunResult.terminalTrace
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    QueryLog (duplexSpongeChallengeOracle StmtIn U) :=
  match result with
  | .complete _ normal => normal.state.trace
  | .stopped _ _ record => record.trace
  | .underlyingAbort _ normal => normal.state.trace
  | .fuelExhausted _ normal => normal.state.trace

/-- For the revised absorbing runner, a terminal trace is bad exactly on the monitored-stop
face.  A reusable normal state carries `¬ E` by construction, whereas a stop record retains the
one appended occurrence on which `Monitor` failed.  This is the semantic bridge from the
operational first-stop event to the paper's event `E(\operatorname{tr})`; neither an underlying
search abort nor fuel exhaustion is charged as a bad event. -/
@[simp] lemma D2SAdaptiveRunResult.isMonitorStop_iff_badEvent_terminalTrace
    {S : Type}
    (result : D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S) :
    result.isMonitorStop ↔ BadEventDS.E result.terminalTrace := by
  cases result with
  | complete control normal =>
      simp [D2SAdaptiveRunResult.isMonitorStop, D2SAdaptiveRunResult.terminalTrace,
        normal.monitorPassed]
  | stopped control normal record =>
      simp [D2SAdaptiveRunResult.isMonitorStop, D2SAdaptiveRunResult.terminalTrace,
        record.monitorFails_trace]
  | underlyingAbort control normal =>
      simp [D2SAdaptiveRunResult.isMonitorStop, D2SAdaptiveRunResult.terminalTrace,
        normal.monitorPassed]
  | fuelExhausted control normal =>
      simp [D2SAdaptiveRunResult.isMonitorStop, D2SAdaptiveRunResult.terminalTrace,
        normal.monitorPassed]

/-- The direct dispatcher satisfies the state-threaded kernel contract by preserving the carried
state on continuations.  This makes the generic aggregate theorem below a strict extension of the
already-proved one-step gateway facts, rather than a new probabilistic assumption. -/
noncomputable def d2sQueryStepRevisedKernelFirstBadContract
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    {S : Type} :
    D2SAdaptiveKernelFirstBadContract
      (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P) gImpl (S := S)) where
  monitorStop_le state normal q j hCoherent hBaseLength := by
    rw [d2sQueryStepRevisedKernel, probEvent_map]
    change Pr[ fun result =>
      (D2SAdaptiveStepResult.ofRevised state result).isMonitorStop |
        simulateQ
          (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal q)] ≤ _
    rw [show (fun result : D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        ((duplexSpongeChallengeOracle StmtIn U).Range q) =>
        (D2SAdaptiveStepResult.ofRevised state result).isMonitorStop) =
        fun result => result.isMonitorStop from funext fun result =>
          propext (D2SAdaptiveStepResult.ofRevised_isMonitorStop state result)]
    exact d2sQueryStepRevised_monitorStop_le_of_baseLength_le
      gImpl normal q hCoherent j hBaseLength
  continueInvariant state normal q j hCoherent hBaseLength answer state' normal' hResult := by
    rw [d2sQueryStepRevisedKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» rawAnswer rawNormal =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        injection hEq with hAnswer hState hNormal
        subst answer
        subst state'
        subst normal'
        have hInvariant := d2sQueryStepRevised_maintainsInvariant normal hCoherent q
          gImpl (.continue rawAnswer rawNormal) hRaw
        refine ⟨hInvariant.1, ?_⟩
        exact Nat.le_trans
          (d2sQueryStepRevised_continue_baseTrace_length_le normal q gImpl rawAnswer rawNormal
            hRaw)
          (Nat.succ_le_succ hBaseLength)
    | stopped rawNormal rawRecord =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq

/-- The direct revised dispatcher satisfies the exact history contract by the branch-complete
one-occurrence theorem.  This is the non-probabilistic companion to its first-bad contract. -/
noncomputable def d2sQueryStepRevisedKernelTraceContract
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    {S : Type} :
    D2SAdaptiveKernelTraceContract
      (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P) gImpl (S := S)) where
  continue_append_one state normal q answer state' normal' hResult := by
    rw [d2sQueryStepRevisedKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» rawAnswer rawNormal =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        injection hEq with hAnswer hState hNormal
        subst answer
        subst state'
        subst normal'
        exact d2sQueryStepRevised_continue_trace_extension normal q gImpl rawAnswer rawNormal hRaw
    | stopped rawNormal rawRecord =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq

/-- The direct revised dispatcher satisfies the complete terminal-history contract.  The
continuing face follows the exact one-occurrence theorem above; the stopped face follows the
branch-complete terminal-record theorem in `D2SFirstBadHistory`.  Thus the generic adaptive
runner may treat a direct monitor stop exactly like a literal extension of the input raw trace. -/
noncomputable def d2sQueryStepRevisedKernelHistoryContract
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    {S : Type} :
    D2SAdaptiveKernelHistoryContract
      (d2sQueryStepRevisedKernel (T_H := T_H) (T_P := T_P) gImpl (S := S)) where
  continue_append_one :=
    (d2sQueryStepRevisedKernelTraceContract (T_H := T_H) (T_P := T_P) gImpl).continue_append_one
  monitorStop_prefix state normal q stoppedNormal record hResult := by
    rw [d2sQueryStepRevisedKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» answer rawNormal =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | stopped rawNormal rawRecord =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        have hTrace := d2sQueryStepRevised_stopped_trace_extension normal q gImpl rawNormal
          rawRecord hRaw
        cases hEq
        exact hTrace
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq

omit [VCVCompatible U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- Aggregate the exact first-bad charge through an arbitrary state-threaded adaptive kernel.
The proof is the same one-bind-per-reached-query induction as the direct dispatcher theorem; the
contract isolates the only two facts a memo/table-aware live interpreter must establish.

In particular, `S` can carry a D2SAlgo memo and lazy-sampling tables.  An underlying abort is
terminal and costs zero, while a monitor stop is charged at the exact step that appended its
attempted occurrence. -/
lemma d2sQueryRunRevisedAdaptiveWithStep_monitorStop_le
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
    Pr[ fun result => result.isMonitorStop |
      d2sQueryRunRevisedAdaptiveWithStep kernel control fuel controlState normal] ≤
      ((fuel * (2 * j + fuel) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  classical
  induction fuel generalizing controlState normal j with
  | zero =>
      cases hNext : control.next controlState normal <;>
        simp [d2sQueryRunRevisedAdaptiveWithStep, hNext, D2SAdaptiveRunResult.isMonitorStop]
  | succ fuel ih =>
      cases hNext : control.next controlState normal with
      | done =>
          rw [d2sQueryRunRevisedAdaptiveWithStep, hNext, probEvent_pure]
          simp [D2SAdaptiveRunResult.isMonitorStop]
      | query q advance =>
          let next := fun stepResult : D2SAdaptiveStepResult
              (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
              (δ := δ) (T_H := T_H) (T_P := T_P) S q =>
            match stepResult with
            | .continue answer state' normal' =>
                d2sQueryRunRevisedAdaptiveWithStep kernel control fuel
                  (advance state' answer normal') normal'
            | .stopped normal' record => pure (.stopped controlState normal' record)
            | .underlyingAbort => pure (.underlyingAbort controlState normal)
          have hStep := contract.monitorStop_le controlState normal q j hCoherent hBaseLength
          have hBound := probEvent_bind_le_add
            (mx := kernel.step controlState normal q)
            (my := next)
            (p := fun stepResult => ¬ stepResult.isMonitorStop)
            (q := fun result => ¬ result.isMonitorStop)
            (ε₁ := ((2 * j + 1 : ℕ) : ℝ≥0∞) / BadEventDS.capacitySpaceSize (U := U))
            (ε₂ := ((fuel * (2 * (j + 1) + fuel) : ℕ) : ℝ≥0∞) /
              BadEventDS.capacitySpaceSize (U := U))
            (by simpa only [not_not] using hStep) (by
              intro stepResult hResult hNotStop
              cases stepResult with
              | «continue» answer state' normal' =>
                  have hInvariant := contract.continueInvariant controlState normal q j hCoherent
                    hBaseLength answer state' normal' hResult
                  simpa only [next, not_not] using
                    ih (advance state' answer normal') normal' (j + 1) hInvariant.1 hInvariant.2
              | stopped _ _ =>
                  simp only [D2SAdaptiveStepResult.isMonitorStop, not_true_eq_false] at hNotStop
              | underlyingAbort =>
                  simp [next, D2SAdaptiveRunResult.isMonitorStop])
          rw [← ENNReal.add_div] at hBound
          simp only [not_not] at hBound
          have hcharge :
              2 * j + 1 + fuel * (2 * (j + 1) + fuel) =
                (fuel + 1) * (2 * j + (fuel + 1)) := by
            ring
          have hchargeENN :
              ((2 * j + 1 : ℕ) : ℝ≥0∞) +
                  ((fuel * (2 * (j + 1) + fuel) : ℕ) : ℝ≥0∞) =
                (((fuel + 1) * (2 * j + (fuel + 1)) : ℕ) : ℝ≥0∞) := by
            exact_mod_cast hcharge
          rw [hchargeENN] at hBound
          simpa [d2sQueryRunRevisedAdaptiveWithStep, hNext, next] using hBound

omit [VCVCompatible U] [Fintype U] [Nonempty U] in
@[simp] lemma d2sQueryRunRevisedAdaptive_zero
    {S : Type}
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (control : D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P) S)
    (controlState : S)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    d2sQueryRunRevisedAdaptive gImpl control 0 controlState normal = pure (.continue () normal) :=
  rfl

/-- The fixed-stream controller, included to make the old finite runner a proved specialization of
the adaptive core rather than a parallel semantics. -/
noncomputable def D2SAdaptiveControl.ofList :
    D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (List (duplexSpongeChallengeOracle StmtIn U).Domain) where
  next queries _ :=
    match queries with
    | [] => .done
    | q :: queries => .query q fun _ _ _ => queries

/-- The canonical adaptive controller for one concrete oracle program whose only external oracle
is the duplex sponge.  Its control state is the residual `OracleComp`: a `pure` residual has no
next D2S request, while a `queryBind` residual exposes exactly its head request and advances to its
typed continuation on the returned answer. -/
noncomputable def D2SAdaptiveControl.ofOracleComp (α : Type) :
    D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp (duplexSpongeChallengeOracle StmtIn U) α) where
  next residual _ :=
    match residual with
    | .pure _ => .done
    | .queryBind q continuation => .query q fun _ answer _ => continuation answer

/-- The canonical controller for the exact wide verifier interface `[]ₒ + DS`.  This is not a
coercion that silently discards an ambient oracle: its left summand is definitionally `PEmpty`,
and the impossible case is eliminated by the type.  Thus each exposed request is a genuine DS
request and the residual program is advanced with its typed DS answer.

This is the controller required by the paper's verifier experiments.  A future refinement may
use it for `runForwardVerifierWide` only after proving the corresponding query fuel and the
initial normal-state/log relation; this definition supplies the exact structural interface, not
that semantic refinement. -/
noncomputable def D2SAdaptiveControl.ofEmptyLiftedOracleComp (α : Type) :
    D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α) where
  next residual _ :=
    match residual with
    | .pure _ => .done
    | .queryBind (.inl impossible) _ => PEmpty.elim impossible
    | .queryBind (.inr q) continuation => .query q fun _ answer _ => continuation answer

omit [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveControl.ofOracleComp_next_pure
    {α : Type}
    (value : α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SAdaptiveControl.ofOracleComp (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (T_H := T_H) (T_P := T_P) α).next (pure value) normal = .done := rfl

omit [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveControl.ofOracleComp_next_queryBind
    {α : Type} (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (continuation : (duplexSpongeChallengeOracle StmtIn U).Range q →
      OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SAdaptiveControl.ofOracleComp (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (T_H := T_H) (T_P := T_P) α).next
        (OracleComp.queryBind q continuation) normal =
      .query q (fun _ answer _ => continuation answer) := rfl

omit [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveControl.ofEmptyLiftedOracleComp_next_pure
    {α : Type}
    (value : α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SAdaptiveControl.ofEmptyLiftedOracleComp
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (T_H := T_H) (T_P := T_P) α).next (pure value) normal = .done := rfl

omit [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
@[simp] lemma D2SAdaptiveControl.ofEmptyLiftedOracleComp_next_queryBind
    {α : Type} (q : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (continuation : (duplexSpongeChallengeOracle StmtIn U).Range q →
      OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) α)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    (D2SAdaptiveControl.ofEmptyLiftedOracleComp
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
      (δ := δ) (T_H := T_H) (T_P := T_P) α).next
        (OracleComp.queryBind (.inr q) continuation) normal =
      .query q (fun _ answer _ => continuation answer) := rfl

/-! ## The concrete pure-`Hyb₁` verifier segment -/

/-- The live state carried by the pure-paper `Hyb₁` verifier segment.  The first component is
the one eagerly sampled, immutable `g` table from Eq. (15); the second is the actual residual
wide forward-verifier program.  Keeping both components in the adaptive state avoids a second
oracle semantics or a caller-supplied verifier sampler. -/
abbrev Hyb1VerifierState (StmtOut : Type) [VCVCompatible StmtIn] : Type :=
  (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier ×
    OracleComp ([]ₒ + duplexSpongeChallengeOracle StmtIn U) (Option StmtOut)

/-- The exact adaptive controller for a pure-paper `Hyb₁` verifier residual.  Its left oracle
summand is definitionally empty, so every nonterminal residual query is a D2S request.  On a
successful D2S step, the typed answer advances precisely that residual program; the fixed
eagerly sampled `g` table is retained in the control state. -/
noncomputable def hyb1VerifierControl {StmtOut : Type} [VCVCompatible StmtIn] :
    D2SAdaptiveControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut) where
  next state normal :=
    match (D2SAdaptiveControl.ofEmptyLiftedOracleComp
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Option StmtOut)).next state.2 normal with
    | .done => .done
    | .query q advance => .query q fun state' answer normal' =>
      (state'.1, advance state'.2 answer normal')

/-- The actual pure-`Hyb₁` D2S step interpreter.  It reads the sampled `D_Σ` carrier stored in
the control state and otherwise invokes the sole revised D2SQuery dispatcher.  In particular,
the carrier is not resampled or updated between verifier requests. -/
noncomputable def hyb1VerifierStepKernel {StmtOut : Type} [VCVCompatible StmtIn] :
    D2SAdaptiveStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut) where
  step state normal q := do
    D2SAdaptiveStepResult.ofRevised state <$> simulateQ
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1 +
        ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryStepRevised normal q)

/-- The real pure-`Hyb₁` step kernel satisfies the generic first-bad contract.  This is not a
new independence argument: after fixing the eagerly sampled `g` table, it is exactly the direct
dispatcher proof, pointwise in that table. -/
noncomputable def hyb1VerifierStepKernelFirstBadContract {StmtOut : Type}
    [VCVCompatible StmtIn] :
    D2SAdaptiveKernelFirstBadContract
      (hyb1VerifierStepKernel
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtOut := StmtOut)) where
  monitorStop_le state normal q j hCoherent hBaseLength := by
    rw [hyb1VerifierStepKernel, probEvent_map]
    change Pr[ fun result =>
      (D2SAdaptiveStepResult.ofRevised state result).isMonitorStop |
        simulateQ
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1 +
            ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
          (d2sQueryStepRevised normal q)] ≤ _
    rw [show (fun result : D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        ((duplexSpongeChallengeOracle StmtIn U).Range q) =>
        (D2SAdaptiveStepResult.ofRevised state result).isMonitorStop) =
        fun result => result.isMonitorStop from funext fun result =>
          propext (D2SAdaptiveStepResult.ofRevised_isMonitorStop state result)]
    exact d2sQueryStepRevised_monitorStop_le_of_baseLength_le
      ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1) normal q hCoherent j hBaseLength
  continueInvariant state normal q j hCoherent hBaseLength answer state' normal' hResult := by
    rw [hyb1VerifierStepKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» rawAnswer rawNormal =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        injection hEq with hAnswer hState hNormal
        subst answer
        subst state'
        subst normal'
        have hInvariant := d2sQueryStepRevised_maintainsInvariant normal hCoherent q
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1)
          (.continue rawAnswer rawNormal) hRaw
        refine ⟨hInvariant.1, ?_⟩
        exact Nat.le_trans
          (d2sQueryStepRevised_continue_baseTrace_length_le normal q
            ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1) rawAnswer rawNormal hRaw)
          (Nat.succ_le_succ hBaseLength)
    | stopped rawNormal rawRecord =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq

/-- The pure Hyb₁ verifier kernel also exposes the exact insertion-ordered history required by
the stateful replay proof.  This is the non-probabilistic companion of
`hyb1VerifierStepKernelFirstBadContract`: a successful step appends one occurrence, while a
monitor stop exposes the record's own post-occurrence trace.  The sampled finite `g` table is
read-only, so it is preserved as the controller component on every continuing branch. -/
noncomputable def hyb1VerifierStepKernelHistoryContract {StmtOut : Type}
    [VCVCompatible StmtIn] :
    D2SAdaptiveKernelHistoryContract
      (hyb1VerifierStepKernel
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtOut := StmtOut)) where
  continue_append_one state normal q answer state' normal' hResult := by
    rw [hyb1VerifierStepKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» rawAnswer rawNormal =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        injection hEq with hAnswer hState hNormal
        subst answer
        subst state'
        subst normal'
        exact d2sQueryStepRevised_continue_trace_extension normal q
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1) rawAnswer rawNormal hRaw
    | stopped rawNormal rawRecord =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
  monitorStop_prefix state normal q stoppedNormal record hResult := by
    rw [hyb1VerifierStepKernel, support_map] at hResult
    obtain ⟨result, hRaw, hEq⟩ := hResult
    cases result with
    | «continue» rawAnswer rawNormal =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq
    | stopped rawNormal rawRecord =>
        simp only [D2SAdaptiveStepResult.ofRevised] at hEq
        have hTrace := d2sQueryStepRevised_stopped_trace_extension normal q
          ((D_SigmaFinite (U := U) StmtIn pSpec δ).toImpl state.1) rawNormal rawRecord hRaw
        cases hEq
        exact hTrace
    | underlyingAbort =>
        simp [D2SAdaptiveStepResult.ofRevised] at hEq

/-- Run the concrete verifier segment reached by the paper's pure `Hyb₁` experiment.  This
definition starts from the actual `runForwardVerifierWide` residual and the once-sampled `D_Σ`
carrier.  It deliberately does not yet assert the live game-refinement equality or identify
`fuel` with `N_𝒱`; those are the remaining semantic bridge obligations. -/
noncomputable def hyb1PureVerifierAdaptiveRun {StmtOut : Type} [VCVCompatible StmtIn]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (fuel : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)) :
    ProbComp (D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut)) :=
  d2sQueryRunRevisedAdaptiveWithStep
    (hyb1VerifierStepKernel
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtOut := StmtOut))
    (hyb1VerifierControl
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtOut := StmtOut))
    fuel (kSigma, runForwardVerifierWide δ V stmtIn proof) normal

/-- Exact first-bad charge for a concrete pure-`Hyb₁` verifier segment from an arbitrary
coherent revised-D2S state.  This is the probability component used by the stateful replay
bridge: once that bridge identifies the runner fuel with its actual D2S request count and bounds
the pre-existing base trace by `j`, the bound below is already the required conditional charge.

For the complete forward verifier, `N_𝒱 + 1` is sufficient fuel: `N_𝒱` is the exact stateful
schedule count of forward permutation calls, and the extra unit covers the initial `DS.Start`
hash query.  The proof below intentionally needs only this upper bound; it does not silently
claim that every response-dependent execution has exactly that many requests.

The theorem intentionally does not claim that a public hybrid has this distribution.  Establishing
that equality is the separate live-executor refinement obligation. -/
lemma hyb1PureVerifierAdaptiveRun_monitorStop_le {StmtOut : Type}
    [VCVCompatible StmtIn]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (fuel : ℕ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (j : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j) :
    Pr[ fun result => result.isMonitorStop |
      hyb1PureVerifierAdaptiveRun
        (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof fuel normal] ≤
      ((fuel * (2 * j + fuel) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  simpa [hyb1PureVerifierAdaptiveRun] using
    d2sQueryRunRevisedAdaptiveWithStep_monitorStop_le
      (hyb1VerifierStepKernel
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtOut := StmtOut))
      (hyb1VerifierStepKernelFirstBadContract
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtOut := StmtOut))
      (hyb1VerifierControl
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtOut := StmtOut))
      fuel (kSigma, runForwardVerifierWide δ V stmtIn proof) normal j hCoherent hBaseLength

/-- The full-verifier stateful-count form of the pure-`Hyb₁` first-bad bound.  Its runner fuel is
`N_𝒱 + 1`, where `N_𝒱 = verifierPermCallCount pSpec δ` is the exact schedule count of forward
calls and the extra one covers the initial `DS.Start` hash request.  This is a sufficient,
non-rounded fuel bound rather than an assertion that every execution takes exactly this many
adaptive requests.

The theorem is unconditional about completion: the separate replay-realization theorem must show
that this fuel reaches `.complete` in the live verifier application.  Consequently no false
completion claim is hidden in the probability calculation. -/
lemma hyb1PureVerifierAdaptiveRun_at_verifierPermCallCount_succ_monitorStop_le {StmtOut : Type}
    [VCVCompatible StmtIn]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (j : ℕ) (hCoherent : RateOnlyCacheCoherent normal)
    (hBaseLength : (getBaseTrace normal.state.trace).length ≤ j) :
    Pr[ fun result => result.isMonitorStop |
      hyb1PureVerifierAdaptiveRun
        (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
        (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal] ≤
      (((verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) *
          (2 * j + (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1)) : ℕ) : ℝ≥0∞) /
        BadEventDS.capacitySpaceSize (U := U) := by
  exact hyb1PureVerifierAdaptiveRun_monitorStop_le
    (T_H := T_H) (T_P := T_P) kSigma V stmtIn proof
    (verifierPermCallCount (pSpec := pSpec) (δ := δ) + 1) normal j hCoherent hBaseLength

/-- A standalone pure-`Hyb₁` verifier segment from a fresh D2S state.  This is useful as the
zero-prefix base case for the adaptive first-bad arithmetic, but it is **not** the verifier phase
of the combined Figure-4 game: that phase must use `hyb1PureVerifierAdaptiveRun` with the exact
normal state returned by the prover.  The eagerly sampled `D_Σ` carrier remains fixed throughout
either execution. -/
noncomputable def hyb1PureVerifierAdaptiveRunFromInitial {StmtOut : Type} [VCVCompatible StmtIn]
    (kSigma : (D_SigmaFinite (U := U) StmtIn pSpec δ).Carrier)
    (V : Verifier []ₒ StmtIn StmtOut pSpec)
    (stmtIn : StmtIn) (proof : DSSaltedProof (pSpec := pSpec) (U := U) δ)
    (fuel : ℕ) :
    ProbComp (D2SAdaptiveRunResult
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) (T_H := T_H) (T_P := T_P)
      (Hyb1VerifierState (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ) StmtOut)) :=
  hyb1PureVerifierAdaptiveRun
    (T_H := T_H) (T_P := T_P) (kSigma := kSigma) V stmtIn proof fuel
    (D2SNormalState.initial
      (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) (δ := δ))

end DuplexSpongeFS.ProverTransform
