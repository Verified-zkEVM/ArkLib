/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.D2SFirstBadDispatcher

/-!
# Absorbing-run invariant for revised D2SQuery

This focused module lifts the one-step invariant of the live revised dispatcher over its actual
absorbing finite runner.  It is separated from `D2SFirstBadDispatcher` so both modules remain
below the repository's size limit while the probability layer may import only the boundary it
needs.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.ProverTransform

open DSTraceStorage

variable {StmtIn : Type} {n : Nat} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [codec : Codec pSpec U] {δ : Nat}
  [DecidableEq StmtIn] [DecidableEq U]
  {T_H : Type} {T_P : Type}
  [LawfulTraceNablaImpl T_H T_P StmtIn U]
  [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)]

/-- The whole finite-query counterpart of `D2SQueryStepMaintainsInvariant`.  It fixes the exact
absorbing `d2sQueryRunRevised` recursion, so after a monitored stop or an underlying abort no
suffix query is in the support.  This is the entry theorem the adaptive first-witness aggregation
for Lemma 5.8 must prove and consume. -/
def D2SQueryRunMaintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (queries : List (duplexSpongeChallengeOracle StmtIn U).Domain) : Prop :=
  ∀ (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
      (result : D2SRevisedStepResult
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit),
    result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryRunRevised normal queries)) →
      D2SRunOutcomeInvariant result

/-- A one-step support invariant lifts through the actual finite revised D2SQuery runner.

This is deliberately independent of the six handler implementations: their dispatcher proof need
only establish `D2SQueryStepMaintainsInvariant` for every coherent reusable state.  The induction
then follows the two defining equations of `d2sQueryRunRevised`, so it also proves the essential
absorbing fact: neither a monitor stop nor an underlying abort can expose a suffix query.  This
is the structural bridge from the five local first-bad gateways to one whole-execution Lemma 5.8
argument. -/
lemma d2sQueryRunMaintainsInvariant_of_step
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (queries : List (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hNormal : RateOnlyCacheCoherent normal)
    (hStep : ∀ (current : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
      RateOnlyCacheCoherent current →
      ∀ q : (duplexSpongeChallengeOracle StmtIn U).Domain,
        D2SQueryStepMaintainsInvariant current q) :
    D2SQueryRunMaintainsInvariant normal queries := by
  induction queries generalizing normal with
  | nil =>
      intro gImpl result hresult
      rw [d2sQueryRunRevised_nil, simulateQ_pure, mem_support_pure_iff] at hresult
      subst result
      exact ⟨hNormal, normal.monitorPassed⟩
  | cons q qs ih =>
      intro gImpl result hresult
      rw [d2sQueryRunRevised_cons, simulateQ_bind, mem_support_bind_iff] at hresult
      obtain ⟨stepResult, hStepResult, hResult⟩ := hresult
      have hStepInvariant := hStep normal hNormal q gImpl stepResult hStepResult
      match stepResult with
      | .continue answer nextNormal =>
          rcases hStepInvariant with ⟨hNextCoherent, _⟩
          exact ih nextNormal hNextCoherent gImpl result (by simpa using hResult)
      | .stopped nextNormal record =>
          have hEq : result = .stopped nextNormal record := by
            simpa using hResult
          subst result
          exact hStepInvariant
      | .underlyingAbort =>
          have hEq : result = .underlyingAbort := by
            simpa using hResult
          subst result
          trivial

/-- The concrete revised D2SQuery runner preserves the invariant across every finite query
stream.  No hand-supplied branch premise remains: the preceding theorem discharges every live
hash, inverse, ordinary-forward, tail, and Program case. -/
lemma d2sQueryRunRevised_maintainsInvariant
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (queries : List (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hCoherent : RateOnlyCacheCoherent normal) :
    D2SQueryRunMaintainsInvariant normal queries := by
  apply d2sQueryRunMaintainsInvariant_of_step normal queries hCoherent
  intro current hCurrent q
  exact d2sQueryStepRevised_maintainsInvariant current hCurrent q

set_option linter.unusedFintypeInType false in
/-- A monitored terminal result of the concrete finite runner exposes one retained stop record
and that record's canonical first bad index.  This is the exact structural input to the later
first-event probability aggregation; search/parser aborts cannot enter this theorem. -/
lemma d2sQueryRunRevised_monitorStop_support_firstBad
    [VCVCompatible U] [Fintype U] [Nonempty U] [SampleableType U]
    (normal : D2SNormalState
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (queries : List (duplexSpongeChallengeOracle StmtIn U).Domain)
    (hCoherent : RateOnlyCacheCoherent normal)
    (gImpl : QueryImpl (gSpec (U := U) StmtIn pSpec δ) ProbComp)
    (result : D2SRevisedStepResult
      (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U) Unit)
    (hResult : result ∈ support (simulateQ
      (gImpl + ((d2sUnitSampleImpl (U := U)) + QueryImpl.id' unifSpec))
      (d2sQueryRunRevised normal queries)))
    (hStop : result.isMonitorStop) :
    ∃ (stopNormal : D2SNormalState
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
      (record : D2SPostOccurrenceStopRecord
        (δ := δ) (T_H := T_H) (T_P := T_P)
        (StmtIn := StmtIn) (pSpec := pSpec) (U := U) stopNormal),
      result = .stopped stopNormal record ∧
        BadEventDS.E_first_at record.trace record.firstBadIndex := by
  have hInvariant := d2sQueryRunRevised_maintainsInvariant normal queries hCoherent
    gImpl result hResult
  cases result
  · simp only [D2SRevisedStepResult.isMonitorStop_continue] at hStop
  · exact ⟨_, _, rfl, hInvariant.2⟩
  · simp only [D2SRevisedStepResult.isMonitorStop_underlyingAbort] at hStop

end DuplexSpongeFS.ProverTransform
