/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Run
/-!
# Correctness of the milestone-one decoder dispatch

The computed selector is identified with the paper's ordered guards.  The impossible-agreement,
constant-message, and authorized bounded-fallback branches satisfy the repository's full
`ExactOutput` contract.  The final theorem says every successful milestone-one supplied-equation
run is exact; large symbolic inputs fail explicitly because their constructor is a later
milestone.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder

open Polynomial JetHornerMachine

variable {F : Type*} [Field F] [Fintype F]

/-! ## Dispatch refinement -/

/-- The first paper guard has priority over every other branch. -/
theorem dispatch_eq_impossibleAgreement_iff {n : Nat} (input : Input F n) (opts : Options) :
    dispatch (F := F) input opts = .impossibleAgreement ↔ n < input.agreement := by
  by_cases hA : n < input.agreement
  · simp [dispatch, hA]
  · by_cases hk : input.k = 1
    · simp [dispatch, hA, hk]
    · by_cases hfallback : fallbackRequired F input opts <;>
        simp [dispatch, hA, hk, hfallback]

/-- Once `A <= n`, the second paper guard selects exactly `k = 1`. -/
theorem dispatch_eq_constant_iff {n : Nat} (input : Input F n) (opts : Options)
    (hA : input.agreement ≤ n) :
    dispatch (F := F) input opts = .constant ↔ input.k = 1 := by
  by_cases hk : input.k = 1
  · simp [dispatch, Nat.not_lt.mpr hA, hk]
  · by_cases hfallback : fallbackRequired F input opts <;>
      simp [dispatch, Nat.not_lt.mpr hA, hk, hfallback]

/-- After the first two guards, fallback is selected exactly for the paper's disjunction. -/
theorem dispatch_eq_boundedFallback_iff {n : Nat} (input : Input F n) (opts : Options)
    (hA : input.agreement ≤ n) (hk : input.k ≠ 1) :
    dispatch (F := F) input opts = .boundedFallback ↔
      n < boundedThreshold opts ∨ input.k ≤ opts.order ∨
        ¬ prescribedGuardsPass input.characteristic input.characteristic n input.k opts := by
  change dispatch (F := F) input opts = .boundedFallback ↔ fallbackRequired F input opts
  by_cases hfallback : fallbackRequired F input opts <;>
    simp [dispatch, Nat.not_lt.mpr hA, hk, hfallback]

/-- After the first two guards, the symbolic branch is exactly the negation of the fallback
disjunction. -/
theorem dispatch_eq_symbolic_iff {n : Nat} (input : Input F n) (opts : Options)
    (hA : input.agreement ≤ n) (hk : input.k ≠ 1) :
    dispatch (F := F) input opts = .symbolic ↔
      boundedThreshold opts ≤ n ∧ ¬ input.k ≤ opts.order ∧
        prescribedGuardsPass input.characteristic input.characteristic n input.k opts := by
  constructor
  · intro hdispatch
    have hfallback : ¬ fallbackRequired F input opts := by
      intro hfallback
      have hwrong : dispatch (F := F) input opts = .boundedFallback := by
        simp [dispatch, Nat.not_lt.mpr hA, hk, hfallback]
      rw [hwrong] at hdispatch
      contradiction
    rcases not_or.mp hfallback with ⟨hlarge, hrest⟩
    rcases not_or.mp hrest with ⟨horder, hguards⟩
    exact ⟨Nat.le_of_not_gt hlarge, horder, Classical.byContradiction hguards⟩
  · rintro ⟨hlarge, horder, hguards⟩
    have hfallback : ¬ fallbackRequired F input opts := by
      simp only [fallbackRequired, not_or, not_lt]
      exact ⟨hlarge, horder, not_not.mpr hguards⟩
    simp [dispatch, Nat.not_lt.mpr hA, hk, hfallback]

/-- Valid large options satisfy every prescribed arithmetic guard. -/
theorem prescribedGuardsPass_of_valid_of_large {n : Nat} (input : Input F n)
    (opts : Options) (hinput : ValidInput input) (hopts : ValidOptions input opts)
    (hlarge : boundedThreshold opts ≤ n) :
    prescribedGuardsPass input.characteristic input.characteristic n input.k opts := by
  rcases hinput with ⟨hkpos, hkn, _, hnchar, _⟩
  rcases hopts with ⟨_, _, _, _, _⟩
  have hjetThreshold : opts.jetDegree < boundedThreshold opts := by
    unfold boundedThreshold
    omega
  have hcoordinateThreshold : coordinateGridGuard opts < boundedThreshold opts := by
    unfold boundedThreshold
    omega
  have hcenterThreshold : centerLinearGuard opts < boundedThreshold opts := by
    unfold boundedThreshold
    omega
  have hkpredChar : input.k - 1 < input.characteristic := by
    omega
  refine ⟨max_lt hkpredChar (hjetThreshold.trans_le (hlarge.trans hnchar)),
    hcoordinateThreshold.trans_le (hlarge.trans hnchar), ?_⟩
  have hcenterN : centerLinearGuard opts < n := hcenterThreshold.trans_le hlarge
  have hnpos : 0 < n := lt_of_lt_of_le hkpos hkn
  calc
    centerLinearGuard opts * n < n * n := Nat.mul_lt_mul_of_pos_right hcenterN hnpos
    _ = n ^ 2 := by simp [pow_two]
    _ ≤ input.characteristic ^ 2 := Nat.pow_le_pow_left hnchar 2

/-! ## Executed branch equations -/

variable [DecidableEq F]
variable (cmp : F → F → Ordering)

/-- `A > n` executes the successful empty output before inspecting the equation. -/
theorem runSupplied_of_A_gt_n {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : n < input.agreement) :
    runSupplied cmp input opts equation = .ok [] := by
  simp [runSupplied, dispatch, hA]

/-- `k = 1` executes frequency counting after the impossible-agreement check. -/
theorem runSupplied_of_constant {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : input.agreement ≤ n) (hk : input.k = 1) :
    runSupplied cmp input opts equation =
      .ok (ConstantDecoder.run cmp input.agreement input.received) := by
  simp [runSupplied, dispatch, Nat.not_lt.mpr hA, hk]

/-- The authorized fallback executes the position-subset decoder after the first two checks. -/
theorem runSupplied_of_fallback {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : input.agreement ≤ n) (hk : input.k ≠ 1)
    (hfallback : fallbackRequired F input opts) :
    runSupplied cmp input opts equation =
      .ok (PositionSubsetDecoder.run input.domain input.received input.k input.agreement) := by
  simp [runSupplied, dispatch, Nat.not_lt.mpr hA, hk, hfallback]

/-- A large guarded symbolic input reports the symbolic error and never retries with subsets. -/
theorem runSupplied_of_symbolic {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : input.agreement ≤ n) (hk : input.k ≠ 1)
    (hfallback : ¬ fallbackRequired F input opts) (hequation : equation.boundsPass (n := n)) :
    runSupplied cmp input opts equation = .error .symbolicBackendUnavailable := by
  simp [runSupplied, dispatch, symbolicDecode, Nat.not_lt.mpr hA, hk, hfallback, hequation]

/-- A malformed equation is rejected at the symbolic boundary, without invoking fallback. -/
theorem runSupplied_of_invalidEquation {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : input.agreement ≤ n) (hk : input.k ≠ 1)
    (hfallback : ¬ fallbackRequired F input opts) (hequation : ¬ equation.boundsPass (n := n)) :
    runSupplied cmp input opts equation = .error .invalidEquation := by
  simp [runSupplied, dispatch, Nat.not_lt.mpr hA, hk, hfallback, hequation]

/-! ## Easy-branch exactness -/

omit [Fintype F] in
/-- An agreement threshold above the block length has exact empty output. -/
theorem exactOutput_nil_of_A_gt_n {n : Nat} (input : Input F n)
    (hA : n < input.agreement) :
    ExactOutput input.domain input.received input.k input.agreement [] := by
  apply exactOutput_of_sound_complete input.domain input.received input.k input.agreement []
    List.nodup_nil
  · simp
  · intro P _ hagreement
    exact False.elim (by
      have := Code.agree_le_card
        (u := evalOnPoints input.domain P) (v := input.received)
      simp only [Fintype.card_fin] at this
      omega)

variable [BEq F] [LawfulBEq F]
variable [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

omit [BEq F] [LawfulBEq F] [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- The first paper branch is closed and exact. -/
theorem runSupplied_exact_of_A_gt_n {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hA : n < input.agreement) :
    ∃ out, runSupplied cmp input opts equation = .ok out ∧
      ExactOutput input.domain input.received input.k input.agreement out := by
  exact ⟨[], runSupplied_of_A_gt_n cmp input opts equation hA,
    exactOutput_nil_of_A_gt_n input hA⟩

/-- The constant-message branch is closed and exact for valid input. -/
theorem runSupplied_exact_of_constant {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hinput : ValidInput input)
    (hA : input.agreement ≤ n) (hk : input.k = 1) :
    ∃ out, runSupplied cmp input opts equation = .ok out ∧
      ExactOutput input.domain input.received input.k input.agreement out := by
  have hthreshold : 1 ≤ input.agreement := hinput.1.trans hinput.2.2.1
  exact ⟨ConstantDecoder.run cmp input.agreement input.received,
    runSupplied_of_constant cmp input opts equation hA hk,
    by simpa [hk] using
      ConstantDecoder.run_exact cmp input.domain input.received input.agreement hthreshold⟩

omit [BEq F] [LawfulBEq F] [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- The paper-authorized bounded-position branch is closed and exact for valid input. -/
theorem runSupplied_exact_of_fallback {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hinput : ValidInput input)
    (hA : input.agreement ≤ n) (hk : input.k ≠ 1)
    (hfallback : fallbackRequired F input opts) :
    ∃ out, runSupplied cmp input opts equation = .ok out ∧
      ExactOutput input.domain input.received input.k input.agreement out := by
  exact ⟨PositionSubsetDecoder.run input.domain input.received input.k input.agreement,
    runSupplied_of_fallback cmp input opts equation hA hk hfallback,
    PositionSubsetDecoder.run_exact input.domain input.received input.k input.agreement
      hinput.2.2.1⟩

/-- Every successful milestone-one supplied-equation run is exact.

At this milestone success is possible only in the three closed easy branches.  The symbolic path
returns a typed error, so this theorem does not assume a placeholder candidate-coverage oracle.
-/
theorem runSupplied_ok_exact {n : Nat} (input : Input F n) (opts : Options)
    (equation : SuppliedEquation F opts) (hinput : ValidInput input) (out : List (List F))
    (hrun : runSupplied cmp input opts equation = .ok out) :
    ExactOutput input.domain input.received input.k input.agreement out := by
  cases hbranch : dispatch (F := F) input opts with
  | impossibleAgreement =>
      simp only [runSupplied, hbranch] at hrun
      injection hrun with hout
      subst out
      exact exactOutput_nil_of_A_gt_n input
        ((dispatch_eq_impossibleAgreement_iff (F := F) input opts).mp hbranch)
  | constant =>
      simp only [runSupplied, hbranch] at hrun
      injection hrun with hout
      subst out
      have hA : input.agreement ≤ n := by
        by_contra h
        have himpossible : dispatch (F := F) input opts = .impossibleAgreement :=
          (dispatch_eq_impossibleAgreement_iff (F := F) input opts).mpr (by omega)
        simp_all
      have hk : input.k = 1 :=
        (dispatch_eq_constant_iff (F := F) input opts hA).mp hbranch
      have hthreshold : 1 ≤ input.agreement := hinput.1.trans hinput.2.2.1
      simpa [hk] using
        ConstantDecoder.run_exact cmp input.domain input.received input.agreement hthreshold
  | boundedFallback =>
      simp only [runSupplied, hbranch] at hrun
      injection hrun with hout
      subst out
      exact PositionSubsetDecoder.run_exact input.domain input.received input.k
        input.agreement hinput.2.2.1
  | symbolic =>
      simp only [runSupplied, hbranch, symbolicDecode] at hrun
      split at hrun <;> contradiction

/-! ## Certified-support entrypoint -/

omit [BEq F] [LawfulBEq F] [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] in
/-- A valid support executes interpolation and reaches the identical supplied-equation run with
an equation satisfying the public semantic contract. -/
theorem runCertified_eq_runSupplied_of_valid {n : Nat} (input : Input F n) (opts : Options)
    (certificate : SupportCertificate) (hinput : ValidInput input)
    (hvalid : certificate.Valid input opts) :
    ∃ equation, construct input opts certificate = .ok equation ∧
      equation.Explains input ∧
      runCertified cmp input opts certificate = runSupplied cmp input opts equation := by
  obtain ⟨equation, hconstruct, hexplains⟩ :=
    construct_explains input opts certificate hinput hvalid
  refine ⟨equation, hconstruct, hexplains, ?_⟩
  cases hbranch : dispatch (F := F) input opts <;>
    simp [runCertified, runSupplied, hbranch, hconstruct]

/-- Every successful certified-support run in milestone one is exact. -/
theorem runCertified_ok_exact {n : Nat} (input : Input F n) (opts : Options)
    (certificate : SupportCertificate) (hinput : ValidInput input) (out : List (List F))
    (hrun : runCertified cmp input opts certificate = .ok out) :
    ExactOutput input.domain input.received input.k input.agreement out := by
  cases hbranch : dispatch (F := F) input opts with
  | impossibleAgreement =>
      simp only [runCertified, hbranch] at hrun
      injection hrun with hout
      subst out
      exact exactOutput_nil_of_A_gt_n input
        ((dispatch_eq_impossibleAgreement_iff (F := F) input opts).mp hbranch)
  | constant =>
      simp only [runCertified, hbranch] at hrun
      injection hrun with hout
      subst out
      have hA : input.agreement ≤ n := by
        by_contra h
        have himpossible : dispatch (F := F) input opts = .impossibleAgreement :=
          (dispatch_eq_impossibleAgreement_iff (F := F) input opts).mpr (by omega)
        simp_all
      have hk : input.k = 1 :=
        (dispatch_eq_constant_iff (F := F) input opts hA).mp hbranch
      have hthreshold : 1 ≤ input.agreement := hinput.1.trans hinput.2.2.1
      simpa [hk] using
        ConstantDecoder.run_exact cmp input.domain input.received input.agreement hthreshold
  | boundedFallback =>
      simp only [runCertified, hbranch] at hrun
      injection hrun with hout
      subst out
      exact PositionSubsetDecoder.run_exact input.domain input.received input.k
        input.agreement hinput.2.2.1
  | symbolic =>
      cases hconstruct : construct input opts certificate with
      | error error => simp [runCertified, hbranch, hconstruct] at hrun
      | ok equation =>
          apply runSupplied_ok_exact cmp input opts equation hinput out
          simpa [runCertified, hbranch, hconstruct] using hrun

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder
