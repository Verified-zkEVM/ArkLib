/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.CompositionSoundness
import ArkLibTest.Interaction.CompositionSoundness

/-!
# A derived oracle and a fresh final decision

The prefix publishes a sample with mass one-half on each of `0` and `1`, and exports its input
value plus that sample. The suffix reads only the exported interface, makes a fresh random query,
and may reject. The composition bound charges a true midpoint separately from the remaining
branch's one-half error. Its weighted bound is three-quarters.
-/

namespace Interaction.Oracle.CompositionSoundnessExample

open OracleComp OracleSpec MeasureTheory TwoParty
open PFunctor.FreeM.Displayed (Decoration)
open NativeCompositionTest.Weighted (branchSpec branchMeasure)
open scoped ENNReal

noncomputable section

abbrev ambient := branchSpec
abbrev inputSpec : OracleSpec Unit := Unit →ₒ Nat

def inputImpl : QueryImpl inputSpec Id := fun _ => 7

@[reducible]
def natInterface : OracleInterface Nat where
  Query := Unit
  toOC.spec := Unit →ₒ Nat
  toOC.impl _ := read

abbrev family : OracleFamily Unit (fun _ => Nat) := ⟨fun _ => natInterface⟩
abbrev firstProtocol : Protocol := .public .receiver (Fin 3) fun _ => .done
abbrev secondProtocol : Protocol := .done
abbrev combined : Protocol :=
  ⟨PFunctor.FreeM.append firstProtocol.tree (fun _ => secondProtocol.tree),
    Decoration.append firstProtocol.roles (fun _ => secondProtocol.roles),
    Decoration.append firstProtocol.oracles (fun _ => secondProtocol.oracles)⟩

/-- A derived exported query uses the actual input source and the public sample. -/
def exportView (sample : Fin 3) : VirtualOracle inputSpec family :=
  ⟨fun _ => do return (← liftM (inputSpec.query ())) + sample.val⟩

def firstVerifier : Verifier.Fragment ambient firstProtocol.tree firstProtocol.roles
    firstProtocol.oracles inputSpec.toPFunctor (fun _ => OpenClaim inputSpec (Fin 3) family) := do
  let sample ← liftM ((ambient + inputSpec).query (.inl ()))
  return ⟨sample, ⟨sample, exportView sample⟩⟩

/-- A terminal query can reject; any returned claim retains the exported oracle. -/
def secondVerifier (_ : firstProtocol.tree.BranchPath) (_ : Fin 3) :
    Verifier.Strategy ambient secondProtocol.tree secondProtocol.roles secondProtocol.oracles
      family.spec.toPFunctor (fun _ => Option (OpenClaim family.spec Nat family)) := by
  change OracleComp (ambient + family.spec) (Option (OpenClaim family.spec Nat family))
  exact do
    let value : Nat ← liftM ((ambient + family.spec).query (.inr ⟨(), ()⟩))
    let coin : Fin 3 ← liftM ((ambient + family.spec).query (.inl ()))
    if value = 7 ∨ coin = 1 then return some ⟨value, VirtualOracle.id family⟩
    else return none

def prover : Prover.Strategy ambient combined.tree combined.roles (fun _ => Unit) :=
  fun _ => pure ()

abbrev Boundary := ExportedBoundary ambient firstProtocol.tree (fun _ => secondProtocol.tree)
  (fun _ => secondProtocol.roles) firstProtocol.oracles inputSpec.toPFunctor
  (fun _ => Fin 3) (fun _ _ => Nat) (fun _ => family) (fun _ => Unit)

abbrev prefixProgram := exportedPrefixRun ambient firstProtocol.tree
  (fun _ => secondProtocol.tree) firstProtocol.roles (fun _ => secondProtocol.roles)
  firstProtocol.oracles inputSpec.toPFunctor inputImpl (fun _ => Fin 3)
  (fun _ _ => Nat) (fun _ => family) (fun _ => Unit) prover firstVerifier

abbrev nextProgram := exportedSuffixRun ambient firstProtocol.tree
  (fun _ => secondProtocol.tree) (fun _ => secondProtocol.roles) firstProtocol.oracles
  (fun _ => secondProtocol.oracles) inputSpec.toPFunctor inputImpl (fun _ => Fin 3)
  (fun _ _ => Nat) (fun _ => family) (fun _ => Nat) (fun _ _ => Nat) (fun _ => family)
  (fun _ => Unit) secondVerifier

@[reducible]
def boundary (sample : Fin 3) : Boundary :=
  ⟨⟨sample, PUnit.unit⟩, (), ⟨sample, exportView sample⟩⟩

instance : MeasurableSpace Boundary := ⊤
instance : DiscreteMeasurableSpace Boundary := ⟨fun _ => trivial⟩

theorem prefix_execution : prefixProgram = (query (spec := ambient) () >>= fun sample =>
    pure (boundary sample)) := by
  rfl

theorem prefix_measure : 𝒟[prefixProgram] =
    (1 / 2 : ENNReal) • Measure.dirac (boundary 0) +
      (1 / 2 : ENNReal) • Measure.dirac (boundary 1) := by
  rw [prefix_execution, evalDist_bind_of_discrete, OracleComp.evalDist_query (spec := ambient),
    MeasureTheory.trim_eq_self]
  change Measure.bind branchMeasure _ = _
  simp only [evalDist_pure]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [branchMeasure, Measure.map_add _ _ Measurable.of_discrete]
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete]

/-- Midpoint truth is tested on its actual closed exported behavior. -/
def midpointTrue (_ : firstProtocol.tree.BranchPath) (claim : ClosedClaim (Fin 3) family) : Prop :=
  claim.oracles ⟨(), ()⟩ = (7 : Nat)

def admissible (_ : firstProtocol.tree.BranchPath) (claim : ClosedClaim (Fin 3) family) : Prop :=
  claim.oracles ⟨(), ()⟩ ≠ (7 : Nat)

def finalTrue (_ : combined.tree.BranchPath) (claim : ClosedClaim Nat family) : Prop :=
  claim.oracles ⟨(), ()⟩ = claim.stmt

abbrev closedMid (b : Boundary) := b.2.2.closeWith
  ((TypeTree.ExecutionPath.ofTypeTreePath b.1).closingImpl firstProtocol.oracles
    inputSpec.toPFunctor inputImpl)

abbrev trueMid (b : Boundary) :=
  midpointTrue (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath (closedMid b)

abbrev allowed (b : Boundary) :=
  admissible (TypeTree.ExecutionPath.ofTypeTreePath b.1).toBranchPath (closedMid b)

def error (b : Boundary) : ENNReal := by
  classical
  exact if b.1.1 = (1 : Fin 3) then 1 / 2 else 0

theorem trueMid_boundary (sample : Fin 3) : trueMid (boundary sample) ↔ sample = 0 := by
  change 7 + sample.val = 7 ↔ sample = 0
  omega

theorem allowed_boundary (sample : Fin 3) : allowed (boundary sample) ↔ sample ≠ 0 := by
  change 7 + sample.val ≠ 7 ↔ sample ≠ 0
  omega

theorem prefix_truth : Pr{let b ← prefixProgram}[trueMid b] = (1 / 2 : ENNReal) := by
  classical
  rw [prEvent_eq_evalDist_of_discrete, prefix_measure]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply' _ MeasurableSet.of_discrete,
    Measure.dirac_apply' _ MeasurableSet.of_discrete]
  have h0 : boundary 0 ∈ {x | trueMid x} := (trueMid_boundary 0).2 rfl
  have h1 : boundary 1 ∉ {x | trueMid x} := fun h => by
    have := (trueMid_boundary 1).1 h
    contradiction
  simp only [Set.indicator]
  change ((1 / 2 : ENNReal) * (if trueMid (boundary 0) then 1 else 0) +
    (1 / 2 : ENNReal) * (if trueMid (boundary 1) then 1 else 0)) = _
  change trueMid (boundary 0) at h0
  change ¬ trueMid (boundary 1) at h1
  rw [ite_eq_left h0, ite_eq_right h1, mul_one, mul_zero, add_zero]

theorem prefix_false_invalid :
    Pr{let b ← prefixProgram}[¬ trueMid b ∧ ¬ allowed b] = 0 := by
  classical
  rw [prEvent_eq_evalDist_of_discrete, prefix_measure]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  rw [Measure.dirac_apply' _ MeasurableSet.of_discrete,
    Measure.dirac_apply' _ MeasurableSet.of_discrete]
  have h0 : boundary 0 ∉ {x | ¬ trueMid x ∧ ¬ allowed x} :=
    fun h => h.1 ((trueMid_boundary 0).2 rfl)
  have h1 : boundary 1 ∉ {x | ¬ trueMid x ∧ ¬ allowed x} :=
    fun h => h.2 ((allowed_boundary 1).2 (by decide))
  simp only [Set.indicator]
  rw [ite_eq_right h0, ite_eq_right h1]
  simp

/-- True midpoint claims may be inadmissible without being charged a second time. -/
theorem prefix_inadmissible : Pr{let b ← prefixProgram}[¬ allowed b] = (1 / 2 : ENNReal) := by
  calc
    _ = Pr{let b ← prefixProgram}[trueMid b] := prEvent_congr _ _ _ (fun b => by
      change ¬ (closedMid b).oracles ⟨(), ()⟩ ≠ (7 : Nat) ↔
        (closedMid b).oracles ⟨(), ()⟩ = (7 : Nat)
      exact not_not)
    _ = _ := prefix_truth

theorem exported_behavior (sample : Fin 3) :
    (exportView sample).eval
      ((TypeTree.ExecutionPath.ofTypeTreePath (boundary sample).1).closingImpl
        firstProtocol.oracles inputSpec.toPFunctor inputImpl) = fun _ => 7 + sample.val := by
  funext q
  rcases q with ⟨⟨⟩, ⟨⟩⟩
  rfl

theorem suffix_execution (sample : Fin 3) : nextProgram (boundary sample) = (do
    let coin ← query (spec := ambient) ()
    if 7 + sample.val = 7 ∨ coin = 1 then
      pure ⟨PUnit.unit, some ⟨7 + sample.val, fun _ => 7 + sample.val⟩⟩
    else pure ⟨PUnit.unit, none⟩) := by
  dsimp [nextProgram, exportedSuffixRun, boundary, secondProtocol,
    Verifier.toCounterpartWith, Interaction.TwoParty.run]
  simp only [pure_bind, bind_map_left]
  change (simulateQ (Verifier.liftAccessImpl ambient family.spec.toPFunctor
      ((exportView sample).eval inputImpl)) (secondVerifier ⟨sample, PUnit.unit⟩ sample) >>=
      fun out => pure (⟨PUnit.unit, out.map (fun claim => claim.closeWith
        ((exportView sample).eval inputImpl))⟩ :
          (path : secondProtocol.tree.BranchPath) × Option (ClosedClaim Nat family))) = _
  have h : (exportView sample).eval inputImpl = fun _ => 7 + sample.val :=
    exported_behavior sample
  rw [h]
  dsimp [secondVerifier, id]
  simp only [simulateQ_bind, simulateQ_spec_query, Verifier.liftAccessImpl, bind_assoc]
  change (do
    let value ← pure (7 + sample.val)
    let coin ← query (spec := ambient) ()
    let out ← simulateQ (Verifier.liftAccessImpl ambient family.spec.toPFunctor
      (fun _ => 7 + sample.val))
      (if value = 7 ∨ coin = 1 then
        pure (some (⟨value, VirtualOracle.id family⟩ : OpenClaim family.spec Nat family))
       else pure none)
    pure (⟨PUnit.unit, out.map (fun claim : OpenClaim family.spec Nat family =>
      claim.closeWith (fun _ => 7 + sample.val))⟩ :
      (path : secondProtocol.tree.BranchPath) × Option (ClosedClaim Nat family))) = _
  simp only [pure_bind]
  apply bind_congr
  intro coin
  split_ifs <;> simp [simulateQ_pure, OpenClaim.closeWith, VirtualOracle.eval_id]

def suffixTrue (result : (_path : secondProtocol.tree.BranchPath) ×
    Option (ClosedClaim Nat family)) : Prop :=
  result.2.map (fun claim => claim.oracles ⟨(), ()⟩ = claim.stmt) = some True

theorem suffix_mass (sample : Fin 3) :
    Pr{let result ← nextProgram (boundary sample)}[suffixTrue result] =
      if sample = 0 then (1 : ENNReal) else 1 / 2 := by
  classical
  have h := congrArg (fun mx => Pr{let result ← mx}[suffixTrue result]) (suffix_execution sample)
  have hsome : suffixTrue ⟨PUnit.unit.{1}, some ⟨7 + sample.val, fun _ => 7 + sample.val⟩⟩ :=
    congrArg some (eq_true rfl)
  have hnone : ¬ suffixTrue ⟨PUnit.unit.{1}, none⟩ := nofun
  simp only [expect_norm, propInd_eq_one_iff.mpr hsome, propInd_eq_zero_iff.mpr hnone] at h
  rw [h, MeasureProgramLogic.wp_eq_lintegral _ _ Measurable.of_discrete,
    OracleComp.evalDist_query (spec := ambient), MeasureTheory.trim_eq_self,
    show OracleSpec.IsMeasureSpec.toMeasure (spec := ambient) () = branchMeasure from rfl]
  fin_cases sample <;>
    simp only [branchMeasure, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul, Fin.isValue]
  all_goals simp only [Nat.reduceAdd, Nat.reduceEqDiff, Fin.reduceEq, or_true, or_false,
    or_self, ↓reduceIte, one_div, mul_one, mul_zero, zero_add, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Fin.isValue, one_ne_zero]
  exact ENNReal.inv_two_add_inv_two

/-- Structural support includes a sample of probability zero. -/
theorem null_boundary_supported : boundary 2 ∈ support prefixProgram := by
  rw [prefix_execution, mem_support_bind_iff]
  exact ⟨(2 : Fin 3), OracleComp.mem_support_query (spec := ambient) () (2 : Fin 3), by simp⟩

/-- That null branch violates the local error bound, so a pointwise premise would be stronger. -/
theorem null_boundary_suffix_bound_fails :
    ¬ Pr{let result ← nextProgram (boundary 2)}[suffixTrue result] ≤ error (boundary 2) := by
  rw [suffix_mass]
  have he : error (boundary 2) = 0 := by
    unfold error
    exact ite_eq_right (show (2 : Fin 3) ≠ 1 by decide)
  rw [he, ite_eq_right (by decide : (2 : Fin 3) ≠ 0)]
  norm_num

theorem suffix_bound_ae : ∀ᵐ b ∂𝒟[prefixProgram], ¬ trueMid b → allowed b →
    Pr{let result ← nextProgram b}[suffixTrue result] ≤ error b := by
  classical
  rw [prefix_measure, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;>
    rw [ae_dirac_iff MeasurableSet.of_discrete]
  · intro hfalse _
    exact False.elim (hfalse ((trueMid_boundary 0).2 rfl))
  · intro _ _
    rw [suffix_mass]
    have he : error (boundary 1) = (1 / 2 : ENNReal) := by
      unfold error
      exact ite_eq_left rfl
    rw [he, ite_eq_right (by decide : (1 : Fin 3) ≠ 0)]

theorem average_error :
    (∫⁻ b in {b | ¬ trueMid b ∧ allowed b}, error b ∂𝒟[prefixProgram]) =
      (1 / 4 : ENNReal) := by
  classical
  calc
    _ = ∫⁻ b : Boundary, {b | ¬ trueMid b ∧ allowed b}.indicator error b
        ∂𝒟[prefixProgram] := (lintegral_indicator MeasurableSet.of_discrete error).symm
    _ = _ := by
      rw [prefix_measure]
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
      simp only [lintegral_dirac]
      have h0 : ¬ (¬ trueMid (boundary 0) ∧ allowed (boundary 0)) :=
        fun h => h.1 ((trueMid_boundary 0).2 rfl)
      have h1 : ¬ trueMid (boundary 1) ∧ allowed (boundary 1) :=
        ⟨fun h => (by decide : (1 : Fin 3) ≠ 0) ((trueMid_boundary 1).1 h),
          (allowed_boundary 1).2 (by decide)⟩
      change boundary 0 ∉ {b | ¬ trueMid b ∧ allowed b} at h0
      change boundary 1 ∈ {b | ¬ trueMid b ∧ allowed b} at h1
      rw [Set.indicator_of_notMem h0, Set.indicator_of_mem h1]
      have he : error (boundary 1) = (1 / 2 : ENNReal) := by
        unfold error
        exact ite_eq_left rfl
      rw [he]
      change (1 / 2 : ENNReal) * 0 + (1 / 2) * (1 / 2) = 1 / 4
      norm_num [← ENNReal.mul_inv]

/-- The actual composed execution has at most three-quarters true final-claim probability. -/
theorem weighted_success :
    Pr{let result ← (executeStrategies ambient combined.tree combined.roles combined.oracles
      inputSpec.toPFunctor inputImpl prover
      (Verifier.appendExported ambient firstProtocol.tree (fun _ => secondProtocol.tree)
        firstProtocol.roles (fun _ => secondProtocol.roles) firstProtocol.oracles
        (fun _ => secondProtocol.oracles) inputSpec.toPFunctor (fun _ => Fin 3)
        (fun _ _ => Nat) (fun _ => family) (fun _ => Nat) (fun _ _ => Nat)
        (fun _ => family) firstVerifier secondVerifier))}[
      result.2.2.map (fun claim : OpenClaim (ofPFunctor
        (TypeTree.accessAfter combined.tree combined.oracles inputSpec.toPFunctor
          result.1.toBranchPath)) Nat family => finalTrue result.1.toBranchPath
        (claim.closeWith (result.1.closingImpl combined.oracles inputSpec.toPFunctor inputImpl))) =
          some True] ≤ (3 / 4 : ENNReal) := by
  have h := executeStrategies_appendExported_soundness_weighted_ae ambient firstProtocol.tree
    (fun _ => secondProtocol.tree) firstProtocol.roles (fun _ => secondProtocol.roles)
    firstProtocol.oracles (fun _ => secondProtocol.oracles) inputSpec.toPFunctor inputImpl
    (fun _ => Fin 3) (fun _ _ => Nat) (fun _ => family) (fun _ => Nat) (fun _ _ => Nat)
    (fun _ => family) (fun _ => Unit) prover firstVerifier secondVerifier
    midpointTrue admissible finalTrue error (1 / 2) 0
    prefix_truth.le prefix_false_invalid.le suffix_bound_ae
  change _ ≤ (1 / 2 : ENNReal) + 0 +
    ∫⁻ b in {b | ¬ trueMid b ∧ allowed b}, error b ∂𝒟[prefixProgram] at h
  rw [average_error] at h
  calc
    _ ≤ (1 / 2 : ENNReal) + 0 + 1 / 4 := h
    _ = 3 / 4 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_add]

end
end Interaction.Oracle.CompositionSoundnessExample
