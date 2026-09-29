/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.CompositionSoundness
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Data.ZMod.Basic

/-!
# Two fresh guesses with arbitrary native prover continuations

Each phase receives a guess before sampling its own uniform challenge in `ZMod 17`.
The verifier remembers whether either guess matched. The quantitative composition theorem
bounds this event by `2/17` for every ordinary strategy on the full appended protocol.
The single-phase lemma permits dependent private outputs, so the prefix can return an arbitrary
native suffix strategy with all its private memory and effects.
-/

open Interaction Interaction.TwoParty OracleComp OracleSpec
open scoped ENNReal

namespace NativeCompositionTest

noncomputable section

abbrev F := ZMod 17

def guessTree : TypeTree := .node F fun _ => .node F fun _ => .done

def guessRoles : RoleDecoration guessTree :=
  ⟨.sender, fun _ => ⟨.receiver, fun _ => PUnit.unit⟩⟩

abbrev Focal (m : Type → Type) (tree : TypeTree) (roles : RoleDecoration tree)
    (Out : PFunctor.FreeM.Path tree → Type) :=
  StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal tree roles Out

abbrev Counterpart (m : Type → Type) (tree : TypeTree) (roles : RoleDecoration tree)
    (Out : PFunctor.FreeM.Path tree → Type) :=
  StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart tree roles Out

/-- The guess is fixed before sampling; arbitrary prover response effects execute afterwards. -/
def guessVerifier {m : Type → Type} [Monad m] (challenge : m F) (prior : Prop) :
    Counterpart m guessTree guessRoles (fun _ => Prop) :=
  fun guess => pure (do
    let sample ← challenge
    return ⟨sample, prior ∨ guess = sample⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Every native strategy is bounded by the fresh challenge's per-value collision bound.
Its dependent private output and post-challenge response effects are unrestricted. -/
theorem guess_soundness {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {Out : PFunctor.FreeM.Path guessTree → Type}
    (challenge : m F) (ε : ENNReal)
    (hsample : ∀ guess : F, Pr{let sample ← challenge}[guess = sample] ≤ ε)
    (prior : Prop) (hprior : ¬ prior) (prover : Focal m guessTree guessRoles Out) :
    Pr{let result ← run guessTree guessRoles prover (guessVerifier challenge prior)}[result.2.2] ≤
      ε := by
  simp only [guessTree, guessRoles]
  dsimp only [run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs]
  simp only [guessVerifier, bind_assoc, pure_bind]
  have hlocal : ∀ chosen : (guess : F) × ((sample : F) → m (Out ⟨guess, ⟨sample, PUnit.unit⟩⟩)),
      Pr{let truth ← (do
        let sample ← challenge
        let _ ← chosen.2 sample
        return prior ∨ chosen.1 = sample : m Prop)}[truth] ≤ ε := by
    rintro ⟨guess, respond⟩
    have hb := prEvent_bind_le_prEvent_of_forall_eq_zero challenge
      (fun sample => do
        let _ ← respond sample
        return prior ∨ guess = sample)
      (fun sample => guess = sample) (fun truth => truth) (by
        intro sample hne
        simpa only [bind_assoc, pure_bind, prEvent_norm, id_map'] using
          (prEvent_const_of_not (respond sample) (show ¬ (prior ∨ guess = sample) by
            simp [hprior, hne])))
    simpa only [prEvent_norm, id_map'] using hb.trans (hsample guess)
  have h := prEvent_bind_le_of_forall_le prover
    (fun chosen => do
      let sample ← challenge
      let _ ← chosen.2 sample
      return prior ∨ chosen.1 = sample) (fun truth => truth) (by
      intro chosen
      convert hlocal chosen using 1
      simp only [prEvent_norm, id_map']
      rfl)
  convert h using 1
  simp only [prEvent_norm, id_map']
  rfl

/-- A fresh uniform field challenge matches every fixed guess with mass `1/17`. -/
theorem uniform_guess (guess : F) :
    Pr{let sample ← ($ᵗ F)}[guess = sample] ≤ (1 : ENNReal) / 17 := by
  rw [SampleableType.prEvent_uniformSample]
  have hset : Finset.univ.filter (Eq guess) = ({guess} : Finset F) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact eq_comm
  rw [hset]
  simp

/-- Every full native prover, including arbitrary private memory and post-challenge effects,
has probability at most `2/17` of matching either fresh challenge. -/
theorem two_guesses
    (prover : Focal (OracleComp unifSpec)
      (guessTree.append (fun _ => guessTree))
      (guessRoles.append (fun _ => guessRoles)) (fun _ => Unit)) :
    Pr{let result ← (run (guessTree.append (fun _ => guessTree))
      (guessRoles.append (fun _ => guessRoles)) prover
      (StrategyOver.TwoParty.Counterpart.appendFlat (Output₂ := fun _ => Prop)
        (guessVerifier ($ᵗ F) False)
        (fun _ prior => guessVerifier ($ᵗ F) prior)))}[result.2.2] ≤ (2 : ENNReal) / 17 := by
  have h := run_appendFlat_soundness
    (s₁ := guessTree) (s₂ := fun _ => guessTree)
    (r₁ := guessRoles) (r₂ := fun _ => guessRoles)
    (OutputP := fun _ => Unit) (OutputC := fun _ => Prop) prover (guessVerifier ($ᵗ F) False)
    (fun _ prior => guessVerifier ($ᵗ F) prior)
    (fun _ prior => prior) (fun _ success => success)
    ((1 : ENNReal) / 17) ((1 : ENNReal) / 17)
    (fun strategy => guess_soundness ($ᵗ F) _ uniform_guess False (by simp) strategy)
    (fun _ prior hprior strategy => guess_soundness ($ᵗ F) _ uniform_guess prior hprior strategy)
  convert h using 1
  simpa only [div_eq_mul_inv, one_mul] using (two_mul (17 : ENNReal)⁻¹)

end
end NativeCompositionTest

/-! ## Reachable boundaries and branch-dependent errors

The oracle has three structural answers, but puts mass `1/2` each on answers `0` and `1`
and mass zero on answer `2`. The verifier publishes the answer, stores it in `Fin 4`, and
accepts the suffix exactly when that stored value is nonzero. Value `3` is an invalid stored
boundary that the prefix cannot produce. Suffix errors are `0` and `1` on the two positive-mass
public branches. The almost-everywhere bound ignores both the invalid boundary and the supported
zero-mass branch `2`, where the claimed error `0` would fail.
-/

namespace NativeCompositionTest.Weighted

open MeasureTheory

noncomputable section

@[reducible] def branchSpec : OracleSpec Unit := fun _ => Fin 3

def branchMeasure : Measure (Fin 3) :=
  (1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 1

instance : OracleSpec.IsMeasureSpec branchSpec where
  toMeasure _ := branchMeasure
  isProbabilityMeasure _ := by
    constructor
    change branchMeasure Set.univ = 1
    simp only [branchMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, one_div]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp)]

abbrev M := OracleComp branchSpec

def tree : TypeTree := .node (Fin 3) fun _ => .done

def roles : RoleDecoration tree := ⟨.receiver, fun _ => PUnit.unit⟩

def prover : Focal M (tree.append (fun _ => TypeTree.done))
    (roles.append (fun _ => PUnit.unit)) (fun _ => Unit) := fun _ => pure ()

def prefixVerifier : Counterpart M tree roles (fun _ => Fin 4) := do
  let sample ← (query (spec := branchSpec) () : M (Fin 3))
  pure ⟨sample, sample.castSucc⟩

def suffixVerifier (_ : TypeTree.Path tree) (out : Fin 4) :
    Counterpart M .done PUnit.unit (fun _ => Bool) := (out != 0)

abbrev Boundary := AppendBoundary (m := M) (s₂ := fun _ : TypeTree.Path tree => .done)
  (r₂ := fun _ => PUnit.unit) (OutputP := fun _ => Unit) (MidC := fun _ => Fin 4)

instance : MeasurableSpace Boundary := ⊤

instance : DiscreteMeasurableSpace Boundary := ⟨fun _ => trivial⟩

@[reducible] def boundary (sample : Fin 3) : Boundary := ⟨⟨sample, PUnit.unit⟩, (), sample.castSucc⟩

def error (b : Boundary) : ENNReal := if b.2.2 = 1 then 1 else 0

theorem prefix_execution : run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover)
    prefixVerifier = (query (spec := branchSpec) () : M (Fin 3)) >>=
      fun sample => pure (boundary sample) := by
  rfl

theorem prefix_measure : 𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover)
    prefixVerifier] =
      (1 / 2 : ENNReal) • Measure.dirac (boundary 0) +
        (1 / 2 : ENNReal) • Measure.dirac (boundary 1) := by
  rw [prefix_execution, evalDist_bind_of_discrete, OracleComp.evalDist_query (spec := branchSpec),
    MeasureTheory.trim_eq_self]
  change Measure.bind branchMeasure _ = _
  simp only [evalDist_pure]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [branchMeasure, Measure.map_add _ _ Measurable.of_discrete]
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete]

theorem suffix_at_boundary (sample : Fin 3) :
    Pr{let result ← (run TypeTree.done PUnit.unit (boundary sample).2.1
      (suffixVerifier (boundary sample).1 (boundary sample).2.2))}[result.2.2 = true] =
        if sample = 0 then 0 else 1 := by
  simp [boundary, suffixVerifier, run, InteractionOver.runTypeTree,
    participantProfile, collectParticipantOutputs]

/-- The actual prefix has the supported zero-mass boundary `2`. -/
theorem null_boundary_supported : boundary 2 ∈ support
    (run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover) prefixVerifier) := by
  rw [prefix_execution, mem_support_bind_iff]
  exact ⟨(2 : Fin 3), OracleComp.mem_support_query (spec := branchSpec) () (2 : Fin 3), by simp⟩

theorem null_boundary_mass : 𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover)
    prefixVerifier] {boundary 2} = 0 := by
  rw [prefix_measure]
  have h0 : boundary 0 ≠ boundary 2 := by
    intro h
    have hout := congrArg (fun b : Boundary => b.2.2) h
    exact (by decide : (0 : Fin 4) ≠ 2) hout
  have h1 : boundary 1 ≠ boundary 2 := by
    intro h
    have hout := congrArg (fun b : Boundary => b.2.2) h
    exact (by decide : (1 : Fin 4) ≠ 2) hout
  simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply', h0, h1]

/-- At that supported null boundary the proposed suffix error bound is false. -/
theorem null_boundary_suffix_bound_fails : ¬
    Pr{let result ← (run TypeTree.done PUnit.unit (boundary 2).2.1
      (suffixVerifier (boundary 2).1 (boundary 2).2.2))}[result.2.2 = true] ≤
        error (boundary 2) := by
  rw [suffix_at_boundary]
  change ¬ (1 : ENNReal) ≤ 0
  norm_num

/-- The invalid verifier output `3` is absent even from structural support. -/
theorem invalid_boundary_unreachable :
    (⟨⟨0, PUnit.unit⟩, (), (3 : Fin 4)⟩ : Boundary) ∉ support
      (run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover) prefixVerifier) := by
  rw [prefix_execution, mem_support_bind_iff]
  rintro ⟨sample, _, h⟩
  have heq := eq_of_mem_support_pure h
  have hout : (3 : Fin 4) = sample.castSucc := congrArg (fun b : Boundary => b.2.2) heq
  have hval := congrArg Fin.val hout
  exact (Nat.ne_of_gt sample.isLt) hval

/-- The weighted integral retains the different errors `0` and `1`; its value is `1/2`. -/
theorem average_error :
    (∫⁻ b in {_b : Boundary | ¬ False}, error b
      ∂𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover) prefixVerifier]) =
        (1 / 2 : ENNReal) := by
  rw [prefix_measure]
  simp [lintegral_add_measure, lintegral_smul_measure, error, boundary, Fin.ext_iff]

/-- The exported AE composition theorem gives `1/2`, even though neither all-boundary nor
support-restricted suffix hypotheses could justify the chosen error function. -/
theorem weighted_success :
    Pr{let result ← (run (tree.append (fun _ => TypeTree.done))
      (roles.append (fun _ => PUnit.unit)) prover
      (StrategyOver.TwoParty.Counterpart.appendFlat (Output₂ := fun _ => Bool)
        prefixVerifier suffixVerifier))}[
        result.2.2 = true] ≤ (1 / 2 : ENNReal) := by
  have hsuffix : ∀ᵐ b ∂𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover)
      prefixVerifier], ¬ False →
        Pr{let result ← run .done PUnit.unit b.2.1 (suffixVerifier b.1 b.2.2)}[
          result.2.2 = true] ≤ error b := by
    rw [prefix_measure, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      rw [ae_dirac_iff MeasurableSet.of_discrete] <;>
      intro _ <;> rw [suffix_at_boundary]
    · change (if (0 : Fin 3) = 0 then (0 : ENNReal) else 1) ≤ 0
      simp
    · change (if (1 : Fin 3) = 0 then (0 : ENNReal) else 1) ≤ 1
      simp
  have h := run_appendFlat_soundness_weighted_ae (OutputC := fun _ => Bool)
    prover prefixVerifier suffixVerifier
    (fun _ => False) (fun _ out => out = true) error hsuffix
  simpa only [prEvent_const_of_not _ not_false, zero_add, average_error] using h


/-- The final action makes a fresh query and can reject an otherwise accepted suffix. -/
def finishWithQuery (_ : TypeTree.Path (tree.append (fun _ => TypeTree.done)))
    (_ : Unit) (accepted : Bool) : M Bool := do
  let sample ← query (spec := branchSpec) ()
  return accepted && sample == 1

/-- The final query halves the success mass on an accepted branch. -/
theorem finishWithQuery_mass (path : TypeTree.Path (tree.append (fun _ => TypeTree.done)))
    (accepted : Bool) :
    Pr{let answer ← finishWithQuery path () accepted}[answer = true] =
      if accepted then (1 / 2 : ENNReal) else 0 := by
  unfold finishWithQuery
  rw [prEvent_bind_eq_lintegral_of_discrete, OracleComp.evalDist_query (spec := branchSpec),
    MeasureTheory.trim_eq_self]
  change (∫⁻ sample : Fin 3,
    Pr{let answer ← (pure (accepted && sample == 1) : M Bool)}[answer = true]
      ∂branchMeasure) = _
  cases accepted <;>
    simp [branchMeasure, lintegral_add_measure, lintegral_smul_measure]

/-- The composition bound includes the final query, giving `1/4` instead of `1/2`. -/
theorem weighted_success_after_final_query :
    Pr{let answer ← (do
      let result ← run (tree.append (fun _ => TypeTree.done))
        (roles.append (fun _ => PUnit.unit)) prover
        (StrategyOver.TwoParty.Counterpart.appendFlat (Output₂ := fun _ => Bool)
          prefixVerifier suffixVerifier)
      finishWithQuery result.1 result.2.1 result.2.2)}[answer = true] ≤
        (1 / 4 : ENNReal) := by
  have hsuffix : ∀ᵐ b ∂𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover)
      prefixVerifier], ¬ False →
        Pr{let answer ← (do
          let result ← run .done PUnit.unit b.2.1 (suffixVerifier b.1 b.2.2)
          finishWithQuery (PFunctor.FreeM.Path.append tree (fun _ => TypeTree.done) b.1 result.1)
            result.2.1 result.2.2)}[answer = true] ≤ error b / 2 := by
    rw [prefix_measure, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      rw [ae_dirac_iff MeasurableSet.of_discrete] <;> intro _ <;>
      simp only [boundary, suffixVerifier, run, InteractionOver.runTypeTree,
        participantProfile, collectParticipantOutputs, pure_bind]
    all_goals rw [finishWithQuery_mass]
    all_goals norm_num [error, boundary]
  have h := run_appendFlat_soundness_weighted_ae_finish (OutputC := fun _ => Bool)
    prover prefixVerifier suffixVerifier (fun _ => False)
    finishWithQuery (fun answer => answer = true) (fun b => error b / 2) hsuffix
  have havg : (∫⁻ b in {_b : Boundary | ¬ False}, error b / 2
      ∂𝒟[run tree roles (StrategyOver.TwoParty.Focal.splitPrefix prover) prefixVerifier]) =
        (1 / 4 : ENNReal) := by
    rw [prefix_measure]
    simp [lintegral_add_measure, lintegral_smul_measure, error, boundary, Fin.ext_iff,
      ← ENNReal.mul_inv]
    norm_num
  simpa only [prEvent_const_of_not _ not_false, zero_add, havg] using h

end
end NativeCompositionTest.Weighted
