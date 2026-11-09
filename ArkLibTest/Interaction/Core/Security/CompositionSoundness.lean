/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.CompositionSoundness
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Data.ZMod.Basic

/-!
# Composition soundness over arbitrary counterparts

Two fresh guesses: each phase receives a guess before sampling its own uniform challenge in
`ZMod 17`, and the counterpart remembers whether either guess matched. The seam theorem bounds this
event by `2/17` for every whole prover. The single-phase lemma permits dependent private outputs, so
the prefix can return an arbitrary suffix strategy with all its private memory and effects.

Reachable boundaries and branch-dependent errors: an oracle with three structural answers puts mass
`1/2` each on `0` and `1` and none on `2`. The prefix counterpart publishes the answer and stores it
in `Fin 4`; the suffix accepts exactly when that stored value is nonzero.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Core.CompositionSoundnessTests

noncomputable section

attribute [local implicit_reducible] owner

abbrev F := ZMod 17

/-- A guess message followed by a challenge. -/
abbrev guessTree : Protocol :=
  .liftBind (.message F) fun _ => .liftBind (.challenge F) fun _ => .pure ⟨⟩

/-- The guess is fixed before sampling; the counterpart's output records a match or `prior`. -/
def guessVerifierEnd {m : Type → Type} [Monad m] (challenge : m F) (prior : Prop) :
    PureEnd plainSig m .counterpart guessTree (fun _ => Prop) :=
  pure fun guess => (fun sample => ⟨sample, prior ∨ guess = sample⟩) <$> challenge

/-- The guess counterpart as an ordinary counterpart. -/
abbrev guessVerifier {m : Type → Type} [Monad m] (challenge : m F) (prior : Prop) :
    Counterpart plainSig m guessTree (fun _ => Prop) :=
  (guessVerifierEnd challenge prior).toStrategy

/-- The guess run: the prover's guess, its post-guess slot, the fresh challenge, the prover's
response, and the counterpart's output. -/
theorem run_guess {m : Type → Type} [Monad m] [LawfulMonad m]
    {Out : PathAlong plainSig guessTree → Type} (challenge : m F) (prior : Prop)
    (prover : Focal plainSig m guessTree Out) :
    TwoParty.Lens.run guessTree prover (guessVerifier challenge prior) = (do
      let v ← (show m ((guess : F) × m ((sample : F) → m (Out ⟨guess, sample, ⟨⟩⟩))) from prover)
      let respond ← v.2
      let sample ← challenge
      let out ← respond sample
      pure ⟨⟨v.1, sample, ⟨⟩⟩, out, prior ∨ v.1 = sample⟩) := by
  dsimp only [TwoParty.Lens.run, runWith, Interaction.InteractionOver.run, contexts, interaction,
    participantProfile, collectParticipantOutputs, step, Schedule.seq, owner_plain_message,
    owner_plain_challenge, guessVerifier, guessVerifierEnd, PureEnd.toStrategy,
    PureEnd.mapOutput, Choice.map]
  simp only [LawfulMonad.bind_assoc, LawfulApplicative.map_pure, LawfulMonad.pure_bind,
    bind_map_left]
  rfl

-- Row 1 (`guess_soundness`), restated over `TwoParty.Lens.run` on plainSig
-- `.message F; .challenge F` with a `Prop`-output counterpart; the frozen
-- `respectTransparency false` override is dropped.
/-- Every strategy is bounded by the fresh challenge's per-value collision bound. Its dependent
private output and post-challenge response effects are unrestricted. -/
theorem guess_soundness {m : Type → Type} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {Out : PathAlong plainSig guessTree → Type}
    (challenge : m F) (ε : ℝ≥0∞)
    (hsample : ∀ guess : F, Pr{let sample ← challenge}[guess = sample] ≤ ε)
    (prior : Prop) (hprior : ¬ prior) (prover : Focal plainSig m guessTree Out) :
    Pr{let result ← TwoParty.Lens.run guessTree prover (guessVerifier challenge prior)}[
      result.2.2] ≤ ε := by
  rw [run_guess]
  refine prEvent_bind_le_of_forall_le _ _ _ fun chosen => ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun respond => ?_
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero challenge _
    (fun sample => chosen.1 = sample) _ fun sample hne => ?_).trans (hsample chosen.1)
  rw [LawfulMonad.bind_pure_comp, prEvent_map]
  exact prEvent_const_of_not _ (by simp [hprior, hne])

-- Row 2 (`uniform_guess`), unchanged.
/-- A fresh uniform field challenge matches every fixed guess with mass `1/17`. -/
theorem uniform_guess (guess : F) :
    Pr{let sample ← ($ᵗ F)}[guess = sample] ≤ (1 : ℝ≥0∞) / 17 := by
  rw [SampleableType.prEvent_uniformSample]
  have hset : Finset.univ.filter (Eq guess) = ({guess} : Finset F) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact eq_comm
  rw [hset]
  simp

-- Row 3 (`two_guesses`), restated: `run_appendFlat_soundness` over `FreeM.append`, same `2/17`.
/-- Every whole prover, including arbitrary private memory and post-challenge effects, has
probability at most `2/17` of matching either fresh challenge. -/
theorem two_guesses
    (prover : Focal plainSig ProbComp (guessTree.append fun _ => guessTree) (fun _ => Unit)) :
    Pr{let result ← (TwoParty.Lens.run (guessTree.append fun _ => guessTree) prover
      (Counterpart.appendFlat (Out := fun _ => Prop) (guessVerifierEnd ($ᵗ F) False)
        (fun _ prior => guessVerifier ($ᵗ F) prior)))}[result.2.2] ≤ (2 : ℝ≥0∞) / 17 := by
  have h := run_appendFlat_soundness (OutC := fun _ => Prop)
    (guessVerifierEnd ($ᵗ F) False) (fun _ prior => guessVerifier ($ᵗ F) prior)
    (fun _ success => success) prover (fun _ prior => prior)
    ((1 : ℝ≥0∞) / 17) ((1 : ℝ≥0∞) / 17)
    (fun strategy => guess_soundness ($ᵗ F) _ uniform_guess False (by simp) strategy)
    (fun _ prior hprior strategy => guess_soundness ($ᵗ F) _ uniform_guess prior hprior strategy)
  convert h using 1
  simpa only [div_eq_mul_inv, one_mul] using (two_mul (17 : ℝ≥0∞)⁻¹)

end

end Interaction.Core.CompositionSoundnessTests

namespace Interaction.Core.CompositionSoundnessTests.Weighted

open MeasureTheory

noncomputable section

@[reducible] def branchSpec : OracleSpec Unit := fun _ => Fin 3

def branchMeasure : Measure (Fin 3) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

instance : OracleSpec.AnswerMeasure branchSpec where
  toMeasure _ := branchMeasure
  isProbabilityMeasure _ := by
    constructor
    change branchMeasure Set.univ = 1
    simp only [branchMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, one_div]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp)]

abbrev M := OracleComp branchSpec

/-- One challenge with three structural answers. -/
def tree : Protocol := .liftBind (.challenge (Fin 3)) fun _ => .pure ⟨⟩

/-- The empty suffix. -/
def rest : Path tree → Protocol := fun _ => .pure ⟨⟩

def prover : Focal plainSig M (tree.append rest) (fun _ => Unit) := pure fun _ => pure ()

/-- The prefix counterpart publishes the answer and stores it in `Fin 4`. -/
def prefixVerifier : PureEnd plainSig M .counterpart tree (fun _ => Fin 4) := do
  let sample ← (query (spec := branchSpec) () : M (Fin 3))
  pure ⟨sample, sample.castSucc⟩

/-- The suffix counterpart accepts exactly when the stored value is nonzero. -/
def suffixVerifier (_ : PathAlong plainSig tree) (out : Fin 4) :
    Counterpart plainSig M (.pure ⟨⟩) (fun _ => Bool) := pure (out != 0)

abbrev Boundary := AppendBoundary plainSig M tree rest (fun _ => Unit) (fun _ => Fin 4)

instance : MeasurableSpace Boundary := ⊤

instance : DiscreteMeasurableSpace Boundary := ⟨fun _ => trivial⟩

@[reducible] def boundary (sample : Fin 3) : Boundary :=
  ⟨⟨sample, ⟨⟩⟩, (pure () : M Unit), sample.castSucc⟩

def error (b : Boundary) : ℝ≥0∞ := if b.2.2 = 1 then 1 else 0

-- Row 4 (`Weighted.prefix_execution`), restated over `PathAlong`.
theorem prefix_execution : TwoParty.Lens.run tree (Focal.splitPrefix prover)
    prefixVerifier.toStrategy = (query (spec := branchSpec) () : M (Fin 3)) >>=
      fun sample => pure (boundary sample) := by
  rfl

-- Row 5 (`prefix_measure`), restated.
theorem prefix_measure : 𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover)
    prefixVerifier.toStrategy] =
      (1 / 2 : ℝ≥0∞) • Measure.dirac (boundary 0) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (boundary 1) := by
  rw [prefix_execution, evalDist_bind_of_discrete, OracleComp.evalDist_query (spec := branchSpec),
    MeasureTheory.trim_eq_self]
  change Measure.bind branchMeasure _ = _
  simp only [evalDist_pure]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [branchMeasure, Measure.map_add _ _ Measurable.of_discrete]
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete]

/-- An empty suffix with pure slots returns both outputs without effects. -/
theorem leaf_run (accepted : Bool) :
    TwoParty.Lens.run (l := plainSig) (m := M) (OutP := fun _ => Unit) (OutC := fun _ => Bool)
      (.pure ⟨⟩) (pure ()) (pure accepted) = pure ⟨⟨⟩, (), accepted⟩ := by
  rfl

/-- The suffix at a boundary returns the stored test without further effects. -/
theorem suffix_run (sample : Fin 3) :
    TwoParty.Lens.run (l := plainSig) (m := M) (OutP := fun _ => Unit) (OutC := fun _ => Bool)
      (.pure ⟨⟩) (boundary sample).2.1
      (suffixVerifier (boundary sample).1 (boundary sample).2.2) =
        pure ⟨⟨⟩, (), sample.castSucc != 0⟩ := by
  rfl

-- Row 6 (`suffix_at_boundary`), restated.
theorem suffix_at_boundary (sample : Fin 3) :
    Pr{let result ← (TwoParty.Lens.run (.pure ⟨⟩) (boundary sample).2.1
      (suffixVerifier (boundary sample).1 (boundary sample).2.2))}[result.2.2 = true] =
        if sample = 0 then 0 else 1 := by
  erw [suffix_run]
  fin_cases sample <;> simp

-- Row 7 (`null_boundary_supported`), restated.
/-- The actual prefix has the supported zero-mass boundary `2`. -/
theorem null_boundary_supported : boundary 2 ∈ support
    (TwoParty.Lens.run tree (Focal.splitPrefix prover) prefixVerifier.toStrategy) := by
  rw [prefix_execution, mem_support_bind_iff]
  exact ⟨(2 : Fin 3), OracleComp.mem_support_query (spec := branchSpec) () (2 : Fin 3), by simp⟩

-- Row 8 (`null_boundary_mass`), restated.
theorem null_boundary_mass : 𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover)
    prefixVerifier.toStrategy] {boundary 2} = 0 := by
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

-- Row 9 (`null_boundary_suffix_bound_fails`), restated.
/-- At that supported null boundary the proposed suffix error bound is false. -/
theorem null_boundary_suffix_bound_fails : ¬
    Pr{let result ← (TwoParty.Lens.run (.pure ⟨⟩) (boundary 2).2.1
      (suffixVerifier (boundary 2).1 (boundary 2).2.2))}[result.2.2 = true] ≤
        error (boundary 2) := by
  rw [suffix_at_boundary]
  change ¬ (1 : ℝ≥0∞) ≤ 0
  norm_num

-- Row 10 (`invalid_boundary_unreachable`), restated: the prefix stays a generic counterpart
-- with `Fin 4` midpoint output.
/-- The invalid counterpart output `3` is absent even from structural support. -/
theorem invalid_boundary_unreachable :
    (⟨⟨(0 : Fin 3), ⟨⟩⟩, (pure () : M Unit), (3 : Fin 4)⟩ : Boundary) ∉ support
      (TwoParty.Lens.run tree (Focal.splitPrefix prover) prefixVerifier.toStrategy) := by
  rw [prefix_execution, mem_support_bind_iff]
  rintro ⟨sample, _, h⟩
  have heq := eq_of_mem_support_pure h
  have hout : (3 : Fin 4) = sample.castSucc := congrArg (fun b : Boundary => b.2.2) heq
  have hval := congrArg Fin.val hout
  exact (Nat.ne_of_gt sample.isLt) hval

-- Row 11 (`average_error`), restated.
/-- The weighted integral retains the different errors `0` and `1`; its value is `1/2`. -/
theorem average_error :
    (∫⁻ b in {_b : Boundary | ¬ False}, error b
      ∂𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover) prefixVerifier.toStrategy]) =
        (1 / 2 : ℝ≥0∞) := by
  rw [prefix_measure]
  simp [lintegral_add_measure, lintegral_smul_measure, error, boundary, Fin.ext_iff]

-- Row 12 (`weighted_success`), restated.
/-- The almost-everywhere seam theorem gives `1/2`, although neither all-boundary nor
support-restricted suffix hypotheses could justify the chosen error function. -/
theorem weighted_success :
    Pr{let result ← (TwoParty.Lens.run (tree.append rest) prover
      (Counterpart.appendFlat (Out := fun _ => Bool) prefixVerifier
        suffixVerifier))}[result.2.2 = true] ≤ (1 / 2 : ℝ≥0∞) := by
  have hsuffix : ∀ᵐ b ∂𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover)
      prefixVerifier.toStrategy], ¬ False →
        Pr{let result ← (TwoParty.Lens.run (.pure ⟨⟩) b.2.1
          (suffixVerifier b.1 b.2.2))}[result.2.2 = true] ≤ error b := by
    rw [prefix_measure, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      rw [ae_dirac_iff MeasurableSet.of_discrete] <;>
      intro _ <;> rw [suffix_at_boundary]
    · change (if (0 : Fin 3) = 0 then (0 : ℝ≥0∞) else 1) ≤ 0
      simp
    · change (if (1 : Fin 3) = 0 then (0 : ℝ≥0∞) else 1) ≤ 1
      simp
  have h := run_appendFlat_soundness_weighted_ae (OutC := fun _ => Bool)
    prover prefixVerifier suffixVerifier
    (fun _ => False) (fun _ out => out = true) error hsuffix
  simpa only [prEvent_const_of_not _ not_false, zero_add, average_error] using h

/-- The final action makes a fresh query and can reject an otherwise accepted suffix. -/
def finishWithQuery (_ : PathAlong plainSig (tree.append rest))
    (_ : Unit) (accepted : Bool) : M Bool := do
  let sample ← query (spec := branchSpec) ()
  return accepted && sample == 1

-- Row 13 (`finishWithQuery_mass`), restated over `PathAlong`.
/-- The final query halves the success mass on an accepted branch. -/
theorem finishWithQuery_mass (path : PathAlong plainSig (tree.append rest))
    (accepted : Bool) :
    Pr{let answer ← finishWithQuery path () accepted}[answer = true] =
      if accepted then (1 / 2 : ℝ≥0∞) else 0 := by
  unfold finishWithQuery
  rw [prEvent_bind_eq_lintegral_of_discrete, OracleComp.evalDist_query (spec := branchSpec),
    MeasureTheory.trim_eq_self]
  change (∫⁻ sample : Fin 3,
    Pr{let answer ← (pure (accepted && sample == 1) : M Bool)}[answer = true]
      ∂branchMeasure) = _
  cases accepted <;>
    simp [branchMeasure, lintegral_add_measure, lintegral_smul_measure]

-- Row 14 (`weighted_success_after_final_query`), restated.
/-- The composition bound includes the final query, giving `1/4` instead of `1/2`. -/
theorem weighted_success_after_final_query :
    Pr{let answer ← (do
      let result ← TwoParty.Lens.run (tree.append rest) prover
        (Counterpart.appendFlat (Out := fun _ => Bool) prefixVerifier suffixVerifier)
      finishWithQuery result.1 result.2.1 result.2.2)}[answer = true] ≤
        (1 / 4 : ℝ≥0∞) := by
  have hsuffix : ∀ᵐ b ∂𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover)
      prefixVerifier.toStrategy], ¬ False →
        Pr{let answer ← (do
          let result ← TwoParty.Lens.run (.pure ⟨⟩) b.2.1 (suffixVerifier b.1 b.2.2)
          finishWithQuery (PathAlong.append plainSig tree rest b.1 result.1)
            result.2.1 result.2.2)}[answer = true] ≤ error b / 2 := by
    rw [prefix_measure, ae_add_measure_iff]
    constructor <;> apply Measure.ae_smul_measure <;>
      rw [ae_dirac_iff MeasurableSet.of_discrete] <;> intro _ <;>
      simp only [boundary, suffixVerifier] <;> erw [leaf_run] <;>
      rw [LawfulMonad.pure_bind, finishWithQuery_mass]
    all_goals norm_num [error, boundary]
  have h := run_appendFlat_soundness_weighted_ae_finish (OutC := fun _ => Bool)
    prover prefixVerifier suffixVerifier (fun _ => False)
    finishWithQuery (fun answer => answer = true) (fun b => error b / 2) hsuffix
  have havg : (∫⁻ b in {_b : Boundary | ¬ False}, error b / 2
      ∂𝒟[TwoParty.Lens.run tree (Focal.splitPrefix prover) prefixVerifier.toStrategy]) =
        (1 / 4 : ℝ≥0∞) := by
    rw [prefix_measure]
    simp [lintegral_add_measure, lintegral_smul_measure, error, boundary, Fin.ext_iff,
      ← ENNReal.mul_inv]
    norm_num
  simpa only [prEvent_const_of_not _ not_false, zero_add, havg] using h

end

end Interaction.Core.CompositionSoundnessTests.Weighted
