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

An exported derived oracle and a fresh final decision: the prefix challenge has the same
distribution, and the prefix exports its input `7` plus the challenge. The suffix reads only the
export, makes a fresh ambient query, and may reject. The bound charges a true midpoint separately
from the remaining branch's `1/2` error, giving `3/4`.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.Core.CompositionSoundnessTests

noncomputable section

attribute [local implicit_reducible] owner

/-- The field of the guess and the challenge. -/
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
-- `.message F; .challenge F` with a `Prop`-output counterpart; the frozen transparency
-- override is dropped.
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

/-- One oracle with three answers. -/
@[reducible] def branchSpec : OracleSpec Unit := fun _ => Fin 3

/-- Answers `0` and `1` each with probability `1/2`; answer `2` has mass zero. -/
def branchMeasure : Measure (Fin 3) :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 0 + (1 / 2 : ℝ≥0∞) • Measure.dirac 1

/-- Every query of `branchSpec` is answered by `branchMeasure`. -/
instance : OracleSpec.AnswerMeasure branchSpec where
  toMeasure _ := branchMeasure
  isProbabilityMeasure _ := by
    constructor
    change branchMeasure Set.univ = 1
    simp only [branchMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, one_div]
    rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp)]

/-- Programs querying `branchSpec`. -/
abbrev M := OracleComp branchSpec

/-- One challenge with three structural answers. -/
def tree : Protocol := .liftBind (.challenge (Fin 3)) fun _ => .pure ⟨⟩

/-- The empty suffix. -/
def rest : Path tree → Protocol := fun _ => .pure ⟨⟩

/-- The prover has pure slots and the unit output. -/
def prover : Focal plainSig M (tree.append rest) (fun _ => Unit) := pure fun _ => pure ()

/-- The prefix counterpart publishes the answer and stores it in `Fin 4`. -/
def prefixVerifier : PureEnd plainSig M .counterpart tree (fun _ => Fin 4) := do
  let sample ← (query (spec := branchSpec) () : M (Fin 3))
  pure ⟨sample, sample.castSucc⟩

/-- The suffix counterpart accepts exactly when the stored value is nonzero. -/
def suffixVerifier (_ : PathAlong plainSig tree) (out : Fin 4) :
    Counterpart plainSig M (.pure ⟨⟩) (fun _ => Bool) := pure (out != 0)

/-- The append boundary: the prefix transcript, the suffix strategy and the stored value. -/
abbrev Boundary := AppendBoundary plainSig M tree rest (fun _ => Unit) (fun _ => Fin 4)

/-- Every set of boundaries is measurable. -/
instance : MeasurableSpace Boundary := ⊤

/-- The measurable structure on boundaries is discrete. -/
instance : DiscreteMeasurableSpace Boundary := ⟨fun _ => trivial⟩

/-- The boundary after the answer `sample`, which stores `sample` in `Fin 4`. -/
@[reducible] def boundary (sample : Fin 3) : Boundary :=
  ⟨⟨sample, ⟨⟩⟩, (pure () : M Unit), sample.castSucc⟩

/-- The suffix error: one at the boundary storing `1`, zero elsewhere. -/
def error (b : Boundary) : ℝ≥0∞ := if b.2.2 = 1 then 1 else 0

-- Row 4 (`Weighted.prefix_execution`), restated over `PathAlong`.
/-- The prefix run queries once and returns the boundary of the answer. -/
theorem prefix_execution : TwoParty.Lens.run tree (Focal.splitPrefix prover)
    prefixVerifier.toStrategy = (query (spec := branchSpec) () : M (Fin 3)) >>=
      fun sample => pure (boundary sample) := by
  rfl

-- Row 5 (`prefix_measure`), restated.
/-- The prefix boundary has mass `1/2` at each of the answers `0` and `1`. -/
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
/-- The suffix accepts with probability zero after the answer `0` and one otherwise. -/
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
/-- The supported boundary `2` has mass zero. -/
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

namespace Interaction.Core.CompositionSoundnessTests.OracleExample

open MeasureTheory Interaction.Oracle
open Weighted (branchSpec branchMeasure)

noncomputable section

/-- The ambient oracle: a three-valued coin with mass `1/2` on each of `0` and `1`. -/
abbrev ambient := branchSpec

/-- One natural-number input slot, used for the exports as well. -/
@[instance_reducible] def nats : OracleFamily Unit (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- The input slot holds `7`. -/
def input : ∀ _ : Unit, Nat := fun _ => 7

/-- The verifier sends a `Fin 3` challenge. -/
@[instance_reducible] def first : OracleProtocol :=
  .liftBind (.challenge (Fin 3)) (fun _ => .pure ⟨⟩)

/-- The empty suffix. -/
@[instance_reducible] def second : OracleProtocol := .pure ⟨⟩

/-- The challenge, then nothing. -/
abbrev combined : OracleProtocol := first.append (fun _ => second)

/-- The full run interface: ambient coins and the challenge. -/
abbrev full := ambient + challengeSpec oracleSig combined

/-- `branchMeasure` is a probability measure. -/
theorem branchMeasure_isProbability : IsProbabilityMeasure branchMeasure :=
  inferInstanceAs
    (IsProbabilityMeasure (OracleSpec.AnswerMeasure.toMeasure (spec := branchSpec) ()))

/-- Ambient coins and the challenge both have the distribution `branchMeasure`. -/
def fullMeasure : (c : full.Domain) → @Measure (full.Range c) ⊤
  | .inl _ => branchMeasure
  | .inr ⟨.inl _, _⟩ => branchMeasure
  | .inr ⟨.inr ⟨_, n⟩, _⟩ => n.elim

/-- Ambient coins and challenges are answered by `fullMeasure`. -/
instance : OracleSpec.AnswerMeasure full :=
  @PFunctor.AnswerMeasure.mk full.toPFunctor (fun _ => ⊤) fullMeasure fun c => by
    rcases c with _ | ⟨_ | ⟨_, n⟩, _⟩
    · exact branchMeasure_isProbability
    · exact branchMeasure_isProbability
    · exact n.elim

/-- The sample published by the prefix, read from the verifier view. -/
def sampleOf {p : Path first} (v : View first p) : Fin 3 := v.1.1

/-- The prefix exports its input value plus the sample, querying only the input. -/
def exportMap (sample : Fin 3) (p : Path first) :
    OracleMap (sumFamily nats (pathFamily first p)) nats where
  f x _ := (show Nat from x (.inl ())) + sample.val
  impl _ := do
    let value : Nat ← liftM ((sumFamily nats (pathFamily first p)).spec.query ⟨.inl (), ()⟩)
    pure (value + sample.val)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- The prefix decision returns the sample; its output is the derived export. -/
def firstVerifier : OracleVerifier ambient first Unit (Fin 3) nats nats where
  decide _ _ v := pure (sampleOf v)
  outputMap _ p v := exportMap (sampleOf v) p

/-- The suffix decision reads the export, makes a fresh ambient query, and accepts iff the export
is `7` or the coin is `1`. It returns the export value and keeps the exported oracle. -/
def secondVerifier (_ : Path first) : OracleVerifier ambient second (Fin 3) Nat nats nats where
  decide _ p _ := OptionT.mk do
    let value : Nat ← liftM ((ambient + (sumFamily nats (pathFamily second p)).spec).query
      (.inr ⟨.inl (), ()⟩))
    let coin : Fin 3 ← liftM ((ambient + (sumFamily nats (pathFamily second p)).spec).query
      (.inl ()))
    pure (if value = 7 ∨ coin = 1 then some value else none)
  outputMap _ p _ := OracleMap.embedding (sumFamily nats (pathFamily second p)) .inl

/-- The composite output map is the suffix output map after `suffixRoute`. -/
def compatible : OracleVerifier.OutputCompatibility firstVerifier secondVerifier where
  outputMap stmt p v :=
    ((secondVerifier (Path.split first (fun _ => second) p).1).outputMap 0
      (Path.split first (fun _ => second) p).2
      (View.split first (fun _ => second) p v).2).comp
        (OracleVerifier.suffixRoute firstVerifier stmt p v)
  agrees _ _ _ _ _ _ := rfl

/-- The composed verifier. -/
def verifier := firstVerifier.append secondVerifier compatible

/-- The prover sends nothing and keeps no output. -/
def prover : Prover oracleSig ambient combined (fun _ => Unit) := pure fun _ => pure ()

/-- The append boundary of a run. -/
abbrev Boundary := RunBoundary oracleSig ambient first (fun _ => second) (fun _ => Unit)

/-- Every set of boundaries is measurable. -/
instance : MeasurableSpace Boundary := ⊤

/-- The measurable structure on boundaries is discrete. -/
instance : DiscreteMeasurableSpace Boundary := ⟨fun _ => trivial⟩

/-- The boundary after the challenge `sample`. -/
@[reducible] def boundary (sample : Fin 3) : Boundary :=
  ⟨⟨sample, ⟨⟩⟩, (pure () : OracleComp full Unit), ⟨⟩⟩

/-- The challenge query of the combined run. -/
def challengeQuery : full.Domain := .inr ⟨.inl ⟨⟩, rfl⟩

/-- The challenge draw of the combined run. -/
def challengeDraw : OracleComp full (Fin 3) := query (spec := full) challengeQuery

/-- The ambient coin of the combined run. -/
def coinDraw : OracleComp full (Fin 3) := query (spec := full) (.inl ())

/-- The challenge has distribution `branchMeasure`. -/
theorem challengeDraw_measure : 𝒟[challengeDraw] = branchMeasure := by
  let : MeasurableSpace (full.Range challengeQuery) := ⊤
  exact (OracleComp.evalDist_query (spec := full) challengeQuery).trans MeasureTheory.trim_eq_self

/-- The ambient coin has distribution `branchMeasure`. -/
theorem coinDraw_measure : 𝒟[coinDraw] = branchMeasure := by
  let : MeasurableSpace (full.Range (.inl ())) := ⊤
  exact (OracleComp.evalDist_query (spec := full) (.inl ())).trans MeasureTheory.trim_eq_self

-- Oracle example row 1 (`prefix_execution`), restated: the sample is the run's challenge and the
-- boundary is the prefix interaction result.
/-- The prefix interaction draws the challenge and stops at its boundary. -/
theorem prefix_execution : appendPrefixRun (s₂ := fun _ => second) prover =
    (challengeDraw >>= fun sample => pure (boundary sample)) := by
  rfl

-- Oracle example row 2 (`prefix_measure`), restated.
/-- The boundary has mass `1/2` on each of the samples `0` and `1`. -/
theorem prefix_measure : 𝒟[appendPrefixRun (s₂ := fun _ => second) prover] =
    (1 / 2 : ℝ≥0∞) • Measure.dirac (boundary 0) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (boundary 1) := by
  rw [prefix_execution, evalDist_bind_of_discrete, challengeDraw_measure]
  simp only [evalDist_pure]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]
  rw [branchMeasure, Measure.map_add _ _ Measurable.of_discrete]
  rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_smul _ Measurable.of_discrete.aemeasurable,
    Measure.map_dirac' Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete]

/-- The challenge at a boundary. -/
def sampleAt (b : Boundary) : Fin 3 := b.1.1

/-- The materialized export at a boundary: the prefix output map on the input and the prefix
payloads, at the prefix view. -/
def exported (b : Boundary) : Nat :=
  (firstVerifier.outputMap () (projectPathAlong oracleSig first b.1) (toView first b.1)).f
    (sumData input (payloads first b.1)) ()

/-- The midpoint is true when the export is `7`. -/
def trueMid (b : Boundary) : Prop := exported b = 7

/-- The midpoint is admissible when the export is not `7`. -/
def allowed (b : Boundary) : Prop := exported b ≠ 7

/-- The suffix error is `1/2` at sample `1` and zero elsewhere. -/
def error (b : Boundary) : ℝ≥0∞ := if sampleAt b = 1 then 1 / 2 else 0

-- Oracle example row 3 (`trueMid_boundary`), restated: truth on the materialized export.
/-- The midpoint is true exactly at sample `0`. -/
theorem trueMid_boundary (sample : Fin 3) : trueMid (boundary sample) ↔ sample = 0 := by
  change 7 + sample.val = 7 ↔ sample = 0
  omega

-- Oracle example row 4 (`allowed_boundary`), restated.
/-- The midpoint is admissible exactly away from sample `0`. -/
theorem allowed_boundary (sample : Fin 3) : allowed (boundary sample) ↔ sample ≠ 0 := by
  change 7 + sample.val ≠ 7 ↔ sample ≠ 0
  omega

-- Oracle example row 5 (`prefix_truth`), restated.
/-- The midpoint is true with probability `1/2`. -/
theorem prefix_truth :
    Pr{let b ← appendPrefixRun (s₂ := fun _ => second) prover}[trueMid b] = 1 / 2 := by
  classical
  rw [prEvent_eq_evalDist_of_discrete, prefix_measure]
  simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply', trueMid_boundary]

-- Oracle example row 6 (`prefix_false_invalid`), restated.
/-- False inadmissible midpoints have probability zero. -/
theorem prefix_false_invalid :
    Pr{let b ← appendPrefixRun (s₂ := fun _ => second) prover}[¬ trueMid b ∧ ¬ allowed b] =
      0 := by
  classical
  rw [prEvent_eq_evalDist_of_discrete, prefix_measure]
  simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply', trueMid_boundary,
    allowed_boundary]

-- Oracle example row 7 (`prefix_inadmissible`), restated.
/-- Inadmissible midpoints have probability `1/2`; they are the true ones, charged once. -/
theorem prefix_inadmissible :
    Pr{let b ← appendPrefixRun (s₂ := fun _ => second) prover}[¬ allowed b] = 1 / 2 := by
  rw [prEvent_congr _ (fun b => ¬ allowed b) trueMid (fun _ => not_not), prefix_truth]

-- Oracle example row 8 (`exported_behavior`), restated: the materialized export is
-- `7 + sample`, and the export's query implementation answers the same on the run's data.
/-- The export at a boundary is `7 + sample`, both as data and as simulated queries. -/
theorem exported_behavior (sample : Fin 3) :
    (firstVerifier.outputMap () (projectPathAlong oracleSig first (boundary sample).1)
        (toView first (boundary sample).1)).f
          (sumData input (payloads first (boundary sample).1)) = (fun _ => 7 + sample.val) ∧
    ∀ q, simulateQ ((sumFamily nats (pathFamily first ⟨⟨⟩, ⟨⟩⟩)).behaviorOfRealizations
        (sumData input (payloads first (boundary sample).1)))
      ((firstVerifier.outputMap () ⟨⟨⟩, ⟨⟩⟩ (toView first (boundary sample).1)).impl q) =
        (7 + sample.val : Nat) :=
  ⟨rfl, fun q => (OracleMap.law _ _ q).trans rfl⟩

/-- A claim: the returned statement and the output data. -/
abbrev Claim := Nat × (∀ _ : Unit, Nat)

/-- A final claim is true when its output oracle answers its statement. -/
def finalTrue (claim : Claim) : Prop := claim.2 () = claim.1

/-- The run returns a true final claim. -/
def suffixTrue (obs : Observation oracleSig combined (fun _ => Unit) Claim) : Prop :=
  obs.2.2.map finalTrue = some True

-- Oracle example row 9 (`suffix_execution`), restated: the rest of the run after the boundary,
-- with both decisions and the routed export query.
/-- After a boundary, the run makes one fresh ambient query and accepts iff the export is `7` or
the coin is `1`. -/
theorem suffix_execution (sample : Fin 3) : verifier.suffixRun () input (boundary sample) =
    (do
      let coin ← coinDraw
      pure ⟨⟨sample, ⟨⟩⟩, (), (if 7 + sample.val = 7 ∨ coin = 1 then some (7 + sample.val)
        else none).map fun t => (t, fun _ => 7 + sample.val)⟩) := by
  rfl

-- Oracle example row 10 (`suffix_mass`), restated.
/-- The rest of the run returns a true claim with probability `1` at sample `0`, else `1/2`. -/
theorem suffix_mass (sample : Fin 3) :
    Pr{let obs ← verifier.suffixRun () input (boundary sample)}[suffixTrue obs] =
      if sample = 0 then 1 else 1 / 2 := by
  classical
  rw [suffix_execution, prEvent_bind_eq_lintegral_of_discrete, coinDraw_measure]
  fin_cases sample <;>
    simp [branchMeasure, lintegral_add_measure, lintegral_smul_measure, suffixTrue, finalTrue,
      ENNReal.inv_two_add_inv_two]

-- Oracle example row 11 (`null_boundary_supported`), restated: support of the prefix
-- interaction program.
/-- The sample `2` has zero mass but lies in the structural support. -/
theorem null_boundary_supported :
    boundary 2 ∈ support (appendPrefixRun (s₂ := fun _ => second) prover) := by
  rw [prefix_execution, mem_support_bind_iff]
  exact ⟨(2 : Fin 3), OracleComp.mem_support_query (spec := full) challengeQuery (2 : Fin 3),
    by simp⟩

-- Oracle example row 12 (`null_boundary_suffix_bound_fails`), restated.
/-- At the null boundary the error bound fails, so a pointwise premise would be stronger. -/
theorem null_boundary_suffix_bound_fails :
    ¬ Pr{let obs ← verifier.suffixRun () input (boundary 2)}[suffixTrue obs] ≤
      error (boundary 2) := by
  rw [suffix_mass]
  simp [error, sampleAt]

-- Oracle example row 13 (`suffix_bound_ae`), restated.
/-- Almost every false admissible boundary meets its error bound. -/
theorem suffix_bound_ae : ∀ᵐ b ∂𝒟[appendPrefixRun (s₂ := fun _ => second) prover],
    ¬ trueMid b → allowed b →
      Pr{let obs ← verifier.suffixRun () input b}[suffixTrue obs] ≤ error b := by
  rw [prefix_measure, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;>
    rw [ae_dirac_iff MeasurableSet.of_discrete] <;> intro hfalse _
  · exact absurd ((trueMid_boundary 0).2 rfl) hfalse
  · rw [suffix_mass]
    simp [error, sampleAt]

-- Oracle example row 14 (`average_error`), restated.
/-- The error averaged over false admissible boundaries is `1/4`. -/
theorem average_error :
    (∫⁻ b in {b | ¬ trueMid b ∧ allowed b}, error b
      ∂𝒟[appendPrefixRun (s₂ := fun _ => second) prover]) = 1 / 4 := by
  classical
  rw [← lintegral_indicator MeasurableSet.of_discrete, prefix_measure, lintegral_add_measure,
    lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac, lintegral_dirac]
  simp [Set.indicator, trueMid_boundary, allowed_boundary, error, sampleAt, ← ENNReal.mul_inv]
  norm_num

-- Oracle example row 15 (`weighted_success`), restated: `OracleVerifier.append` with
-- `OutputCompatibility`, bounded by `OracleVerifier.run_append_soundness_weighted_ae`.
/-- The composed run returns a true final claim with probability at most `3/4`. -/
theorem weighted_success :
    Pr{let obs ← verifier.run () input prover}[suffixTrue obs] ≤ 3 / 4 := by
  have h := OracleVerifier.run_append_soundness_weighted_ae verifier () input prover
    trueMid allowed suffixTrue error (1 / 2) 0 prefix_truth.le prefix_false_invalid.le
    suffix_bound_ae
  rw [average_error] at h
  refine h.trans ?_
  rw [add_zero]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp ?_ |>.le
  norm_num [ENNReal.toReal_add]

end

end Interaction.Core.CompositionSoundnessTests.OracleExample

namespace Interaction.Core.CompositionSoundnessTests.Standalone

/-!
The standalone corollary with each named discharge of its reordering hypothesis, for arbitrary
verifiers, provers, implementations and challenge samplers. Each discharge equates the whole
observations, which implies the verdict equality the corollary asks for.
-/

variable {ι σ : Type} {ambient : OracleSpec ι} {s₁ : Protocol} {s₂ : Path s₁ → Protocol}
  {S T U : Type} {Out : PathAlong plainSig (s₁.append s₂) → Type}

/-- A prefix decision without ambient queries composes with a standalone-sound suffix at
`ε₁ + δ + ε₂`. -/
theorem append_soundness_of_pure_decide
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T U)
    (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hpure : ∀ p v, ∃ r, (V₁.decide stmt p v).run = pure r)
    (hprefix : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init impl (prefixDraw plainSig s₁ s₂ challenges)
      (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t, o.2.2 = some t ∧
        ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state, (V₂ p).soundness (pure state) impl
      (suffixDraw plainSig s₁ s₂ challenges p) middle output ε₂) :
    Pr{let obs ← (experiment init impl challenges ((V₁.append V₂).run stmt prover))}[
      ∃ u, obs.2.2 = some u ∧ output.language () u] ≤ ε₁ + δ + ε₂ :=
  Verifier.append_soundness_of_standalone V₁ V₂ init impl challenges middle output stmt prover
    ε₁ δ ε₂ (Verifier.boundaryDecidedRun_eq_of_pure V₁ V₂ stmt prover hpure ▸ .refl _) hprefix
    hadmissible hsuffix

/-- Under a stateless ambient implementation any prefix verifier composes with a standalone-sound
suffix at `ε₁ + δ + ε₂`. -/
theorem append_soundness_of_stateless
    (V₁ : Verifier ambient s₁ S T) (V₂ : (p : Path s₁) → Verifier ambient (s₂ p) T U)
    (init : ProbComp σ) (g : QueryImpl ambient ProbComp)
    (challenges : QueryImpl (challengeSpec plainSig (s₁.append s₂)) ProbComp)
    (middle : StatementProblem T) (output : StatementProblem U) (stmt : S)
    (prover : Prover plainSig ambient (s₁.append s₂) Out) (ε₁ δ ε₂ : ℝ≥0∞)
    (hprefix : Pr{let o ← (experiment init (g.liftTarget (StateT σ ProbComp))
      (prefixDraw plainSig s₁ s₂ challenges) (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t,
        o.2.2 = some t ∧ middle.language () t] ≤ ε₁)
    (hadmissible : Pr{let o ← (experiment init (g.liftTarget (StateT σ ProbComp))
      (prefixDraw plainSig s₁ s₂ challenges) (V₁.run stmt (Focal.splitPrefix prover)))}[∃ t,
        o.2.2 = some t ∧ ¬ middle.admissible () t] ≤ δ)
    (hsuffix : ∀ p state, (V₂ p).soundness (pure state) (g.liftTarget (StateT σ ProbComp))
      (suffixDraw plainSig s₁ s₂ challenges p) middle output ε₂) :
    Pr{let obs ← (experiment init (g.liftTarget (StateT σ ProbComp)) challenges
      ((V₁.append V₂).run stmt prover))}[∃ u, obs.2.2 = some u ∧ output.language () u] ≤
        ε₁ + δ + ε₂ :=
  Verifier.append_soundness_of_standalone V₁ V₂ init _ challenges middle output stmt prover
    ε₁ δ ε₂ ((Verifier.boundaryDecidedRun_evalDistEq_of_stateless V₁ V₂ stmt prover init g
      challenges).map _) hprefix hadmissible hsuffix

end Interaction.Core.CompositionSoundnessTests.Standalone
