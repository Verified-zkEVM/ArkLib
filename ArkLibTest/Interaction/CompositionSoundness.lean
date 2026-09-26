/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.CompositionSoundness
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
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
        simpa only [bind_assoc, pure_bind] using
          (prEvent_const_of_not (respond sample) (show ¬ (prior ∨ guess = sample) by
            simp [hprior, hne])))
    simpa only [bind_pure] using hb.trans (hsample guess)
  have h := prEvent_bind_le_of_forall_le prover
    (fun chosen => do
      let sample ← challenge
      let _ ← chosen.2 sample
      return prior ∨ chosen.1 = sample) (fun truth => truth) (by
      intro chosen
      convert hlocal chosen using 1
      simp only [bind_pure]
      rfl)
  convert h using 1
  simp only [bind_pure]
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
