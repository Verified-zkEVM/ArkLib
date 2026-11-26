/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.CryptoFoundations.HardnessAssumptions.PairingDLog

/-!
# Sampling an adversary before the PairingDLog experiment

Independent adversary seeds commute with the experiment's exponent sampling.
This bridge should move upstream to VCVio.
-/

@[expose] public section

open OracleComp OracleSpec

namespace PairingDLog

/-- Sampling an adversary inside the game has the same event probability as sampling it first.
This lemma should move upstream to VCVio. -/
theorem experiment_sample {F G₁ G₂ T : Type} [Semiring F] [SampleableType F]
    [DecidableEq F] [AddCommMonoid G₁] [Module F G₁]
    [AddCommMonoid G₂] [Module F G₂] {q₁ q₂ : ℕ}
    (g₁ : G₁) (g₂ : G₂) (sample : ProbComp T)
    (A : T → Adversary F G₁ G₂ q₁ q₂) (event : Bool → Prop) :
    Pr{let b ← experiment g₁ g₂ (fun ck vk => do
      let t ← sample
      A t ck vk)}[event b] =
    Pr{let b ← (do
      let t ← sample
      experiment g₁ g₂ (A t))}[event b] := by
  unfold experiment
  simp only [bind_assoc, map_bind]
  exact prEvent_bind_bind_swap_of_uniform _ _ _

end PairingDLog
