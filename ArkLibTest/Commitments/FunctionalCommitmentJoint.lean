/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.FunctionalCommitment.JointBinding

/-!
# Joint function binding checks

The examples check the empty chain and give an adversary that uses the first opening's challenge
as the answer in its second claim.
-/

open OracleComp OracleSpec Interaction FunctionalCommitment PFunctor FreeM

namespace FunctionalCommitmentJointTest

section EmptyChain

variable {ι : Type} {ambient : OracleSpec.{0, 0} ι} {Data : Type} {I : OracleInterface Data}
variable (FC : FunctionalCommitment ambient Data I) (chal : FC.ChallengeSampler)

private theorem game_zero (A : FC.JointAdversary 0) :
    FC.functionBindingGame chal 0 A = (do
      let pp ← FC.setup
      let (_, terminal) ← A pp
      let _ ← terminal
      return noConsistentData (I := I) (L := 0) Fin.elim0) := by
  simp only [functionBindingGame, JointBinding.collect, JointBinding.checkOpenings,
    chain, sampler, samplerEnd, TwoParty.Lens.PureEnd.toStrategy,
    bind_map_left, LawfulMonad.pure_bind, Fin.mOfFn_zero]
  refine bind_congr fun pp => bind_congr fun ⟨cm, terminal⟩ => ?_
  erw [TwoParty.Lens.run_done]
  have emptyClaims : (fun i : Fin 0 => (i.elim0 : JointBinding.Opening FC).1) =
      (Fin.elim0 : Fin 0 → (q : I.Query) × I.spec q) :=
    funext fun i => i.elim0
  simp [TwoParty.Lens.PureEnd.mapOutput, JointBinding.openings, emptyClaims]

example (A : FC.PP → OracleComp (unifSpec + ambient) FC.Cm) :
    FC.functionBindingGame chal 0 (fun pp => (fun cm => (cm, pure ⟨⟩)) <$> A pp) = (do
      let pp ← FC.setup
      let _ ← A pp
      return noConsistentData (I := I) (L := 0) Fin.elim0) := by
  rw [game_zero]
  simp only [bind_map_left, LawfulMonad.pure_bind]

/-- Even with an effectful leaf, the empty chain returns the same Boolean in every run. -/
example {σ : Type} (init : ProbComp σ) (impl : QueryImpl ambient (StateT σ ProbComp))
    (A : FC.JointAdversary 0) :
    evalDist (FC.functionBindingExperiment init impl chal 0 A) =
      evalDist (pure (noConsistentData (I := I) (L := 0) Fin.elim0) : ProbComp Bool) := by
  let actions : OracleComp (unifSpec + ambient) PUnit := do
    let pp ← FC.setup
    let (_, terminal) ← A pp
    terminal
  have game : FC.functionBindingGame chal 0 A =
      (actions >>= fun _ => pure (noConsistentData (I := I) (L := 0) Fin.elim0)) := by
    rw [game_zero]
    simp only [actions, bind_assoc]
    refine bind_congr fun pp => ?_
    erw [bind_assoc]
  simp only [functionBindingExperiment, game, runGame, run'_simulateQ_bind, simulateQ_pure,
    StateT.run'_pure']
  rw [← bind_assoc, OracleComp.evalDist_bind_const]

end EmptyChain

@[instance_reducible] private def boolInterface : OracleInterface Bool where
  Query := Unit
  spec _ := Bool
  answer d _ := d

private def challengeOpening : Protocol :=
  .liftBind (.challenge Bool) (fun _ => .pure ())

private def scheme : FunctionalCommitment (OracleSpec.emptySpec.{0, 0}) Bool boolInterface where
  PP := Unit
  Cm := Unit
  Aux := Unit
  setup := pure ()
  commit _ _ := pure ((), ())
  openSpec _ := challengeOpening
  prover _ _ _ _ _ _ := pure fun _ => pure ⟨⟩
  verifier _ := ⟨fun _ _ _ => pure ⟨⟩⟩

/-- The adversary claims `false` first and uses the first challenge as the second claimed answer. -/
private def adaptiveAdversary : scheme.JointAdversary 2 := fun _ =>
  pure ⟨(), pure ⟨⟨(), false⟩, pure fun firstChallenge =>
    pure ⟨⟨(), firstChallenge⟩, pure fun _ => pure ⟨⟩⟩⟩⟩

noncomputable example (chal : scheme.ChallengeSampler) :
    OracleComp (unifSpec + OracleSpec.emptySpec.{0, 0}) Bool :=
  scheme.functionBindingGame chal 2 adaptiveAdversary

end FunctionalCommitmentJointTest
