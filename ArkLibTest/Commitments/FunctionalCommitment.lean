/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Commitments.FunctionalCommitment.Merkle
import ArkLib.Commitments.Functional.KZG.FunctionalCommitment

/-!
# Functional commitment checks

These examples check that the KZG and Merkle functional commitments have the intended public
parameters, commitments and opening proofs. The examples also check that a plain fixed-claim
adversary converts to a one-message adversary and back, and that a fixed-data chooser gives
the fixed-data correctness game.
-/

open OracleComp OracleSpec Interaction FunctionalCommitment BinaryTree

section KZG

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
  (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (n : ℕ)

/-- The KZG public parameters are the committer key and the verifier key. -/
example : (KZG.functionalCommitment e g₁ g₂ n).PP = ((Fin (n + 1) → G₁) × (Fin 2 → G₂)) := rfl

/-- A KZG commitment is one group element. -/
example : (KZG.functionalCommitment e g₁ g₂ n).Cm = G₁ := rfl

/-- The KZG opening protocol at `q` is one message carrying a group element. -/
example (q : F) : (KZG.functionalCommitment e g₁ g₂ n).openSpec q = oneMessageSpec G₁ := rfl

/-- The KZG answer to a query is the evaluation of the polynomial. -/
example (c : Fin (n + 1) → F) (q : F) :
    (KZG.oracleInterface F n).answer c q = KZG.evaluate c q := rfl

end KZG

section Merkle

variable (α : Type) [DecidableEq α] (s : Skeleton)

/-- A Merkle commitment is a root hash. -/
example : (Merkle.functionalCommitment α s).Cm = α := rfl

/-- The Merkle opening protocol at a leaf index carries an authentication path. -/
example (idx : SkeletonLeafIndex s) :
    (Merkle.functionalCommitment α s).openSpec idx = oneMessageSpec (List.Vector α idx.depth) :=
  rfl

end Merkle

/-- The adaptive game recovers the fixed-data game for a one-leaf Merkle tree. -/
example (chal : (Merkle.functionalCommitment Bool .leaf).ChallengeSampler) :
    let FC := Merkle.functionalCommitment Bool .leaf
    let d : LeafData Bool .leaf := .leaf true
    let choose : FC.QueryChooser := fun _ _ => pure .ofLeaf
    FC.correctnessGame chal (FC.fixed d choose) = FC.fixedDataCorrectnessGame chal d choose := by
  simp only [correctnessGame_fixed]

/-- Converting a plain adversary to a one-message adversary and back gives it again. -/
example {ι : Type} {ambient : OracleSpec.{0, 0} ι} {Data : Type} {I : OracleInterface Data}
    {PP Cm : Type} {Proof : I.Query → Type} {L : ℕ} (B : PlainAdversary ambient PP Cm Proof L) :
    toPlainAdversary (ofPlainAdversary B) = B :=
  toPlainAdversary_ofPlainAdversary B
