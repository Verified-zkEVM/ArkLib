/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSuffix
import ArkLib.OracleReduction.Security.EmptyAmbient
import ArkLib.OracleReduction.Composition.Sequential.Append.AveragedEmpty

/-! # Axiom checks for arbitrary prover continuations -/

/-- info: 'Prover.runFromBoundary_suffix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.runFromBoundary_suffix

/-- info: 'Prover.runToRound_split_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.runToRound_split_boundary

/-- info: 'Prover.runFromBoundary_preserves_boundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.runFromBoundary_preserves_boundary

/-- info: 'ProtocolSpec.prEvent_rbrGame_emptyAmbient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ProtocolSpec.prEvent_rbrGame_emptyAmbient

/-- info: 'Verifier.averaged_suffix_mixture_bound_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.averaged_suffix_mixture_bound_empty

/-- info: 'Verifier.append_rbrKnowledgeSoundnessAveraged_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundnessAveraged_empty

/-- info: 'Verifier.append_rbrKnowledgeSoundnessAveraged_stateless' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundnessAveraged_stateless

/-- info: 'Verifier.append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless

/-- info: 'Prover.runToRound_prefixWithOutput' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Prover.runToRound_prefixWithOutput

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

-- The explicit averaged name preserves old typeclass evidence definitionally.
example {σ A B WA WB : Type} {m : ℕ} {p : ProtocolSpec m}
    [∀ i, SampleableType (p.Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl (Bool →ₒ Bool) (StateT σ ProbComp))
    (V : Verifier (Bool →ₒ Bool) A B p) (R : Set (A × WA)) (S : Set (B × WB))
    [h : Verifier.IsRBRKnowledgeSound init impl R S V] :
    Verifier.IsRBRKnowledgeSoundAveraged init impl R S V := h

-- Nonempty ambient specifications are supported; no `IsEmpty` instance is available here.
example {σ A B C WA WB WC : Type} [Inhabited WB]
    {m n : ℕ} {p : ProtocolSpec m} {q : ProtocolSpec n}
    [∀ i, SampleableType (p.Challenge i)] [∀ i, SampleableType (q.Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl (Bool →ₒ Bool) ProbComp)
    (V : Verifier (Bool →ₒ Bool) A B p) (U : Verifier (Bool →ₒ Bool) B C q)
    (R : Set (A × WA)) (S : Set (B × WB)) (T : Set (C × WC))
    (G : V.GuardedForm) (ε : p.ChallengeIdx → ℝ≥0) (η : q.ChallengeIdx → ℝ≥0)
    (hV : V.rbrKnowledgeSoundness init (impl.liftTarget (StateT σ ProbComp)) R S ε)
    (hU : U.rbrKnowledgeSoundnessAveraged init (impl.liftTarget (StateT σ ProbComp)) S T η) :
    (V.append U).rbrKnowledgeSoundnessAveraged init
      (impl.liftTarget (StateT σ ProbComp)) R T
      (Sum.elim ε η ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundnessAveraged_stateless init impl G hV hU

-- The stronger reuse interface accepts averaged certificates for both components.
example {σ A B C WA WB WC : Type} [Inhabited B] [Inhabited WB]
    {m n : ℕ} {p : ProtocolSpec m} {q : ProtocolSpec n}
    [∀ i, SampleableType (p.Challenge i)] [∀ i, SampleableType (q.Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl (Bool →ₒ Bool) ProbComp)
    (V : Verifier (Bool →ₒ Bool) A B p) (U : Verifier (Bool →ₒ Bool) B C q)
    (R : Set (A × WA)) (S : Set (B × WB)) (T : Set (C × WC))
    (G : V.GuardedForm) (ε : p.ChallengeIdx → ℝ≥0) (η : q.ChallengeIdx → ℝ≥0)
    (hV : V.rbrKnowledgeSoundnessAveraged init (impl.liftTarget (StateT σ ProbComp)) R S ε)
    (hU : U.rbrKnowledgeSoundnessAveraged init (impl.liftTarget (StateT σ ProbComp)) S T η) :
    (V.append U).rbrKnowledgeSoundnessAveraged init
      (impl.liftTarget (StateT σ ProbComp)) R T
      (Sum.elim ε η ∘ ChallengeIdx.sumEquiv.symm) :=
  Verifier.append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless init impl G hV hU
