/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman, ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.OneMessage
import ArkLib.OracleReduction.Composition.Sequential.Append.RoundByRound
import ArkLib.OracleReduction.Composition.Sequential.Completeness

/-!
# Specialized composition contracts and their axiom boundaries

The one-message specialization retains arbitrary effectful component provers and accepts the
all-distributions suffix premise used by the original theorem. The n-ary and fixed-prefix RBR
results must not acquire dependencies on the legacy admitted composition contracts.
-/

open OracleComp OracleSpec ProtocolSpec

namespace AppendSpecializationRegression

/-- Specializing an all-distributions suffix premise recovers the one-message contract. -/
theorem oneMessage_all_distributions
    {ι σ S₁ W₁ S₂ W₂ S₃ W₃ M₁ M₂ : Type} {oSpec : OracleSpec ι}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ (oneMessage M₁))
    (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ (oneMessage M₂))
    (V₁ : R₁.verifier.PureForm) (V₂ : R₂.verifier.PureForm)
    {rel₁ : Set (S₁ × W₁)} {rel₂ : Set (S₂ × W₂)} {rel₃ : Set (S₃ × W₃)}
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : ∀ start : ProbComp σ, R₂.perfectCompleteness start impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ :=
  Reduction.append_perfectCompleteness_of_oneMessage R₁ R₂ V₁ V₂ h₁ (fun s => h₂ (pure s))

/-- A message-only suffix of arbitrary length factors after any prefix, retaining the
challenge-free execution case without a separate proof ladder or a prover purity assumption. -/
theorem messageOnly_suffix_factorization
    {ι S₁ W₁ S₂ W₂ S₃ W₃ : Type} {oSpec : OracleSpec ι}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    (P₁ : Prover oSpec S₁ W₁ S₂ W₂ pSpec₁)
    (P₂ : Prover oSpec S₂ W₂ S₃ W₃ pSpec₂)
    (hRight : ∀ i, pSpec₂.dir i = .P_to_V) (stmt : S₁) (wit : W₁) :
    (P₁.append P₂).run stmt wit = (do
      let r₁ ← liftAppendLeft pSpec₂ (P₁.run stmt wit)
      let r₂ ← liftAppendRight pSpec₁ (P₂.run r₁.2.1 r₁.2.2)
      pure (r₁.1 ++ₜ r₂.1, r₂.2)) :=
  Prover.append_run_of_seam (fun hn => Or.inr (hRight ⟨0, hn⟩)) stmt wit

end AppendSpecializationRegression

/--
info: 'AppendSpecializationRegression.oneMessage_all_distributions' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AppendSpecializationRegression.oneMessage_all_distributions

/--
info: 'Reduction.append_perfectCompleteness_of_oneMessage' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.append_perfectCompleteness_of_oneMessage

/--
info: 'Reduction.seqCompose_completeness_of_pure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_completeness_of_pure

/--
info: 'Reduction.seqCompose_perfectCompleteness_of_pure' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Reduction.seqCompose_perfectCompleteness_of_pure

/--
info: 'Verifier.append_rbrSoundnessWorstCase_of_pure_first' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrSoundnessWorstCase_of_pure_first

/--
info: 'Verifier.append_rbrSoundness_of_worstCase_of_pure_first' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.append_rbrSoundness_of_worstCase_of_pure_first

/--
info: 'OracleVerifier.append_rbrSoundness_of_worstCase_of_pure_first' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms OracleVerifier.append_rbrSoundness_of_worstCase_of_pure_first

/--
info: 'AppendSpecializationRegression.messageOnly_suffix_factorization' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AppendSpecializationRegression.messageOnly_suffix_factorization
