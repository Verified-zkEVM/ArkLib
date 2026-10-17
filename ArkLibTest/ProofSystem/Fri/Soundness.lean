/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Fri.Spec.Soundness
import ArkLib.ProofSystem.Fri.ErrorBounds

/-!
# Computable FRI soundness trust checks

These checks inspect proof bodies from a classic client. They protect both the exact
computable-verifier bridge and the final security theorems against admitted dependencies.
-/

/--
info: 'Fri.Spec.reduction_run' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.reduction_run

/--
info: 'Fri.Spec.soundness_proximity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.soundness_proximity

/--
info: 'Fri.Spec.soundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.soundness

/--
info: 'Fri.Spec.rbrSoundness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.rbrSoundness

/--
info: 'Fri.foldingAgreementFailure_prob_le_generalizedJohnson' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.foldingAgreementFailure_prob_le_generalizedJohnson

/--
info: 'Verifier.prob_terminal_event_le_of_badEvents' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.prob_terminal_event_le_of_badEvents

/--
info: 'Verifier.soundness_of_rejection_event' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Verifier.soundness_of_rejection_event

/--
info: 'Fri.FoldTrace.exists_codeword_of_query_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.FoldTrace.exists_codeword_of_query_probability

/--
info: 'Fri.FoldTrace.exists_unique_codeword_agree_of_query_probability' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.FoldTrace.exists_unique_codeword_agree_of_query_probability

/--
info: 'Fri.FoldTrace.interpolate_accepting_agrees' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.FoldTrace.interpolate_accepting_agrees

open OracleComp

section SeparateParameters

variable {F : Type} [Field F] [DecidableEq F]
variable {domain : Domain.SmoothCosetFftDomain 2 F} (tr : Fri.FoldTrace domain 2)

-- At rate 1/2, δ = 1/4 < θ = 3/4 is permitted, although the old threshold on θ fails.
example : ¬ (2 : ℝ) ≤ 2 ^ 2 * (1 - 3 / 4) := by norm_num

example {t : ℕ} (ht : 0 < t) (hsafe : tr.Safe (3 / 4))
    (hprob : ENNReal.ofReal (1 - (1 / 4 : ℝ)) ^ t ≤ Pr{
      let xs ← $ᵗ (Fin t → Fin (2 ^ 2))}[tr.Accepts xs]) :
    Code.relDistFromCode tr.initial
      (ReedSolomon.code (domain : Fin (2 ^ 2) ↪ F) 2 : Set (Fin (2 ^ 2) → F)) ≤
        ENNReal.ofReal (1 / 4) :=
  (tr.exists_codeword_of_query_probability (3 / 4) (1 / 4) (by decide) ht hsafe
    (by norm_num) (by norm_num) hprob).1

-- The non-strict rate boundary δ = 1 - ρ is included as well.
example {t : ℕ} (ht : 0 < t) (hsafe : tr.Safe (3 / 4))
    (hprob : ENNReal.ofReal (1 - (1 / 2 : ℝ)) ^ t ≤ Pr{
      let xs ← $ᵗ (Fin t → Fin (2 ^ 2))}[tr.Accepts xs]) :
    Code.relDistFromCode tr.initial
      (ReedSolomon.code (domain : Fin (2 ^ 2) ↪ F) 2 : Set (Fin (2 ^ 2) → F)) ≤
        ENNReal.ofReal (1 / 2) :=
  (tr.exists_codeword_of_query_probability (3 / 4) (1 / 2) (by decide) ht hsafe
    (by norm_num) (by norm_num) hprob).1

end SeparateParameters
