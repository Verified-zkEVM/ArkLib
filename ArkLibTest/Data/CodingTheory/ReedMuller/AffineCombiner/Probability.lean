/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Probability
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for the Reed–Muller sampling interface -/

open ReedMuller
open scoped ProbabilityTheory

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The error bounds the native probability over a uniform `α ∈ F₅³` for each word pair.
example (f g : (Fin 2 → ZMod 5) → ZMod 5) :
    Pr{let α ← $ᵗ (Fin 3 → ZMod 5)}[∃ P, IsAffineExceptional f g 1 10 5 α P] ≤
      affineMcaError (ZMod 5) (ZMod 5) 2 1 10 5 :=
  prob_isAffineExceptional_le f g 1 10 5

-- The error is the supremum of these native probabilities.
example : affineMcaError (ZMod 5) (ZMod 5) 2 1 10 5 =
    ⨆ w : ((Fin 2 → ZMod 5) → ZMod 5) × ((Fin 2 → ZMod 5) → ZMod 5),
      Pr{let α ← $ᵗ (Fin 3 → ZMod 5)}[∃ P, IsAffineExceptional w.1 w.2 1 10 5 α P] :=
  affineMcaError_eq_iSup_prob 2 1 10 5

/-- info: 'ReedMuller.affineMcaError_eq_iSup_prob' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.affineMcaError_eq_iSup_prob

/-- info: 'ReedMuller.prob_isAffineExceptional_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.prob_isAffineExceptional_eq

/-- info: 'ReedMuller.prob_isAffineExceptional_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.prob_isAffineExceptional_le
