/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Computable
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Probability
import Mathlib.Algebra.Field.ZMod

/-! # Executable errors and their probability interfaces -/

open ReedSolomon CoreDefinitions
open scoped ProbabilityTheory

private def binaryDomain : ZMod 2 ↪ ZMod 2 := (Equiv.refl _).toEmbedding

/-- info: 1 -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 1 2 0

/-- info: 0 -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 1 2 1

/-- info: (1 : Rat)/2 -/
#guard_msgs in
#eval scalarMcaErrorRat binaryDomain 0 2 0

-- An unattainable agreement threshold excludes every candidate.
/-- info: 0 -/
#guard_msgs in
#eval affineMcaErrorRat binaryDomain 0 3 0

-- The exact rational value bounds the native event for every received word pair.
example {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι] [SampleableType F]
    (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F)}[∃ P, IsAffineExceptional domain f g d A s c.1 c.2 P] ≤
      ENNReal.ofReal (affineMcaErrorRat domain d A s : ℝ) := by
  rw [ofReal_affineMcaErrorRat]
  exact prob_isAffineExceptional_le domain f g d A s

-- The scalar zero-loss value computes the matching affine-line MCA error.
example {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι] [SampleableType F]
    (domain : ι ↪ F) (d A : ℕ) (δ : ℝ) (hδ : ⌈(Fintype.card ι : ℝ) * (1 - δ)⌉₊ = A) :
    ENNReal.ofReal (scalarMcaErrorRat domain d A 0 : ℝ) =
      mcaError (AffineLineGenerator F) (code domain (d + 1)) δ := by
  rw [ofReal_scalarMcaErrorRat]
  exact scalarMcaError_zero_eq_mcaError domain d A δ hδ

/-- info: 'ReedSolomon.ofReal_affineMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_affineMcaErrorRat

/-- info: 'ReedSolomon.ofReal_scalarMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_scalarMcaErrorRat
