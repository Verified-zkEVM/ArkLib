/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeComputable
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegreeSampling
import Mathlib.Algebra.Field.ZMod

/-! # Executable equal-degree errors -/

open ReedSolomon
open scoped ProbabilityTheory

private def binaryDomain : ZMod 2 ↪ ZMod 2 := (Equiv.refl _).toEmbedding

-- Constant multipliers can obstruct the required degrees even if all agreements may be lost.
/-- info: (3 : Rat)/8 -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 1 2 2

-- Degree-two candidates on two points retain their full polynomial identity.
/-- info: (1 : Rat)/2 -/
#guard_msgs in
#eval equalDegreeMcaErrorRat binaryDomain 2 2 1

example {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι] [SampleableType F]
    (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) :
    Pr{let c ← $ᵗ (F × F × F)}[∃ P, IsEqualDegreeExceptional domain f g d A s c.1 c.2.1 c.2.2 P] ≤
      ENNReal.ofReal (equalDegreeMcaErrorRat domain d A s : ℝ) := by
  rw [ofReal_equalDegreeMcaErrorRat]
  exact prob_isEqualDegreeExceptional_le domain f g d A s

/-- info: 'ReedSolomon.ofReal_equalDegreeMcaErrorRat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.ofReal_equalDegreeMcaErrorRat
