/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldProbability
import ArkLibTest.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement

/-!
# Tensor-fold probability clients

These clients evaluate the probability bound for the full code over `ZMod 3`, whose level witness
has count `0`: a height-three fold, and the event that the fold does not decompose, both have
probability `0`. They also check the height-zero boundary for an arbitrary witness, derive the
height-three statement over a finite field from the general one, and apply the bound to an
interleaved witness with a nonzero count.
-/

open Code LinearCode TensorMCA CoreDefinitions
open scoped ProbabilityTheory

namespace BinaryTensorFoldProbabilityTest

open BinaryTensorFoldAgreementTest

-- With count `0` the height-three fold of the full code is never exceptional.
example (u : (Fin 3 → Bool) → Fin 2 → ZMod 3) :
    Pr{let r ← $ᵗ (Fin 3 → ZMod 3)}[r ∈ tensorFoldBad fullCode_level u] = 0 :=
  le_antisymm ((tensorFoldBad_probability_height_three fullCode_level u).trans (by simp))
    zero_le

-- The decomposition then holds with probability one: its failure has probability `0`.
example (u : (Fin 3 → Bool) → Fin 2 → ZMod 3) :
    Pr{let r ← $ᵗ (Fin 3 → ZMod 3)}[¬ HasFullTensorDecomposition fullCode 2 r u] = 0 :=
  le_antisymm ((prob_not_hasFullTensorDecomposition_le fullCode_level u).trans (by simp))
    zero_le

-- At height zero the bound is `0` for every witness, whatever its count.
example {C : ModuleCode (Fin 2) (ZMod 3) (ZMod 3)} {a e : ℕ} (h : FullSetLevelWitness C a e)
    (u : (Fin 0 → Bool) → Fin 2 → ZMod 3) :
    Pr{let r ← $ᵗ (Fin 0 → ZMod 3)}[r ∈ tensorFoldBad h u] = 0 :=
  le_antisymm ((tensorFoldBad_probability_le h u).trans (by simp)) zero_le

-- The height-three statement over a finite field, from the general one.
example {ι F A : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [SampleableType F]
    [AddCommMonoid A] [Module F A] [DecidableEq A]
    {C : ModuleCode ι F A} {agreement exceptionalCount : ℕ}
    (hlevel : FullSetLevelWitness C agreement exceptionalCount)
    (u : (Fin 3 → Bool) → ι → A) :
    Pr{let r ← $ᵗ (Fin 3 → F)}[r ∈ tensorFoldBad hlevel u] ≤
      ENNReal.ofReal ((3 * exceptionalCount : ℕ) / (Fintype.card F : ℝ)) := by
  simpa using tensorFoldBad_probability_le hlevel u

-- A family of four leaf arrays folded with shared challenges costs the same `h * e / |F|`.
example {C : ModuleCode (Fin 2) (ZMod 3) (ZMod 3)} {a e : ℕ} (h : FullSetLevelWitness C a e)
    (u : Fin 4 → (Fin 2 → Bool) → Fin 2 → ZMod 3) :
    Pr{let r ← $ᵗ (Fin 2 → ZMod 3)}[r ∈ tensorFoldFamilyBad h u] ≤
      ENNReal.ofReal ((2 * e : ℕ) / 3) := by
  simpa using tensorFoldFamilyBad_probability_le h u

-- The bound applies to the interleaved witness with the same count.
example {C : ModuleCode (Fin 2) (ZMod 3) (ZMod 3)} {a e : ℕ} (h : FullSetLevelWitness C a e)
    (u : (Fin 3 → Bool) → Fin 2 → Fin 5 → ZMod 3) :
    Pr{let r ← $ᵗ (Fin 3 → ZMod 3)}[r ∈ tensorFoldBad (h.moduleInterleavedCode (κ := Fin 5)) u] ≤
      ENNReal.ofReal ((3 * e : ℕ) / 3) := by
  simpa using tensorFoldBad_probability_le (h.moduleInterleavedCode (κ := Fin 5)) u

end BinaryTensorFoldProbabilityTest
