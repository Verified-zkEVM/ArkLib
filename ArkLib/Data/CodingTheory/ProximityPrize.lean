/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.Codingtheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Domain.CosetFftDomain.Defs
import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import Mathlib

/-!

## Main results

-/

open NNReal ENNReal unitInterval LinearCode CoreDefinitions
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]

def lineGenerator (t : F) : Generator F (Fin 2) F := fun _ i ↦ if i = 0 then 1 else t

noncomputable def ε_mca [Fintype F] [DecidableEq F] [Nonempty ι] (LC : LinearCode ι F) (δ : I) :=
    SupSet.sSup (Set.image (fun U ↦ Pr_{let x ←$ᵖ F}[(IsMCA (lineGenerator x) LC x U δ)]) Set.univ)

def δ_C (ε_star : I) : I := sorry

theorem grand_MCA_challenge {n : ℕ} [Fintype F] [DecidableEq F]
    (k : ℕ) (L : Domain.SmoothCosetFftDomain n F)
    (hrate : LinearCode.rate (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k)
            ∈ ({1 / 2, 1 / 4, 1 / 8, 1 / 16} : Set ℚ≥0))
    (ε_star : I) :
    (ε_mca (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k) (δ_C ε_star)).toReal ≤ ε_star.1 ∧
    ∀ δ : I, (ε_mca (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k) δ).toReal ≤ ε_star.1 → δ < δ_C ε_star := by
    sorry

def δ_C' (ε_star : I) : I := sorry

noncomputable def listDecodingBound (C : Set (ι → F)) (δ : I) : ℕ :=
  SupSet.sSup (Set.image (fun f ↦ (ListDecodable.closeCodewordsRel C f δ).ncard) Set.univ)

theorem grand_ListDecoding_challenge  {n : ℕ} [Fintype F] [DecidableEq F]
    (k : ℕ) (L : Domain.SmoothCosetFftDomain n F)
    (hrate : LinearCode.rate (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k)
            ∈ ({1 / 2, 1 / 4, 1 / 8, 1 / 16} : Set ℚ≥0))
    (ε_star : I) (m : ℕ) :
    listDecodingBound (Code.interleavedCodeSet (κ := Fin m) (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k).carrier) (δ_C' ε_star) ≤
     ε_star.1 * (Fintype.card F) ∧
     ∀ δ : I, listDecodingBound (Code.interleavedCodeSet (κ := Fin m) (ReedSolomon.code (L : Fin (2 ^ n) ↪ F) k).carrier) δ ≤
     ε_star.1 * (Fintype.card F) → δ ≤ δ_C' ε_star := by sorry
