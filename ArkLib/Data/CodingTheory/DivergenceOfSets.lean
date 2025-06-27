/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic

/-!
  Divergence of sets.
-/

namespace DivergenceOfSets

noncomputable section

open Classical Code

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V C : Set (ι → F)}

/-- The set of possible relative Hamming distances between two sets.
-/
def possibleDeltas (U V : Set (ι → F)) : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ u ∈ U, δᵣ(u,V) = d}

/-- The set of possible relative Hamming distances between two sets is well-defined.
-/
@[simp]
lemma possibleDeltas_subset_relHammingDistRange :
  possibleDeltas U C ⊆ relHammingDistRange ι :=
  fun _ _ ↦ by aesop (add simp possibleDeltas)

/-- The set of possible relative Hamming distances between two sets is finite.
-/
@[simp]
lemma finite_possibleDeltas : (possibleDeltas U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDeltas_subset_relHammingDistRange

open Classical in
def divergence (U V : Set (ι → F)) : ℚ :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

end

end DivergenceOfSets
