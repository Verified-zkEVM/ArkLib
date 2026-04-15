/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
/-! # List Decodability -/


namespace ListDecodable

section

variable {ι : Type*} [Fintype ι]
         {F : Type*}

abbrev Code.{u, v} (ι : Type u) (S : Type v) : Type (max u v) := Set (ι → S)

open Classical in
/-- Hamming ball of radius `r` centred at a word `y`. -/
def hammingBall (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {x | hammingDist y x ≤ r}

open Classical in
/-- Ball of radius `r` centred at a word `y` with respect to the relative Hamming distance. -/
def relHammingBall (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {x | Code.relHammingDist y x ≤ r}

/-- The set of `r`-close codewords to a given word `y` with respect to the Hamming distance. -/
def closeCodewords (C : Code ι F) (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ hammingBall y r}

/-- The set of `r`-close codewords to a given word `y` with respect to the relative Hamming
distance.
Note that this is exactly `Λ (C, y, r)` from [ACFY24] and ` List (C, y, r)` from [ACFY24stir]. -/
def closeCodewordsRel (C : Code ι F) (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ relHammingBall y r}

/-- A code `C` is `(r,ℓ)`-list decodable.

- Remark:
   Note that the number of codewords `ℓ` in the Hamming ball of radius `r`
   centred around `y` is a real number. The reasoning for this is to accommodate the statement of
   the Johnson Bound Theorem. For simplicity and ease of proving statements, `ℓ` can be considered a
   a natural number by taking the floor of the real value. This will not lead to information loss
   since the cardinality of the set of close codewords is a natural number anyway. -/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : ι → F, (closeCodewordsRel C y r).ncard ≤ ℓ

/-- A code `C` is uniquely decodable up to a relative distance `r` if for any word `y : ι → F`,
there is at most one codeword in `C` within a relative Hamming distance of `r`.
This is a special case of list decodability where the list size `ℓ` is `1`. -/
def uniqueDecodable (C : Code ι F) (r : ℝ) : Prop :=
  listDecodable C r 1

end

end ListDecodable
