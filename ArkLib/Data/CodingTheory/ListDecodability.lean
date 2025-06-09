/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic

open Classical

namespace ListDecodable

noncomputable section

variable {ι : ℕ}
         {F : Type*}

abbrev Code.{u} (ι : ℕ) (S : Type u) : Type u := Set (Fin ι → S)

/--
Hamming ball of radius `r` centred at a word `y`.
-/
def hammingBall (C : Code ι F) (y : Fin ι → F) (r : ℕ) : Code ι F :=
  { c | c ∈ C ∧ hammingDist y c ≤ r }

/--
Ball of radius `r` centred at a word `y` with respect to the relative Hamming distance.
-/
def relHammingBall (C : Code ι F) (y : Fin ι → F) (r : ℝ)  : Code ι F :=
  { c | c ∈ C ∧ dist y c ≤ r }

/--
The number of close codewords to a given word `y` with respect to the Hamming distance metric.
-/
def listOfCloseCodewords (C : Code ι F) (y : Fin ι → F) (r : ℕ) : ℕ :=
  Nat.card (hammingBall C y r)

/--
The number of close codewords to a given word `y` with respect to the relative Hamming
distance metric.
-/
def listOfCloseCodewordsRel (C : Code ι F) (y : Fin ι → F) (r : ℝ) : ℕ :=
  Nat.card (relHammingBall C y r)

/--
The code `C` is `(r,ℓ)`-list decodable.

- Remark:
   Note that the number of codewords `ℓ` in the Hamming ball of radius `r`
   centred around `y` is a real number. The reasoning for this is to accommodate the statement of
   the Johnson Bound Theorem. For simplicity and ease of proving statements, `ℓ` can be considered a
   a natural number by taking the floor of the real value. This will not lead to information loss
   since the cardinality of the set of close codewords is a natural number anyway.
-/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : Fin ι → F, listOfCloseCodewordsRel C y r ≤ ℓ

section

variable {C : Code ι F} {y : Fin ι → F} {n : ℕ} {r : ℝ} {ℓ : ℝ}

lemma listOfCloseCodewords_eq_zero :
  listOfCloseCodewords C y n = 0 ↔ IsEmpty (hammingBall C y n) ∨ Infinite (hammingBall C y n) := by
  simp [listOfCloseCodewords, Nat.card_eq_zero]

lemma listOfCloseCodewordsRel_eq_zero :
  listOfCloseCodewordsRel C y r = 0 ↔
  IsEmpty (relHammingBall C y r) ∨ Infinite (relHammingBall C y r) := by
  simp [listOfCloseCodewordsRel, Nat.card_eq_zero]

end

end

end ListDecodable
