/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.ToMathlib.Fintype.CardEmbedding
import Mathlib.Data.ZMod.Defs

/-!
# Acceptance tests for embeddings of `Fin n` counted by their images
-/

open Finset

/-- Of the two-element subsets of `ZMod 3`, two contain `0`, so `2! * 2 = 4` embeddings
`Fin 2 ↪ ZMod 3` hit `0`. -/
example : #{f : Fin 2 ↪ ZMod 3 | (0 : ZMod 3) ∈ univ.map f} = 4 := by
  refine (Fintype.card_filter_embedding_map_univ 2 fun T ↦ (0 : ZMod 3) ∈ T).trans ?_
  decide

/-- The subset `{0, 1}` of `ZMod 3` is the image of `2! = 2` embeddings `Fin 2 ↪ ZMod 3`. -/
example : #{f : Fin 2 ↪ ZMod 3 | univ.map f = {0, 1}} = 2 :=
  Fintype.card_filter_embedding_map_univ_eq_factorial (by decide)
