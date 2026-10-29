/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Multilinear monomial generators

Iterated tensor products of affine lines produce the squarefree monomial basis, with the
constant half preceding the variable half at each step.
-/

@[expose] public section

namespace CoreDefinitions

/-- Flatten the outer binary coordinate and the remaining monomial coordinates. -/
def multilinearIndex (t : ℕ) : Fin 2 × Fin (2 ^ t) ≃ Fin (2 ^ (t + 1)) :=
  finProdFinEquiv.trans (finCongr (by omega))

/-- Squarefree monomials, ordered recursively with the constant half first.
This is the explicit tensor generator of affine lines under canonical reindexing. -/
def multilinearGenerator (F : Type) [Field F] :
    (t : ℕ) → Generator (Fin t → F) (Fin (2 ^ t)) F
  | 0 => fun _ _ => 1
  | t + 1 => fun r j =>
    TensorGenerator_Explicit (AffineLineGenerator F) (multilinearGenerator F t)
      ((Fin.consEquiv (fun _ : Fin (t + 1) => F)).symm r)
      ((multilinearIndex t).symm j)

/-- The same monomial generator presented with the `m + 1` index used by batching. -/
def multilinearBatchGenerator (F : Type) [Field F] (t : ℕ) :
    Generator (Fin t → F) (Fin ((2 ^ t - 1) + 1)) F :=
  fun r j => multilinearGenerator F t r
    (Fin.cast (Nat.sub_add_cancel (Nat.one_le_two_pow)) j)

end CoreDefinitions
