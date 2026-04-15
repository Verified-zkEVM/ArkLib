/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-! # Smooth Cyclic Groups -/


/-
  Redefinition of IsCyclic from Mathlib with computable generator.
  This avoids the use of Classical.choose to extract the generator,
  making dependent definitions incomputable.
-/
class IsCyclicWithGen (G : Type) [Pow G ℤ] where
  gen : G
  zpow_surjective : Function.Surjective (gen ^ · : ℤ → G)

/- Derivation of an instance of Mathlib's `IsCyclic` from an instance if `IsCylicWithGen`. -/
instance {G} [Pow G ℤ] [inst : IsCyclicWithGen G] : IsCyclic G where
  exists_zpow_surjective := ⟨inst.gen, inst.zpow_surjective⟩


/- Class indicating that a cyclic Monoid of order `2^n`. -/
class SmoothPowerOfTwo (n : ℕ) (G : Type) [Pow G ℤ] [Monoid G] [inst : IsCyclicWithGen G] where
  smooth : orderOf inst.gen = 2 ^ n
