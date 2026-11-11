/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Classes.CloseToUniform

/-!
# `Deserialize.CloseToUniform` for prime fields

The reduce-modulo-order challenge decoder of `ZMod p` resolves its `CloseToUniform` instance,
with the error `p / 256 ^ n` it inherits from CompPoly's fiber count.
-/

namespace ArkLibTest.CloseToUniform

open CompPoly

local instance (n : ℕ) : MeasurableSpace (Vector UInt8 n) := ⊤

local instance (n : ℕ) : DiscreteMeasurableSpace (Vector UInt8 n) := ⟨fun _ => trivial⟩

example (p n : ℕ) [NeZero p] : Nonempty (Deserialize.CloseToUniform (ZMod p) (Vector UInt8 n)) :=
  ⟨inferInstance⟩

example (p n : ℕ) [NeZero p] :
    ((inferInstance : Deserialize.CloseToUniform (ZMod p) (Vector UInt8 n)).ε : ℝ) =
      (p : ℝ) / 256 ^ n := by
  rfl

end ArkLibTest.CloseToUniform
