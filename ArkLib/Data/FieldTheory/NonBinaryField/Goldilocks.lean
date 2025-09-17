/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # Goldilocks prime field `2^{64} - 2^{32} + 1`

  This is the field used in Plonky2/3.
-/

namespace Goldilocks

@[reducible]
def fieldSize : Nat := 2 ^ 64 - 2 ^ 32 + 1

abbrev Field := ZMod fieldSize

theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

end Goldilocks
