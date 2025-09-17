/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # BabyBear Field `2^{31} - 2^{27} + 1`

  This is the field used by Risc Zero.
-/

namespace BabyBear

@[reducible]
def fieldSize : Nat := 2 ^ 31 - 2 ^ 27 + 1

abbrev Field := ZMod fieldSize

theorem is_prime : Nat.Prime fieldSize := by
  unfold fieldSize
  pratt

end BabyBear
