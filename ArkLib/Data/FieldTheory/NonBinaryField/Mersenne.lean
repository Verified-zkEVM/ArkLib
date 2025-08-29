/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.NumberTheory.PrattCertificate

/-!
  # Mersenne prime field `2^{31} - 1`

  This is the field used in Circle STARKs.
-/

namespace Mersenne31

-- 2^{31} - 1
@[reducible]
def FIELD_CARD : Nat := 2147483647

abbrev Field := ZMod FIELD_CARD

theorem is_prime : Nat.Prime FIELD_CARD := by
  unfold FIELD_CARD
  pratt

end Mersenne31
