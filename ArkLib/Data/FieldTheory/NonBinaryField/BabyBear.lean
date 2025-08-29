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

-- 2^{31} - 2^{27} + 1
@[reducible]
def FIELD_CARD : Nat := 2013265921

abbrev Field := ZMod FIELD_CARD

theorem is_prime : Nat.Prime FIELD_CARD := by
  unfold FIELD_CARD
  pratt

end BabyBear
