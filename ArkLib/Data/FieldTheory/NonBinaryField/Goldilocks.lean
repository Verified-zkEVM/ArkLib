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

-- 2^{64} - 2^{32} + 1
@[reducible]
def FIELD_CARD : Nat := 18446744069414584321

abbrev Field := ZMod FIELD_CARD

theorem is_prime : Nat.Prime FIELD_CARD := by
  unfold FIELD_CARD
  pratt

end Goldilocks
