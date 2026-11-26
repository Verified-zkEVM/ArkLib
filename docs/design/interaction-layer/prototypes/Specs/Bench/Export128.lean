/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench

/-!
# Bench case: sum-check with 128 rounds, skeleton export

The export of the skeleton of `sumcheckSpec ℚ 2 128 D` to JSON and to TeX. The skeleton keeps
only the TeX name of the domain `D^n` of the input claim, and `Dom` computes its elements only on
demand, so the export cost grows with the number of rounds, not with the size of `D^n` (see
`Specs.Bench`).
-/

set_option linter.hashCommand false

namespace Specs.Bench.Export128

#guard jsonSize (sumcheckSpec ℚ 2 128 D).skeleton > 0
#guard texSize (sumcheckSpec ℚ 2 128 D).skeleton > 0

end Specs.Bench.Export128
