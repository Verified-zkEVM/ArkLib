/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench

/-!
# Bench case: sum-check with 20 rounds, skeleton export

The export of the skeleton of `sumcheckSpec ℚ 2 20 D` to JSON and to TeX. With
`Specs.Bench.Export128` it shows that the export cost does not grow with the number of rounds (see
`Specs.Bench`).
-/

set_option linter.hashCommand false

namespace Specs.Bench.Export20

#guard jsonSize (sumcheckSpec ℚ 2 20 D).skeleton > 0
#guard texSize (sumcheckSpec ℚ 2 20 D).skeleton > 0

end Specs.Bench.Export20
