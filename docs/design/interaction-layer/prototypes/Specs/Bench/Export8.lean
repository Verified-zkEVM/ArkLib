/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Bench

/-!
# Bench case: sum-check with 8 rounds, skeleton export

The export of the skeleton of `sumcheckSpec ℚ 2 8 D` to JSON and to TeX. Its cost grows as
`2^n`, because computing the skeleton builds the domain `D^n` of the input claim (see
`Specs.Bench`), so the static export cases stop at 20 rounds.
-/

namespace Specs.Bench.Export8

#guard jsonSize (sumcheckSpec ℚ 2 8 D).skeleton > 0
#guard texSize (sumcheckSpec ℚ 2 8 D).skeleton > 0

end Specs.Bench.Export8
