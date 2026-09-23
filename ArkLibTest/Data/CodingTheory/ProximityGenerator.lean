/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement

open TensorMCA

namespace ProximityGeneratorTest

example :
    binaryTensorFold ![(0 : ℚ)]
        (fun b : Fin 1 → Bool ↦ ![if b 0 then (7 : ℚ) else 4]) =
      fun i ↦ ∑ leaf,
        PolynomialGenIsMCA.tensorGeneratorPi (fun _ ↦ binaryEqualityGenerator) ![(0 : ℚ)] leaf •
          (fun b : Fin 1 → Bool ↦ ![if b 0 then (7 : ℚ) else 4]) leaf i :=
  binaryTensorFold_eq_tensorGeneratorPi _ _

end ProximityGeneratorTest
