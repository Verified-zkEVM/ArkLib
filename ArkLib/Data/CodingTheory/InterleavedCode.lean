/-
Aggregator module for InterleavedCode. This file just re-exports the
split modules so downstream imports remain stable.
To work on a specific result, open the corresponding submodule file.
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.MinDistEq
import ArkLib.Data.CodingTheory.InterleavedCode.Lemma43
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.ClosePoints
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.ThreeClosePoints
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma45
import ArkLib.Data.CodingTheory.InterleavedCode.GeneralInequalityAndCounterexample
