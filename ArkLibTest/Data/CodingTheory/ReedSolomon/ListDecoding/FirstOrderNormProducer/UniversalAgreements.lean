/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalAgreements

/-! Executed universal, coprime and proper-split branches, including inherited old labels. -/

namespace UniversalAgreementTests

open CompPoly CPolynomial
open ReedSolomon.ListDecoding.FirstOrderNormProducer
open ReedSolomon.ListDecoding.FirstOrderNormProducer.UniversalAgreements

/-- The transcript forces all three decisions; final exact labels expose incorrect inheritance. -/
def run : IO Unit := do
  let x : CPolynomial ℚ := X
  let h := x * (x - 1) * (x - 2)
  let es := [h, 1, x, x - 1, x * (x - 1)]
  let out := UniversalAgreements.run h es
  unless out.blocks.length == 3 do
    throw (IO.userError "universal scan has wrong component count")
  unless out.blocks.map Block.modulus == [x, x - 1, x - 2] do
    throw (IO.userError "universal scan returned wrong component factors")
  unless out.blocks.map Block.universal == [[4, 2, 0], [4, 3, 0], [0]] do
    throw (IO.userError "universal labels were lost or assigned to a nonuniversal child")
  unless (out.blocks.map Block.modulus).prod == h do
    throw (IO.userError "universal scan did not preserve the input polynomial")
  unless out.transcript.map Stage.position == [0, 1, 2, 3, 4] do
    throw (IO.userError "transcript positions are not in input order")
  unless out.transcript.map Stage.decisions ==
      [[.universal], [.coprime], [.split], [.coprime, .split],
        [.universal, .universal, .coprime]] do
    throw (IO.userError "transcript did not execute all prescribed split branches")
  let empty := UniversalAgreements.run h []
  unless empty.blocks.map Block.modulus == [h] && empty.transcript.isEmpty do
    throw (IO.userError "empty residual scan changed the initial component")
  let zero := UniversalAgreements.run h [0]
  unless zero.blocks.map Block.universal == [[0]] do
    throw (IO.userError "zero residual was not universal")
  let unit := UniversalAgreements.run (1 : CPolynomial ℚ) [0, x]
  unless unit.blocks.map Block.modulus == [1] do
    throw (IO.userError "unit component policy changed its polynomial product")

end UniversalAgreementTests
