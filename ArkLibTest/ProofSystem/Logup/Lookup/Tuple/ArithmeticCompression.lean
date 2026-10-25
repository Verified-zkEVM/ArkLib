/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticCompression
import ArkLibTest.ProofSystem.Logup.Lookup.Tuple.Completeness
import Lean.Compiler.IR

/-! # Actual eager value/weight construction and all nine compression-profile coordinates -/

open CompPoly OracleComp OracleSpec Logup.Lookup Logup.Lookup.Tuple
namespace LogupTupleCompressionTest

example {B E : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E]
    {b W n M P : Nat} {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}
    (f : B →+* E) (prepared : PreparedProvider schema layout n M) (beta : E)
    (mu : Vector (CMlPolynomialEval B n) P) :
    compressedData (simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta mu)) =
      prepared.weightedData f beta mu := simulateQ_compressedTablesProgram f prepared beta mu

namespace Asymmetric
abbrev F := LogupTupleHonestTest.Small.F
def f : F →+* F := RingHom.id F
def schema : TaggedTuple.Schema F 2 3 :=
  (TaggedTuple.Schema.mk? #v[1, 0] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 3 := (ProviderLayout.create? 2 3 #[0, 1, 0]).get (by decide)
def keys : Vector (CMlPolynomialEval schema.Key 1) 5 :=
  #v[#v[⟨0, #v[1]⟩, ⟨1, #v[]⟩], #v[⟨0, #v[4]⟩, ⟨0, #v[9]⟩],
    #v[⟨0, #v[1]⟩, ⟨0, #v[0]⟩], #v[⟨1, #v[]⟩, ⟨1, #v[]⟩],
    #v[⟨0, #v[9]⟩, ⟨0, #v[4]⟩]]
def prepared : PreparedProvider schema layout 1 2 :=
  PreparedProvider.prepare schema layout keys (by decide)
def mu : Vector (CMlPolynomialEval F 1) 3 := #v[#v[2, 3], #v[0, 5], #v[6, 0]]
def program (beta : F) := compressedTablesProgram f prepared beta mu

/-- Independently count the actual issued requests instead of evaluating the profile interpreter. -/
def counted : QueryImpl (ArithmeticSpec F) (StateM (Array Nat)) := fun op => do
  let i := match op with
    | .add _ _ => 0 | .sub _ _ => 1 | .mul _ _ => 2 | .inv _ => 3 | .eq _ _ => 4
    | .coefficientRead _ _ => 5 | .nodeRead _ _ => 6 | .valueRead _ _ => 7 | .metadata => 8
  modify (fun counts => counts.modify i (· + 1))
  pure (arithmeticAnswer op)
end Asymmetric

namespace OneSided
abbrev F := LogupTupleHonestTest.ZeroRound.F
abbrev schema := LogupTupleHonestTest.ZeroRound.schema
abbrev layout := LogupTupleHonestTest.ZeroRound.layout

def tableOnly : PreparedProvider schema layout 0 0 :=
  PreparedProvider.prepare schema layout
    #v[#v[⟨0, #v[]⟩], #v[⟨1, #v[]⟩]] (by decide)

def noTables : ProviderLayout 2 0 := ⟨#v[]⟩
def queryOnly : PreparedProvider schema noTables 0 1 :=
  PreparedProvider.prepare schema noTables #v[#v[⟨0, #v[]⟩]]
    (fun piece => Fin.elim0 piece)
end OneSided

#eval (show IO _ from do
  let (cache, cost) := profileArithmetic (Asymmetric.program 2)
  unless cache ==
      #v[#v[#v[0, 7], #v[3, 8], #v[0, 16], #v[7, 7], #v[8, 3]],
        #v[#v[1, 1], #v[1, 1], #v[15, 14], #v[0, 12], #v[11, 0]]] do
    throw (IO.userError "asymmetric rows, global tag exponent, padding or signed mu changed")
  unless cost .add == 30 && cost .mul == 30 && cost .sub == 6 && cost .metadata == 86 &&
      cost .inv == 0 && cost .eq == 0 && cost .coefficientRead == 0 &&
      cost .nodeRead == 0 && cost .valueRead == 0 do
    throw (IO.userError "compression lost an exact arithmetic/marker coordinate")
  let (actualCache, actualCounts) :=
    (simulateQ Asymmetric.counted (Asymmetric.program 2)).run (Array.replicate 9 0)
  unless actualCache == cache && actualCounts == #[30, 6, 30, 0, 0, 0, 0, 0, 86] do
    throw (IO.userError "actual primitive execution disagrees with the measured profile")
  for beta in List.finRange 17 do
    let b : Asymmetric.F := beta.val
    let result := simulateQ arithmeticAnswer (Asymmetric.program b)
    for kind in List.finRange 2 do
      for slot in List.finRange 5 do
        unless compressedData result (kind, slot) ==
            Asymmetric.prepared.weightedData Asymmetric.f b Asymmetric.mu (kind, slot) do
          throw (IO.userError "direct-reader cache disagrees with key fingerprint")
  let zeroMu := multiplicities (B := LogupTupleHonestTest.ZeroRound.F)
    (n := 0) (P := 2) LogupTupleHonestTest.ZeroRound.indices
  for beta in List.finRange 17 do
    let b : LogupTupleHonestTest.ZeroRound.F := beta.val
    let (result, profile) := profileArithmetic
      (compressedTablesProgram LogupTupleHonestTest.ZeroRound.f
        LogupTupleHonestTest.ZeroRound.prepared b zeroMu)
    unless profile .mul == 0 && profile .add == 0 && profile .sub == 2 &&
        profile .metadata == 17 && result[0] == #v[#v[0], #v[0], #v[1]] do
      throw (IO.userError "n0/W0/tag0 value construction or singleton Horner cost changed")
  let (tableCache, tableCost) := profileArithmetic
    (compressedTablesProgram (RingHom.id OneSided.F) OneSided.tableOnly 0 #v[#v[2], #v[0]])
  unless tableCache == #v[#v[#v[0], #v[1]], #v[#v[15], #v[0]]] &&
      tableCost .metadata == 12 && tableCost .sub == 2 && tableCost .add == 0 &&
      tableCost .mul == 0 do
    throw (IO.userError "table-only eager cache changed")
  let (queryCache, queryCost) := profileArithmetic
    (compressedTablesProgram (RingHom.id OneSided.F) OneSided.queryOnly 0 #v[])
  unless queryCache == #v[#v[#v[0]], #v[#v[1]]] && queryCost .metadata == 5 &&
      queryCost .sub == 0 && queryCost .add == 0 && queryCost .mul == 0 do
    throw (IO.userError "query-only eager cache changed")
  let extensionMu := multiplicities (B := LogupTupleHonestTest.Extension.B)
    (n := 1) (P := 3) LogupTupleHonestTest.Small.indices
  let beta := KoalaBear.ext6Gen
  let (extensionCache, extensionCost) := profileArithmetic
    (compressedTablesProgram LogupTupleHonestTest.Extension.f
      LogupTupleHonestTest.Extension.prepared beta extensionMu)
  unless extensionCost .mul == 16 && extensionCost .add == 16 && extensionCost .sub == 6 &&
      extensionCost .metadata == 62 do
    throw (IO.userError "actual base-to-Ext6 compression profile changed")
  for kind in List.finRange 2 do
    for slot in List.finRange 4 do
      unless compressedData extensionCache (kind, slot) ==
          LogupTupleHonestTest.Extension.prepared.weightedData LogupTupleHonestTest.Extension.f
            beta extensionMu (kind, slot) do
        throw (IO.userError "actual stored-base-to-Ext6 Horner data changed")
  pure actualCounts)

open Lean Elab Command in
run_cmd do
  for name in #[``compressedValuesProgram, ``compressedWeightsProgram, ``compressedTablesProgram,
      ``compressedData, ``compressionCost, ``Asymmetric.program, ``Asymmetric.counted] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_compressedValuesProgram,
      ``profileArithmetic_compressedWeightsProgram, ``profileArithmetic_compressedTablesProgram,
      ``simulateQ_compressedTablesProgram] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"
end LogupTupleCompressionTest
