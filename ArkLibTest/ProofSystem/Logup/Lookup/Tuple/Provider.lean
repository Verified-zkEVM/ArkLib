/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Lookup.Tuple.Provider
import Lean.Compiler.IR


/-! # Checked provider shapes, stored coefficients and structural ownership without lookup truth -/

open CompPoly Logup.Lookup Logup.Lookup.Tuple
open Lean Elab Command
namespace LogupTupleProviderTest

def schema : TaggedTuple.Schema Int 2 2 :=
  (TaggedTuple.Schema.mk? #v[2, 1] #v[2, 3]).get (by decide)
def layout : ProviderLayout 2 2 := (ProviderLayout.create? 2 2 #[0, 1]).get (by decide)
def raw : Array (Array (Nat × Array Int)) :=
  #[#[(0, #[0, 1]), (1, #[0])],
    #[(0, #[0, 0]), (0, #[0, 0])],
    #[(1, #[0]), (1, #[0])]]
def keys : Vector (CMlPolynomialEval schema.Key 1) 3 :=
  #v[#v[⟨0, #v[0, 1]⟩, ⟨1, #v[0]⟩],
    #v[⟨0, #v[0, 0]⟩, ⟨0, #v[0, 0]⟩],
    #v[⟨1, #v[0]⟩, ⟨1, #v[0]⟩]]
def prepared : PreparedProvider schema layout 1 1 :=
  PreparedProvider.prepare schema layout keys (by decide)

theorem raw_heights : ∀ slot : Fin 3, raw[slot.val].size = 2 := by decide

theorem parsed_columns (slot : Fin 3) : keyRows? schema raw[slot.val] = some keys[slot.val] := by
  apply keyRows?_eq_some_of_cells schema _ _ (raw_heights slot)
  exact (show ∀ slot : Fin 3, ∀ row : Fin 2,
    schema.key?
      (raw[slot.val][row.val]'(by rw [raw_heights slot]; exact row.isLt)).1
      (raw[slot.val][row.val]'(by rw [raw_heights slot]; exact row.isLt)).2 =
      some (keys[slot.val].get row) by decide) slot

theorem from_raw : PreparedProvider.prepareRaw? schema layout raw = some prepared :=
  PreparedProvider.prepareRaw?_eq_some_prepare schema layout raw keys (by decide)
    parsed_columns (by decide)

theorem raw_preserved : raw.size = 3 ∧ ∀ slot : Fin 3, ∃ column,
    raw[slot.val]? = some column ∧ column.size = 2 ∧
    ∀ row : Fin 2, ∃ pair, column[row.val]? = some pair ∧
      schema.key? pair.1 pair.2 = some (prepared.keyRows[slot.val].get row) :=
  PreparedProvider.rawData_of_prepareRaw?_eq_some from_raw

/-- Ownership and valid shapes do not assert that a query occurs in any table piece. -/
theorem false_lookup : ¬ InLanguage prepared.keyData := by unfold InLanguage; decide

theorem coefficient_exact (slot : Fin 1 ⊕ Fin 2) (j : Fin 3) (row : Fin 2) :
    (prepared.coefficientTable slot j).get row =
      schema.coefficient ((prepared.keyData slot).get row) j :=
  prepared.get_coefficientTable slot j row

def wrongOwner : Array (Array (Nat × Array Int)) :=
  raw.set! 2 #[(0, #[0, 0]), (0, #[0, 0])]
def shortRow : Array (Array (Nat × Array Int)) := raw.set! 0 #[(0, #[0, 1])]
def longRow : Array (Array (Nat × Array Int)) := raw.set! 1
  #[(0, #[0, 0]), (0, #[0, 0]), (0, #[0, 0])]
def badWidth : Array (Array (Nat × Array Int)) := raw.set! 0 #[(0, #[0]), (1, #[0])]
def badBus : Array (Array (Nat × Array Int)) := raw.set! 0 #[(2, #[0]), (1, #[0])]

/-- A zero tag and zero width are both valid; the only coefficient is the declared tag. -/
def zeroSchema : TaggedTuple.Schema Int 2 0 :=
  (TaggedTuple.Schema.mk? #v[0, 0] #v[0, 1]).get (by decide)
def zeroRaw : Array (Array (Nat × Array Int)) :=
  #[#[(0, #[]), (1, #[])], #[(0, #[]), (0, #[])], #[(1, #[]), (1, #[])]]
def zeroKeys : Vector (CMlPolynomialEval zeroSchema.Key 1) 3 :=
  #v[#v[⟨0, #v[]⟩, ⟨1, #v[]⟩],
    #v[⟨0, #v[]⟩, ⟨0, #v[]⟩], #v[⟨1, #v[]⟩, ⟨1, #v[]⟩]]
def zeroPrepared : PreparedProvider zeroSchema layout 1 1 :=
  PreparedProvider.prepare zeroSchema layout zeroKeys (by decide)

/-- A data-only provider can be empty; the active protocol's checked grouping rejects total0. -/
def emptySchema : TaggedTuple.Schema Int 0 0 :=
  (TaggedTuple.Schema.mk? #v[] #v[]).get (by decide)
def emptyLayout : ProviderLayout 0 0 := (ProviderLayout.create? 0 0 #[]).get (by decide)
def emptyPrepared : PreparedProvider emptySchema emptyLayout 2 0 :=
  PreparedProvider.prepare emptySchema emptyLayout #v[] (fun p => Fin.elim0 p)

/-- Generic checked preparation requires no field, payload equality or finite payload carrier. -/
def genericPrepare {B : Type} [Zero B] {b W n M P : Nat}
    (schema : TaggedTuple.Schema B b W) (layout : ProviderLayout b P)
    (keys : Vector (CMlPolynomialEval schema.Key n) (M + P)) :
    Option (PreparedProvider schema layout n M) := PreparedProvider.prepare? schema layout keys

run_cmd do
  unless (ProviderLayout.create? 2 2 #[0, 1]).isSome do
    throwError "valid physical-piece registry rejected"
  unless !(ProviderLayout.create? 2 2 #[0]).isSome &&
      !(ProviderLayout.create? 2 2 #[0, 2]).isSome do
    throwError "wrong piece count or unregistered owner accepted"
  unless (ProviderLayout.create? 1 3 #[0, 0, 0]).isSome do
    throwError "multiple physical pieces for one bus rejected"
  unless (PreparedProvider.prepareRaw? schema layout raw).map (·.coefficientColumns) ==
      some prepared.coefficientColumns do
    throwError "raw parsing did not reach the exact typed eager coefficient constructor"
  unless prepared.coefficientColumns ==
      #v[#v[#v[0, 0], #v[1, 0], #v[2, 3]],
         #v[#v[0, 0], #v[0, 0], #v[2, 2]],
         #v[#v[0, 0], #v[0, 0], #v[3, 3]]] do
    throwError "eager stored coefficients changed tag/payload/padding or piece order"
  unless prepared.coefficientTable (.inl 0) 2 == #v[2, 3] &&
      prepared.coefficientTable (.inl 0) 1 == #v[1, 0] do
    throwError "row-varying query bus was replaced by one constant tag or payload width"
  for invalid in [wrongOwner, shortRow, longRow, badWidth, badBus, raw.pop] do
    unless !(PreparedProvider.prepareRaw? (n := 1) (M := 1) schema layout invalid).isSome do
      throwError "invalid ownership, row height, key shape, bus or column count accepted"
  unless (PreparedProvider.prepareRaw? zeroSchema layout zeroRaw).map (·.coefficientColumns) ==
      some zeroPrepared.coefficientColumns do
    throwError "raw zero-width provider was rejected or changed its coefficient tables"
  unless zeroPrepared.coefficientColumns == #v[#v[#v[0, 1]], #v[#v[0, 0]], #v[#v[1, 1]]] do
    throwError "zero-width tag-only schema changed its exact stored columns"
  unless (PreparedProvider.prepareRaw? (n := 2) (M := 0) emptySchema emptyLayout #[]).isSome do
    throwError "empty raw provider required a default semantic key"
  unless emptyPrepared.keyRows.toArray.isEmpty &&
      emptyPrepared.coefficientColumns.toArray.isEmpty do
    throwError "empty provider required an impossible default semantic key"
  unless (genericPrepare schema layout prepared.keyRows).isSome do
    throwError "typed preparation did not share the valid raw preparation path"

run_cmd do
  for name in #[``ProviderLayout.create?, ``PreparedProvider.prepare, ``PreparedProvider.prepare?,
      ``keyRows?, ``PreparedProvider.prepareRaw?, ``PreparedProvider.keyData,
      ``PreparedProvider.coefficientTable, ``genericPrepare, ``prepared, ``zeroPrepared,
      ``emptyPrepared] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing checked provider executable IR: {name}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``ProviderLayout.isSome_create?, ``ProviderLayout.data_of_create?_eq_some,
      ``PreparedProvider.keyRows_of_prepare?_eq_some,
      ``PreparedProvider.rawData_of_prepareRaw?_eq_some,
      ``keyRows?_eq_some_of_cells, ``PreparedProvider.prepareRaw?_eq_some_prepare,
      ``PreparedProvider.get_coefficientTable,
      ``PreparedProvider.keyData_table_bus, ``from_raw, ``raw_preserved, ``false_lookup,
      ``coefficient_exact, ``raw_heights, ``parsed_columns] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "checked provider has an unexpected axiom: {name}"
end LogupTupleProviderTest
