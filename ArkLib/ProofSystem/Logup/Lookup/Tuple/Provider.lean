/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Polynomial.TaggedTuple
public import ArkLib.ProofSystem.Logup.Lookup.Language

/-!
# Checked typed providers with stored coefficient columns

Each declared physical table piece belongs to one public bus. Queries may change bus between
Boolean rows. Raw preparation checks the exact common row height, each schema key and every
piece's declared owner; it does not check whether a query occurs in a table.

One eager constructor stores the original key rows and their padded coefficient tables. Later
source queries select those stored coefficient tables instead of rebuilding columns from keys.
The raw and typed preparation paths share that constructor. No field, finite key carrier or
payload equality is needed by preparation; equality of finite bus indices suffices for ownership.
The schema's tag uniqueness and width bounds are its separate checked structural boundary.
-/

@[expose] public section

open CompPoly
namespace Logup.Lookup.Tuple

/-- The declared bus owner of each physical table piece. -/
structure ProviderLayout (b P : Nat) where
  /-- Repeated bus owners across different pieces are allowed. -/
  tableBus : Vector (Fin b) P

/-- Check the piece count and each raw bus owner against the registered bus count. -/
def ProviderLayout.create? (b P : Nat) (owners : Array Nat) : Option (ProviderLayout b P) :=
  if hsize : owners.size = P then
    let ids : Vector Nat P := ⟨owners, hsize⟩
    if h : ∀ p : Fin P, ids[p.val] < b then
      some ⟨Vector.ofFn fun p => ⟨ids[p.val], h p⟩⟩
    else none
  else none

/-- Layout validation checks only the exact piece count and finite owner indices. -/
theorem ProviderLayout.isSome_create? (b P : Nat) (owners : Array Nat) :
    (ProviderLayout.create? b P owners).isSome ↔ owners.size = P ∧
      ∀ i : Fin owners.size, owners[i.val] < b := by
  by_cases hsize : owners.size = P
  · subst P
    by_cases hbus : ∀ i : Fin owners.size, owners[i.val] < b
    · simp [create?, hbus]
    · simp [create?, hbus]
  · simp [create?, hsize]

/-- Successful layout validation retains the supplied owner sequence exactly. -/
theorem ProviderLayout.data_of_create?_eq_some {b P : Nat} {owners : Array Nat}
    {layout : ProviderLayout b P} (h : create? b P owners = some layout) :
    (Vector.map Fin.val layout.tableBus).toArray = owners := by
  unfold create? at h
  split at h
  · rename_i hsize
    dsimp only at h
    split at h
    · cases h
      simpa only [Vector.map_ofFn, Function.comp_def] using congrArg Vector.toArray
        (Vector.ofFn_getElem (xs := (⟨owners, hsize⟩ : Vector Nat P)))
    · contradiction
  · contradiction

variable {B : Type} {b W n M P : Nat}

/-- Typed rows and eagerly stored coefficient columns, with exact source and owner coherence. -/
structure PreparedProvider [Zero B] (schema : TaggedTuple.Schema B b W)
    (layout : ProviderLayout b P) (n M : Nat) where
  /-- All query columns followed by all declared table pieces. -/
  keyRows : Vector (CMlPolynomialEval schema.Key n) (M + P)
  /-- Stored tables for every padded coefficient of every source column. -/
  coefficientColumns : Vector (Vector (CMlPolynomialEval B n) (W + 1)) (M + P)
  /-- Every stored entry is the corresponding original key coefficient. -/
  coefficients : ∀ slot : Fin (M + P), ∀ j : Fin (W + 1), ∀ row : Fin (2 ^ n),
    coefficientColumns[slot.val][j.val].get row = schema.coefficient (keyRows[slot.val].get row) j
  /-- Every table row belongs to its publicly declared piece owner. -/
  owners : ∀ piece : Fin P, ∀ row : Fin (2 ^ n),
    (keyRows[(Fin.natAdd M piece).val].get row).1 = layout.tableBus[piece.val]

/-- Construct the coefficient tables once from correctly owned typed key rows. -/
def PreparedProvider.prepare [Zero B] (schema : TaggedTuple.Schema B b W)
    (layout : ProviderLayout b P) (keys : Vector (CMlPolynomialEval schema.Key n) (M + P))
    (howner : ∀ piece : Fin P, ∀ row : Fin (2 ^ n),
      (keys[(Fin.natAdd M piece).val].get row).1 = layout.tableBus[piece.val]) :
    PreparedProvider schema layout n M where
  keyRows := keys
  coefficientColumns := Vector.ofFn fun slot => Vector.ofFn fun j => Vector.ofFn fun row =>
    schema.coefficient (keys[slot.val].get row) j
  coefficients := by intro slot j row; simp only [Vector.get_eq_getElem, Vector.getElem_ofFn]
  owners := howner

/-- Check typed table-row ownership, then run the single eager coefficient constructor. -/
def PreparedProvider.prepare? [Zero B] (schema : TaggedTuple.Schema B b W)
    (layout : ProviderLayout b P) (keys : Vector (CMlPolynomialEval schema.Key n) (M + P)) :
    Option (PreparedProvider schema layout n M) :=
  if h : ∀ piece : Fin P, ∀ row : Fin (2 ^ n),
      (keys[(Fin.natAdd M piece).val].get row).1 = layout.tableBus[piece.val] then
    some (prepare schema layout keys h)
  else none

private theorem get_ofFnM_eq_some {α : Type} {L : Nat} (f : Fin L → Option α)
    (values : Vector α L) (h : Vector.ofFnM f = some values) (i : Fin L) :
    f i = some values[i.val] := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    rw [Vector.ofFnM_succ'] at h
    change (f 0).bind (fun a => (Vector.ofFnM fun j => f j.succ).bind
      (fun rest => some (Vector.cast (by omega) (#v[a] ++ rest)))) = some values at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    rcases h with ⟨a, ha, rest, hrest, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using ih (fun j => f j.succ) rest hrest j

/-- Check one raw key column against its exact Boolean row count and typed bus schema. -/
def keyRows? (schema : TaggedTuple.Schema B b W) (raw : Array (Nat × Array B)) :
    Option (CMlPolynomialEval schema.Key n) :=
  if hsize : raw.size = 2 ^ n then
    Vector.ofFnM fun row : Fin (2 ^ n) =>
      schema.key? raw[row.val].1 raw[row.val].2
  else none

/-- Pointwise checked keys give successful construction of the exact supplied row vector. -/
theorem keyRows?_eq_some_of_cells (schema : TaggedTuple.Schema B b W)
    (raw : Array (Nat × Array B)) (rows : CMlPolynomialEval schema.Key n)
    (hsize : raw.size = 2 ^ n)
    (hcells : ∀ row : Fin (2 ^ n),
      schema.key? raw[row.val].1 raw[row.val].2 = some (rows.get row)) :
    keyRows? schema raw = some rows := by
  unfold keyRows?
  rw [dite_eq_left hsize]
  have hf : (fun row : Fin (2 ^ n) => schema.key? raw[row.val].1 raw[row.val].2) =
      fun row => pure rows[row.val] := by
    funext row
    exact hcells row
  rw [hf, Vector.ofFnM_pure]
  exact congrArg some Vector.ofFn_getElem

/-- Check raw columns in query-then-table order, exact row heights, keys and table owners. -/
def PreparedProvider.prepareRaw? [Zero B] (schema : TaggedTuple.Schema B b W)
    (layout : ProviderLayout b P) (raw : Array (Array (Nat × Array B))) :
    Option (PreparedProvider schema layout n M) :=
  if hsize : raw.size = M + P then
    (Vector.ofFnM fun slot : Fin (M + P) =>
      keyRows? schema raw[slot.val]).bind (prepare? schema layout)
  else none

/-- Correct raw columns and table owners produce the one canonical eager preparation. -/
theorem PreparedProvider.prepareRaw?_eq_some_prepare [Zero B]
    (schema : TaggedTuple.Schema B b W) (layout : ProviderLayout b P)
    (raw : Array (Array (Nat × Array B)))
    (keys : Vector (CMlPolynomialEval schema.Key n) (M + P))
    (hsize : raw.size = M + P)
    (hcolumns : ∀ slot : Fin (M + P), keyRows? schema raw[slot.val] = some keys[slot.val])
    (howner : ∀ piece : Fin P, ∀ row : Fin (2 ^ n),
      (keys[(Fin.natAdd M piece).val].get row).1 = layout.tableBus[piece.val]) :
    prepareRaw? schema layout raw = some (prepare schema layout keys howner) := by
  unfold prepareRaw?
  rw [dite_eq_left hsize]
  have hf : (fun slot : Fin (M + P) => keyRows? schema raw[slot.val]) =
      fun slot => pure keys[slot.val] := funext hcolumns
  rw [hf, Vector.ofFnM_pure, Vector.ofFn_getElem, Option.pure_def, Option.bind_some]
  unfold prepare?
  rw [dite_eq_left howner]

private theorem keyRows?_data {schema : TaggedTuple.Schema B b W}
    {raw : Array (Nat × Array B)} {rows : CMlPolynomialEval schema.Key n}
    (h : keyRows? schema raw = some rows) :
    raw.size = 2 ^ n ∧ ∀ row : Fin (2 ^ n), ∃ pair,
      raw[row.val]? = some pair ∧ schema.key? pair.1 pair.2 = some (rows.get row) := by
  unfold keyRows? at h
  split at h
  · rename_i hsize
    constructor
    · exact hsize
    · intro row
      refine ⟨raw[row.val], Array.getElem?_eq_getElem (by omega), ?_⟩
      simpa only [Vector.get_eq_getElem] using get_ofFnM_eq_some _ rows h row
  · contradiction

/-- Typed ownership validation retains the exact supplied key rows. -/
theorem PreparedProvider.keyRows_of_prepare?_eq_some [Zero B]
    {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}
    {keys : Vector (CMlPolynomialEval schema.Key n) (M + P)}
    {prepared : PreparedProvider schema layout n M}
    (h : prepare? schema layout keys = some prepared) : prepared.keyRows = keys := by
  unfold prepare? at h
  split at h
  · cases h; rfl
  · contradiction

/-- Successful raw preparation retains every bus/payload through the checked key constructor
and accepts exactly the declared column count and common row height. -/
theorem PreparedProvider.rawData_of_prepareRaw?_eq_some [Zero B]
    {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}
    {raw : Array (Array (Nat × Array B))} {prepared : PreparedProvider schema layout n M}
    (h : prepareRaw? schema layout raw = some prepared) :
    raw.size = M + P ∧ ∀ slot : Fin (M + P), ∃ column,
      raw[slot.val]? = some column ∧ column.size = 2 ^ n ∧
      ∀ row : Fin (2 ^ n), ∃ pair, column[row.val]? = some pair ∧
        schema.key? pair.1 pair.2 = some (prepared.keyRows[slot.val].get row) := by
  unfold prepareRaw? at h
  split at h
  · rename_i hsize
    rcases Option.bind_eq_some_iff.mp h with ⟨keys, hkeys, hprepared⟩
    rw [keyRows_of_prepare?_eq_some hprepared]
    constructor
    · exact hsize
    · intro slot
      refine ⟨raw[slot.val], Array.getElem?_eq_getElem (by omega), ?_⟩
      exact keyRows?_data (get_ofFnM_eq_some _ keys hkeys slot)
  · contradiction

/-- View stored key rows through the existing query/table-role indexing convention. -/
def PreparedProvider.keyData [Zero B] {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M) :
    Data schema.Key n M P :=
  fun slot => prepared.keyRows[(finSumFinEquiv slot).val]

/-- Select a stored coefficient table without constructing or mapping a table. -/
def PreparedProvider.coefficientTable [Zero B] {schema : TaggedTuple.Schema B b W}
    {layout : ProviderLayout b P} (prepared : PreparedProvider schema layout n M)
    (slot : Fin M ⊕ Fin P) (j : Fin (W + 1)) : CMlPolynomialEval B n :=
  prepared.coefficientColumns[(finSumFinEquiv slot).val][j.val]

/-- The stored source coefficient is exactly that of the corresponding semantic key row. -/
@[simp]
theorem PreparedProvider.get_coefficientTable [Zero B]
    {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}
    (prepared : PreparedProvider schema layout n M) (slot : Fin M ⊕ Fin P)
    (j : Fin (W + 1)) (row : Fin (2 ^ n)) :
    (prepared.coefficientTable slot j).get row =
      schema.coefficient ((prepared.keyData slot).get row) j :=
  prepared.coefficients (finSumFinEquiv slot) j row

/-- Semantic table rows retain their checked public owner bus. -/
@[simp]
theorem PreparedProvider.keyData_table_bus [Zero B]
    {schema : TaggedTuple.Schema B b W} {layout : ProviderLayout b P}
    (prepared : PreparedProvider schema layout n M) (piece : Fin P) (row : Fin (2 ^ n)) :
    ((prepared.keyData (.inr piece)).get row).1 = layout.tableBus[piece.val] := by
  simpa only [keyData, finSumFinEquiv_apply_right] using prepared.owners piece row
end Logup.Lookup.Tuple
