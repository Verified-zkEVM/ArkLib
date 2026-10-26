/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Multilinear.Basic
public import ArkLib.Data.Vector.Lookup

/-!
# Scalar lookup language and indexed multiplicities

All query columns and declared physical table pieces have the same Boolean row domain. An indexed
witness selects a position in the entire table collection for every query. Natural histograms are
cast only after counting; no division, table uniqueness or canonical choice of duplicate is needed.

The signed collection assigns weight1 to queries and the negative retained multiplicity to table
positions. Its key fibers are query counts minus table multiplicity totals. The converse needs only
the total query count below the explicit characteristic, irrespective of the number of table pieces.
The mapped converse is exactly a nonzero fiber after an injective field map, ready for scalar
weighted LogUp. These are language and algebra statements; the actual retained source and initial
multiplicity-message protocol are separate owners.
-/

@[expose] public section

open CompPoly
open scoped BigOperators
namespace Logup.Lookup
variable {B : Type} {n M P : ℕ}
/-- Original query columns and every declared table piece, indexed by their two roles. -/
abbrev Data (B : Type) (n M P : ℕ) := (Fin M ⊕ Fin P) → CMlPolynomialEval B n

/-- Flatten columns with row index inside column index, using `finProdFinEquiv`. -/
def columnEntries {K : ℕ} (tables : Fin K → CMlPolynomialEval B n) : Vector B (K * 2 ^ n) :=
  Vector.ofFn fun i => (tables (finProdFinEquiv.symm i).1).get (finProdFinEquiv.symm i).2

/-- Every queried entry occurs in at least one position of the declared table collection. -/
def InLanguage (data : Data B n M P) : Prop :=
  ∀ q : Fin M, ∀ row : Fin (2 ^ n), ∃ piece : Fin P, ∃ tableRow : Fin (2 ^ n),
    (data (.inl q)).get row = (data (.inr piece)).get tableRow

/-- Every explicit selected table position carries the corresponding queried value. -/
def ValidIndices (data : Data B n M P) (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) : Prop :=
  ∀ i : Fin (M * 2 ^ n),
    (columnEntries (fun p => data (.inr p)))[(indices[i.val]).val] =
      (columnEntries (fun q => data (.inl q)))[i.val]

/-- Check an explicit lookup witness with executable equality, without extracting one. -/
def checkIndices [DecidableEq B] (data : Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) : Bool :=
  let tables := columnEntries (fun p => data (.inr p))
  let queries := columnEntries (fun q => data (.inl q))
  (List.finRange (M * 2 ^ n)).all fun i => tables[(indices[i.val]).val] == queries[i.val]

/-- A flattened position reads the corresponding column and row. -/
@[simp]
theorem columnEntries_get {K : ℕ} (tables : Fin K → CMlPolynomialEval B n)
    (i : Fin (K * 2 ^ n)) : (columnEntries tables).get i =
      (tables (finProdFinEquiv.symm i).1).get (finProdFinEquiv.symm i).2 := by
  simp only [columnEntries, Vector.get_eq_getElem, Vector.getElem_ofFn]

/-- Flattening a column-row pair preserves that exact entry. -/
@[simp]
theorem columnEntries_get_pair {K : ℕ} (tables : Fin K → CMlPolynomialEval B n)
    (p : Fin K) (r : Fin (2 ^ n)) :
    (columnEntries tables).get (finProdFinEquiv (p, r)) = (tables p).get r := by
  rw [columnEntries_get, Equiv.symm_apply_apply]


/-- Count selected positions naturally, then cast and reshape into physical table pieces. -/
def multiplicities [NatCast B] {L : ℕ} (indices : Vector (Fin (P * 2 ^ n)) L) :
    Vector (CMlPolynomialEval B n) P :=
  let counts := Vector.histogram indices
  Vector.ofFn fun p => Vector.ofFn fun row => (counts[(finProdFinEquiv (p, row)).val] : B)

/-- Original values with query weights1 and table weights equal to negative multiplicities. -/
def weightedData [One B] [Neg B] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) : Fin 2 × Fin (M + P) → CMlPolynomialEval B n :=
  fun i => if i.1 = 0 then data (finSumFinEquiv.symm i.2) else
    (finSumFinEquiv.symm i.2).elim (fun _ => Vector.replicate (2 ^ n) 1)
      (fun p => Vector.map Neg.neg (mu[p.val]))

/-- The signed collection retains every original value column in order. -/
@[simp]
theorem weightedData_value [One B] [Neg B] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (i : Fin (M + P)) :
    weightedData data mu (0, i) = data (finSumFinEquiv.symm i) := by
  simp [weightedData]

/-- Every query position has unit weight. -/
@[simp]
theorem weightedData_query_weight [One B] [Neg B] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (i : Fin M) :
    weightedData data mu (1, Fin.castAdd P i) = Vector.replicate (2 ^ n) 1 := by
  simp [weightedData]

/-- Every table position has the negative of its supplied multiplicity. -/
@[simp]
theorem weightedData_table_weight [One B] [Neg B] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (i : Fin P) :
    weightedData data mu (1, Fin.natAdd M i) = Vector.map Neg.neg (mu[i.val]) := by
  simp [weightedData]

/-- Flattened membership is the original query-column/table-piece language. -/
theorem inLanguage_iff_entries (data : Data B n M P) : InLanguage data ↔
    ∀ i : Fin (M * 2 ^ n), ∃ j : Fin (P * 2 ^ n),
      (columnEntries (fun p => data (.inr p)))[j.val] =
        (columnEntries (fun q => data (.inl q)))[i.val] := by
  constructor
  · intro h i
    obtain ⟨p, r, heq⟩ := h (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
    refine ⟨finProdFinEquiv (p, r), ?_⟩
    simpa only [← Vector.get_eq_getElem, columnEntries_get_pair, columnEntries_get,
      Equiv.symm_apply_apply] using heq.symm
  · intro h q r
    obtain ⟨j, heq⟩ := h (finProdFinEquiv (q, r))
    refine ⟨(finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2, ?_⟩
    simpa only [← Vector.get_eq_getElem, columnEntries_get_pair, columnEntries_get,
      Equiv.symm_apply_apply] using heq.symm


private theorem sum_rows_columns {R : Type} [AddCommMonoid R] {K : ℕ}
    (g : Fin K → Fin (2 ^ n) → R) :
    (∑ c, ∑ u : Fin n → Fin 2, g c (finFunctionFinEquiv u)) =
      ∑ i : Fin (K * 2 ^ n), g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  simp_rw [finFunctionFinEquiv.sum_comp]
  rw [← Fintype.sum_prod_type (fun p => g p.1 p.2)]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (by intro i; simp)

private theorem sumFiber_one_eq_count [DecidableEq B] {R : Type} [AddCommMonoidWithOne R]
    {K : ℕ} (xs : Vector B K) (key : B) :
    Finset.univ.sumFiber (fun i : Fin K => xs[i.val]) (fun _ => (1 : R)) key =
      (xs.toList.count key : R) := by
  have h := Vector.sumFiber_cast_histogram (R := R) xs xs (Vector.ofFn id)
    (by intro i; simp) key
  simpa [Vector.getElem_histogram, Vector.toList_ofFn, List.ofFn_id, List.count_finRange] using h

/-- The signed fiber is the query count minus the supplied table multiplicity total. -/
theorem weighted_fiber_eq_sub [CommRing B] [DecidableEq B] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (key : B) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun p => (weightedData data mu (0, p.2)).get (finFunctionFinEquiv p.1))
      (fun p => (weightedData data mu (1, p.2)).get (finFunctionFinEquiv p.1)) key =
    ((columnEntries (fun q => data (.inl q))).toList.count key : B) -
      Finset.univ.sumFiber
        (fun i : Fin (P * 2 ^ n) => (columnEntries (fun p => data (.inr p)))[i.val])
        (fun i => (columnEntries (fun p : Fin P => mu[p.val]))[i.val]) key := by
  rw [Finset.sumFiber_eq_sum_ite, Finset.product_eq_sprod, Finset.sum_product]
  simp only [weightedData_value]
  rw [Finset.sum_comm, Fin.sum_univ_add]
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    weightedData_query_weight, weightedData_table_weight, Vector.get_eq_getElem,
    Vector.getElem_replicate, Vector.getElem_map]
  have hneg (p : Prop) [Decidable p] (a : B) :
      (if p then -a else 0) = -(if p then a else 0) := by split_ifs <;> simp
  simp_rw [hneg, Finset.sum_neg_distrib]
  rw [sum_rows_columns (fun c r => if (data (.inl c))[r.val] = key then (1 : B) else 0),
    sum_rows_columns (fun c r => if (data (.inr c))[r.val] = key then mu[c.val][r.val] else 0)]
  rw [← sumFiber_one_eq_count]
  simp only [Finset.sumFiber_eq_sum_ite, columnEntries, Vector.getElem_ofFn]
  simp only [Vector.get_eq_getElem, sub_eq_add_neg]

/-- The executable witness check is exactly selected-position correctness. -/
theorem checkIndices_eq_true [DecidableEq B] (data : Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) :
    checkIndices data indices = true ↔ ValidIndices data indices := by
  simp [checkIndices, ValidIndices, List.all_eq_true]

/-- The language has an explicit indexed witness; choice is confined to this proof. -/
theorem inLanguage_iff_exists_validIndices (data : Data B n M P) :
    InLanguage data ↔ ∃ indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n),
      ValidIndices data indices := by
  rw [inLanguage_iff_entries]
  constructor
  · intro h
    classical
    refine ⟨Vector.ofFn fun i => Classical.choose (h i), ?_⟩
    intro i
    simpa using Classical.choose_spec (h i)
  · rintro ⟨indices, h⟩ i
    exact ⟨indices[i.val], h i⟩

/-- Flattening the cast multiplicities recovers the original natural histogram after casting. -/
@[simp]
theorem columnEntries_multiplicities [NatCast B] {L : ℕ}
    (indices : Vector (Fin (P * 2 ^ n)) L) :
    columnEntries (fun p => (multiplicities (B := B) indices)[p.val]) =
      Vector.map Nat.cast (Vector.histogram indices) := by
  apply Vector.ext
  intro i hi
  simp only [columnEntries, multiplicities, Vector.getElem_ofFn, Vector.get_eq_getElem,
    Vector.getElem_map]
  change ((Vector.histogram indices)[(finProdFinEquiv
    ((finProdFinEquiv.symm ⟨i, hi⟩).1, (finProdFinEquiv.symm ⟨i, hi⟩).2)).val] : B) = _
  simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- Zero signed fibers imply lookup membership when query counts cannot wrap modulo p. -/
theorem inLanguage_of_weighted_fiber_eq_zero [CommRing B] [DecidableEq B]
    (p : ℕ) [CharP B p] (data : Data B n M P) (mu : Vector (CMlPolynomialEval B n) P)
    (hbudget : M * 2 ^ n < p)
    (hzero : ∀ key, ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1)) key = 0) :
    InLanguage data := by
  rw [inLanguage_iff_entries]
  apply Vector.exists_getElem_eq_of_sumFiber_eq_count_of_length_lt_char p
    (columnEntries fun i => data (.inr i)) (columnEntries fun i => data (.inl i))
    (fun i => (columnEntries fun p : Fin P => mu[p.val])[i.val])
    (fun key => (sub_eq_zero.mp ((weighted_fiber_eq_sub data mu key).symm.trans (hzero key))).symm)
    hbudget

/-- A correct indexed histogram balances every key in every characteristic. -/
theorem weighted_fiber_multiplicities_eq_zero [CommRing B] [DecidableEq B]
    (data : Data B n M P) (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices data indices) (key : B) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (weightedData data (multiplicities indices) (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (weightedData data (multiplicities indices) (1, i.2)).get (finFunctionFinEquiv i.1))
      key = 0 := by
  rw [weighted_fiber_eq_sub, columnEntries_multiplicities]
  simp only [Vector.getElem_map]
  rw [Vector.sumFiber_cast_histogram _ _ indices hvalid key, sub_self]

/-- A false lookup has a nonzero mapped fiber for every multiplicity assignment when query counts
remain below the characteristic. -/
theorem exists_mapped_weighted_fiber_ne_zero [Field B] {E : Type} [Field E]
    [DecidableEq E] (f : B →+* E) (p : ℕ) [CharP B p] (data : Data B n M P)
    (mu : Vector (CMlPolynomialEval B n) P) (hbudget : M * 2 ^ n < p)
    (hfalse : ¬ InLanguage data) :
    ∃ key, ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => f ((weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1)))
      (fun i => f ((weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1))) key ≠ 0 := by
  classical
  by_contra! hzero
  apply hfalse
  apply inLanguage_of_weighted_fiber_eq_zero p data mu hbudget
  intro key
  let occ := (Finset.univ : Finset (Fin n → Fin 2)).product
    (Finset.univ : Finset (Fin (M + P)))
  let values := fun i : (Fin n → Fin 2) × Fin (M + P) =>
    (weightedData data mu (0, i.2)).get (finFunctionFinEquiv i.1)
  let weights := fun i : (Fin n → Fin 2) × Fin (M + P) =>
    (weightedData data mu (1, i.2)).get (finFunctionFinEquiv i.1)
  have htransport : occ.sumFiber (f ∘ values) (f ∘ weights) (f key) =
      f (occ.sumFiber values weights key) := by
    rw [Finset.sumFiber_comp_eq_of_isolated occ values (f ∘ weights) f key
      (fun i _ h => f.injective h)]
    exact Finset.sumFiber_map f.toAddMonoidHom occ values weights key
  have hcast : f (occ.sumFiber values weights key) = 0 := htransport.symm.trans (hzero (f key))
  exact f.injective (hcast.trans f.map_zero.symm)

/-- Honest indexed multiplicities remain balanced under any ring map, including collisions. -/
theorem mapped_weighted_fiber_multiplicities_eq_zero [CommRing B] {E : Type} [CommRing E]
    [DecidableEq E] (f : B →+* E) (data : Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices data indices) (key : E) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => f ((weightedData data (multiplicities indices) (0, i.2)).get
        (finFunctionFinEquiv i.1)))
      (fun i => f ((weightedData data (multiplicities indices) (1, i.2)).get
        (finFunctionFinEquiv i.1))) key = 0 := by
  classical
  let occ := (Finset.univ : Finset (Fin n → Fin 2)).product
    (Finset.univ : Finset (Fin (M + P)))
  let values := fun i : (Fin n → Fin 2) × Fin (M + P) =>
    (weightedData data (multiplicities indices) (0, i.2)).get (finFunctionFinEquiv i.1)
  let weights := fun i : (Fin n → Fin 2) × Fin (M + P) =>
    (weightedData data (multiplicities indices) (1, i.2)).get (finFunctionFinEquiv i.1)
  have hzero (original : B) : occ.sumFiber values (f ∘ weights) original = 0 := by
    calc
      _ = f (occ.sumFiber values weights original) :=
        Finset.sumFiber_map f.toAddMonoidHom occ values weights original
      _ = 0 := by rw [weighted_fiber_multiplicities_eq_zero data indices hvalid, map_zero]
  exact Finset.sumFiber_comp_eq_zero occ values (f ∘ weights) f hzero key

end Logup.Lookup
