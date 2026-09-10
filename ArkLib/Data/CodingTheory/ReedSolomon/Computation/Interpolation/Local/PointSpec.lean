/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.PointMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.RewriteSpec
/-!
# Exact semantics of a materialized interpolation point block

The row frame is collected from actual dense columns. Consequently its coefficient equations
are equivalent to polynomial vanishing, including cancellations and redundant zero rows.
The polynomial remains the full low-contact local constraint, not full substitution.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine

noncomputable section

open PolynomialDifferential
open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Coefficient vector pairing in the solver's exact convention. -/
def dot (cs : List F) (w : ℕ → F) : F :=
  ∑ i ∈ Finset.range cs.length, cs.getD i 0 * w i

theorem dot_cons (c : F) (cs : List F) (w : ℕ → F) :
    dot (c :: cs) w = c * w 0 + dot cs (fun i => w (i + 1)) := by
  simp [dot, Finset.sum_range_succ', add_comm]

/-- Ordered linear combination, with the same shifted coordinate convention as row pairing. -/
def combine {V : Type*} [AddCommMonoid V] [Module F V] : List V → (ℕ → F) → V
  | [], _ => 0
  | p :: ps, w => w 0 • p + combine ps (fun i => w (i + 1))

/-- Polynomial represented by the already computed column list and unknown coefficients. -/
def denseCombination (cols : List (DenseColumn F)) (w : ℕ → F) : LocalPolynomial F d :=
  combine (cols.map (LocalColumnRewriteMachine.denseRepresented d)) w

theorem coeff_denseCombination (q : LocalColumnRewriteMachine.Term F)
    (hq : q.jets.length = d) (cols : List (DenseColumn F))
    (hw : ∀ c ∈ cols, ∀ t ∈ c, t.2.length = d + 2) (w : ℕ → F) :
    coeff (LocalColumnRewriteMachine.exponent d q) (denseCombination cols w) =
      dot (cols.map (fun c => LocalColumnRewriteMachine.coordinate
        (q.t :: q.e :: q.jets) c)) w := by
  induction cols generalizing w with
  | nil => simp [denseCombination, combine, dot]
  | cons c cs ih =>
    have hh := LocalColumnRewriteMachine.coordinate_coeff q hq c (hw c (by simp))
    have ht := ih (fun c hc => hw c (by simp [hc])) (fun i => w (i + 1))
    simp only [denseCombination, List.map_cons, combine, coeff_add, coeff_smul,
      smul_eq_mul, dot_cons] at ht ⊢
    rw [← hh, ht, mul_comm (w 0)]

omit [CommRing F] in
/-- Every dense term has a valid structured decoding, including its exact coefficient. -/
theorem decode_term (term : Rewrite.DenseTerm F) (h : term.2.length = d + 2) :
    ∃ q : LocalColumnRewriteMachine.Term F,
      term = (q.coefficient, q.t :: q.e :: q.jets) ∧ q.jets.length = d := by
  obtain ⟨c, row⟩ := term
  cases row with
  | nil => simp at h
  | cons t row =>
    cases row with
    | nil => simp at h
    | cons e xs => exact ⟨⟨c, t, e, xs⟩, rfl, by simpa using h⟩

/-- Outside all materialized exponents, a represented column coefficient is zero. -/
theorem coeff_dense_zero (e : LocalVariable d →₀ ℕ) (col : DenseColumn F)
    (h : ∀ t ∈ col, coeff e (LocalColumnRewriteMachine.densePolynomial d t) = 0) :
    coeff e (LocalColumnRewriteMachine.denseRepresented d col) = 0 := by
  induction col with
  | nil => simp [LocalColumnRewriteMachine.denseRepresented]
  | cons t ts ih =>
    have hh := h t (by simp)
    have ht := ih (fun t hm => h t (by simp [hm]))
    simpa [LocalColumnRewriteMachine.denseRepresented] using
      (show coeff e (LocalColumnRewriteMachine.densePolynomial d t) +
        coeff e (LocalColumnRewriteMachine.denseRepresented d ts) = 0 by rw [hh, ht, add_zero])

/-- A coefficient absent from all columns is absent from every linear combination. -/
theorem coeff_combination_zero (e : LocalVariable d →₀ ℕ) (cols : List (DenseColumn F))
    (h : ∀ col ∈ cols, coeff e (LocalColumnRewriteMachine.denseRepresented d col) = 0)
    (w : ℕ → F) : coeff e (denseCombination cols w) = 0 := by
  induction cols generalizing w with
  | nil => simp [denseCombination, combine]
  | cons c cs ih =>
    have hh := h c (by simp)
    have ht := ih (fun c hm => h c (by simp [hm])) (fun i => w (i + 1))
    simpa [denseCombination, combine, hh] using ht

/-- The adaptive frame's homogeneous equations are exactly polynomial vanishing. -/
theorem block_satisfies_iff (cols : List (DenseColumn F))
    (hw : ∀ c ∈ cols, ∀ t ∈ c, t.2.length = d + 2) (w : ℕ → F) :
    Matrix.PivotSelectionMachine.Satisfies (block cols).1 w ↔
      denseCombination (d := d) cols w = 0 := by
  have hs : Matrix.PivotSelectionMachine.Satisfies (block cols).1 w ↔
      ∀ q ∈ (frame cols).1,
        dot (cols.map (fun c => LocalColumnRewriteMachine.coordinate q c)) w = 0 := by
    simp only [block, rows_result, Matrix.PivotSelectionMachine.Satisfies,
      List.forall_mem_map, dot]
  rw [hs]
  constructor
  · intro h
    ext e
    rw [coeff_zero]
    by_cases he : ∃ col ∈ cols, ∃ term ∈ col,
        coeff e (LocalColumnRewriteMachine.densePolynomial d term) ≠ 0
    · obtain ⟨col, hc, term, ht, he⟩ := he
      obtain ⟨q, rfl, hq⟩ := decode_term term (hw col hc term ht)
      have heq : LocalColumnRewriteMachine.exponent d q = e := by
        by_contra hne
        simp [LocalColumnRewriteMachine.densePolynomial,
          LocalColumnRewriteMachine.termPolynomial, hne] at he
      rw [← heq, coeff_denseCombination q hq cols hw w]
      apply h
      rw [frame_result]
      exact List.mem_flatMap.mpr ⟨col, hc, List.mem_map.mpr ⟨_, ht, rfl⟩⟩
    · apply coeff_combination_zero e cols _ w
      intro col hc
      apply coeff_dense_zero
      intro term ht
      by_contra hn
      exact he ⟨col, hc, term, ht, hn⟩
  · intro h q hq
    rw [frame_result] at hq
    obtain ⟨col, hc, ht⟩ := List.mem_flatMap.mp hq
    obtain ⟨term, ht', rfl⟩ := List.mem_map.mp ht
    obtain ⟨q, rfl, hq'⟩ := decode_term term (hw col hc term ht')
    rw [← coeff_denseCombination q hq' cols hw w, h, coeff_zero]

/-- Every allocated row has one coefficient per computed column and an explicit zero RHS. -/
theorem block_shape (cols : List (DenseColumn F)) :
    ∀ r ∈ (block cols).1, r.1.length = cols.length ∧ r.2 = 0 := by
  simp [block, rows_result]

/-- A proof-facing name for the actual column output, with a harmless failure default. -/
def columnValue (d m : ℕ) (a y : F) (v : List ℕ) : DenseColumn F :=
  (makeColumn d m a y v).1.getD []

/-- Source monomial in the exact support-vector coordinate order. -/
def sourceValue (d : ℕ) : List ℕ → DifferentialPolynomial F d
  | x :: b :: xs => sourceMonomial x b
      (fun j => xs.getD j.val 0)
  | _ => 0

/-- Source polynomial in actual support order and the solver's coefficient convention. -/
def sourceCombination (d : ℕ) (vs : List (List ℕ)) (w : ℕ → F) :
    DifferentialPolynomial F d := combine (vs.map (sourceValue d)) w

theorem ofFn_getD (xs : List ℕ) (hx : xs.length = d) :
    List.ofFn (fun j : Fin d => xs.getD j.val 0) = xs := by
  apply List.ext_getElem (by simp [hx])
  intro i hi hi'
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']

/-- Valid vector decoding inherits exact column semantics, width, size, and cost. -/
theorem makeColumn_refines (m : ℕ) (a y : F) (x b : ℕ) (xs : List ℕ)
    (hx : xs.length = d) :
    ∃ c, makeColumn d m a y (x :: b :: xs) =
      (some (columnValue d m a y (x :: b :: xs)), c) ∧
      LocalColumnRewriteMachine.denseRepresented d (columnValue d m a y (x :: b :: xs)) =
        localConstraintAt m a y (sourceValue d (x :: b :: xs)) ∧
      (∀ t ∈ columnValue d m a y (x :: b :: xs), t.2.length = d + 2) ∧
      (columnValue d m a y (x :: b :: xs)).length ≤ (d + 2) ^ (m + 2) * (m * m) ∧
      c ≤ 288 * (x + b + m + 2) * (m + 1) +
        8192 * (m + 2) * (d + 2) ^ (m + 2) * (m * m + 1) + 64 := by
  obtain ⟨ts, c, hc, hp, hw, hl, hcost⟩ := LocalColumnRewriteMachine.column_refines
    a y x b m (fun j : Fin d => xs.getD j.val 0)
  rw [ofFn_getD xs hx] at hc
  have hv : columnValue d m a y (x :: b :: xs) = ts := by
    simp [columnValue, makeColumn, hc]
  refine ⟨32 + c, ?_, ?_, ?_, ?_, ?_⟩
  · simp [makeColumn, hc, hv]
  · simpa only [hv, sourceValue] using hp
  · simpa only [hv] using hw
  · simpa only [hv] using hl
  · omega

/-- Gap-only bound for emitted terms in any support column. -/
def columnSize (d m : ℕ) : ℕ := (d + 2) ^ (m + 2) * (m * m)

/-- Uniform column charge over support with strict total-jet cutoff `J`. -/
def columnBudgetWithBudget (d m J A : ℕ) : ℕ :=
  288 * (m * A + J + m + 2) * (m + 1) +
    8192 * (m + 2) * (d + 2) ^ (m + 2) * (m * m + 1) + 64

/-- Legacy column charge for strict cutoff `2 * m`. -/
def columnBudget (d m A : ℕ) : ℕ := columnBudgetWithBudget d m (2 * m) A

/-- Every enumerated support vector gives a successful and correctly interpreted column. -/
theorem support_column_refinesWithBudget (D m J A : ℕ) (a y : F) (v : List ℕ)
    (hv : v ∈ InterpolationSupportMachine.supportSpec
      (InterpolationSupportMachine.parametersWithBudget D d m J A)) :
    ∃ c, makeColumn d m a y v = (some (columnValue d m a y v), c) ∧
      LocalColumnRewriteMachine.denseRepresented d (columnValue d m a y v) =
        localConstraintAt m a y (sourceValue d v) ∧
      (∀ t ∈ columnValue d m a y v, t.2.length = d + 2) ∧
      (columnValue d m a y v).length ≤ columnSize d m ∧
        c ≤ columnBudgetWithBudget d m J A := by
  have hw := InterpolationSupportMachine.supportSpec_width _ hv
  simp only [InterpolationSupportMachine.parametersWithBudget] at hw
  obtain ⟨x, b, xs, rfl⟩ : ∃ x b xs, v = x :: b :: xs := by
    cases v with
    | nil => simp at hw
    | cons x v =>
      cases v with
      | nil => simp at hw
      | cons b xs => exact ⟨x, b, xs, rfl⟩
  have hx : xs.length = d := by simpa using hw
  obtain ⟨c, hc, hp, hwidth, hl, hcost⟩ := makeColumn_refines m a y x b xs hx
  obtain ⟨_, hsum, hweight⟩ := (InterpolationSupportMachine.mem_supportSpec_iff _ x (b :: xs)).mp hv
  simp only [InterpolationSupportMachine.parametersWithBudget, List.sum_cons] at hsum hweight
  refine ⟨c, hc, hp, hwidth, hl, ?_⟩
  unfold columnBudgetWithBudget
  have hh : x + b + m + 2 ≤ m * A + J + m + 2 := by omega
  have hmul := Nat.mul_le_mul_right (m + 1) (Nat.mul_le_mul_left 288 hh)
  exact hcost.trans (Nat.add_le_add_right (Nat.add_le_add_right hmul _) 64)

/-- Legacy column refinement at strict cutoff `2 * m`. -/
theorem support_column_refines (D m A : ℕ) (a y : F) (v : List ℕ)
    (hv : v ∈ InterpolationSupportMachine.supportSpec
      (InterpolationSupportMachine.parameters D d m A)) :
    ∃ c, makeColumn d m a y v = (some (columnValue d m a y v), c) ∧
      LocalColumnRewriteMachine.denseRepresented d (columnValue d m a y v) =
        localConstraintAt m a y (sourceValue d v) ∧
      (∀ t ∈ columnValue d m a y v, t.2.length = d + 2) ∧
      (columnValue d m a y v).length ≤ columnSize d m ∧ c ≤ columnBudget d m A := by
  simpa [InterpolationSupportMachine.parameters, columnBudget] using
    support_column_refinesWithBudget (d := d) D m (2 * m) A a y v hv

/-- Column interpretation commutes with the ordered linear combination. -/
theorem combination_localConstraint (m : ℕ) (a y : F) (vs : List (List ℕ))
    (h : ∀ v ∈ vs,
      LocalColumnRewriteMachine.denseRepresented d (columnValue d m a y v) =
        localConstraintAt m a y (sourceValue d v)) (w : ℕ → F) :
    denseCombination (vs.map (columnValue d m a y)) w =
      localConstraintAt m a y (sourceCombination d vs w) := by
  induction vs generalizing w with
  | nil => simp [denseCombination, sourceCombination, combine]
  | cons v vs ih =>
    have hh := h v (by simp)
    have ht := ih (fun v hm => h v (by simp [hm])) (fun i => w (i + 1))
    simpa [denseCombination, sourceCombination, combine, hh] using
      congrArg (fun p => w 0 • localConstraintAt m a y (sourceValue d v) + p) ht

/-- Closed block budget for support with strict total-jet cutoff `J`. -/
def assemblyBudgetWithBudget (d m J A L : ℕ) : ℕ :=
  32 * InterpolationSupportMachine.linearFactor (d + 1) J * (m * A + 1) +
    (columnBudgetWithBudget d m J A + 64) * (L + 1) +
    512 * (d + 4) * (columnSize d m + 1) ^ 2 * (L + 1) ^ 2 + 32

/-- Legacy block budget for strict cutoff `2 * m`. -/
def assemblyBudget (d m A L : ℕ) : ℕ := assemblyBudgetWithBudget d m (2 * m) A L

/-- Full one-point interpolation assembly succeeds, is solver-compatible, and has exactly the
local constraint kernel. Across n points the redundant raw row count can be O(n*supportLength).
The bound is polynomial of absolute degree, with exponential constants only in d,m. -/
theorem assembleWithBudget_refines (D m J A : ℕ) (a y : F) :
    ∃ rs c, assembleWithBudget D d m J A a y = (some rs, c) ∧
      rs = (block ((InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A)).map
          (columnValue d m a y))).1 ∧
      (∀ r ∈ rs, r.1.length =
        (InterpolationSupportMachine.supportSpec
          (InterpolationSupportMachine.parametersWithBudget D d m J A)).length ∧ r.2 = 0) ∧
      (∀ w : ℕ → F, Matrix.PivotSelectionMachine.Satisfies rs w ↔
        localConstraintAt m a y (sourceCombination d
          (InterpolationSupportMachine.supportSpec
            (InterpolationSupportMachine.parametersWithBudget D d m J A)) w) = 0) ∧
      rs.length ≤ columnSize d m * (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A)).length ∧
      c ≤ assemblyBudgetWithBudget d m J A (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A)).length := by
  let vs := InterpolationSupportMachine.supportSpec
    (InterpolationSupportMachine.parametersWithBudget D d m J A)
  let cs := vs.map (columnValue d m a y)
  have h (v : List ℕ) (hv : v ∈ vs) := support_column_refinesWithBudget D m J A a y v hv
  obtain ⟨sc, hs, hsc⟩ := InterpolationSupportMachine.enumerateWithBudget_correct D d m J A
  obtain ⟨cc, hc, hcc⟩ := columns_correct d m (columnBudgetWithBudget d m J A) a y vs
    (columnValue d m a y) (by
      intro v hv
      obtain ⟨c, hc, _, _, _, hb⟩ := h v hv
      exact ⟨c, hc, hb⟩)
  have hw : ∀ col ∈ cs, ∀ t ∈ col, t.2.length = d + 2 := by
    intro col hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact (h v hv).choose_spec.2.2.1
  have hl : ∀ col ∈ cs, col.length ≤ columnSize d m := by
    intro col hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact (h v hv).choose_spec.2.2.2.1
  obtain ⟨hbl, hbc⟩ := block_bounds (columnSize d m) (d + 2) cs hl
    (fun col hc t ht => (hw col hc t ht).le)
  refine ⟨(block cs).1, 32 + sc + cc + (block cs).2, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [assembleWithBudget, hs]
    change (match (columns d m a y vs).1 with
      | none => _
      | some cols => _) = _
    rw [hc]
  · simpa only [cs, List.length_map] using block_shape cs
  · intro w
    rw [block_satisfies_iff cs hw w, combination_localConstraint m a y vs]
    intro v hv
    exact (h v hv).choose_spec.2.1
  · simpa only [cs, List.length_map] using hbl
  · have hlen : cs.length = vs.length := List.length_map _
    rw [hlen] at hbc
    change 32 + sc + cc + (block cs).2 ≤ assemblyBudgetWithBudget d m J A vs.length
    unfold assemblyBudgetWithBudget
    change (block cs).2 ≤
      512 * (d + 4) * (columnSize d m + 1) ^ 2 * (vs.length + 1) ^ 2 at hbc
    omega

/-- Legacy one-point assembly refinement at strict cutoff `2 * m`. -/
theorem assemble_refines (D m A : ℕ) (a y : F) :
    ∃ rs c, assemble D d m A a y = (some rs, c) ∧
      rs = (block ((InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D d m A)).map (columnValue d m a y))).1 ∧
      (∀ r ∈ rs, r.1.length =
        (InterpolationSupportMachine.supportSpec
          (InterpolationSupportMachine.parameters D d m A)).length ∧ r.2 = 0) ∧
      (∀ w : ℕ → F, Matrix.PivotSelectionMachine.Satisfies rs w ↔
        localConstraintAt m a y (sourceCombination d
          (InterpolationSupportMachine.supportSpec
            (InterpolationSupportMachine.parameters D d m A)) w) = 0) ∧
      rs.length ≤ columnSize d m * (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D d m A)).length ∧
      c ≤ assemblyBudget d m A (InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D d m A)).length := by
  simpa [assemble, InterpolationSupportMachine.enumerate,
    InterpolationSupportMachine.parameters, InterpolationSupportMachine.parametersWithBudget,
    assemblyBudget] using
    assembleWithBudget_refines (d := d) D m (2 * m) A a y

/-- Each materialized row consists of exact polynomial coefficients in column order. -/
theorem block_entries (cols : List (DenseColumn F))
    (hw : ∀ c ∈ cols, ∀ t ∈ c, t.2.length = d + 2) (r : Row F) (hr : r ∈ (block cols).1) :
    ∃ q : LocalColumnRewriteMachine.Term F, q.jets.length = d ∧
      r = (cols.map (fun c => coeff (LocalColumnRewriteMachine.exponent d q)
        (LocalColumnRewriteMachine.denseRepresented d c)), 0) := by
  rw [block, rows_result] at hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  rw [frame_result] at hv
  obtain ⟨col, hc, ht⟩ := List.mem_flatMap.mp hv
  obtain ⟨term, ht', hvec⟩ := List.mem_map.mp ht
  obtain ⟨q, rfl, hq⟩ := decode_term term (hw col hc term ht')
  subst v
  refine ⟨q, hq, ?_⟩
  congr 1
  apply List.map_congr_left
  intro c hc
  exact LocalColumnRewriteMachine.coordinate_coeff q hq c (hw c hc)

/-- A row returned by public assembly has the actual localConstraintAt coefficients. -/
theorem assembleWithBudget_entries (D m J A : ℕ) (a y : F) (rs : List (Row F)) (cost : ℕ)
    (hs : assembleWithBudget D d m J A a y = (some rs, cost)) (r : Row F) (hr : r ∈ rs) :
    ∃ q : LocalColumnRewriteMachine.Term F, q.jets.length = d ∧
      r = ((InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parametersWithBudget D d m J A)).map
          (fun v => coeff (LocalColumnRewriteMachine.exponent d q)
            (localConstraintAt m a y (sourceValue d v))), 0) := by
  obtain ⟨out, c, he, hout, _⟩ := assembleWithBudget_refines D m J A a y
  have ho : out = rs := by simpa using congrArg Prod.fst (he.symm.trans hs)
  rw [← ho, hout] at hr
  have hw : ∀ col ∈ (InterpolationSupportMachine.supportSpec
      (InterpolationSupportMachine.parametersWithBudget D d m J A)).map (columnValue d m a y),
      ∀ t ∈ col, t.2.length = d + 2 := by
    intro col hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    exact (support_column_refinesWithBudget D m J A a y v hv).choose_spec.2.2.1
  obtain ⟨q, hq, heq⟩ := block_entries _ hw r hr
  refine ⟨q, hq, ?_⟩
  rw [heq, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact congrArg (coeff (LocalColumnRewriteMachine.exponent d q))
    (support_column_refinesWithBudget D m J A a y v hv).choose_spec.2.1

/-- Legacy row-entry theorem at strict cutoff `2 * m`. -/
theorem assemble_entries (D m A : ℕ) (a y : F) (rs : List (Row F)) (cost : ℕ)
    (hs : assemble D d m A a y = (some rs, cost)) (r : Row F) (hr : r ∈ rs) :
    ∃ q : LocalColumnRewriteMachine.Term F, q.jets.length = d ∧
      r = ((InterpolationSupportMachine.supportSpec
        (InterpolationSupportMachine.parameters D d m A)).map
          (fun v => coeff (LocalColumnRewriteMachine.exponent d q)
            (localConstraintAt m a y (sourceValue d v))), 0) := by
  simpa [InterpolationSupportMachine.parameters,
    InterpolationSupportMachine.parametersWithBudget] using
      assembleWithBudget_entries (d := d) D m (2 * m) A a y rs cost
        (by simpa [assemble] using hs) r hr

end
end ReedSolomon.HiddenDerivative.InterpolationPointBlockMachine
