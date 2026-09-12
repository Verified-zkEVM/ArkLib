/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Proofs
public import ArkLib.Data.Matrix.NonzeroKernelCompletion
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Global.Multiplicity
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.ToCompPoly.Multivariate.Eval
public import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
public import CompPoly.Multivariate.Rename

/-!
# Certified interpolation on an arbitrary finite support

This file adapts the existing local interpolation column program and nonzero-kernel machine to a
caller-supplied finite list of monomial exponents. The executed path materializes every local
column and every matrix row, runs homogeneous elimination, and converts the resulting coefficient
vector to a concrete sparse differential equation.

The validity predicate is the truth of an executable Boolean check: vector widths, duplicate
freedom, the paper's specialization-degree budget, positive multiplicity, and a strict comparison
between the actual materialized row count and the support length. No kernel vector or vanishing
equation is supplied by the caller.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Explainer

open Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

abbrev Row (F : Type*) := Matrix.PivotSelectionMachine.Row F

/-- Runtime data for a prescribed interpolation support. Each vector is ordered as
`[X,Y₀,...,Y_d]`; `multiplicity` is the local contact order. -/
structure Support where
  vectors : List (List ℕ)
  multiplicity : ℕ
  deriving DecidableEq, Repr

/-- Execute all local interpolation columns for one received point and allocate the resulting
homogeneous row block. Invalid exponent-vector widths make column execution fail. -/
def pointRows {F : Type*} [CommRing F] (d : ℕ) (support : Support) (point : F × F) :
    Option (List (Row F)) :=
  match (InterpolationPointBlockMachine.columns d support.multiplicity
      point.1 point.2 support.vectors).1 with
  | none => none
  | some columns => some (InterpolationPointBlockMachine.block columns).1

/-- Execute and concatenate the actual local row blocks for all received points. -/
def matrixRows {F : Type*} [CommRing F] (d : ℕ) (support : Support) :
    List (F × F) → Option (List (Row F))
  | [] => some []
  | point :: points => do
      let head ← pointRows d support point
      let tail ← matrixRows d support points
      pure (head ++ tail)

/-- The actual number of rows materialized by the arbitrary-support interpolation program.
Assembly failure has row count zero; `Valid` separately proves that failure is impossible. -/
def rowCount {F : Type*} [CommRing F] (d : ℕ) (support : Support)
    (received : List (F × F)) : ℕ :=
  ((matrixRows d support received).getD []).length

/-- Finite matrix represented by a materialized homogeneous row list. Missing entries are zero;
rectangularity in `Valid` proves that every required entry is present. -/
def rowMatrix {F : Type*} [Zero F] (columns : ℕ) (rows : List (Row F)) :
    Matrix (Fin rows.length) (Fin columns) F :=
  fun i j => rows[i].1.getD j.val 0

/-- The actual materialized interpolation map used in the checked dimension margin. -/
def constraintMap {F : Type*} [Field F] (d : ℕ) (support : Support)
    (received : List (F × F)) :
    (Fin support.vectors.length → F) →ₗ[F]
      (Fin (rowCount d support received) → F) :=
  (rowMatrix support.vectors.length ((matrixRows d support received).getD [])).mulVecLin

/-- Executable form of the exact `(1,D,D-1,...,D-d)` interpolation weight for a dense
fixed-width exponent vector. -/
def denseInterpolationWeight (d D : ℕ) (v : List ℕ) : ℕ :=
  v.getD 0 0 + ∑ j : Fin (d + 1), (D - j.val) * v.getD (j.val + 1) 0

/-- Executable total degree in the dense jet coordinates `Y₀,…,Y_d`. -/
def denseJetDegree (d : ℕ) (v : List ℕ) : ℕ :=
  ∑ j : Fin (d + 1), v.getD (j.val + 1) 0

/-- The executable dense weight agrees with the semantic differential-monomial weight. -/
theorem denseInterpolationWeight_eq (d D : ℕ) (v : List ℕ) :
    denseInterpolationWeight d D v =
      exactInterpolationMonomialWeight D (NonzeroInterpolationMachine.exponent d v) := by
  classical
  rw [exactInterpolationMonomialWeight_eq]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [denseInterpolationWeight, NonzeroInterpolationMachine.exponent_none,
    NonzeroInterpolationMachine.exponent_some, mul_comm]

/-- The executable dense jet degree agrees with the semantic finitely-supported degree. -/
theorem denseJetDegree_eq (d : ℕ) (v : List ℕ) :
    denseJetDegree d v =
      totalJetDegree (NonzeroInterpolationMachine.exponent d v) := by
  classical
  rw [totalJetDegree, Finsupp.degree_eq_sum]
  simp [denseJetDegree, NonzeroInterpolationMachine.exponent_some]

/-- Proposition exposed by the executable support check. -/
def Conditions {F : Type*} [Field F] (d D A : ℕ) (support : Support)
    (received : List (F × F)) : Prop :=
  0 < support.multiplicity ∧
    support.vectors.Nodup ∧
    (∀ v ∈ support.vectors, v.length = d + 2) ∧
    (∀ v ∈ support.vectors,
      denseInterpolationWeight d D v < support.multiplicity * A) ∧
    rowCount d support received < support.vectors.length

/-- Execute every finite support and dimension check used by arbitrary-support interpolation. -/
def check {F : Type*} [Field F] (d D A : ℕ) (support : Support)
    (received : List (F × F)) : Bool :=
  decide (0 < support.multiplicity) &&
    decide support.vectors.Nodup &&
    (support.vectors.all fun v =>
      decide (v.length = d + 2) &&
        decide (denseInterpolationWeight d D v < support.multiplicity * A)) &&
    decide (rowCount d support received < support.vectors.length)

/-- A valid support certificate is exactly one accepted by the finite runtime check. -/
def Valid {F : Type*} [Field F] (d D A : ℕ) (support : Support)
    (received : List (F × F)) : Prop :=
  check d D A support received = true

/-- Logical characterization of the executable support check. -/
theorem check_eq_true_iff {F : Type*} [Field F] (d D A : ℕ) (support : Support)
    (received : List (F × F)) :
    check d D A support received = true ↔ Conditions d D A support received := by
  simp only [check, Conditions, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  aesop

/-- Concrete output of the support explainer. The coefficients and chosen unit coordinate expose
the executed nonzero-kernel result; `equation` is the canonical computable polynomial consumed by
the decoder. -/
structure Result (F : Type*) [Zero F] (d : ℕ) where
  chosen : ℕ
  coefficients : List F
  equation : CPoly.CMvPolynomial (d + 2) F

/-- Convert one dense exponent vector to the fixed-width CompPoly monomial used by the symbolic
decoder. -/
def concreteMonomial (d : ℕ) (v : List ℕ) : CPoly.CMvMonomial (d + 2) :=
  Vector.ofFn fun i => v.getD i.val 0

/-- Executable conversion of a support-ordered coefficient vector to a concrete sparse
multivariate polynomial. Width mismatch is rejected. -/
def concreteCombination {F : Type*} [Field F] [DecidableEq F] (d : ℕ) :
    List (List ℕ) → List F → Option (CPoly.CMvPolynomial (d + 2) F)
  | [], [] => some 0
  | v :: vs, c :: cs => do
      let tail ← concreteCombination d vs cs
      pure (CPoly.CMvPolynomial.monomial (concreteMonomial d v) c + tail)
  | _, _ => none

/-- Execute the actual arbitrary-support interpolation matrix, the total nonzero-kernel solver,
and concrete sparse-equation materialization. Every failure is explicit. -/
def construct? {F : Type*} [Field F] [DecidableEq F] (d D A : ℕ) (support : Support)
    (received : List (F × F)) : Option (Result F d) :=
  if check d D A support received then
    match matrixRows d support received with
    | none => none
    | some rows =>
        match (Matrix.NonzeroKernelMachine.runFuel support.vectors.length
          (Matrix.NonzeroKernelMachine.budget rows.length support.vectors.length)
          (.check rows rows)).1 with
        | .done chosen coefficients =>
            (concreteCombination d support.vectors coefficients).map fun equation =>
              ⟨chosen, coefficients, equation⟩
        | _ => none
  else none

section Semantics

variable {F : Type*} [Field F] [DecidableEq F] {d D A : ℕ}

omit [DecidableEq F] in
private theorem columns_refines_vectors (multiplicity : ℕ) (vectors : List (List ℕ))
    (point : F × F) (hwidth : ∀ v ∈ vectors, v.length = d + 2) :
    ∃ cost,
      InterpolationPointBlockMachine.columns d multiplicity point.1 point.2 vectors =
        (some (vectors.map
          (InterpolationPointBlockMachine.columnValue d multiplicity point.1 point.2)),
          cost) ∧
      (∀ v ∈ vectors,
        LocalColumnRewriteMachine.denseRepresented d
            (InterpolationPointBlockMachine.columnValue d multiplicity point.1 point.2 v) =
          localConstraintAt multiplicity point.1 point.2
            (InterpolationPointBlockMachine.sourceValue d v)) ∧
      ∀ column ∈ vectors.map
          (InterpolationPointBlockMachine.columnValue d multiplicity point.1 point.2),
        ∀ term ∈ column, term.2.length = d + 2 := by
  induction vectors with
  | nil => exact ⟨32, rfl, by simp, by simp⟩
  | cons v vectors ih =>
      have hv := hwidth v (by simp only [List.mem_cons, true_or])
      obtain ⟨x, b, xs, rfl⟩ : ∃ x b xs, v = x :: b :: xs := by
        cases v with
        | nil => simp at hv
        | cons x v =>
            cases v with
            | nil => simp at hv
            | cons b xs => exact ⟨x, b, xs, rfl⟩
      have hx : xs.length = d := by simpa using hv
      obtain ⟨headCost, hhead, hsem, hterms, _⟩ :=
        InterpolationPointBlockMachine.makeColumn_refines multiplicity point.1 point.2
          x b xs hx
      obtain ⟨tailCost, htail, htailSem, htailTerms⟩ :=
        ih (fun u hu => hwidth u (List.mem_cons_of_mem _ hu))
      refine ⟨32 + headCost + tailCost, ?_, ?_, ?_⟩
      · simp [InterpolationPointBlockMachine.columns, hhead, htail]
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hsem
        · exact htailSem u hu
      · intro column hc term ht
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hterms term ht
        · exact htailTerms column hc term ht

omit [DecidableEq F] in
/-- Valid support widths make every local block execute, with exact homogeneous semantics. -/
theorem pointRows_refines (support : Support) (point : F × F)
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2) :
    ∃ rows, pointRows d support point = some rows ∧
      (∀ row ∈ rows, row.1.length = support.vectors.length ∧ row.2 = 0) ∧
      ∀ coefficients : ℕ → F,
        Matrix.PivotSelectionMachine.Satisfies rows coefficients ↔
          localConstraintAt support.multiplicity point.1 point.2
            (InterpolationPointBlockMachine.sourceCombination d support.vectors coefficients) =
                0 := by
  classical
  obtain ⟨cost, hcolumns, hsem, hterms⟩ :=
    columns_refines_vectors support.multiplicity support.vectors point hwidth
  let columns := support.vectors.map
    (InterpolationPointBlockMachine.columnValue d support.multiplicity point.1 point.2)
  refine ⟨(InterpolationPointBlockMachine.block columns).1, ?_, ?_, ?_⟩
  · simp [pointRows, hcolumns, columns]
  · simpa only [columns, List.length_map] using
      InterpolationPointBlockMachine.block_shape columns
  · intro coefficients
    rw [InterpolationPointBlockMachine.block_satisfies_iff columns hterms coefficients]
    rw [InterpolationPointBlockMachine.combination_localConstraint
      support.multiplicity point.1 point.2 support.vectors hsem coefficients]

omit [DecidableEq F] in
/-- Valid widths make the complete arbitrary-support matrix execute. Its rows are rectangular and
its kernel is exactly simultaneous local contact at every supplied point. -/
theorem matrixRows_refines (support : Support) (received : List (F × F))
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2) :
    ∃ rows, matrixRows d support received = some rows ∧
      rows.length = rowCount d support received ∧
      (∀ row ∈ rows, row.1.length = support.vectors.length ∧ row.2 = 0) ∧
      ∀ coefficients : ℕ → F,
        Matrix.PivotSelectionMachine.Satisfies rows coefficients ↔
          ∀ point ∈ received,
            localConstraintAt support.multiplicity point.1 point.2
              (InterpolationPointBlockMachine.sourceCombination d support.vectors coefficients) =
                0 := by
  classical
  induction received with
  | nil =>
      refine ⟨[], rfl, ?_, by simp, ?_⟩
      · rw [rowCount, matrixRows]
        rfl
      intro coefficients
      simp [Matrix.PivotSelectionMachine.Satisfies]
  | cons point received ih =>
      obtain ⟨head, hhead, hheadShape, hheadKernel⟩ :=
        pointRows_refines support point hwidth
      obtain ⟨tail, htail, htailCount, htailShape, htailKernel⟩ := ih
      refine ⟨head ++ tail, by simp [matrixRows, hhead, htail], ?_, ?_, ?_⟩
      · rw [rowCount, matrixRows, hhead, htail]
        simp
      · intro row hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hheadShape row hr
        · exact htailShape row hr
      · intro coefficients
        have happend : Matrix.PivotSelectionMachine.Satisfies (head ++ tail) coefficients ↔
            Matrix.PivotSelectionMachine.Satisfies head coefficients ∧
              Matrix.PivotSelectionMachine.Satisfies tail coefficients := by
          constructor
          · intro h
            exact ⟨fun row hr => h row (List.mem_append_left _ hr),
              fun row hr => h row (List.mem_append_right _ hr)⟩
          · rintro ⟨hh, ht⟩ row hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hh row hr
            · exact ht row hr
        rw [happend, hheadKernel, htailKernel]
        simp only [List.forall_mem_cons]

/-- Distinct fixed-width vectors denote distinct source monomials. -/
theorem exponent_nodup (support : Support)
    (hnodup : support.vectors.Nodup)
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2) :
    (support.vectors.map (NonzeroInterpolationMachine.exponent d)).Nodup := by
  apply List.Nodup.map_on _ hnodup
  intro v hv u hu he
  exact NonzeroInterpolationMachine.exponent_injective v u (hwidth v hv) (hwidth u hu) he

omit [DecidableEq F] in
/-- The arbitrary-support source combination is the corresponding ordered monomial sum. -/
theorem sourceCombination_eq (support : Support)
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2) (coefficients : ℕ → F) :
    InterpolationPointBlockMachine.sourceCombination d support.vectors coefficients =
      NonzeroInterpolationMachine.monomialCombination
        (support.vectors.map (NonzeroInterpolationMachine.exponent d)) coefficients := by
  unfold InterpolationPointBlockMachine.sourceCombination
    NonzeroInterpolationMachine.monomialCombination
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact NonzeroInterpolationMachine.sourceValue_eq_monomial v (hwidth v hv)

omit [DecidableEq F] in
/-- A unit chosen coordinate in a distinct support produces a nonzero source equation. -/
theorem sourceCombination_ne_zero (support : Support)
    (hnodup : support.vectors.Nodup)
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2)
    (coefficients : List F) (chosen : ℕ) (hchosen : chosen < support.vectors.length)
    (hunit : coefficients.getD chosen 0 = 1) :
    InterpolationPointBlockMachine.sourceCombination d support.vectors
      (fun i => coefficients.getD i 0) ≠ 0 := by
  classical
  rw [sourceCombination_eq support hwidth]
  apply (NonzeroInterpolationMachine.combination_ne_zero_iff _
    (exponent_nodup support hnodup hwidth) _).mpr
  exact ⟨chosen, by simpa, by rw [hunit]; exact one_ne_zero⟩

omit [DecidableEq F] in
/-- Every source monomial obeying the checked support budget yields the same bound for the
constructed equation. -/
theorem sourceCombination_weightedDegree_lt (support : Support)
    (hwidth : ∀ v ∈ support.vectors, v.length = d + 2)
    (hweight : ∀ v ∈ support.vectors,
      exactInterpolationMonomialWeight D (NonzeroInterpolationMachine.exponent d v) <
        support.multiplicity * A)
    (hpositive : 0 < support.multiplicity * A)
    (coefficients : ℕ → F) :
    differentialWeightedDegree D
        (InterpolationPointBlockMachine.sourceCombination d support.vectors coefficients) <
      support.multiplicity * A := by
  classical
  rw [sourceCombination_eq support hwidth]
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree,
    Finset.sup_lt_iff hpositive]
  intro exponent hexponent
  obtain ⟨v, hv, he⟩ := List.mem_map.mp
    (NonzeroInterpolationMachine.combination_support _ coefficients exponent hexponent)
  rw [← he]
  simpa [exactInterpolationMonomialWeight] using hweight v hv

private theorem finToJetVariable_injective (d : ℕ) :
    Function.Injective (finToJetVariable d) := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j hij => ?_) j
    simp [finToJetVariable] at hij
  · refine Fin.cases (fun hij => ?_) (fun j hij => ?_) j
    · simp [finToJetVariable] at hij
    · exact congrArg Fin.succ (Option.some.inj hij)

/-- The concrete fixed-width monomial carries exactly the arbitrary support exponent. -/
theorem concreteMonomial_exponent (v : List ℕ) :
    Finsupp.mapDomain (finToJetVariable d)
        (CPoly.CMvMonomial.toFinsupp (concreteMonomial d v)) =
      NonzeroInterpolationMachine.exponent d v := by
  apply Finsupp.ext
  intro z
  cases z with
  | none =>
      rw [← show finToJetVariable d (0 : Fin (d + 2)) = none by rfl,
        Finsupp.mapDomain_apply (finToJetVariable_injective d)]
      rw [CPoly.toFinsupp_apply]
      rw [concreteMonomial, Vector.get_ofFn]
      change v.getD 0 0 = NonzeroInterpolationMachine.exponent d v none
      exact (NonzeroInterpolationMachine.exponent_none v).symm
  | some j =>
      rw [← show finToJetVariable d j.succ = some j by rfl,
        Finsupp.mapDomain_apply (finToJetVariable_injective d)]
      rw [CPoly.toFinsupp_apply]
      rw [concreteMonomial, Vector.get_ofFn]
      change v.getD (j.val + 1) 0 = NonzeroInterpolationMachine.exponent d v (some j)
      exact (NonzeroInterpolationMachine.exponent_some v j).symm

/-- Executable conversion to CompPoly preserves the exact differential source equation. -/
theorem concreteCombination_refines (vectors : List (List ℕ)) (coefficients : List F)
    (hcoefficients : coefficients.length = vectors.length)
    (hwidth : ∀ v ∈ vectors, v.length = d + 2) :
    ∃ equation, concreteCombination d vectors coefficients = some equation ∧
      semanticEquation equation =
        InterpolationPointBlockMachine.sourceCombination d vectors
          (fun i => coefficients.getD i 0) := by
  induction vectors generalizing coefficients with
  | nil =>
      cases coefficients <;>
        simp_all [concreteCombination, semanticEquation,
          InterpolationPointBlockMachine.sourceCombination,
          InterpolationPointBlockMachine.combine]
  | cons v vectors ih =>
      cases coefficients with
      | nil => simp at hcoefficients
      | cons c coefficients =>
          have htail : coefficients.length = vectors.length := by simpa using hcoefficients
          obtain ⟨tail, hrun, hsem⟩ := ih coefficients htail
            (fun u hu => hwidth u (List.mem_cons_of_mem v hu))
          refine ⟨CPoly.CMvPolynomial.monomial (concreteMonomial d v) c + tail, ?_, ?_⟩
          · simp [concreteCombination, hrun]
          · simp only [semanticEquation, CPoly.CMvPolynomial.fromCMvPolynomial_add',
              map_add, CPoly.CMvPolynomial.fromCMvPolynomial_monomial,
              MvPolynomial.rename_monomial, concreteMonomial_exponent]
            change MvPolynomial.monomial (NonzeroInterpolationMachine.exponent d v) c +
                semanticEquation tail =
              c • InterpolationPointBlockMachine.sourceValue d v +
                InterpolationPointBlockMachine.sourceCombination d vectors
                  (fun i => coefficients.getD i 0)
            rw [hsem, NonzeroInterpolationMachine.sourceValue_eq_monomial v
              (hwidth v (by simp))]
            rw [Algebra.smul_def, MvPolynomial.algebraMap_eq,
              MvPolynomial.C_mul_monomial, mul_one]

omit [DecidableEq F] in
/-- Any rectangular homogeneous system with fewer rows than columns has a nonzero solution.
This is the dimension argument consumed by the executable kernel extractor. -/
theorem exists_nonzero_satisfies_of_rank_lt (n : ℕ) (rows : List (Row F))
    (hshape : ∀ row ∈ rows, row.1.length = n ∧ row.2 = 0)
    (hrank : Module.finrank F (rowMatrix n rows).mulVecLin.range < n) :
    ∃ coefficients : ℕ → F,
      Matrix.PivotSelectionMachine.Satisfies rows coefficients ∧
        ∃ i < n, coefficients i ≠ 0 := by
  classical
  let matrix := rowMatrix (F := F) n rows
  have hrows : rows = List.ofFn (fun i => (List.ofFn (matrix i), (0 : F))) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hs := hshape rows[i] (List.getElem_mem hi)
      apply Prod.ext
      · apply List.ext_getElem
        · simpa using hs.1
        · intro j hj hj'
          simp only [List.getElem_ofFn]
          change rows[i].1[j] = rows[i].1.getD j 0
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          rfl
      · simpa using hs.2
  have hnullity := matrix.mulVecLin.finrank_range_add_finrank_ker
  change Module.finrank F matrix.mulVecLin.range < n at hrank
  have hkerPositive : 0 < Module.finrank F (LinearMap.ker matrix.mulVecLin) := by
    have hnullity' : Module.finrank F matrix.mulVecLin.range +
        Module.finrank F matrix.mulVecLin.ker = n := by
      simpa only [Module.finrank_fin_fun] using hnullity
    omega
  have hker : LinearMap.ker matrix.mulVecLin ≠ ⊥ := by
    intro hzero
    rw [hzero] at hkerPositive
    simp at hkerPositive
  obtain ⟨x, hxker, hxzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let coefficients : ℕ → F := fun i => if hi : i < n then x ⟨i, hi⟩ else 0
  refine ⟨coefficients, ?_, ?_⟩
  · rw [hrows, Matrix.PivotSelectionMachine.satisfies_ofFn]
    have hx : Matrix.mulVec matrix x = 0 := LinearMap.mem_ker.mp hxker
    convert hx using 1
    · funext i
      simp [coefficients]
    · rfl
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxzero
    refine ⟨i.val, i.isLt, ?_⟩
    simpa [coefficients, i.isLt] using hi

/-- Complete semantic certificate for the actually extracted arbitrary-support equation. -/
def Certified (D A : ℕ) (support : Support) (received : List (F × F))
    (result : Result F d) : Prop :=
  result.coefficients.length = support.vectors.length ∧
    result.chosen < result.coefficients.length ∧
    result.coefficients.getD result.chosen 0 = 1 ∧
    semanticEquation result.equation =
      InterpolationPointBlockMachine.sourceCombination d support.vectors
        (fun i => result.coefficients.getD i 0) ∧
    semanticEquation result.equation ≠ 0 ∧
    differentialWeightedDegree D (semanticEquation result.equation) < support.multiplicity * A ∧
    ∀ point ∈ received,
      localConstraintAt support.multiplicity point.1 point.2
        (semanticEquation result.equation) = 0

/-- A valid strict dimension margin forces the actual kernel machine and concrete equation
materializer to succeed. No kernel vector or coverage statement is an input. -/
theorem construct?_success (support : Support) (received : List (F × F))
    (hvalid : Valid (F := F) d D A support received) :
    ∃ result, construct? (F := F) d D A support received = some result ∧
      Certified D A support received result := by
  have hconditions := (check_eq_true_iff d D A support received).mp hvalid
  rcases hconditions with ⟨hm, hnodup, hwidth, hweight, hmargin⟩
  have hweightSemantic : ∀ v ∈ support.vectors,
      exactInterpolationMonomialWeight D (NonzeroInterpolationMachine.exponent d v) <
        support.multiplicity * A := by
    intro v hv
    rw [← denseInterpolationWeight_eq]
    exact hweight v hv
  obtain ⟨rows, hrows, hcount, hshape, hkernel⟩ :=
    matrixRows_refines support received hwidth
  have hrank : Module.finrank F (rowMatrix support.vectors.length rows).mulVecLin.range <
      support.vectors.length := by
    have hrange : Module.finrank F
        (rowMatrix support.vectors.length rows).mulVecLin.range ≤ rows.length := by
      simpa only [Module.finrank_fin_fun] using
        (rowMatrix support.vectors.length rows).mulVecLin.range.finrank_le
    apply hrange.trans_lt
    rwa [hcount]
  have hrect : Matrix.ForwardEchelonMachine.Rectangular support.vectors.length rows :=
    fun row hr => (hshape row hr).1
  have hhomogeneous : ∀ row ∈ rows, row.2 = 0 := fun row hr => (hshape row hr).2
  obtain ⟨witness, hwitness, hwitnessNonzero⟩ :=
    exists_nonzero_satisfies_of_rank_lt support.vectors.length rows hshape hrank
  obtain ⟨chosen, coefficients, cost, hsolve, hcoefficients, hchosen, hunit,
      hsatisfies, _⟩ :=
    Matrix.NonzeroKernelMachine.evaluation_runFuel support.vectors.length rows hrect
      hhomogeneous ⟨witness, hwitness, hwitnessNonzero⟩
  obtain ⟨equation, hequation, hsemantic⟩ :=
    concreteCombination_refines support.vectors coefficients hcoefficients hwidth
  let result : Result F d := ⟨chosen, coefficients, equation⟩
  have hsourceNonzero :
      InterpolationPointBlockMachine.sourceCombination d support.vectors
        (fun i => coefficients.getD i 0) ≠ 0 :=
    sourceCombination_ne_zero support hnodup hwidth coefficients chosen
      (by simpa [hcoefficients] using hchosen) hunit
  have hpositive : 0 < support.multiplicity * A := by
    obtain ⟨i, hi, _⟩ := hwitnessNonzero
    have hv := hweightSemantic support.vectors[i] (List.getElem_mem hi)
    omega
  have hdegree := sourceCombination_weightedDegree_lt support hwidth hweightSemantic hpositive
    (fun i => coefficients.getD i 0)
  refine ⟨result, ?_, hcoefficients, by simpa [result, hcoefficients] using hchosen,
    hunit, hsemantic, ?_, ?_, ?_⟩
  · change check d D A support received = true at hvalid
    unfold construct?
    rw [if_pos hvalid]
    simp only [hrows]
    have hsolveFst := congrArg Prod.fst hsolve
    simp only at hsolveFst
    rw [hsolveFst]
    simp only
    rw [hequation]
    rfl
  · rw [hsemantic]
    exact hsourceNonzero
  · rw [hsemantic]
    exact hdegree
  · intro point hp
    rw [hsemantic]
    exact (hkernel _).mp hsatisfies point hp

/-- The finite received-point list associated with an ordinary Reed--Solomon input. -/
def receivedPoints {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) : List (F × F) :=
  List.ofFn fun i => (domain i, received i)

/-- Every degree-bounded message meeting the agreement threshold is annihilated by a certified
arbitrary-support equation. -/
theorem Certified.vanishes_of_agreements {n : ℕ} (support : Support)
    (domain : Fin n ↪ F) (received : Fin n → F) (result : Result F d)
    (hcertified : Certified D A support (receivedPoints domain received) result)
    (P : F[X]) (hdegree : P.natDegree ≤ D)
    (hagreement : A ≤ (polynomialAgreementSet domain received P).card) :
    differentialSpecialization (semanticEquation result.equation) P = 0 := by
  let indices := polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_global_multiplicity domain indices
    support.multiplicity A (semanticEquation result.equation) P
  · exact domain.injective.injOn
  · exact hagreement
  · intro i hi
    apply X_sub_C_pow_dvd_differentialSpecialization_of_contact
      (semanticEquation result.equation) P (domain i) (received i)
    · simpa [indices, polynomialAgreementSet] using hi
    · exact hcertified.2.2.2.2.2.2 (domain i, received i) (by
        simp [receivedPoints])
  · exact (natDegree_differentialSpecialization_le
      (semanticEquation result.equation) P hdegree).trans_lt
        hcertified.2.2.2.2.2.1

end Semantics

end ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Explainer
