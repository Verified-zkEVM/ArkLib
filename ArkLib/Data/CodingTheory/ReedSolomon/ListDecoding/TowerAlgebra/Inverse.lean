/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.ReductionAlgebra

/-!
# Constructive inversion in a bounded-fiber tower

This file implements the finite-dimensional linear-algebra step behind inverse materialization in
`(F[U]/G)[V]/h`. The main operation consumes and returns reduced tower representatives; coordinate
helpers expose its correspondence with finite-dimensional linear algebra.

The algorithm uses the canonical monomial slice `U^i V^j`, forms multiplication by the input on
that slice, and solves the system for `1` by Cramer's rule.  The decoded candidate is reduced back
through `TowerRepresentation.reduceElement` and is accepted only after direct left- and right-hand
multiplication checks in the same quotient representation.  Thus a representation bug in the
linear solve can never manufacture a false inverse.

This implementation is a correctness reference, not an efficient inversion backend: Mathlib
`Matrix.det` expands over permutations, and Cramer's rule evaluates one determinant per coordinate.
Its running time is factorial in `G.natDegree * h.natDegree`; it does not establish the paper's
polynomial-time inversion bound.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Matrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

abbrev CoordinateIndex (G : CPolynomial F)
    (h : CPolynomial (CPolynomial F)) :=
  Fin h.natDegree × Fin G.natDegree

/-- Read the coefficient of `U^i V^j` from a nested polynomial. -/
def coordinate (G : CPolynomial F) (h p : CPolynomial (CPolynomial F))
    (ij : CoordinateIndex G h) : F :=
  (p.coeff ij.1.val).coeff ij.2.val

/-- Re-encode a coordinate vector as a nested computable polynomial. -/
def ofCoordinates (G : CPolynomial F) (h : CPolynomial (CPolynomial F))
    (x : CoordinateIndex G h → F) : CPolynomial (CPolynomial F) :=
  CPolynomial.ofArray <| Array.ofFn fun j : Fin h.natDegree ↦
    CPolynomial.ofArray <| Array.ofFn fun i : Fin G.natDegree ↦ x (j, i)

/-- Decoding and reading a rectangular coordinate vector are inverse operations. -/
@[simp] theorem coordinate_ofCoordinates (G : CPolynomial F)
    (h : CPolynomial (CPolynomial F)) (x : CoordinateIndex G h → F)
    (ij : CoordinateIndex G h) : coordinate G h (ofCoordinates G h x) ij = x ij := by
  simp [coordinate, ofCoordinates, CPolynomial.coeff_ofArray, Array.getD]

/-- Every reduced representative is recovered from its rectangular coordinates. -/
theorem ofCoordinates_coordinate (G : CPolynomial F)
    (h p : CPolynomial (CPolynomial F)) (hp : TowerRepresentation.ElementReduced G h p) :
    ofCoordinates G h (coordinate G h p) = p := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro j
  rw [ofCoordinates, CPolynomial.coeff_ofArray]
  by_cases hj : j < h.natDegree
  · simp only [Array.getD, Array.size_ofFn, hj, ↓reduceDIte,
      Array.getInternal_eq_getElem, Array.getElem_ofFn]
    change CPolynomial.ofArray (Array.ofFn
      (fun i : Fin G.natDegree ↦ coordinate G h p (⟨j, hj⟩, i))) = p.coeff j
    apply CPolynomial.eq_iff_coeff.mpr
    intro i
    rw [CPolynomial.coeff_ofArray]
    by_cases hi : i < G.natDegree
    · simp [Array.getD, hi, coordinate]
    · have hz : (p.coeff j).coeff i = 0 := by
        rw [CPolynomial.coeff_toPoly]
        apply Polynomial.coeff_eq_zero_of_degree_lt
        exact lt_of_lt_of_le (hp.2 j) (le_trans Polynomial.degree_le_natDegree
          (by simpa [CPolynomial.natDegree_toPoly] using (Nat.le_of_not_gt hi)))
      simp [Array.getD, hi, hz]
  · have hz : p.coeff j = 0 := by
      rw [CPolynomial.coeff_toPoly]
      apply Polynomial.coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hp.1 (le_trans Polynomial.degree_le_natDegree
        (by simpa [CPolynomial.natDegree_toPoly] using (Nat.le_of_not_gt hj)))
    simp [Array.getD, hj, hz]

/-- The canonical monomial `U^i V^j` corresponding to one quotient coordinate. -/
def basisElement (G : CPolynomial F) (h : CPolynomial (CPolynomial F))
    (ij : CoordinateIndex G h) : CPolynomial (CPolynomial F) :=
  ofCoordinates G h (fun kl ↦ if kl = ij then 1 else 0)

/-- Coefficient extraction respects addition. -/
@[simp] theorem coordinate_add (G : CPolynomial F)
    (h p q : CPolynomial (CPolynomial F)) :
    coordinate G h (p + q) = coordinate G h p + coordinate G h q := by
  funext ij
  simp [coordinate, CPolynomial.coeff_add]

/-- Coefficient extraction respects multiplication by a base-field constant. -/
@[simp] theorem coordinate_C_mul (G : CPolynomial F)
    (h p : CPolynomial (CPolynomial F)) (a : F) :
    coordinate G h (CPolynomial.C (CPolynomial.C a) * p) = a • coordinate G h p := by
  funext ij
  simp [coordinate, CPolynomial.coeff_C_mul]

omit [BEq F] [LawfulBEq F] in
/-- The scaled Cramer vector solves a nonsingular square system. -/
theorem mulVec_scaled_cramer {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (b : n → F) (hM : M.det ≠ 0) :
    M *ᵥ (fun i ↦ M.det⁻¹ * M.cramer b i) = b := by
  change M *ᵥ (M.det⁻¹ • M.cramer b) = b
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hM, one_smul]

/-- Coefficients commute with finite sums of tower representatives. -/
theorem nested_coeff_sum {ι : Type*} (s : Finset ι)
    (p : ι → CPolynomial (CPolynomial F)) (j i : ℕ) :
    ((∑ k ∈ s, p k).coeff j).coeff i = ∑ k ∈ s, ((p k).coeff j).coeff i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [CPolynomial.coeff_zero]
  | @insert k s hk ih => simp [Finset.sum_insert, hk, CPolynomial.coeff_add, ih]

/-- Decoding is the finite linear combination of rectangular basis elements. -/
theorem ofCoordinates_eq_sum (G : CPolynomial F) (h : CPolynomial (CPolynomial F))
    (x : CoordinateIndex G h → F) :
    ofCoordinates G h x =
      ∑ k : CoordinateIndex G h, CPolynomial.C (CPolynomial.C (x k)) * basisElement G h k := by
  apply CPolynomial.eq_iff_coeff.mpr
  intro j
  apply CPolynomial.eq_iff_coeff.mpr
  intro i
  rw [nested_coeff_sum]
  simp only [CPolynomial.coeff_C_mul]
  by_cases hj : j < h.natDegree
  · by_cases hi : i < G.natDegree
    · simp only [basisElement, ofCoordinates, CPolynomial.coeff_ofArray]
      simp only [Array.getD, Array.size_ofFn, hj, ↓reduceDIte,
        Array.getInternal_eq_getElem, Array.getElem_ofFn, CPolynomial.coeff_ofArray, hi,
        mul_ite, mul_one, mul_zero]
      exact (Fintype.sum_ite_eq _ _).symm
    · simp [basisElement, ofCoordinates, CPolynomial.coeff_ofArray, Array.getD, hj, hi]
  · simp [basisElement, ofCoordinates, CPolynomial.coeff_ofArray, Array.getD, hj,
      CPolynomial.coeff_zero]

/-- A decoded vector lies in the rectangular representative slice. -/
theorem ofCoordinates_elementReduced {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic) (x : CoordinateIndex G h → F) :
    TowerRepresentation.ElementReduced G h (ofCoordinates G h x) := by
  have hGn := ((CPolynomial.monic_toPoly_iff G).mp hG).ne_zero
  have hhn := ((CPolynomial.monic_toPoly_iff h).mp hh).ne_zero
  refine ⟨?_, ?_⟩
  · rw [Polynomial.degree_eq_natDegree hhn, ← CPolynomial.natDegree_toPoly]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro j hj
    rw [← CPolynomial.coeff_toPoly]
    simp [ofCoordinates, CPolynomial.coeff_ofArray, Array.getD, Nat.not_lt.mpr hj]
  · intro j
    rw [Polynomial.degree_eq_natDegree hGn, ← CPolynomial.natDegree_toPoly]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro i hi
    rw [← CPolynomial.coeff_toPoly]
    by_cases hj : j < h.natDegree
    · simp [ofCoordinates, CPolynomial.coeff_ofArray, Array.getD, hj, Nat.not_lt.mpr hi]
    · simp [ofCoordinates, CPolynomial.coeff_ofArray, Array.getD, hj, CPolynomial.coeff_zero]

/-- Reduced representatives are determined by their finite coordinate vector. -/
theorem coordinate_injective_on_reduced (G : CPolynomial F)
    (h p q : CPolynomial (CPolynomial F)) (hp : TowerRepresentation.ElementReduced G h p)
    (hq : TowerRepresentation.ElementReduced G h q) (heq : coordinate G h p = coordinate G h q) :
    p = q := by
  rw [← ofCoordinates_coordinate G h p hp, heq, ofCoordinates_coordinate G h q hq]

/-- Reduction commutes with a finite sum. -/
theorem reduceElement_sum {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic) {ι : Type*} (s : Finset ι)
    (p : ι → CPolynomial (CPolynomial F)) :
    TowerRepresentation.reduceElement G h (∑ k ∈ s, p k) =
      ∑ k ∈ s, TowerRepresentation.reduceElement G h (p k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hz := TowerRepresentation.reduceElement_C_mul hG hh (0 : F) 0
    simpa [CPolynomial.C_zero] using hz
  | @insert k s hk ih =>
    simp [Finset.sum_insert, hk, TowerRepresentation.reduceElement_add hG hh, ih]

/-- Matrix of multiplication by `u`, with every product reduced in the actual tower quotient.
The coordinate interface is exposed for proofs connecting geometric nonvanishing to injectivity. -/
def multiplicationMatrix (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Matrix (CoordinateIndex G h) (CoordinateIndex G h) F :=
  fun row col ↦ coordinate G h
    (TowerRepresentation.reduceElement G h (u * basisElement G h col)) row

/-- The executable matrix acts by actual quotient multiplication. -/
theorem multiplicationMatrix_mulVec {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic)
    (u : CPolynomial (CPolynomial F)) (x : CoordinateIndex G h → F) :
    multiplicationMatrix G h u *ᵥ x =
      coordinate G h (TowerRepresentation.reduceElement G h (u * ofCoordinates G h x)) := by
  rw [ofCoordinates_eq_sum, Finset.mul_sum, reduceElement_sum hG hh]
  funext ij
  simp only [coordinate, nested_coeff_sum, Matrix.mulVec, dotProduct, multiplicationMatrix]
  apply Finset.sum_congr rfl
  intro k _
  rw [show u * (CPolynomial.C (CPolynomial.C (x k)) * basisElement G h k) =
    CPolynomial.C (CPolynomial.C (x k)) * (u * basisElement G h k) by ring,
    TowerRepresentation.reduceElement_C_mul hG hh, CPolynomial.coeff_C_mul,
    CPolynomial.coeff_C_mul]
  exact mul_comm _ _

/-- Coordinates of the quotient unit. -/
def oneCoordinates (G : CPolynomial F) (h : CPolynomial (CPolynomial F)) :
    CoordinateIndex G h → F :=
  coordinate G h (TowerRepresentation.reduceElement G h 1)

/-- Decode the Cramer solution and immediately project it back to the canonical quotient slice. -/
def cramerCandidate (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    CPolynomial (CPolynomial F) :=
  let M := multiplicationMatrix G h u
  let rhs := oneCoordinates G h
  let x : CoordinateIndex G h → F := fun i ↦ M.det⁻¹ * M.cramer rhs i
  TowerRepresentation.reduceElement G h (ofCoordinates G h x)

/-- Direct executable verification that `v` is a two-sided inverse of `u` modulo the tower ideal. -/
def verifiesInverse (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F)) : Bool :=
  (TowerRepresentation.reduceElement G h (u * v) ==
      TowerRepresentation.reduceElement G h 1) &&
    (TowerRepresentation.reduceElement G h (v * u) ==
      TowerRepresentation.reduceElement G h 1)

theorem verifiesInverse_eq_true_iff
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F)) :
    verifiesInverse G h u v = true ↔
      TowerRepresentation.reduceElement G h (u * v) =
          TowerRepresentation.reduceElement G h 1 ∧
        TowerRepresentation.reduceElement G h (v * u) =
          TowerRepresentation.reduceElement G h 1 := by
  simp [verifiesInverse]

/-- Quotient-level unitness stated independently of the inversion algorithm. -/
def IsTowerUnit (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) : Prop :=
  ∃ v : CPolynomial (CPolynomial F),
    TowerRepresentation.reduceElement G h (u * v) =
        TowerRepresentation.reduceElement G h 1 ∧
      TowerRepresentation.reduceElement G h (v * u) =
        TowerRepresentation.reduceElement G h 1

/-- Compute a two-sided inverse representative in `(F[U]/G)[V]/h`.

`none` is an explicit failure signal.  A zero multiplication determinant is rejected immediately;
a nonzero determinant is solved by Cramer's rule, re-encoded, reduced, and finally checked by
actual multiplication in the tower quotient before it is returned. -/
def inverseRepresentative? (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Option (CPolynomial (CPolynomial F)) :=
  let M := multiplicationMatrix G h u
  if M.det == 0 then
    none
  else
    let candidate := cramerCandidate G h u
    if verifiesInverse G h u candidate then some candidate else none

/-- A nonzero multiplication determinant makes the executable inverse succeed. -/
theorem inverseRepresentative?_exists_of_det_ne_zero
    {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hdet : (multiplicationMatrix G h u).det ≠ 0) :
    ∃ v, inverseRepresentative? G h u = some v := by
  let x : CoordinateIndex G h → F := fun i ↦
    (multiplicationMatrix G h u).det⁻¹ * (multiplicationMatrix G h u).cramer
      (oneCoordinates G h) i
  have hc : cramerCandidate G h u = ofCoordinates G h x :=
    TowerRepresentation.reduceElement_eq_self hG hh (ofCoordinates_elementReduced hG hh x)
  have he : TowerRepresentation.reduceElement G h (u * cramerCandidate G h u) =
      TowerRepresentation.reduceElement G h 1 := by
    rw [hc]
    apply coordinate_injective_on_reduced G h _ _
      (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _)
      (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _)
    rw [← multiplicationMatrix_mulVec hG hh]
    exact mulVec_scaled_cramer _ _ hdet
  refine ⟨cramerCandidate G h u, ?_⟩
  have hv : verifiesInverse G h u (cramerCandidate G h u) = true :=
    (verifiesInverse_eq_true_iff _ _ _ _).mpr ⟨he, by simpa [mul_comm] using he⟩
  simp [inverseRepresentative?, hdet, hv]

/-- A reduced factor may be normalized before multiplication without changing the result. -/
theorem reduceElement_mul_reduce_right {G : CPolynomial F} (hG : G.monic)
    {h : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (p q : CPolynomial (CPolynomial F)) :
    TowerRepresentation.reduceElement G h (p * TowerRepresentation.reduceElement G h q) =
      TowerRepresentation.reduceElement G h (p * q) := by
  rw [TowerRepresentation.reduceElement_mul_reduce hG hh p
    (TowerRepresentation.reduceElement G h q),
    TowerRepresentation.reduceElement_reduceElement hG hh hhpos,
    ← TowerRepresentation.reduceElement_mul_reduce hG hh]

/-- Multiplication by a tower unit is injective on canonical representatives. -/
theorem reduced_mul_injective_of_isTowerUnit
    {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hu : IsTowerUnit G h u) {p q : CPolynomial (CPolynomial F)}
    (hp : TowerRepresentation.ElementReduced G h p)
    (hq : TowerRepresentation.ElementReduced G h q)
    (he : TowerRepresentation.reduceElement G h (u * p) =
      TowerRepresentation.reduceElement G h (u * q)) : p = q := by
  obtain ⟨v, _, hv⟩ := hu
  have cancel (a : CPolynomial (CPolynomial F)) :
      TowerRepresentation.reduceElement G h
        (v * TowerRepresentation.reduceElement G h (u * a)) =
      TowerRepresentation.reduceElement G h a := by
    rw [reduceElement_mul_reduce_right hG hh hhpos, ← mul_assoc,
      TowerRepresentation.reduceElement_mul_reduce hG hh (v * u) a, hv,
      ← TowerRepresentation.reduceElement_mul_reduce hG hh, one_mul]
  have he' := congrArg (fun a ↦ TowerRepresentation.reduceElement G h (v * a)) he
  rw [cancel, cancel, TowerRepresentation.reduceElement_eq_self hG hh hp,
    TowerRepresentation.reduceElement_eq_self hG hh hq] at he'
  exact he'

/-- Injectivity of quotient multiplication implies a nonzero multiplication determinant. -/
theorem multiplicationMatrix_det_ne_zero_of_injective
    {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic)
    (hinj : ∀ {p q : CPolynomial (CPolynomial F)},
      TowerRepresentation.ElementReduced G h p → TowerRepresentation.ElementReduced G h q →
      TowerRepresentation.reduceElement G h (u * p) =
        TowerRepresentation.reduceElement G h (u * q) → p = q) :
    (multiplicationMatrix G h u).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y he
  rw [multiplicationMatrix_mulVec hG hh, multiplicationMatrix_mulVec hG hh] at he
  have he' : TowerRepresentation.reduceElement G h (u * ofCoordinates G h x) =
      TowerRepresentation.reduceElement G h (u * ofCoordinates G h y) := by
    by_cases hhpos : 0 < h.natDegree
    · exact coordinate_injective_on_reduced G h _ _
        (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _)
        (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _) he
    · have hz : h.natDegree = 0 := Nat.eq_zero_of_not_pos hhpos
      have hempty : IsEmpty (CoordinateIndex G h) := by
        rw [CoordinateIndex, hz]
        infer_instance
      have hxy : x = y := Subsingleton.elim _ _
      rw [hxy]
  have hxy := hinj (ofCoordinates_elementReduced hG hh x)
    (ofCoordinates_elementReduced hG hh y) he'
  funext ij
  simpa using congrArg (fun p ↦ coordinate G h p ij) hxy

/-- Unitness alone guarantees success of the computed determinant/adjugate inverse. -/
theorem inverseRepresentative?_exists_of_isTowerUnit
    {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hu : IsTowerUnit G h u) : ∃ v, inverseRepresentative? G h u = some v := by
  apply inverseRepresentative?_exists_of_det_ne_zero hG hh hhpos
  apply multiplicationMatrix_det_ne_zero_of_injective hG hh
  exact reduced_mul_injective_of_isTowerUnit hG hh hhpos hu

/-- Every successful result is a left inverse modulo the full tower ideal. -/
theorem inverseRepresentative?_mul_eq_one
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.reduceElement G h (u * v) =
      TowerRepresentation.reduceElement G h 1 := by
  unfold inverseRepresentative? at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · split at hv
    · have hverify :=
        (verifiesInverse_eq_true_iff G h u (cramerCandidate G h u)).mp ‹_›
      simp only [Option.some.injEq] at hv
      subst v
      exact hverify.1
    · simp at hv

/-- Every successful result is a right inverse modulo the full tower ideal. -/
theorem inverseRepresentative?_mul_eq_one_right
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.reduceElement G h (v * u) =
      TowerRepresentation.reduceElement G h 1 := by
  unfold inverseRepresentative? at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · split at hv
    · have hverify :=
        (verifiesInverse_eq_true_iff G h u (cramerCandidate G h u)).mp ‹_›
      simp only [Option.some.injEq] at hv
      subst v
      exact hverify.2
    · simp at hv

/-- Successful computation proves unitness in the independently stated quotient sense. -/
theorem isTowerUnit_of_inverseRepresentative?_eq_some
    (G : CPolynomial F) (h u v : CPolynomial (CPolynomial F))
    (hv : inverseRepresentative? G h u = some v) : IsTowerUnit G h u := by
  exact ⟨v, inverseRepresentative?_mul_eq_one G h u v hv,
    inverseRepresentative?_mul_eq_one_right G h u v hv⟩

/-- Successful inversion always returns a representative in the canonical bounded tower slice. -/
theorem inverseRepresentative?_elementReduced
    {G : CPolynomial F} (hG : G.monic)
    {h u v : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hv : inverseRepresentative? G h u = some v) :
    TowerRepresentation.ElementReduced G h v := by
  unfold inverseRepresentative? at hv
  dsimp only at hv
  split at hv
  · simp at hv
  · split at hv
    · simp only [Option.some.injEq] at hv
      subst v
      exact TowerRepresentation.elementReduced_reduceElement hG hh hhpos _
    · simp at hv

end ReedSolomon.ListDecoding.TowerAlgebra
