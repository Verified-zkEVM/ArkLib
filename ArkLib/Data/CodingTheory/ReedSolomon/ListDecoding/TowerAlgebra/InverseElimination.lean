/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.Inverse
public import ArkLib.Data.Matrix.SquareSolve

/-!
# Tower inversion by executed elimination

This backend uses the existing elimination machine on the rectangular multiplication matrix.
It never evaluates a determinant or enumerates field elements. The canonical product-of-finite
indices is flattened by `finProdFinEquiv`, so indexing is executable as well. Decidable equality
on the field is an explicit computational input, as required by the elimination machine.
The full matrix dimension is `G.natDegree * h.natDegree`; this backend does not claim the sharper
paper bound obtained by doing linear algebra over the base quotient.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Matrix

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Executable flattening of the rectangular monomial coordinates. -/
def coordinateEquiv (G : CPolynomial F) (h : CPolynomial (CPolynomial F)) :
    Fin (h.natDegree * G.natDegree) ≃ CoordinateIndex G h := finProdFinEquiv.symm

/-- The same quotient multiplication matrix, indexed for the elimination machine. -/
def eliminationMatrix (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Matrix (Fin (h.natDegree * G.natDegree)) (Fin (h.natDegree * G.natDegree)) F :=
  (multiplicationMatrix G h u).submatrix (coordinateEquiv G h) (coordinateEquiv G h)

/-- Execute elimination, decode its solution, and verify it in the actual tower quotient. -/
def inverseElimination? (G : CPolynomial F) (h u : CPolynomial (CPolynomial F)) :
    Option (CPolynomial (CPolynomial F)) :=
  match SquareSolve.solve? (eliminationMatrix G h u)
      (oneCoordinates G h ∘ coordinateEquiv G h) with
  | none => none
  | some x =>
      let v := TowerRepresentation.reduceElement G h
        (ofCoordinates G h (x ∘ (coordinateEquiv G h).symm))
      if verifiesInverse G h u v then some v else none

/-- Every returned result satisfies the two quotient inverse equations. -/
theorem inverseElimination?_sound (G : CPolynomial F)
    (h u v : CPolynomial (CPolynomial F)) (hv : inverseElimination? G h u = some v) :
    TowerRepresentation.reduceElement G h (u * v) = TowerRepresentation.reduceElement G h 1 ∧
      TowerRepresentation.reduceElement G h (v * u) = TowerRepresentation.reduceElement G h 1 := by
  unfold inverseElimination? at hv
  split at hv
  · contradiction
  · dsimp only at hv
    split at hv
    · rename_i hverify
      simp only [Option.some.injEq] at hv
      subst v
      exact (verifiesInverse_eq_true_iff _ _ _ _).mp hverify
    · contradiction

/-- Returned elimination inverses are canonical reduced representatives. -/
theorem inverseElimination?_elementReduced {G : CPolynomial F} (hG : G.monic)
    {h u v : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hv : inverseElimination? G h u = some v) : TowerRepresentation.ElementReduced G h v := by
  unfold inverseElimination? at hv
  split at hv
  · contradiction
  · dsimp only at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      subst v
      exact TowerRepresentation.elementReduced_reduceElement hG hh hhpos _
    · contradiction

/-- A successful executable result certifies quotient unitness. -/
theorem isTowerUnit_of_inverseElimination?_eq_some (G : CPolynomial F)
    (h u v : CPolynomial (CPolynomial F)) (hv : inverseElimination? G h u = some v) :
    IsTowerUnit G h u := ⟨v, inverseElimination?_sound G h u v hv⟩

/-- Elimination succeeds whenever the denominator is a quotient unit. -/
theorem inverseElimination?_exists_of_isTowerUnit {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree)
    (hu : IsTowerUnit G h u) : ∃ v, inverseElimination? G h u = some v := by
  have hM : Function.Injective (multiplicationMatrix G h u).mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    exact multiplicationMatrix_det_ne_zero_of_injective hG hh
      (reduced_mul_injective_of_isTowerUnit hG hh hhpos hu)
  have hE : Function.Injective (eliminationMatrix G h u).mulVec := by
    intro x y he
    simp only [eliminationMatrix, Matrix.submatrix_mulVec_equiv] at he
    have he' : (multiplicationMatrix G h u) *ᵥ (x ∘ (coordinateEquiv G h).symm) =
        (multiplicationMatrix G h u) *ᵥ (y ∘ (coordinateEquiv G h).symm) := by
      funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        congrFun he ((coordinateEquiv G h).symm i)
    have hxy := hM he'
    funext i
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun hxy (coordinateEquiv G h i)
  obtain ⟨x, hx, hsolve⟩ := SquareSolve.solve?_success_of_injective
    (eliminationMatrix G h u) (oneCoordinates G h ∘ coordinateEquiv G h) hE
  let p := ofCoordinates G h (x ∘ (coordinateEquiv G h).symm)
  have hp : TowerRepresentation.ElementReduced G h p := ofCoordinates_elementReduced hG hh _
  have hred : TowerRepresentation.reduceElement G h p = p :=
    TowerRepresentation.reduceElement_eq_self hG hh hp
  have hcoord : coordinate G h (TowerRepresentation.reduceElement G h (u * p)) =
      oneCoordinates G h := by
    rw [← multiplicationMatrix_mulVec hG hh]
    simp only [eliminationMatrix, Matrix.submatrix_mulVec_equiv] at hsolve
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      congrFun hsolve ((coordinateEquiv G h).symm i)
  have hone : TowerRepresentation.reduceElement G h (u * p) =
      TowerRepresentation.reduceElement G h 1 :=
    coordinate_injective_on_reduced G h _ _
      (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _)
      (TowerRepresentation.elementReduced_reduceElement hG hh hhpos _) hcoord
  have hverify : verifiesInverse G h u p = true :=
    (verifiesInverse_eq_true_iff _ _ _ _).mpr ⟨hone, by simpa [mul_comm] using hone⟩
  refine ⟨p, ?_⟩
  simp only [inverseElimination?, hx]
  change (if verifiesInverse G h u (TowerRepresentation.reduceElement G h p) then
    some (TowerRepresentation.reduceElement G h p) else none) = some p
  rw [hred, hverify]
  rfl

/-- Under canonical tower hypotheses, failure is exactly nonunitness. -/
theorem inverseElimination?_eq_none_iff {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree) :
    inverseElimination? G h u = none ↔ ¬ IsTowerUnit G h u := by
  constructor
  · intro hnone hu
    obtain ⟨v, hv⟩ := inverseElimination?_exists_of_isTowerUnit hG hh hhpos hu
    rw [hnone] at hv
    contradiction
  · intro hu
    cases he : inverseElimination? G h u with
    | none => rfl
    | some v => exact (hu (isTowerUnit_of_inverseElimination?_eq_some G h u v he)).elim

/-- Executed elimination returns exactly the canonical inverse specified by Cramer's rule. -/
theorem inverseElimination?_eq_inverseRepresentative? {G : CPolynomial F} (hG : G.monic)
    {h u : CPolynomial (CPolynomial F)} (hh : h.monic) (hhpos : 0 < h.natDegree) :
    inverseElimination? G h u = inverseRepresentative? G h u := by
  cases he : inverseElimination? G h u with
  | none =>
    cases hc : inverseRepresentative? G h u with
    | none => rfl
    | some v =>
      obtain ⟨w, hw⟩ := inverseElimination?_exists_of_isTowerUnit hG hh hhpos
        (isTowerUnit_of_inverseRepresentative?_eq_some G h u v hc)
      rw [he] at hw
      contradiction
  | some v =>
    have hu := isTowerUnit_of_inverseElimination?_eq_some G h u v he
    obtain ⟨w, hw⟩ := inverseRepresentative?_exists_of_isTowerUnit hG hh hhpos hu
    rw [hw]
    congr 1
    apply reduced_mul_injective_of_isTowerUnit hG hh hhpos hu
      (inverseElimination?_elementReduced hG hh hhpos he)
      (inverseRepresentative?_elementReduced hG hh hhpos hw)
    exact (inverseElimination?_sound G h u v he).1.trans
      (inverseRepresentative?_mul_eq_one G h u w hw).symm

end ReedSolomon.ListDecoding.TowerAlgebra
