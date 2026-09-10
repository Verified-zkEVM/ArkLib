/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.IsolatedRoot
public import ArkLib.Data.Polynomial.Rojas.AffineCover
public import ArkLib.Data.Polynomial.UnivariateRepresentation.AffineTranslation
public import ArkLib.Data.Polynomial.UnivariateRepresentation.Point

/-!
# Affine wrapper around a torus univariate-representation backend

The executable wrapper translates a square system through every supplied
scalar chart, calls a supplied torus backend, undoes each chart in the returned
rational maps, and concatenates the results.  The backend remains an explicit
argument: this file does not construct a toric resultant solver.
-/

@[expose] public section

namespace ArkLib.Rojas.AffineSolver

open CPoly CPoly.CMvPolynomial
open ArkLib.UnivariateRepresentation
open ArkLib.Rojas.AffineCover

universe u v

variable {F : Type u} {K : Type v} [Field F] [BEq F] [LawfulBEq F] [Field K]
variable {s : ℕ}

/-- A solver backend consumes one square system and returns raw rational maps. -/
abbrev TorusBackend := List (CMvPolynomial s F) → List (MapData (F := F))

/-- Translate through every chart, run the torus backend, undo the chart in
all returned maps, and concatenate them. -/
def solveAffine (backend : TorusBackend (F := F) (s := s))
    (shifts : List F) (system : Fin s → CMvPolynomial s F) : List (MapData (F := F)) :=
  shifts.flatMap fun c =>
    (backend (List.ofFn fun j => translatePolynomial c (system j))).map
      (inverseTranslateMapData c)

/-- The affine wrapper multiplies a per-system output-count bound by the number of charts.
This counts returned rational maps; it is separate from the backend's arithmetic complexity. -/
theorem solveAffine_length_le (backend : TorusBackend (F := F) (s := s))
    (shifts : List F) (B : ℕ) (hbackend : ∀ system, (backend system).length ≤ B)
    (system : Fin s → CMvPolynomial s F) :
    (solveAffine backend shifts system).length ≤ shifts.length * B := by
  induction shifts with
  | nil => simp [solveAffine]
  | cons c shifts ih =>
    have h := hbackend (List.ofFn fun j => translatePolynomial c (system j))
    simp only [solveAffine, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, one_mul] at *
    omega

/-- Interpret an indexed computable system over a coefficient-field extension. -/
noncomputable def mappedSystem (ι : F →+* K) (system : Fin s → CMvPolynomial s F) :
    Fin s → MvPolynomial (Fin s) K := fun j =>
  (fromCMvPolynomial (system j)).map ι

/-- Correctness contract required of the still-external torus backend. -/
def CoversTorusIsolatedRoots (backend : TorusBackend (F := F) (s := s))
    (ι : F →+* K) : Prop :=
  ∀ (system : Fin s → CMvPolynomial s F) (point : Fin s → K),
    InTorus point →
    (∀ j, (system j).eval₂ ι point = 0) →
    MvPolynomial.HasIsolatingPolynomial.{v, v} (mappedSystem ι system) point →
    ∃ theta output,
      output ∈ backend (List.ofFn system) ∧ output.modulus ≠ 0 ∧
      output.RepresentsPoint ι theta point

/-- A nonsingular root of a square computable system has the generic
polynomial isolation certificate expected by the backend contract. -/
theorem hasIsolatingPolynomial_of_nonsingular
    (ι : F →+* K) (system : Fin s → CMvPolynomial s F) (point : Fin s → K)
    (hroot : ∀ j, (system j).eval₂ ι point = 0)
    (hjacobian : Matrix.det
      (fun j i => (partialDerivative i (system j)).eval₂ ι point) ≠ 0) :
    MvPolynomial.HasIsolatingPolynomial.{v, v} (mappedSystem ι system) point := by
  apply MvPolynomial.hasIsolatingPolynomial_of_jacobian_det_ne_zero
  · intro j
    simpa [mappedSystem, CPoly.eval₂_equiv] using hroot j
  · rw [show (fun j i => MvPolynomial.eval point
        (MvPolynomial.pderiv i (mappedSystem ι system j))) =
      (fun j i => (partialDerivative i (system j)).eval₂ ι point) by
        funext j i
        simp only [mappedSystem]
        rw [MvPolynomial.pderiv_map, ← fromCMvPolynomial_partialDerivative]
        simp [CPoly.eval₂_equiv]]
    exact hjacobian

/-- Undoing a chart converts a represented translated point into the original
point while preserving the eliminant and its nonzero witness. -/
theorem representsPoint_inverseTranslate
    (ι : F →+* K) (c : F) (theta : K) (point : Fin s → K)
    (input : MapData (F := F))
    (hpoint : input.RepresentsPoint ι theta (translatePoint (ι c) point)) :
    (inverseTranslateMapData c input).RepresentsPoint ι theta point := by
  refine ⟨hpoint.1, hpoint.2.1, ?_, ?_⟩
  · simpa using hpoint.2.2.1
  · intro i
    have hi : i.val < input.numerators.length := by
      simpa only [hpoint.2.2.1] using i.isLt
    have hratio := hpoint.2.2.2 i
    have hratio' : input.numerators[i.val].toPoly.eval₂ ι theta /
        input.denominator.toPoly.eval₂ ι theta =
          translatePoint (ι c) point i := by
      simpa [hi] using hratio
    simpa [inverseTranslateMapData, hi, translatePoint] using
      (eval₂_inverseTranslateNumerator ι theta c input.denominator
        input.numerators[i.val] hpoint.2.1).trans
          (congrArg (fun value => value + ι c) hratio')

/-- Conditional affine completeness.  More than `s` distinct shifts move every
nonsingular affine root into a torus chart; a backend covering isolated torus
roots then yields a nonzero raw map representing the original point. -/
theorem solveAffine_covers_nonsingular
    (ι : F →+* K)
    (backend : TorusBackend (F := F) (s := s))
    (hbackend : CoversTorusIsolatedRoots backend ι)
    (shifts : List F) (hnodup : shifts.Nodup) (hlength : s < shifts.length)
    (system : Fin s → CMvPolynomial s F) (point : Fin s → K)
    (hroot : ∀ j, (system j).eval₂ ι point = 0)
    (hjacobian : Matrix.det
      (fun j i => (partialDerivative i (system j)).eval₂ ι point) ≠ 0) :
    ∃ theta output,
      output ∈ solveAffine backend shifts system ∧ output.modulus ≠ 0 ∧
      output.RepresentsPoint ι theta point := by
  obtain ⟨c, hc, htorus⟩ :=
    exists_shift_avoiding_coordinates_extension shifts hnodup hlength ι point
  let translated : Fin s → CMvPolynomial s F := fun j => translatePolynomial c (system j)
  have htranslatedRoot : ∀ j, (translated j).eval₂ ι (translatePoint (ι c) point) = 0 := by
    intro j
    exact (eval₂_translatePolynomial_at_translatePoint ι point c (system j)).trans (hroot j)
  have htranslatedJacobian : Matrix.det
      (fun j i => (partialDerivative i (translated j)).eval₂ ι
        (translatePoint (ι c) point)) ≠ 0 := by
    rw [show (fun j i => (partialDerivative i (translated j)).eval₂ ι
        (translatePoint (ι c) point)) =
      (fun j i => (partialDerivative i (system j)).eval₂ ι point) by
        funext j i
        rw [eval₂_partialDerivative_translatePolynomial]
        simp]
    exact hjacobian
  have hisolated := hasIsolatingPolynomial_of_nonsingular ι translated
    (translatePoint (ι c) point) htranslatedRoot htranslatedJacobian
  obtain ⟨theta, raw, hraw, hrawNonzero, hrepresents⟩ :=
    hbackend translated (translatePoint (ι c) point) htorus htranslatedRoot hisolated
  refine ⟨theta, inverseTranslateMapData c raw, ?_, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    exact ⟨c, hc, List.mem_map.mpr ⟨raw, hraw, rfl⟩⟩
  · simpa using hrawNonzero
  · exact representsPoint_inverseTranslate ι c theta point raw hrepresents

end ArkLib.Rojas.AffineSolver
