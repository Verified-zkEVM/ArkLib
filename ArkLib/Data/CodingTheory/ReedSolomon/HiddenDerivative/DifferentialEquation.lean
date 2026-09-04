/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationSpace
import ArkLib.Data.MvPolynomial.WeightedDegree
import ArkLib.ToMathlib.MvPolynomial.PDeriv
import ArkLib.ToMathlib.Polynomial.HasseTaylor

/-!
# Polynomial differential equations in finite Hasse jets

This file defines the root-finding interface for a polynomial relation in `X` and the finite
Hasse jet `Y₀, ..., Y_d`. It separates three operations that later root-counting proofs must not
conflate:

* `differentialSpecialization` substitutes a genuine polynomial and its Hasse derivatives;
* `jetEvaluation` evaluates the formal variables at one scalar jet;
* `separant` formally differentiates in a selected jet variable.

The derivative order uses `JetVariable d = Option (Fin (d + 1))` from the interpolation layer:
`none` denotes `X`, while `some j` denotes `Y_j`. The root-finding characteristic conditions are
packaged separately from cardinality conditions because passing to a larger extension field does
not increase the characteristic.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15]
-/

namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-! ### Differential specialization and scalar jets -/

/-- Substitute `X`, a polynomial `P`, and its Hasse derivatives into a differential polynomial. -/
def differentialSpecialization [CommSemiring F] (Q : DifferentialPolynomial F d) (P : F[X]) :
    F[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun v ↦ match v with
      | none => Polynomial.X
      | some j => Polynomial.hasseDeriv j P) Q

@[simp]
theorem differentialSpecialization_C [CommSemiring F] (a : F) (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.C a) P = Polynomial.C a := by
  simp [differentialSpecialization]

@[simp]
theorem differentialSpecialization_x [CommSemiring F] (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.X none) P = Polynomial.X := by
  simp [differentialSpecialization]

@[simp]
theorem differentialSpecialization_jet [CommSemiring F] (j : Fin (d + 1)) (P : F[X]) :
    differentialSpecialization (MvPolynomial.X (some j)) P = Polynomial.hasseDeriv j P := by
  simp [differentialSpecialization]

/-- Evaluate a differential polynomial at a base point and a formal Hasse jet. -/
def jetEvaluation [CommSemiring F] (Q : DifferentialPolynomial F d) (a : F)
    (jet : Fin (d + 1) → F) : F :=
  MvPolynomial.eval (fun v ↦ match v with
    | none => a
    | some j => jet j) Q

/-- The scalar Hasse jet of `P` at `a`, through order `d`. -/
def polynomialJet [Semiring F] (a : F) (P : F[X]) : Fin (d + 1) → F :=
  Polynomial.hasseJet (d + 1) a P

/-- Evaluating a differential specialization at `a` is evaluation on the Hasse jet of `P` at
`a`. -/
theorem eval_differentialSpecialization [CommSemiring F] (Q : DifferentialPolynomial F d)
    (P : F[X]) (a : F) :
    (differentialSpecialization Q P).eval a = jetEvaluation Q a (polynomialJet a P) := by
  rw [differentialSpecialization, jetEvaluation]
  change Polynomial.evalRingHom a
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun v ↦ match v with
          | none => Polynomial.X
          | some j => Polynomial.hasseDeriv j P) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  change MvPolynomial.eval₂Hom _ _ Q = MvPolynomial.eval₂Hom (RingHom.id F) _ Q
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp
  · funext v
    cases v with
    | none => simp
    | some j => rfl
  · rfl

/-! ### Bounded-degree solutions -/

/-- A polynomial of degree at most `D` satisfying the differential equation `Q = 0`.

The degree bound is represented by `Polynomial.degreeLT F (D + 1)`, so it includes the zero
polynomial without a separate convention. -/
def BoundedSolution [CommSemiring F] (Q : DifferentialPolynomial F d) (D : ℕ) :=
  {P : Polynomial.degreeLT F (D + 1) // differentialSpecialization Q P = 0}

/-- The polynomial underlying a bounded differential solution. -/
def BoundedSolution.polynomial [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : F[X] :=
  P.1

@[simp]
theorem BoundedSolution.equation [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : differentialSpecialization Q P.polynomial = 0 :=
  P.2

theorem BoundedSolution.degree_le [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : P.polynomial.degree ≤ D := by
  have hmem : P.polynomial ∈ Polynomial.degreeLE F D := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact P.1.2
  exact Polynomial.mem_degreeLE.mp hmem

/-! ### Active variables, separants, and regular jets -/

/-- The individual degree in the formal Hasse variable `Y_j`. -/
def jetDegree [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) : ℕ :=
  Q.degreeOf (some j)

/-- A differential polynomial depends on `Y_j` when its individual degree there is positive. -/
def DependsOnJet [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) : Prop :=
  0 < jetDegree Q j

/-- The finite set of formal Hasse variables on which `Q` depends. -/
def activeJets [CommSemiring F] (Q : DifferentialPolynomial F d) : Finset (Fin (d + 1)) :=
  by
    classical
    exact Finset.univ.filter (DependsOnJet Q)

@[simp]
theorem mem_activeJets [CommSemiring F] {Q : DifferentialPolynomial F d} {j : Fin (d + 1)} :
    j ∈ activeJets Q ↔ DependsOnJet Q j := by
  simp [activeJets]

/-- The greatest active Hasse variable, or `none` when `Q` is independent of every `Y_j`. -/
def highestActiveJet [CommSemiring F] (Q : DifferentialPolynomial F d) :
    Option (Fin (d + 1)) :=
  by
    classical
    exact if h : (activeJets Q).Nonempty then some ((activeJets Q).max' h) else none

/-- Predicate form of being the greatest active Hasse variable. This proof-facing form avoids
transport through the proof argument of `Finset.max'`. -/
def IsHighestActiveJet [CommSemiring F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) : Prop :=
  DependsOnJet Q s ∧ ∀ j, s < j → ¬DependsOnJet Q j

/-- A nonempty active-variable set has the expected computed highest variable. -/
theorem highestActiveJet_eq_some_max [CommSemiring F] (Q : DifferentialPolynomial F d)
    (h : (activeJets Q).Nonempty) :
    highestActiveJet Q = some ((activeJets Q).max' h) := by
  simp [highestActiveJet, h]

/-- The computed highest active variable satisfies the proof-facing maximality predicate. -/
theorem isHighestActiveJet_of_highestActiveJet_eq_some [CommSemiring F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} (h : highestActiveJet Q = some s) :
    IsHighestActiveJet Q s := by
  have hactive : (activeJets Q).Nonempty := by
    by_contra hempty
    have hnone : highestActiveJet Q = none := by
      rw [highestActiveJet]
      simp only [dite_eq_right_iff]
      intro hne
      exact (hempty hne).elim
    rw [hnone] at h
    simp at h
  have hs : (activeJets Q).max' hactive = s := by
    rw [highestActiveJet_eq_some_max Q hactive] at h
    exact Option.some.inj h
  constructor
  · rw [← mem_activeJets, ← hs]
    exact Finset.max'_mem _ _
  · intro j hsj hj
    have hjmem : j ∈ activeJets Q := mem_activeJets.mpr hj
    have hle : j ≤ (activeJets Q).max' hactive := Finset.le_max' _ _ hjmem
    rw [hs] at hle
    exact (not_le_of_gt hsj) hle

/-- `Q` is independent of every formal Hasse variable exactly when no highest active variable
exists. Dependence on the distinguished `X` variable is irrelevant here. -/
theorem highestActiveJet_eq_none_iff [CommSemiring F] (Q : DifferentialPolynomial F d) :
    highestActiveJet Q = none ↔ ∀ j, ¬DependsOnJet Q j := by
  constructor
  · intro h j hj
    have hne : (activeJets Q).Nonempty := ⟨j, mem_activeJets.mpr hj⟩
    rw [highestActiveJet_eq_some_max Q hne] at h
    simp at h
  · intro h
    rw [highestActiveJet]
    split_ifs with hne
    · obtain ⟨j, hj⟩ := hne
      exact (h j (mem_activeJets.mp hj)).elim
    · rfl

/-- Formal derivative of `Q` in the Hasse variable `Y_s`. -/
def separant [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    DifferentialPolynomial F d :=
  MvPolynomial.pderiv (some s) Q

/-- A scalar jet is regular for `Q` in its active variable `Y_s` when it lies on `Q = 0` and the
corresponding separant is nonzero. -/
def IsRegularJet [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (a : F) (jet : Fin (d + 1) → F) : Prop :=
  jetEvaluation Q a jet = 0 ∧ jetEvaluation (separant Q s) a jet ≠ 0

/-- Regular point-jet pairs, packaged for finite counting. -/
def RegularJet [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :=
  {z : F × (Fin (d + 1) → F) // IsRegularJet Q s z.1 z.2}

/-! ### Degree and characteristic parameters -/

/-- Root-specialization weight: `X` has weight one and `Y_j` has weight `D - j`. -/
def differentialWeight (D : ℕ) : JetVariable d → ℕ
  | none => 1
  | some j => D - j

@[simp]
theorem differentialWeight_none (D : ℕ) : differentialWeight (d := d) D none = 1 :=
  rfl

@[simp]
theorem differentialWeight_some (D : ℕ) (j : Fin (d + 1)) :
    differentialWeight D (some j) = D - j :=
  rfl

/-- If the derivative order is below the ambient degree, every jet variable has positive
root-specialization weight. -/
theorem differentialWeight_some_pos_of_order_lt_degree {D : ℕ} (h : d < D)
    (j : Fin (d + 1)) : 0 < differentialWeight D (some j) := by
  simp only [differentialWeight_some]
  have hj : j.val ≤ d := Nat.le_of_lt_succ j.isLt
  omega

/-- At the rejected boundary `D = d`, the top Hasse variable has weight zero. -/
theorem differentialWeight_top_eq_zero (d : ℕ) :
    differentialWeight d (some (Fin.last d)) = 0 := by
  simp [differentialWeight]

/-- Weighted degree controlling the degree after differential specialization. -/
def differentialWeightedDegree [CommSemiring F] (D : ℕ) (Q : DifferentialPolynomial F d) :
    ℕ :=
  Q.weightedTotalDegree (differentialWeight D)

/-- The characteristic hypotheses used by formal derivative descent and coefficient lifting.

This predicate intentionally contains no cardinality lower bound. -/
def IsBelowCharacteristic [CommSemiring F] (D : ℕ) (Q : DifferentialPolynomial F d) : Prop :=
  D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F

end

end HiddenDerivative
end ReedSolomon
