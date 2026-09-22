/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetDegree
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Active jets, regular jets, bounded solutions and jet prefixes

A differential polynomial `Q(X, Y₀, ..., Y_d)` is stored at a fixed ambient depth `d`, but it may
depend only on `Y₀, ..., Y_s` for some `s < d`. This file records which jet variables `Q` depends
on, what it means for a scalar jet to be regular for `Q`, and the bounded-degree solutions of
`Q = 0`. It then shows that `Q` is the renaming of a differential polynomial of depth `s` when
`Y_s` is its highest active jet variable, and that differential specialization, jet evaluation,
separants and regularity commute with this renaming. Theorems proved for the literal top variable
`Y_s` of a depth-`s` polynomial therefore apply at an arbitrary highest active jet.

Every statement holds over a commutative semiring.

`IsRegularJet` asks that the separant value be nonzero. Over a field this is what the lifting
theorems need; over a general commutative ring they instead assume that the slope, a binomial
coefficient times that value, is a unit or left-regular.

## Main statements

* `DependsOnJet`, `activeJets`, `highestActiveJet` and `IsHighestActiveJet`: the jet variables `Q`
  depends on, and the greatest one, as a computed value and as a predicate.
* `isHighestActiveJet_of_highestActiveJet_eq_some` and `highestActiveJet_eq_none_iff`: the
  computed value agrees with the predicate.
* `IsRegularJet` and `RegularJet`: a scalar jet on `Q = 0` at which the separant does not vanish.
* `BoundedSolution`: the polynomials of degree at most `D` solving `Q = 0`.
* `jetPrefixEmbedding` and `restrictJet`: the inclusion of the variables through `Y_s` and the
  matching restriction of scalar jets.
* `exists_prefixDifferentialPolynomial`: if `Y_s` is the highest active jet of `Q`, then `Q` is
  the renaming of a depth-`s` differential polynomial.
* `differentialSpecialization_rename_jetPrefixEmbedding`,
  `jetEvaluation_rename_jetPrefixEmbedding`, `separant_rename_jetPrefixEmbedding`,
  `jetEvaluation_separant_rename_jetPrefixEmbedding` and
  `isRegularJet_rename_jetPrefixEmbedding_iff`: the renaming commutes with the constructions
  above.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-! ### Active jet variables -/

/-- `Q` depends on the jet variable `Y_j` when its degree in `Y_j` is positive. -/
def DependsOnJet [CommSemiring F] (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) : Prop :=
  0 < jetDegree Q j

/-- The finite set of jet variables `Y_j` on which `Q` depends. -/
def activeJets [CommSemiring F] (Q : DifferentialPolynomial F d) : Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter (DependsOnJet Q)

/-- `Y_j` is an active jet of `Q` exactly when `Q` depends on `Y_j`. -/
@[simp]
theorem mem_activeJets [CommSemiring F] {Q : DifferentialPolynomial F d} {j : Fin (d + 1)} :
    j ∈ activeJets Q ↔ DependsOnJet Q j := by
  simp [activeJets]

/-- The greatest jet variable on which `Q` depends, or `none` when `Q` depends on no `Y_j`.
Dependence on the variable `X` is not counted. -/
def highestActiveJet [CommSemiring F] (Q : DifferentialPolynomial F d) :
    Option (Fin (d + 1)) := by
  classical
  exact if h : (activeJets Q).Nonempty then some ((activeJets Q).max' h) else none

/-- `Y_s` is the greatest jet variable on which `Q` depends. Proofs use this predicate instead of
`highestActiveJet`, which avoids the proof argument of `Finset.max'`. -/
def IsHighestActiveJet [CommSemiring F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) : Prop :=
  DependsOnJet Q s ∧ ∀ j, s < j → ¬DependsOnJet Q j

/-- When some jet variable is active, `highestActiveJet` is the maximum of `activeJets`. -/
theorem highestActiveJet_eq_some_max [CommSemiring F] (Q : DifferentialPolynomial F d)
    (h : (activeJets Q).Nonempty) :
    highestActiveJet Q = some ((activeJets Q).max' h) := by
  simp [highestActiveJet, h]

/-- The value computed by `highestActiveJet` satisfies `IsHighestActiveJet`. -/
theorem isHighestActiveJet_of_highestActiveJet_eq_some [CommSemiring F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} (h : highestActiveJet Q = some s) :
    IsHighestActiveJet Q s := by
  have hactive : (activeJets Q).Nonempty := by
    by_contra hempty
    simp [highestActiveJet, hempty] at h
  have hs : (activeJets Q).max' hactive = s := by
    rw [highestActiveJet_eq_some_max Q hactive] at h
    exact Option.some.inj h
  refine ⟨?_, fun j hsj hj ↦ ?_⟩
  · rw [← mem_activeJets, ← hs]
    exact Finset.max'_mem _ _
  · have hle : j ≤ (activeJets Q).max' hactive :=
      Finset.le_max' _ _ (mem_activeJets.mpr hj)
    rw [hs] at hle
    exact not_le_of_gt hsj hle

/-- `highestActiveJet Q = none` exactly when `Q` depends on no jet variable `Y_j`. -/
theorem highestActiveJet_eq_none_iff [CommSemiring F] (Q : DifferentialPolynomial F d) :
    highestActiveJet Q = none ↔ ∀ j, ¬DependsOnJet Q j := by
  constructor
  · intro h j hj
    rw [highestActiveJet_eq_some_max Q ⟨j, mem_activeJets.mpr hj⟩] at h
    simp at h
  · intro h
    rw [highestActiveJet, dite_eq_right]
    rintro ⟨j, hj⟩
    exact (h j (mem_activeJets.mp hj)).elim

/-! ### Regular jets and bounded solutions -/

/-- A scalar jet `jet` at the point `a` is regular for `Q` in the variable `Y_s` when it lies on
`Q = 0` and the separant `∂Q/∂Y_s` does not vanish there. -/
def IsRegularJet [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (a : F) (jet : Fin (d + 1) → F) : Prop :=
  jetEvaluation Q a jet = 0 ∧ jetEvaluation (separant Q s) a jet ≠ 0

/-- The pairs of a point and a scalar jet that are regular for `Q` in `Y_s`, as a type for
counting. -/
def RegularJet [CommSemiring F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :=
  {z : F × (Fin (d + 1) → F) // IsRegularJet Q s z.1 z.2}

/-- The polynomials of degree at most `D` that solve `Q = 0`. The degree bound is membership in
`Polynomial.degreeLT F (D + 1)`, which contains the zero polynomial. -/
def BoundedSolution [CommSemiring F] (Q : DifferentialPolynomial F d) (D : ℕ) :=
  {P : Polynomial.degreeLT F (D + 1) // differentialSpecialization Q P = 0}

/-- The polynomial underlying a bounded solution. -/
def BoundedSolution.polynomial [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : F[X] :=
  P.1

/-- A bounded solution solves `Q = 0`. -/
@[simp]
theorem BoundedSolution.equation [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : differentialSpecialization Q P.polynomial = 0 :=
  P.2

/-- A bounded solution has degree at most `D`. -/
theorem BoundedSolution.degree_le [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (P : BoundedSolution Q D) : P.polynomial.degree ≤ D := by
  have hmem : P.polynomial ∈ Polynomial.degreeLE F D := by
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact P.1.2
  exact Polynomial.mem_degreeLE.mp hmem

/-! ### The prefix of jet variables through `Y_s` -/

/-- The inclusion of the variables `X, Y₀, ..., Y_s` of depth `s` into the variables of the
ambient depth `d`. -/
def jetPrefixEmbedding (s : Fin (d + 1)) : JetVariable s.val ↪ JetVariable d :=
  (Fin.castLEEmb s.isLt).optionMap

/-- The prefix embedding sends `X` to `X`. -/
@[simp]
theorem jetPrefixEmbedding_none (s : Fin (d + 1)) :
    jetPrefixEmbedding s none = none :=
  rfl

/-- The prefix embedding sends `Y_j` of depth `s` to `Y_j` of depth `d`. -/
@[simp]
theorem jetPrefixEmbedding_some (s : Fin (d + 1)) (j : Fin (s.val + 1)) :
    jetPrefixEmbedding s (some j) = some (Fin.castLE s.isLt j) :=
  rfl

/-- The top variable `Y_s` of depth `s` is sent to `Y_s`. -/
@[simp]
theorem jetPrefixEmbedding_some_last (s : Fin (d + 1)) :
    jetPrefixEmbedding s (some (Fin.last s.val)) = some s :=
  rfl

/-- Restrict a scalar jet of depth `d` to its entries through order `s`. -/
def restrictJet (s : Fin (d + 1)) (jet : Fin (d + 1) → F) : Fin (s.val + 1) → F :=
  fun j ↦ jet (Fin.castLE s.isLt j)

/-- Restricting the Hasse jet of `P` through order `d` gives its Hasse jet through order `s`. -/
@[simp]
theorem restrictJet_polynomialJet [Semiring F] (s : Fin (d + 1)) (center : F) (P : F[X]) :
    restrictJet s (polynomialJet (d := d) center P) = polynomialJet (d := s.val) center P :=
  rfl

variable [CommSemiring F]

/-- Every variable of `Q` lies in the prefix through its highest active jet variable. -/
theorem vars_subset_range_jetPrefixEmbedding (Q : DifferentialPolynomial F d)
    {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s) :
    (Q.vars : Set (JetVariable d)) ⊆ Set.range (jetPrefixEmbedding s) := by
  intro v hv
  rcases v with _ | j
  · exact ⟨none, rfl⟩
  · have hactive : DependsOnJet Q j :=
      Nat.pos_of_ne_zero (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv)
    have hle : j.val ≤ s.val := Fin.le_iff_val_le_val.mp (le_of_not_gt fun hsj ↦ hs.2 j hsj hactive)
    exact ⟨some ⟨j.val, Nat.lt_succ_of_le hle⟩, rfl⟩

/-- If `Y_s` is the highest active jet variable of `Q`, then `Q` is the renaming of a differential
polynomial of depth `s`. The renaming is injective, so this polynomial is unique. -/
theorem exists_prefixDifferentialPolynomial (Q : DifferentialPolynomial F d)
    {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s) :
    ∃ Q' : DifferentialPolynomial F s.val, MvPolynomial.rename (jetPrefixEmbedding s) Q' = Q :=
  MvPolynomial.exists_rename_eq_of_vars_subset_range Q (jetPrefixEmbedding s)
    (jetPrefixEmbedding s).injective (vars_subset_range_jetPrefixEmbedding Q hs)

/-- Differential specialization commutes with the prefix renaming. -/
theorem differentialSpecialization_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (P : F[X]) :
    differentialSpecialization (MvPolynomial.rename (jetPrefixEmbedding s) Q) P =
      differentialSpecialization Q P := by
  rw [differentialSpecialization, differentialSpecialization, differentialSpecializationHom,
    differentialSpecializationHom, MvPolynomial.aeval_rename]
  congr 2
  funext v
  rcases v with _ | j <;> rfl

/-- Scalar jet evaluation of a renamed polynomial reads only the restricted jet. -/
theorem jetEvaluation_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (center : F)
    (jet : Fin (d + 1) → F) :
    jetEvaluation (MvPolynomial.rename (jetPrefixEmbedding s) Q) center jet =
      jetEvaluation Q center (restrictJet s jet) := by
  rw [jetEvaluation, jetEvaluation, MvPolynomial.eval_rename]
  congr 2
  funext v
  rcases v with _ | j <;> rfl

/-- The separant in `Y_s` of the renamed polynomial is the renaming of the separant in the top
variable of the depth-`s` polynomial. -/
theorem separant_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) :
    separant (MvPolynomial.rename (jetPrefixEmbedding s) Q) s =
      MvPolynomial.rename (jetPrefixEmbedding s) (separant Q (Fin.last s.val)) := by
  rw [separant, separant, ← MvPolynomial.pderiv_rename (jetPrefixEmbedding s).injective,
    jetPrefixEmbedding_some_last]

/-- The separant value in `Y_s` of the renamed polynomial at the Hasse jet of `P` is the separant
value in the top variable of the depth-`s` polynomial at the shorter jet. -/
theorem jetEvaluation_separant_rename_jetPrefixEmbedding
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (center : F) (P : F[X]) :
    jetEvaluation (separant (MvPolynomial.rename (jetPrefixEmbedding s) Q) s) center
        (polynomialJet (d := d) center P) =
      jetEvaluation (separant Q (Fin.last s.val)) center (polynomialJet (d := s.val) center P) := by
  rw [separant_rename_jetPrefixEmbedding, jetEvaluation_rename_jetPrefixEmbedding,
    restrictJet_polynomialJet]

/-- Regularity in `Y_s` of the renamed polynomial at the Hasse jet of `P` is regularity in the
top variable of the depth-`s` polynomial. -/
theorem isRegularJet_rename_jetPrefixEmbedding_iff
    (s : Fin (d + 1)) (Q : DifferentialPolynomial F s.val) (center : F) (P : F[X]) :
    IsRegularJet (MvPolynomial.rename (jetPrefixEmbedding s) Q) s center
        (polynomialJet (d := d) center P) ↔
      IsRegularJet Q (Fin.last s.val) center (polynomialJet (d := s.val) center P) := by
  rw [IsRegularJet, IsRegularJet, jetEvaluation_separant_rename_jetPrefixEmbedding,
    jetEvaluation_rename_jetPrefixEmbedding, restrictJet_polynomialJet]

end

end PolynomialDifferential
