/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Singular recursion for polynomial differential equations

The `SOLVE` procedure of [Kop15] splits the solutions `P` of an equation `Q(X, P, P^{(1)}, …) = 0`
according to its highest active jet `Y_s`. Either `P` is singular, meaning that it also solves the
separant equation `∂Q/∂Y_s = 0`, or the separant specialization at `P` is a nonzero univariate
polynomial. In the singular case the procedure recurses on the separant. This file proves that the
recursion terminates and that every solution of a nonzero equation reaches a regular branch.

A singular step replaces an equation by its separant in the computed highest active jet. It
strictly lowers `jetTotalDegree`, so the step relation is well founded over every commutative
semiring. An equation with no active jet is a polynomial in `X` alone, so if it is nonzero it has no
solution. Keeping each equation along the path nonzero needs `F` to have no zero divisors and every
positive integer up to each jet degree of the starting equation to be nonzero in `F`. Under these
hypotheses every solution of a nonzero equation reaches a regular leaf: an equation on the path,
solved by `P`, whose separant specialization at `P` is nonzero. A point where that polynomial does
not vanish gives a regular scalar jet.

This file does not produce such a point. A root count over a field that is large enough, in the
root-finding layer, does that.

## Main statements

* `SingularStep` and `singularStep_wellFounded`: the singular step relation is well founded,
  because `jetTotalDegree_lt_of_singularStep`.
* `singularStep_preserves`: a singular step from a nonzero equation satisfying the cast hypotheses
  gives a nonzero equation satisfying them.
* `boundedSolutionBranch`: the split of bounded solutions into `SingularBoundedSolution` and
  `RegularBranchBoundedSolution`.
* `eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none` and
  `isEmpty_boundedSolution_of_highestActiveJet_eq_none`: a nonzero equation with no active jet has
  no solution.
* `exists_regularRecursionLeaf` and `RegularRecursionLeaf.isRegularJet_of_eval_ne_zero`: every
  solution of a nonzero equation reaches a regular leaf, and a nonvanishing point of the leaf's
  separant specialization is a regular jet.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.3 and Section 4.2.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ} [CommSemiring F]

/-! ### One separant step -/

/-- The cast hypotheses at every jet pass from `Q` to any separant of `Q`, since a separant does
not increase any jet degree. -/
theorem jetDegreeCastsNeZero_separant {Q : DifferentialPolynomial F d}
    (hQ : ∀ j, JetDegreeCastsNeZero Q j) (s : Fin (d + 1)) :
    ∀ j, JetDegreeCastsNeZero (separant Q s) j :=
  fun j ↦ (hQ j).mono (jetDegree_separant_le Q s j)

/-- If `Q` depends on `Y_s`, the separant in `Y_s` has strictly smaller `jetTotalDegree`. This
holds in every characteristic, including when the separant is zero. -/
theorem jetTotalDegree_separant_lt {Q : DifferentialPolynomial F d} {s : Fin (d + 1)}
    (hs : DependsOnJet Q s) : jetTotalDegree (separant Q s) < jetTotalDegree Q := by
  have hpos : 0 < jetTotalDegree Q := lt_of_lt_of_le hs (jetDegree_le_total Q s)
  have := separant_total_le Q s
  omega

/-- One singular step replaces an equation by its separant in the computed highest active jet. -/
def SingularStep (next current : DifferentialPolynomial F d) : Prop :=
  ∃ s : Fin (d + 1), highestActiveJet current = some s ∧ next = separant current s

/-- The separant in the computed highest active jet is a singular step. -/
theorem singularStep_separant (Q : DifferentialPolynomial F d) {s : Fin (d + 1)}
    (hs : highestActiveJet Q = some s) : SingularStep (separant Q s) Q :=
  ⟨s, hs, rfl⟩

/-- Every singular step strictly lowers `jetTotalDegree`, in every characteristic. -/
theorem jetTotalDegree_lt_of_singularStep {next current : DifferentialPolynomial F d}
    (hstep : SingularStep next current) : jetTotalDegree next < jetTotalDegree current := by
  obtain ⟨s, hs, rfl⟩ := hstep
  exact jetTotalDegree_separant_lt (isHighestActiveJet_of_highestActiveJet_eq_some hs).1

/-- The singular step relation is well founded over every commutative semiring. This is the
termination argument for the recursion. -/
theorem singularStep_wellFounded : WellFounded (SingularStep (F := F) (d := d)) :=
  (measure jetTotalDegree).wf.mono fun _ _ ↦ jetTotalDegree_lt_of_singularStep

/-- If `F` has no zero divisors and the current equation satisfies the cast hypotheses at every
jet, a singular step gives a nonzero equation that satisfies them too.

The current equation need not be assumed nonzero: it depends on its highest active jet. The cast
hypothesis is needed: over `ZMod 2`, the singular step from `Y₀ ^ 2` gives `0`. -/
theorem singularStep_preserves [NoZeroDivisors F] {next current : DifferentialPolynomial F d}
    (hcurrent : ∀ j, JetDegreeCastsNeZero current j) (hstep : SingularStep next current) :
    next ≠ 0 ∧ ∀ j, JetDegreeCastsNeZero next j := by
  obtain ⟨s, hs, rfl⟩ := hstep
  exact ⟨separant_ne_zero current s ((hcurrent s).natCast_jetDegree_ne_zero
      (isHighestActiveJet_of_highestActiveJet_eq_some hs).1),
    jetDegreeCastsNeZero_separant hcurrent s⟩

/-! ### The singular and regular branches -/

/-- Bounded solutions of `Q = 0` that also solve the separant equation `∂Q/∂Y_s = 0`. -/
def SingularBoundedSolution (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D : ℕ) :=
  {P : BoundedSolution Q D // differentialSpecialization (separant Q s) P.polynomial = 0}

/-- Bounded solutions of `Q = 0` whose separant specialization is a nonzero polynomial. The type
does not record a point where that polynomial is nonzero; over a small field there may be none. -/
def RegularBranchBoundedSolution (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D : ℕ) :=
  {P : BoundedSolution Q D // differentialSpecialization (separant Q s) P.polynomial ≠ 0}

/-- A singular solution is a bounded solution of the separant equation, with the same underlying
polynomial. -/
def SingularBoundedSolution.toSeparantSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : SingularBoundedSolution Q s D) :
    BoundedSolution (separant Q s) D :=
  ⟨P.1.1, P.2⟩

/-- The underlying bounded solution of a singular solution. -/
def SingularBoundedSolution.toBoundedSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : SingularBoundedSolution Q s D) : BoundedSolution Q D :=
  P.1

/-- The underlying bounded solution of a regular-branch solution. -/
def RegularBranchBoundedSolution.toBoundedSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : RegularBranchBoundedSolution Q s D) : BoundedSolution Q D :=
  P.1

/-- Sort a bounded solution by whether it also solves the separant equation. -/
def boundedSolutionBranch (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D : ℕ)
    (P : BoundedSolution Q D) :
    SingularBoundedSolution Q s D ⊕ RegularBranchBoundedSolution Q s D := by
  classical
  exact if h : differentialSpecialization (separant Q s) P.polynomial = 0 then Sum.inl ⟨P, h⟩
    else Sum.inr ⟨P, h⟩

/-- Sorting keeps the underlying bounded solution on either branch. -/
theorem boundedSolutionBranch_forgets (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (D : ℕ) (P : BoundedSolution Q D) :
    (boundedSolutionBranch Q s D P).elim SingularBoundedSolution.toBoundedSolution
      RegularBranchBoundedSolution.toBoundedSolution = P := by
  classical
  rw [boundedSolutionBranch]
  split <;> rfl

/-- If the separant specialization of a regular-branch solution `P` does not vanish at `center`,
the Hasse jet of `P` at `center` is regular for `Q` in `Y_s`. -/
theorem RegularBranchBoundedSolution.isRegularJet_of_eval_ne_zero
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} {D : ℕ}
    (P : RegularBranchBoundedSolution Q s D) (center : F)
    (hcenter : (differentialSpecialization (separant Q s) P.1.polynomial).eval center ≠ 0) :
    IsRegularJet Q s center (polynomialJet center P.1.polynomial) := by
  constructor
  · rw [← eval_differentialSpecialization, P.1.equation, eval_zero]
  · rwa [← eval_differentialSpecialization]

/-! ### Equations with no active jet -/

/-- An equation with no active jet has degree zero in every jet variable. -/
theorem jetDegree_eq_zero_of_highestActiveJet_eq_none {Q : DifferentialPolynomial F d}
    (hterminal : highestActiveJet Q = none) (j : Fin (d + 1)) : jetDegree Q j = 0 :=
  Nat.eq_zero_of_not_pos ((highestActiveJet_eq_none_iff Q).mp hterminal j)

/-- An equation with no active jet is a univariate polynomial in `X`. -/
theorem exists_toMvPolynomial_eq_of_highestActiveJet_eq_none {Q : DifferentialPolynomial F d}
    (hterminal : highestActiveJet Q = none) :
    ∃ q : F[X], q.toMvPolynomial (none : JetVariable d) = Q := by
  let includeX : Unit → JetVariable d := fun _ ↦ none
  have hvars : (Q.vars : Set (JetVariable d)) ⊆ Set.range includeX := by
    intro v hv
    rcases v with _ | j
    · exact ⟨(), rfl⟩
    · exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv
        (jetDegree_eq_zero_of_highestActiveJet_eq_none hterminal j)).elim
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q includeX
    (fun _ _ _ ↦ Subsingleton.elim _ _) hvars
  refine ⟨MvPolynomial.uniqueAlgEquiv F Unit q, ?_⟩
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change MvPolynomial.rename includeX
      ((MvPolynomial.uniqueAlgEquiv F Unit).symm (MvPolynomial.uniqueAlgEquiv F Unit q)) = Q
  rw [AlgEquiv.symm_apply_apply, hq]

/-- Specializing a polynomial in `X` alone at any `P` returns the polynomial. -/
@[simp]
theorem differentialSpecialization_toMvPolynomial (q P : F[X]) :
    differentialSpecialization (d := d) (q.toMvPolynomial (none : JetVariable d)) P = q := by
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change MvPolynomial.eval₂ Polynomial.C _
      (MvPolynomial.rename (fun _ : Unit ↦ (none : JetVariable d))
        ((MvPolynomial.uniqueAlgEquiv F Unit).symm q)) = q
  rw [MvPolynomial.eval₂_rename]
  change (MvPolynomial.uniqueAlgEquiv F Unit) ((MvPolynomial.uniqueAlgEquiv F Unit).symm q) = q
  exact AlgEquiv.apply_symm_apply _ q

/-- An equation with no active jet that has a solution `P`, of any degree, is zero. -/
theorem eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none
    {Q : DifferentialPolynomial F d} (hterminal : highestActiveJet Q = none) {P : F[X]}
    (hP : differentialSpecialization Q P = 0) : Q = 0 := by
  obtain ⟨q, rfl⟩ := exists_toMvPolynomial_eq_of_highestActiveJet_eq_none hterminal
  rw [differentialSpecialization_toMvPolynomial] at hP
  rw [hP, map_zero]

/-- An equation with no active jet that has a bounded solution is zero. -/
theorem eq_zero_of_boundedSolution_of_highestActiveJet_eq_none {Q : DifferentialPolynomial F d}
    {D : ℕ} (hterminal : highestActiveJet Q = none) (P : BoundedSolution Q D) : Q = 0 :=
  eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none hterminal P.equation

/-- A nonzero equation with no active jet has no bounded solution. -/
theorem isEmpty_boundedSolution_of_highestActiveJet_eq_none {Q : DifferentialPolynomial F d}
    {D : ℕ} (hQ : Q ≠ 0) (hterminal : highestActiveJet Q = none) :
    IsEmpty (BoundedSolution Q D) :=
  ⟨fun P ↦ hQ (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none hterminal P)⟩

/-! ### Recursive coverage -/

/-- A regular leaf for the solution `P` of `root`: an equation reached from `root` by zero or more
singular steps, solved by `P`, whose separant specialization at `P` in its highest active jet is
nonzero. -/
structure RegularRecursionLeaf (root : DifferentialPolynomial F d) (P : F[X]) where
  /-- The equation at the leaf. -/
  equation : DifferentialPolynomial F d
  /-- The highest active jet of the leaf equation. -/
  activeJet : Fin (d + 1)
  /-- The leaf is reached from `root` by singular steps. -/
  reachable : Relation.ReflTransGen (SingularStep (F := F) (d := d)) equation root
  /-- `P` solves the leaf equation. -/
  solves : differentialSpecialization equation P = 0
  /-- The separant specialization at `P` is nonzero. -/
  separantSpecialization_ne_zero : differentialSpecialization (separant equation activeJet) P ≠ 0
  /-- `activeJet` is the computed highest active jet. -/
  highestActiveJet_eq : highestActiveJet equation = some activeJet
  /-- The cast hypotheses of the root still hold at the leaf. -/
  castsNeZero : ∀ j, JetDegreeCastsNeZero equation j

/-- If `F` has no zero divisors, `Q ≠ 0`, and `Q` satisfies the cast hypotheses at every jet, then
every solution `P` of `Q = 0` reaches a regular leaf.

The proof is well-founded recursion along singular steps. At each equation, either `P` solves the
separant equation and the recursion continues, or the current equation is a leaf. The cast
hypotheses keep every equation on the path nonzero, and a nonzero equation with no active jet has
no solution, so the recursion cannot end without a leaf. They are needed: over `ZMod 2`, `P = 0`
solves `Y₀ ^ 2 = 0` and there is no leaf. The leaf does not come with a point where its separant
specialization is nonzero. -/
theorem exists_regularRecursionLeaf [NoZeroDivisors F] {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j) {P : F[X]}
    (hP : differentialSpecialization Q P = 0) : Nonempty (RegularRecursionLeaf Q P) := by
  suffices h : ∀ current, Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 → (∀ j, JetDegreeCastsNeZero current j) →
        differentialSpecialization current P = 0 → Nonempty (RegularRecursionLeaf Q P) from
    h Q Relation.ReflTransGen.refl hQ hcast hP
  intro current
  induction current using (singularStep_wellFounded (F := F) (d := d)).induction with
  | _ equation ih =>
  intro hreachable hne hequation hsolution
  cases hactive : highestActiveJet equation with
  | none =>
      exact (hne (eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none
        hactive hsolution)).elim
  | some s =>
      by_cases hseparant : differentialSpecialization (separant equation s) P = 0
      · have hstep := singularStep_separant equation hactive
        have hnext := singularStep_preserves hequation hstep
        exact ih _ hstep (Relation.ReflTransGen.head hstep hreachable) hnext.1 hnext.2 hseparant
      · exact ⟨⟨equation, s, hreachable, hsolution, hseparant, hactive, hequation⟩⟩

/-- Every bounded solution of a nonzero equation satisfying the cast hypotheses reaches a regular
leaf. This is `exists_regularRecursionLeaf` for a bounded solution. -/
theorem exists_regularRecursionLeaf_of_boundedSolution [NoZeroDivisors F]
    {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    {D : ℕ} (P : BoundedSolution Q D) : Nonempty (RegularRecursionLeaf Q P.polynomial) :=
  exists_regularRecursionLeaf hQ hcast P.equation

/-- If the separant specialization of a regular leaf does not vanish at `center`, the Hasse jet
of `P` at `center` is regular for the leaf equation in its highest active jet. -/
theorem RegularRecursionLeaf.isRegularJet_of_eval_ne_zero {root : DifferentialPolynomial F d}
    {P : F[X]} (leaf : RegularRecursionLeaf root P) (center : F)
    (hcenter :
      (differentialSpecialization (separant leaf.equation leaf.activeJet) P).eval center ≠ 0) :
    IsRegularJet leaf.equation leaf.activeJet center (polynomialJet center P) := by
  constructor
  · rw [← eval_differentialSpecialization, leaf.solves, eval_zero]
  · rwa [← eval_differentialSpecialization]

end

end PolynomialDifferential
