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

This file formalizes the recursive-coverage seam in Kopparty's `SOLVE` procedure from
[Kop15, Theorem 4.3 and Section 4.2].  At an equation whose highest active jet is `Y_s`, a
solution is either singular, and hence also solves the separant equation, or its separant
specialization is a nonzero univariate polynomial.  In the latter case any point where that
polynomial is nonzero gives a regular Hasse jet.

Below the characteristic, the separant is nonzero, preserves every individual jet-degree bound,
and strictly decreases the sum of the individual jet degrees.  This supplies a well-founded
recursion.  The terminal equation has no active jet variables; if it is nonzero, it has no
bounded differential solution.

This is a coverage and termination interface, not an enumerator.  In particular, it does not
assert that a regular witness center exists.  The finite-field root count in the subsequent
root-finding layer must produce such a center from the nonzero separant specialization and an
explicit field-size bound.

The regular-lifting API pivots on the literal top coordinate `Fin.last r`.
`RootFinding.JetPrefix` supplies the companion adapter that restricts an arbitrary highest active
jet `s` to its active prefix before invoking that theorem.  No root count or enumeration is
claimed here.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.3 and Section 4.2.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ} [CommSemiring F]

/-! ### One separant step -/

/-- A separant cannot increase the individual degree in any jet variable. -/
theorem jetDegree_separant_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1)) :
    jetDegree (separant Q s) j ≤ jetDegree Q j := by
  exact MvPolynomial.degreeOf_pderiv_le (some s) (some j) Q

/-- Below the characteristic, taking the separant in an active jet lowers that individual
degree by exactly one. -/
theorem jetDegree_separant_eq_sub_one_of_lt_ringChar [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : DependsOnJet Q s)
    (hchar : jetDegree Q s < ringChar F) :
    jetDegree (separant Q s) s = jetDegree Q s - 1 := by
  exact MvPolynomial.degreeOf_pderiv_eq_sub_one_of_lt_ringChar
    (some s) Q hs hchar

/-- The separant in an active jet is nonzero below the characteristic. -/
theorem separant_ne_zero_of_dependsOnJet_of_lt_ringChar [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : DependsOnJet Q s)
    (hchar : jetDegree Q s < ringChar F) : separant Q s ≠ 0 := by
  exact MvPolynomial.pderiv_ne_zero_of_degreeOf_pos_of_lt_ringChar
    (some s) Q hs hchar

/-- In particular, the separant in the computed highest active jet is nonzero below the
characteristic. -/
theorem separant_ne_zero_of_highestActiveJet_eq_some [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hs : highestActiveJet Q = some s) (hchar : jetDegree Q s < ringChar F) :
    separant Q s ≠ 0 := by
  exact separant_ne_zero_of_dependsOnJet_of_lt_ringChar Q s
    (isHighestActiveJet_of_highestActiveJet_eq_some hs).1 hchar

/-- The complete below-characteristic contract is preserved by a separant step. -/
theorem isBelowCharacteristic_separant (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hQ : IsBelowCharacteristic D Q) :
    IsBelowCharacteristic D (separant Q s) := by
  refine ⟨hQ.1, fun j ↦ ?_⟩
  exact (jetDegree_separant_le Q s j).trans_lt (hQ.2 j)

/-! ### A well-founded jet-degree measure -/

/-- Sum of the individual degrees in `Y₀, ..., Y_d`.  The distinguished `X` degree is omitted
because the singular recursion differentiates only in jet variables. -/
def jetDegreeMeasure (Q : DifferentialPolynomial F d) : ℕ :=
  ∑ j, jetDegree Q j

/-- A below-characteristic separant in an active jet strictly decreases `jetDegreeMeasure`. -/
theorem jetDegreeMeasure_separant_lt [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : DependsOnJet Q s)
    (hchar : jetDegree Q s < ringChar F) :
    jetDegreeMeasure (separant Q s) < jetDegreeMeasure Q := by
  rw [jetDegreeMeasure, jetDegreeMeasure]
  apply Finset.sum_lt_sum
  · intro j _
    exact jetDegree_separant_le Q s j
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    rw [jetDegree_separant_eq_sub_one_of_lt_ringChar Q s hs hchar]
    have hspos : 0 < jetDegree Q s := hs
    omega

/-- One recursive singular step replaces an equation by the separant in its computed highest
active jet, under the exact characteristic bound needed for nonannihilation. -/
def SingularStep (next current : DifferentialPolynomial F d) : Prop :=
  ∃ s : Fin (d + 1),
    highestActiveJet current = some s ∧
      jetDegree current s < ringChar F ∧
        next = separant current s

/-- Constructor for the canonical singular step. -/
theorem singularStep_separant (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hs : highestActiveJet Q = some s) (hchar : jetDegree Q s < ringChar F) :
    SingularStep (separant Q s) Q :=
  ⟨s, hs, hchar, rfl⟩

/-- Every singular step strictly decreases the natural-number jet-degree measure. -/
theorem jetDegreeMeasure_lt_of_singularStep [NoZeroDivisors F] [Nontrivial F]
    {next current : DifferentialPolynomial F d} (hstep : SingularStep next current) :
    jetDegreeMeasure next < jetDegreeMeasure current := by
  obtain ⟨s, hs, hchar, rfl⟩ := hstep
  exact jetDegreeMeasure_separant_lt current s
    (isHighestActiveJet_of_highestActiveJet_eq_some hs).1 hchar

/-- The singular-step relation is well founded.  This is the termination certificate for the
equation-level recursion; it does not claim that any search procedure has been implemented. -/
theorem singularStep_wellFounded [NoZeroDivisors F] [Nontrivial F] :
    WellFounded (SingularStep (F := F) (d := d)) := by
  exact (measure jetDegreeMeasure).wf.mono fun _ _ hstep ↦
    jetDegreeMeasure_lt_of_singularStep hstep

/-- A singular step from an equation satisfying the global characteristic contract produces a
nonzero equation satisfying the same contract. -/
theorem singularStep_preserves_contract [NoZeroDivisors F] [Nontrivial F]
    {next current : DifferentialPolynomial F d} (hcurrent : IsBelowCharacteristic D current)
    (hstep : SingularStep next current) :
    next ≠ 0 ∧ IsBelowCharacteristic D next := by
  obtain ⟨s, hs, _, rfl⟩ := hstep
  exact ⟨separant_ne_zero_of_highestActiveJet_eq_some current s hs (hcurrent.2 s),
    isBelowCharacteristic_separant current s hcurrent⟩

/-! ### Exact singular-versus-regular coverage -/

/-- Solutions on the singular side of one separant split. -/
def SingularBoundedSolution (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D : ℕ) :=
  {P : BoundedSolution Q D //
    differentialSpecialization (separant Q s) P.polynomial = 0}

/-- Solutions whose separant specialization is a nonzero polynomial.  Existence of a scalar
point where it remains nonzero is deliberately not built into this type. -/
def RegularBranchBoundedSolution (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) :=
  {P : BoundedSolution Q D //
    differentialSpecialization (separant Q s) P.polynomial ≠ 0}

/-- A singular solution is a bounded solution of the separant equation, with the same underlying
polynomial and degree proof. -/
def SingularBoundedSolution.toSeparantSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : SingularBoundedSolution Q s D) :
    BoundedSolution (separant Q s) D :=
  ⟨P.1.1, P.2⟩

/-- Forget the branch evidence from a singular bounded solution. -/
def SingularBoundedSolution.toBoundedSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : SingularBoundedSolution Q s D) :
    BoundedSolution Q D :=
  P.1

/-- Forget the branch evidence from a regular-branch bounded solution. -/
def RegularBranchBoundedSolution.toBoundedSolution {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} {D : ℕ} (P : RegularBranchBoundedSolution Q s D) :
    BoundedSolution Q D :=
  P.1

/-- Classify a bounded solution by whether it also solves the separant equation. -/
noncomputable def boundedSolutionBranch (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (P : BoundedSolution Q D) :
    SingularBoundedSolution Q s D ⊕ RegularBranchBoundedSolution Q s D := by
  classical
  exact if h : differentialSpecialization (separant Q s) P.polynomial = 0 then
    Sum.inl ⟨P, h⟩
  else
    Sum.inr ⟨P, h⟩

/-- Classification preserves the underlying bounded solution on either branch. -/
theorem boundedSolutionBranch_forgets (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (P : BoundedSolution Q D) :
    (boundedSolutionBranch Q s D P).elim
      SingularBoundedSolution.toBoundedSolution
      RegularBranchBoundedSolution.toBoundedSolution = P := by
  classical
  rw [boundedSolutionBranch]
  split <;> rfl

/-- A point avoiding the nonzero separant specialization turns a regular-branch solution into a
regular scalar Hasse jet.  R4 is responsible for producing such points over a sufficiently large
field. -/
theorem RegularBranchBoundedSolution.isRegularJet_of_eval_ne_zero
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} {D : ℕ}
    (P : RegularBranchBoundedSolution Q s D) (center : F)
    (hcenter :
      (differentialSpecialization (separant Q s) P.1.polynomial).eval center ≠ 0) :
    IsRegularJet Q s center (polynomialJet center P.1.polynomial) := by
  constructor
  · rw [← eval_differentialSpecialization, P.1.equation]
    simp
  · rw [← eval_differentialSpecialization]
    exact hcenter

/-! ### Terminal equations -/

/-- A terminal equation has individual jet degree zero in every formal Hasse variable. -/
theorem jetDegree_eq_zero_of_highestActiveJet_eq_none
    (Q : DifferentialPolynomial F d) (hterminal : highestActiveJet Q = none)
    (j : Fin (d + 1)) : jetDegree Q j = 0 := by
  exact Nat.eq_zero_of_not_pos ((highestActiveJet_eq_none_iff Q).mp hterminal j)

/-- An equation with no active jet variable is the embedding of a univariate polynomial in the
distinguished variable `X`. -/
theorem exists_toMvPolynomial_eq_of_highestActiveJet_eq_none
    (Q : DifferentialPolynomial F d) (hterminal : highestActiveJet Q = none) :
    ∃ q : F[X], q.toMvPolynomial (none : JetVariable d) = Q := by
  let includeX : Unit → JetVariable d := fun _ ↦ none
  have hinjective : Function.Injective includeX := fun _ _ _ ↦ Subsingleton.elim _ _
  have hvars : (Q.vars : Set (JetVariable d)) ⊆ Set.range includeX := by
    intro v hv
    rcases v with _ | j
    · exact ⟨(), rfl⟩
    · have hdegree : jetDegree Q j ≠ 0 := by
        exact MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv
      exact ((highestActiveJet_eq_none_iff Q).mp hterminal j
        (Nat.pos_of_ne_zero hdegree)).elim
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    Q includeX hinjective hvars
  refine ⟨MvPolynomial.uniqueAlgEquiv F Unit q, ?_⟩
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change MvPolynomial.rename includeX
      ((MvPolynomial.uniqueAlgEquiv F Unit).symm (MvPolynomial.uniqueAlgEquiv F Unit q)) = Q
  rw [AlgEquiv.symm_apply_apply]
  exact hq

/-- Differential specialization is a left inverse to embedding a univariate polynomial in the
distinguished `X` variable. -/
@[simp]
theorem differentialSpecialization_toMvPolynomial (q P : F[X]) :
    differentialSpecialization (d := d) (q.toMvPolynomial (none : JetVariable d)) P = q := by
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change MvPolynomial.eval₂ Polynomial.C _
      (MvPolynomial.rename (fun _ : Unit ↦ (none : JetVariable d))
        ((MvPolynomial.uniqueAlgEquiv F Unit).symm q)) = q
  rw [MvPolynomial.eval₂_rename]
  change (MvPolynomial.uniqueAlgEquiv F Unit)
      ((MvPolynomial.uniqueAlgEquiv F Unit).symm q) = q
  exact AlgEquiv.apply_symm_apply _ q

/-- A terminal equation admitting a bounded solution is the zero differential polynomial. -/
theorem eq_zero_of_boundedSolution_of_highestActiveJet_eq_none
    (Q : DifferentialPolynomial F d) (hterminal : highestActiveJet Q = none)
    (P : BoundedSolution Q D) : Q = 0 := by
  obtain ⟨q, hq⟩ := exists_toMvPolynomial_eq_of_highestActiveJet_eq_none Q hterminal
  have hqzero : q = 0 := by
    rw [← differentialSpecialization_toMvPolynomial (d := d) q P.polynomial]
    rw [hq]
    exact P.equation
  rw [← hq, hqzero]
  simp

/-- Consequently a nonzero terminal equation has no bounded solutions. -/
theorem isEmpty_boundedSolution_of_highestActiveJet_eq_none
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hterminal : highestActiveJet Q = none) : IsEmpty (BoundedSolution Q D) :=
  ⟨fun P ↦ hQ (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none Q hterminal P)⟩

/-! ### Recursive coverage -/

/-- A regular leaf reached by zero or more singular separant steps.  The fixed polynomial solves
the leaf equation, while the next separant specialization is nonzero. -/
structure RegularRecursionLeaf (root : DifferentialPolynomial F d) (D : ℕ) (P : F[X]) where
  /-- Equation at this recursion leaf. -/
  equation : DifferentialPolynomial F d
  /-- Highest active jet of the leaf equation. -/
  activeJet : Fin (d + 1)
  /-- Singular-step path from the leaf back to the root equation. -/
  reachable : Relation.ReflTransGen (SingularStep (F := F) (d := d)) equation root
  /-- The fixed polynomial solves the leaf equation. -/
  solves : differentialSpecialization equation P = 0
  /-- The next separant specialization is nonzero. -/
  separantSpecialization_ne_zero :
    differentialSpecialization (separant equation activeJet) P ≠ 0
  /-- `activeJet` is the computed highest active jet. -/
  highestActiveJet_eq : highestActiveJet equation = some activeJet
  /-- Characteristic bounds inherited along the recursion path. -/
  belowCharacteristic : IsBelowCharacteristic D equation

/-- Every bounded solution of a nonzero below-characteristic equation reaches a regular leaf.

The proof is well-founded recursion on `jetDegreeMeasure`.  It only produces a leaf whose
separant specialization is a nonzero polynomial; it does not choose a scalar witness center or
enumerate a lifted solution. -/
theorem exists_regularRecursionLeaf [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0)
    (hchar : IsBelowCharacteristic D Q) (P : BoundedSolution Q D) :
    Nonempty (RegularRecursionLeaf Q D P.polynomial) := by
  let motive := fun current : DifferentialPolynomial F d ↦
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 →
        IsBelowCharacteristic D current →
          differentialSpecialization current P.polynomial = 0 →
            Nonempty (RegularRecursionLeaf Q D P.polynomial)
  have recurse : ∀ current, motive current := by
    intro current
    apply (singularStep_wellFounded (F := F) (d := d)).induction current
    intro equation ih hreachable hne heqChar hsolution
    cases hactive : highestActiveJet equation with
    | none =>
        exact (hne (eq_zero_of_boundedSolution_of_highestActiveJet_eq_none equation hactive
          ⟨P.1, hsolution⟩)).elim
    | some s =>
        by_cases hseparant :
            differentialSpecialization (separant equation s) P.polynomial = 0
        · have hstep := singularStep_separant equation s hactive (heqChar.2 s)
          have hcontract := singularStep_preserves_contract heqChar hstep
          exact ih (separant equation s) hstep
            (Relation.ReflTransGen.head hstep hreachable) hcontract.1 hcontract.2 hseparant
        · exact ⟨{
            equation := equation
            activeJet := s
            reachable := hreachable
            solves := hsolution
            separantSpecialization_ne_zero := hseparant
            highestActiveJet_eq := hactive
            belowCharacteristic := heqChar
          }⟩
  exact recurse Q Relation.ReflTransGen.refl hQ hchar P.equation

/-- Any scalar point avoiding a regular leaf's nonzero separant specialization is a regular
witness center for that leaf equation. -/
theorem RegularRecursionLeaf.isRegularJet_of_eval_ne_zero
    {root : DifferentialPolynomial F d} {D : ℕ} {P : F[X]}
    (leaf : RegularRecursionLeaf root D P) (center : F)
    (hcenter :
      (differentialSpecialization (separant leaf.equation leaf.activeJet) P).eval center ≠ 0) :
    IsRegularJet leaf.equation leaf.activeJet center (polynomialJet center P) := by
  constructor
  · rw [← eval_differentialSpecialization, leaf.solves]
    simp
  · rw [← eval_differentialSpecialization]
    exact hcenter

end

end HiddenDerivative
end ReedSolomon
