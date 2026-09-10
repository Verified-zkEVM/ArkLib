/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.SingularRecursion
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.DegreeBounds.SpecializationDegree
/-!
# Counting through the singular separant recursion

This file supplies the cardinality-composition layer of Kopparty's `SOLVE` recursion from
[Kop15, Theorem 4.3 and Section 4.2].  At every equation in the deterministic separant chain,
the bounded solutions split into a regular part and a singular part.  The singular part embeds
injectively into the bounded solutions of the next separant equation.  Because the sum of the
individual jet degrees strictly decreases at each singular step, a uniform bound for every
regular part accumulates at most `jetDegreeMeasure Q` times.

The central theorem is deliberately conditional on a regular-branch counting inequality.  The
condition is the seam at which regular-jet uniqueness and finite-field witness counting enter;
this file neither assumes iterated lifting nor claims an executable solver.  Keeping the
inequality division-free also preserves the exact finite-field arithmetic used by the later
root-counting theorem.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.3 and Section 4.2.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} {d D : ℕ} [CommSemiring F]

/-- A uniform division-free cardinality budget for the regular part at every equation on the
canonical singular chain below `root`.

The quantifier over finite sets is intentional: recursive counting only needs the regular
solutions inherited from the caller's current finite set, rather than all bounded solutions in
the ambient type. -/
def RegularBranchBudget (root : DifferentialPolynomial F d) (D left cost : ℕ) : Prop :=
  ∀ (current : DifferentialPolynomial F d) (s : Fin (d + 1)),
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current root →
      highestActiveJet current = some s →
        IsBelowCharacteristic D current →
          ∀ regular : Finset (BoundedSolution current D),
            (∀ solution ∈ regular,
              differentialSpecialization (separant current s) solution.polynomial ≠ 0) →
              left * regular.card ≤ cost

/-- The regular side of one separant split. -/
noncomputable def regularSolutions (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (roots : Finset (BoundedSolution Q D)) :
    Finset (BoundedSolution Q D) := by
  classical
  exact roots.filter fun solution ↦
    differentialSpecialization (separant Q s) solution.polynomial ≠ 0

/-- The singular side of one separant split. -/
noncomputable def singularSolutions (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (roots : Finset (BoundedSolution Q D)) :
    Finset (BoundedSolution Q D) := by
  classical
  exact roots.filter fun solution ↦
    differentialSpecialization (separant Q s) solution.polynomial = 0

/-- Every singular solution in `roots` becomes a bounded solution of the next separant
equation.  This is the finite set transported down one deterministic recursion step. -/
noncomputable def singularDescendants (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (roots : Finset (BoundedSolution Q D)) :
    Finset (BoundedSolution (separant Q s) D) := by
  classical
  let singular := singularSolutions Q s D roots
  exact singular.attach.image fun solution : singular ↦
    ⟨solution.1.1, (Finset.mem_filter.mp (show
      solution.1 ∈ roots.filter fun candidate ↦
        differentialSpecialization (separant Q s) candidate.polynomial = 0 by
      simpa [singular, singularSolutions] using solution.2)).2⟩

/-- Transporting the singular part down one separant step loses no elements. -/
theorem card_singularDescendants (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (roots : Finset (BoundedSolution Q D)) :
    (singularDescendants Q s D roots).card =
      (singularSolutions Q s D roots).card := by
  classical
  let singular := singularSolutions Q s D roots
  let descend : singular → BoundedSolution (separant Q s) D := fun solution ↦
    ⟨solution.1.1, (Finset.mem_filter.mp (show
      solution.1 ∈ roots.filter fun candidate ↦
        differentialSpecialization (separant Q s) candidate.polynomial = 0 by
      simpa [singular, singularSolutions] using solution.2)).2⟩
  have hdescend : Function.Injective descend := by
    intro left right heq
    have hvals : left.1.1 = right.1.1 :=
      congrArg (fun solution : BoundedSolution (separant Q s) D ↦ solution.1) heq
    exact Subtype.ext (Subtype.ext hvals)
  change (singular.attach.image descend).card = singular.card
  rw [Finset.card_image_of_injective _ hdescend, Finset.card_attach]

/-- The regular and singular filters form an exact partition of a finite solution set. -/
theorem card_regular_add_card_singular (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (D : ℕ) (roots : Finset (BoundedSolution Q D)) :
    (regularSolutions Q s D roots).card + (singularSolutions Q s D roots).card = roots.card := by
  classical
  simpa only [regularSolutions, singularSolutions, not_ne_iff] using
    Finset.card_filter_add_card_filter_not (s := roots)
    (fun solution ↦
      differentialSpecialization (separant Q s) solution.polynomial ≠ 0)

/-- A regular-branch inequality composes through the complete deterministic separant chain.

If every regular part costs at most `cost` after multiplication by `left`, then the original
finite solution set costs at most `jetDegreeMeasure Q * cost`.  The proof follows the computed
highest active jet, transports the singular filter injectively to the next equation, and recurses
using the strict `jetDegreeMeasure` decrease.  A nonzero terminal equation contributes no
solutions. -/
theorem boundedSolution_recursive_counting [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (left cost : ℕ) (roots : Finset (BoundedSolution Q D))
    (hRegular : RegularBranchBudget Q D left cost) :
    left * roots.card ≤ jetDegreeMeasure Q * cost := by
  classical
  let motive := fun current : DifferentialPolynomial F d ↦
    Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 →
        IsBelowCharacteristic D current →
          ∀ currentRoots : Finset (BoundedSolution current D),
            left * currentRoots.card ≤ jetDegreeMeasure current * cost
  have recurse : ∀ current, motive current := by
    intro current
    apply (singularStep_wellFounded (F := F) (d := d)).induction current
    intro equation ih hreachable hne heqChar currentRoots
    cases hactive : highestActiveJet equation with
    | none =>
        let _ : IsEmpty (BoundedSolution equation D) :=
          isEmpty_boundedSolution_of_highestActiveJet_eq_none equation hne hactive
        have hroots : currentRoots = ∅ := by
          ext solution
          exact isEmptyElim solution
        simp [hroots]
    | some s =>
        let regularRoots := regularSolutions equation s D currentRoots
        let singularRoots := singularSolutions equation s D currentRoots
        let nextRoots := singularDescendants equation s D currentRoots
        have hstep : SingularStep (separant equation s) equation :=
          singularStep_separant equation s hactive (heqChar.2 s)
        have hnextContract := singularStep_preserves_contract heqChar hstep
        have hregular : left * regularRoots.card ≤ cost := by
          apply hRegular equation s hreachable hactive heqChar regularRoots
          intro solution hsolution
          exact (Finset.mem_filter.mp (show
            solution ∈ currentRoots.filter fun candidate ↦
              differentialSpecialization (separant equation s) candidate.polynomial ≠ 0 by
            simpa [regularRoots, regularSolutions] using hsolution)).2
        have hnext : left * nextRoots.card ≤
            jetDegreeMeasure (separant equation s) * cost := by
          exact ih (separant equation s) hstep
            (Relation.ReflTransGen.head hstep hreachable) hnextContract.1 hnextContract.2 nextRoots
        have hsingular : left * singularRoots.card ≤
            jetDegreeMeasure (separant equation s) * cost := by
          rw [← card_singularDescendants equation s D currentRoots]
          exact hnext
        have hpartition : regularRoots.card + singularRoots.card = currentRoots.card := by
          exact card_regular_add_card_singular equation s D currentRoots
        have hmeasure : jetDegreeMeasure (separant equation s) + 1 ≤
            jetDegreeMeasure equation := by
          exact Nat.succ_le_iff.mpr (jetDegreeMeasure_lt_of_singularStep hstep)
        calc
          left * currentRoots.card =
              left * regularRoots.card + left * singularRoots.card := by
                rw [← hpartition, Nat.mul_add]
          _ ≤ cost + jetDegreeMeasure (separant equation s) * cost :=
            Nat.add_le_add hregular hsingular
          _ = (jetDegreeMeasure (separant equation s) + 1) * cost := by
            simp [Nat.add_mul, Nat.add_comm]
          _ ≤ jetDegreeMeasure equation * cost := Nat.mul_le_mul_right cost hmeasure
  exact recurse Q Relation.ReflTransGen.refl hQ hchar roots

/-- A uniform individual jet-degree bound controls the number of regular stages in the singular
chain by `(d + 1) * Δ`. -/
theorem jetDegreeMeasure_le_mul (Q : DifferentialPolynomial F d) (Δ : ℕ)
    (hDegree : ∀ s, jetDegree Q s ≤ Δ) :
    jetDegreeMeasure Q ≤ (d + 1) * Δ := by
  rw [jetDegreeMeasure]
  calc
    ∑ s : Fin (d + 1), jetDegree Q s ≤ ∑ _s : Fin (d + 1), Δ := by
      apply Finset.sum_le_sum
      intro s _hs
      exact hDegree s
    _ = (d + 1) * Δ := by simp

/-- Explicit degree-budget form of `boundedSolution_recursive_counting`: no more than
`(d + 1) * Δ` regular stages can contribute. -/
theorem boundedSolution_recursive_counting_of_jetDegree_le
    [NoZeroDivisors F] [Nontrivial F]
    (Q : DifferentialPolynomial F d) (hQ : Q ≠ 0) (hchar : IsBelowCharacteristic D Q)
    (left cost Δ : ℕ) (roots : Finset (BoundedSolution Q D))
    (hDegree : ∀ s, jetDegree Q s ≤ Δ)
    (hRegular : RegularBranchBudget Q D left cost) :
    left * roots.card ≤ ((d + 1) * Δ) * cost := by
  exact (boundedSolution_recursive_counting Q hQ hchar left cost roots hRegular).trans
    (Nat.mul_le_mul_right cost (jetDegreeMeasure_le_mul Q Δ hDegree))

end

/-! ### Degree budgets along the singular chain -/

noncomputable section

variable {F : Type*} {d D : ℕ}

/-- A singular step cannot increase the root-specialization weighted degree. -/
theorem differentialWeightedDegree_le_of_singularStep [CommSemiring F]
    {next current : DifferentialPolynomial F d} (hstep : SingularStep next current) :
    differentialWeightedDegree D next ≤ differentialWeightedDegree D current := by
  obtain ⟨s, _hs, _hchar, rfl⟩ := hstep
  exact weightedTotalDegree_pderiv_le (differentialWeight D) (some s) current

/-- A singular step cannot increase any individual jet degree. -/
theorem jetDegree_le_of_singularStep [CommSemiring F]
    {next current : DifferentialPolynomial F d}
    (hstep : SingularStep next current) (j : Fin (d + 1)) :
    jetDegree next j ≤ jetDegree current j := by
  obtain ⟨s, _hs, _hchar, rfl⟩ := hstep
  exact jetDegree_separant_le current s j

/-- Root-specialization weighted degree is monotone along the canonical singular chain. -/
theorem differentialWeightedDegree_le_of_reflTransGen_singularStep [CommSemiring F]
    {descendant root : DifferentialPolynomial F d}
    (hreaches : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root) :
    differentialWeightedDegree D descendant ≤ differentialWeightedDegree D root := by
  induction hreaches using Relation.ReflTransGen.trans_induction_on with
  | refl _equation => exact le_rfl
  | single hstep => exact differentialWeightedDegree_le_of_singularStep hstep
  | trans _hleft _hright ihleft ihrigh => exact ihleft.trans ihrigh

/-- Every individual jet degree is monotone along the canonical singular chain. -/
theorem jetDegree_le_of_reflTransGen_singularStep [CommSemiring F]
    {descendant root : DifferentialPolynomial F d}
    (hreaches : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root)
    (j : Fin (d + 1)) : jetDegree descendant j ≤ jetDegree root j := by
  induction hreaches using Relation.ReflTransGen.trans_induction_on with
  | refl _equation => exact le_rfl
  | single hstep => exact jetDegree_le_of_singularStep hstep j
  | trans _hleft _hright ihleft ihrigh => exact ihleft.trans ihrigh

end

end ReedSolomon.HiddenDerivative
