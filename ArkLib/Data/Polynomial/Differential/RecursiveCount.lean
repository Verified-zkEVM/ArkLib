/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.SingularRecursion

/-!
# Counting solutions along the singular recursion

The `SOLVE` procedure of [Kop15] splits the solutions of `Q = 0` at the highest active jet `Y_s` of
`Q`: a solution `P` is regular when the separant specialization `(∂Q/∂Y_s)(X, P, D¹P, …)` is
nonzero, and singular otherwise, in which case it solves the separant equation and the procedure
recurses on `∂Q/∂Y_s`. This file turns a bound on every regular part into a bound on all solutions.

Suppose that every finite set of regular solutions met along the chain of singular steps below
`Q` satisfies `left * #regular ≤ cost`. Then every finite set of solutions of `Q` satisfies
`left * #roots ≤ jetTotalDegree Q * cost`. Each singular step lowers `jetTotalDegree` by at least
one, so at most `jetTotalDegree Q` equations on the chain contribute a regular part; an equation
with no active jet that is nonzero contributes nothing. The cast hypotheses and `NoZeroDivisors`
keep every equation on the chain nonzero (`singularStep_preserves`).

The file also records that the degree budgets used by the regular counts do not increase along
the chain, and bounds `jetTotalDegree` by the sum of the individual jet degrees.

The regular-part bound used with this composition is
`BoundedSolution.card_mul_sub_le_of_isHighestActiveJet`. The root count
`card_mul_sub_le_jetTotalDegree_mul` in `ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount`
is sharper than the composition by the factor `t` in the regular cost.

## Main statements

* `differentialWeightedDegree_le_of_reflTransGen_singularStep`,
  `jetDegree_le_of_reflTransGen_singularStep`, `jetTotalDegree_le_of_reflTransGen_singularStep`:
  degree budgets are monotone along the singular chain.
* `jetTotalDegree_le_sum_jetDegree` and `jetTotalDegree_le_mul`: the total jet degree is at most
  the sum of the individual jet degrees, hence at most `(d + 1) * t` when each is at most `t`.
* `card_mul_le_jetTotalDegree_mul`: the recursive composition of regular-part bounds.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.3 and Section 4.2.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ} [CommSemiring F]

/-! ### Degree budgets along the singular chain -/

/-- A singular step does not increase the root-specialization weighted degree, since a partial
derivative does not increase any weighted total degree. -/
theorem differentialWeightedDegree_le_of_singularStep {D : ℕ}
    {next current : DifferentialPolynomial F d} (hstep : SingularStep next current) :
    differentialWeightedDegree D next ≤ differentialWeightedDegree D current := by
  obtain ⟨s, _, rfl⟩ := hstep
  exact MvPolynomial.weightedTotalDegree_pderiv_le (differentialWeight D) (some s) current

/-- A singular step does not increase any individual jet degree. -/
theorem jetDegree_le_of_singularStep {next current : DifferentialPolynomial F d}
    (hstep : SingularStep next current) (j : Fin (d + 1)) :
    jetDegree next j ≤ jetDegree current j := by
  obtain ⟨s, _, rfl⟩ := hstep
  exact jetDegree_separant_le current s j

/-- A singular step does not increase the total jet degree. It lowers it strictly
(`jetTotalDegree_lt_of_singularStep`); this is the non-strict form used for monotonicity. -/
theorem jetTotalDegree_le_of_singularStep {next current : DifferentialPolynomial F d}
    (hstep : SingularStep next current) : jetTotalDegree next ≤ jetTotalDegree current :=
  (jetTotalDegree_lt_of_singularStep hstep).le

/-- A function that does not increase along one singular step does not increase along the
reflexive-transitive closure. -/
private theorem le_of_reflTransGen_singularStep (f : DifferentialPolynomial F d → ℕ)
    (hf : ∀ {next current}, SingularStep next current → f next ≤ f current)
    {descendant root : DifferentialPolynomial F d}
    (hreach : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root) :
    f descendant ≤ f root := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hf hstep)

/-- The root-specialization weighted degree is monotone along the singular chain: every equation
reached from `root` by singular steps has weighted degree at most that of `root`. -/
theorem differentialWeightedDegree_le_of_reflTransGen_singularStep {D : ℕ}
    {descendant root : DifferentialPolynomial F d}
    (hreach : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root) :
    differentialWeightedDegree D descendant ≤ differentialWeightedDegree D root :=
  le_of_reflTransGen_singularStep _ differentialWeightedDegree_le_of_singularStep hreach

/-- Every individual jet degree is monotone along the singular chain. -/
theorem jetDegree_le_of_reflTransGen_singularStep {descendant root : DifferentialPolynomial F d}
    (hreach : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root)
    (j : Fin (d + 1)) : jetDegree descendant j ≤ jetDegree root j :=
  le_of_reflTransGen_singularStep (jetDegree · j) (jetDegree_le_of_singularStep · j) hreach

/-- The total jet degree is monotone along the singular chain. -/
theorem jetTotalDegree_le_of_reflTransGen_singularStep
    {descendant root : DifferentialPolynomial F d}
    (hreach : Relation.ReflTransGen (SingularStep (F := F) (d := d)) descendant root) :
    jetTotalDegree descendant ≤ jetTotalDegree root :=
  le_of_reflTransGen_singularStep _ jetTotalDegree_le_of_singularStep hreach

/-! ### Total and individual jet degrees -/

/-- The total jet degree is at most the sum of the individual jet degrees. The inequality can be
strict: `Y₀ + Y₁` has total jet degree `1` and individual degrees `1` and `1`. -/
theorem jetTotalDegree_le_sum_jetDegree (Q : DifferentialPolynomial F d) :
    jetTotalDegree Q ≤ ∑ j : Fin (d + 1), jetDegree Q j := by
  refine (jetTotalDegree_le_iff Q _).mpr fun u hu ↦ ?_
  rw [totalJetDegree_eq_sum]
  exact Finset.sum_le_sum fun j _ ↦ MvPolynomial.monomial_le_degreeOf (some j) hu

/-- If every individual jet degree is at most `t`, the total jet degree is at most `(d + 1) * t`.
-/
theorem jetTotalDegree_le_mul (Q : DifferentialPolynomial F d) {t : ℕ}
    (hdegree : ∀ j, jetDegree Q j ≤ t) : jetTotalDegree Q ≤ (d + 1) * t :=
  (jetTotalDegree_le_sum_jetDegree Q).trans <| by
    simpa using Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ hdegree j

/-! ### Recursive composition of regular counts -/

/-- **Recursive counting.** Let `F` have no zero divisors, `Q ≠ 0`, and let `Q` satisfy the cast
hypotheses at every jet. Let `roots` be a finite set of solutions of `Q = 0`. Suppose that for
every equation `current` reached from `Q` by singular steps, with highest active jet `Y_s`, every
subset of `roots` consisting of solutions of `current = 0` with nonzero separant specialization in
`Y_s` satisfies `left * #regular ≤ cost`. Then `left * #roots ≤ jetTotalDegree Q * cost`.

The proof follows the singular chain. At each equation, `roots` splits into the regular part and
the part that solves the separant equation; the latter is counted at the next equation, whose
total jet degree is smaller by at least one. A nonzero equation with no active jet has no
solutions, so the recursion ends with an empty set.

The hypotheses `Q ≠ 0` and the casts are needed: over `ZMod 2` the zero equation, or `Y₀ ^ 2 = 0`
(whose separant is `0`), has solutions but no regular part, so `hregular` holds with `cost = 0`
while `roots` is nonempty. -/
theorem card_mul_le_jetTotalDegree_mul [NoZeroDivisors F] {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j) (roots : Finset F[X])
    (hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0) {left cost : ℕ}
    (hregular : ∀ (current : DifferentialPolynomial F d) (s : Fin (d + 1)),
      Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
        highestActiveJet current = some s → ∀ regular ⊆ roots,
          (∀ P ∈ regular, differentialSpecialization current P = 0 ∧
            differentialSpecialization (separant current s) P ≠ 0) →
            left * regular.card ≤ cost) :
    left * roots.card ≤ jetTotalDegree Q * cost := by
  classical
  suffices h : ∀ current, Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
      current ≠ 0 → (∀ j, JetDegreeCastsNeZero current j) → ∀ S ⊆ roots,
        (∀ P ∈ S, differentialSpecialization current P = 0) →
          left * S.card ≤ jetTotalDegree current * cost from
    h Q Relation.ReflTransGen.refl hQ hcast roots subset_rfl hsolution
  intro current
  induction current using (singularStep_wellFounded (F := F) (d := d)).induction with
  | _ equation ih =>
  intro hreach hne hequation S hS hsolves
  cases hactive : highestActiveJet equation with
  | none =>
      have hempty : S = ∅ := Finset.eq_empty_of_forall_notMem fun P hP ↦ hne
        (eq_zero_of_differentialSpecialization_eq_zero_of_highestActiveJet_eq_none hactive
          (hsolves P hP))
      simp [hempty]
  | some s =>
      have hstep := singularStep_separant equation hactive
      have hnext := singularStep_preserves hequation hstep
      set singular := S.filter fun P ↦ differentialSpecialization (separant equation s) P = 0
      set regular := S.filter fun P ↦ ¬differentialSpecialization (separant equation s) P = 0
      have hreg : left * regular.card ≤ cost :=
        hregular equation s hreach hactive regular ((Finset.filter_subset _ _).trans hS)
          fun P hP ↦ ⟨hsolves P (Finset.filter_subset _ _ hP), (Finset.mem_filter.mp hP).2⟩
      have hsing : left * singular.card ≤ jetTotalDegree (separant equation s) * cost :=
        ih _ hstep (Relation.ReflTransGen.head hstep hreach) hnext.1 hnext.2 singular
          ((Finset.filter_subset _ _).trans hS) fun P hP ↦ (Finset.mem_filter.mp hP).2
      have hlt := jetTotalDegree_lt_of_singularStep hstep
      calc
        left * S.card = left * singular.card + left * regular.card := by
          rw [← Finset.card_filter_add_card_filter_not
            (fun P ↦ differentialSpecialization (separant equation s) P = 0), Nat.mul_add]
        _ ≤ jetTotalDegree (separant equation s) * cost + cost := Nat.add_le_add hsing hreg
        _ = (jetTotalDegree (separant equation s) + 1) * cost := by ring
        _ ≤ jetTotalDegree equation * cost := Nat.mul_le_mul_right cost hlt

end

end PolynomialDifferential
