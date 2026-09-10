/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.Counting
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.RegularJetCounting


/-!
# Counting regular witnesses for bounded differential solutions

This file connects the generic incidence bound in `Counting` with the fixed-point regular-jet
bound in `RegularJetCounting`.  The only solution-specific input is injectivity of the polynomial
jet on the regular roots at each witness point.  The differential equation itself is supplied by
`BoundedSolution.equation`.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {d : ℕ}

/-- A field point is a regular witness for a bounded solution when the selected separant does not
vanish on the solution's Hasse jet there. -/
def IsRegularWitness [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (s : Fin (d + 1)) (solution : BoundedSolution Q D) (point : F) : Prop :=
  jetEvaluation (separant Q s) point (polynomialJet point solution.polynomial) ≠ 0

/-- Package a regular witness of a bounded solution as a regular jet at the fixed witness point.
The equation component is discharged by `BoundedSolution.equation`. -/
def _root_.PolynomialDifferential.BoundedSolution.regularJetAt
    [CommSemiring F] {Q : DifferentialPolynomial F d} {D : ℕ}
    {s : Fin (d + 1)} (solution : BoundedSolution Q D) (point : F)
    (hregular : IsRegularWitness s solution point) : RegularJetAt Q s point := by
  refine ⟨polynomialJet point solution.polynomial, ?_, hregular⟩
  rw [← eval_differentialSpecialization Q solution.polynomial point, solution.equation]
  simp

@[simp]
theorem _root_.PolynomialDifferential.BoundedSolution.regularJetAt_value
    [CommSemiring F]
    {Q : DifferentialPolynomial F d} {D : ℕ} {s : Fin (d + 1)}
    (solution : BoundedSolution Q D) (point : F)
    (hregular : IsRegularWitness s solution point) :
    (solution.regularJetAt point hregular).1 = polynomialJet point solution.polynomial :=
  rfl

/-- Field points where the separant specialized along a bounded solution vanishes.

This is defined as a filter of the whole field rather than as `Polynomial.rootSet`, so it still
has the intended meaning when the specialized separant is the zero polynomial. -/
def separantBadPoints [CommSemiring F] [Fintype F] {Q : DifferentialPolynomial F d} {D : ℕ}
    (s : Fin (d + 1)) (solution : BoundedSolution Q D) : Finset F := by
  classical
  exact Finset.univ.filter fun point ↦
    (differentialSpecialization (separant Q s) solution.polynomial).eval point = 0

@[simp]
theorem mem_separantBadPoints [CommSemiring F] [Fintype F]
    {Q : DifferentialPolynomial F d} {D : ℕ} {s : Fin (d + 1)}
    (solution : BoundedSolution Q D) (point : F) :
    point ∈ separantBadPoints s solution ↔
      (differentialSpecialization (separant Q s) solution.polynomial).eval point = 0 := by
  simp [separantBadPoints]

/-- Membership in the canonical bad-point set is exactly failure of regularity as a witness. -/
theorem mem_separantBadPoints_iff_not_isRegularWitness [Field F] [Fintype F]
    {Q : DifferentialPolynomial F d} {D : ℕ} {s : Fin (d + 1)}
    (solution : BoundedSolution Q D) (point : F) :
    point ∈ separantBadPoints s solution ↔ ¬IsRegularWitness s solution point := by
  rw [mem_separantBadPoints, eval_differentialSpecialization]
  simp [IsRegularWitness]

/-- A nonzero specialized separant has at most its natural degree many bad field points. -/
theorem card_separantBadPoints_le_natDegree [Field F] [Fintype F]
    {Q : DifferentialPolynomial F d} {D : ℕ} (s : Fin (d + 1))
    (solution : BoundedSolution Q D)
    (hnonzero : differentialSpecialization (separant Q s) solution.polynomial ≠ 0) :
    (separantBadPoints s solution).card ≤
      (differentialSpecialization (separant Q s) solution.polynomial).natDegree := by
  let p := differentialSpecialization (separant Q s) solution.polynomial
  have hsets : (↑(separantBadPoints s solution) : Set F) = p.rootSet F := by
    ext point
    change point ∈ separantBadPoints s solution ↔ point ∈ p.rootSet F
    rw [Polynomial.mem_rootSet_of_ne (by simpa [p] using hnonzero)]
    exact mem_separantBadPoints solution point
  calc
    (separantBadPoints s solution).card =
        Set.ncard (↑(separantBadPoints s solution) : Set F) :=
      (Set.ncard_coe_finset _).symm
    _ = Set.ncard (p.rootSet F) := congrArg Set.ncard hsets
    _ ≤ p.natDegree := Polynomial.ncard_rootSet_le p F

/-- Count bounded solutions using root-dependent exceptional witness sets.

At every field point, injectivity of the polynomial-jet map on the regular roots embeds the
point fibre into `RegularJetAt Q s point`.  Its cardinality is therefore at most
`jetDegree Q s * |F| ^ d`, and `hDegree` weakens this to the requested `Δ * |F| ^ d` bound.
No comparison between `H` and `|F|` is required. -/
theorem boundedSolution_counting_pow_le_of_bad [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D H Δ : ℕ)
    (roots : Finset (BoundedSolution Q D))
    (bad : BoundedSolution Q D → Finset F)
    (hBadCard : ∀ solution ∈ roots, (bad solution).card ≤ H)
    (hCoverage :
      ∀ solution ∈ roots, ∀ point : F, point ∉ bad solution →
        IsRegularWitness s solution point)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := d) point solution.polynomial)
        {solution | solution ∈ roots ∧ IsRegularWitness s solution point})
    (hDegree : jetDegree Q s ≤ Δ) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ * Nat.card F ^ d := by
  classical
  let _ := Fintype.ofFinite F
  have hCoverage' :
      ∀ solution ∈ roots, ∀ point ∈ (Finset.univ : Finset F),
        point ∉ bad solution → IsRegularWitness s solution point := by
    intro solution hsolution point _hpoint hpoint
    exact hCoverage solution hsolution point hpoint
  have hWitnessFibers :
      ∀ point ∈ (Finset.univ : Finset F),
        (roots.filter fun solution ↦ IsRegularWitness s solution point).card ≤
          Δ * (Finset.univ : Finset F).card ^ d := by
    intro point _hpoint
    let regularRoots := roots.filter fun solution ↦ IsRegularWitness s solution point
    let _ : Fintype (RegularJetAt Q s point) := by
      unfold RegularJetAt
      infer_instance
    let encode : regularRoots → RegularJetAt Q s point :=
      fun solution ↦ solution.1.regularJetAt point (by
        have hmem : solution.1 ∈
            roots.filter fun root ↦ IsRegularWitness s root point := by
          change solution.1 ∈ regularRoots
          exact solution.2
        exact (Finset.mem_filter.mp hmem).2)
    have hEncode : Function.Injective encode := by
      intro left right heq
      apply Subtype.ext
      apply hJetInj point
      · exact Finset.mem_filter.mp (by
          change left.1 ∈ regularRoots
          exact left.2)
      · exact Finset.mem_filter.mp (by
          change right.1 ∈ regularRoots
          exact right.2)
      · exact congrArg Subtype.val heq
    calc
      (roots.filter fun solution ↦ IsRegularWitness s solution point).card =
          regularRoots.card := rfl
      _ ≤ Nat.card (RegularJetAt Q s point) := by
        simpa [Nat.card_eq_fintype_card] using
          Nat.card_le_card_of_injective encode hEncode
      _ ≤ jetDegree Q s * Nat.card F ^ d := natCard_regularJetAt_le Q s point
      _ ≤ Δ * Nat.card F ^ d := Nat.mul_le_mul_right (Nat.card F ^ d) hDegree
      _ = Δ * (Finset.univ : Finset F).card ^ d := by
        rw [Finset.card_univ, Nat.card_eq_fintype_card]
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
    witness_counting_pow_le_of_bad roots Finset.univ bad
      (fun solution point ↦ IsRegularWitness s solution point) H Δ d
      hBadCard hCoverage' hWitnessFibers

/-- Count bounded solutions using the canonical zero set of the specialized separant.

The bad-set cardinality and regular-witness coverage required by
`boundedSolution_counting_pow_le_of_bad` follow from the two degree hypotheses. -/
theorem boundedSolution_counting_pow_le [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D H Δ : ℕ)
    (roots : Finset (BoundedSolution Q D))
    (hSeparantNonzero : ∀ solution ∈ roots,
      differentialSpecialization (separant Q s) solution.polynomial ≠ 0)
    (hSeparantDegree : ∀ solution ∈ roots,
      (differentialSpecialization (separant Q s) solution.polynomial).natDegree ≤ H)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := d) point solution.polynomial)
        {solution | solution ∈ roots ∧ IsRegularWitness s solution point})
    (hDegree : jetDegree Q s ≤ Δ) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ * Nat.card F ^ d := by
  classical
  let _ := Fintype.ofFinite F
  apply boundedSolution_counting_pow_le_of_bad Q s D H Δ roots
    (fun solution ↦ separantBadPoints s solution)
  · intro solution hsolution
    exact (card_separantBadPoints_le_natDegree s solution
      (hSeparantNonzero solution hsolution)).trans (hSeparantDegree solution hsolution)
  · intro solution _hsolution point hpoint
    exact Classical.not_not.mp ((mem_separantBadPoints_iff_not_isRegularWitness
      solution point).not.mp hpoint)
  · exact hJetInj
  · exact hDegree

/-! ### Boundary canaries -/

namespace RegularWitnessCountingCanary

/-- When `Δ = 0`, the adapter forces the full right-hand side to zero. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (D H : ℕ) (roots : Finset (BoundedSolution Q D))
    (bad : BoundedSolution Q D → Finset F)
    (hBadCard : ∀ solution ∈ roots, (bad solution).card ≤ H)
    (hCoverage : ∀ solution ∈ roots, ∀ point : F, point ∉ bad solution →
      IsRegularWitness s solution point)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := d) point solution.polynomial)
        {solution | solution ∈ roots ∧ IsRegularWitness s solution point})
    (hDegree : jetDegree Q s ≤ 0) :
    (Nat.card F - H) * roots.card = 0 := by
  have hbound := boundedSolution_counting_pow_le_of_bad Q s D H 0 roots bad
    hBadCard hCoverage hJetInj hDegree
  exact Nat.eq_zero_of_le_zero (by simpa using hbound)

/-- At derivative order zero, the per-point exponent disappears rather than contributing an
extra field-cardinality factor. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F 0) (s : Fin 1)
    (D H Δ : ℕ) (roots : Finset (BoundedSolution Q D))
    (bad : BoundedSolution Q D → Finset F)
    (hBadCard : ∀ solution ∈ roots, (bad solution).card ≤ H)
    (hCoverage : ∀ solution ∈ roots, ∀ point : F, point ∉ bad solution →
      IsRegularWitness s solution point)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := 0) point solution.polynomial)
        {solution | solution ∈ roots ∧ IsRegularWitness s solution point})
    (hDegree : jetDegree Q s ≤ Δ) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ := by
  simpa using boundedSolution_counting_pow_le_of_bad Q s D H Δ roots bad
    hBadCard hCoverage hJetInj hDegree

end RegularWitnessCountingCanary

end

end ReedSolomon.HiddenDerivative
