/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for witness counting

* The source statements `boundedSolution_counting_pow_le_of_bad` and
  `regularBranch_counting_pow_le` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, with
  their degree budget `Δ ≥ jetDegree Q s`, the factor order `(q - H) * #roots`, finite sets of
  bounded solutions, and the characteristic guard `D < ringChar F`, follow from the generalized
  theorems.
* Over `ZMod 2`, the equation `y' = 0` at depth `1` with `D = 2` has the three solutions `1`,
  `X ^ 2` and `1 + X ^ 2`. Every hypothesis of `card_mul_sub_le_of_isHighestActiveJet` other than
  the binomial one holds with `H = 0`, and the conclusion `3 * 2 ≤ 2 * (1 * 2)` fails; here
  `(2 choose 1) = 0` in `ZMod 2`.
* When `q ≤ H` the count is vacuous: the left side is `#roots * 0`.
-/

namespace PolynomialDifferential

noncomputable section

open Finset Polynomial

variable {F : Type*} {d : ℕ}

/-- Source shape: `boundedSolution_counting_pow_le_of_bad`, stated for a finite set of bounded
solutions with exceptional sets indexed by bounded solutions and a degree budget `Δ`. The
predicate `IsRegularWitness s solution point` of the source is written out as nonvanishing of the
specialized separant. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (D H Δ : ℕ)
    (roots : Finset (BoundedSolution Q D)) (bad : BoundedSolution Q D → Finset F)
    (hBadCard : ∀ solution ∈ roots, (bad solution).card ≤ H)
    (hCoverage : ∀ solution ∈ roots, ∀ point : F, point ∉ bad solution →
      (differentialSpecialization (separant Q s) solution.polynomial).eval point ≠ 0)
    (hJetInj : ∀ point : F,
      Set.InjOn (fun solution : BoundedSolution Q D ↦
        polynomialJet (d := d) point solution.polynomial)
        {solution | solution ∈ roots ∧
          (differentialSpecialization (separant Q s) solution.polynomial).eval point ≠ 0})
    (hDegree : jetDegree Q s ≤ Δ) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ * Nat.card F ^ d := by
  classical
  have hpoly : Function.Injective (BoundedSolution.polynomial (Q := Q) (D := D)) :=
    fun P P' h ↦ Subtype.ext (Subtype.ext h)
  let bad' : F[X] → Finset F := fun P ↦
    if h : ∃ x ∈ roots, x.polynomial = P then bad h.choose else ∅
  have hbad' : ∀ x ∈ roots, bad' x.polynomial = bad x := by
    intro x hx
    have h : ∃ y ∈ roots, y.polynomial = x.polynomial := ⟨x, hx, rfl⟩
    simp only [bad', h, ↓reduceDIte]
    rw [hpoly h.choose_spec.2]
  have h := card_mul_sub_le_of_card_bad_le Q s (roots.map ⟨_, hpoly⟩) bad' H
    (fun P hP ↦ by obtain ⟨x, _, rfl⟩ := mem_map.mp hP; exact x.equation)
    (fun P hP ↦ by obtain ⟨x, hx, rfl⟩ := mem_map.mp hP; simpa [hbad' x hx] using hBadCard x hx)
    (fun P hP a ha ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hP
      exact hCoverage x hx a (by simpa [hbad' x hx] using ha))
    (fun a P hP P' hP' hjet ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hP.1
      obtain ⟨x', hx', rfl⟩ := mem_map.mp hP'.1
      exact congrArg _ (hJetInj a ⟨hx, hP.2⟩ ⟨hx', hP'.2⟩ hjet))
  rw [card_map] at h
  calc (Nat.card F - H) * roots.card = roots.card * (Nat.card F - H) := mul_comm _ _
    _ ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := h
    _ ≤ Nat.card F * Δ * Nat.card F ^ d := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDegree)

/-- Source shape: `regularBranch_counting_pow_le`, over a finite field with the characteristic
guard `D < ringChar F`, the weighted-degree hypothesis `differentialWeightedDegree D Q ≤ H`, and a
degree budget `Δ`. -/
example [Field F] [Finite F] {D : ℕ} (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (H Δ : ℕ) (hs : IsHighestActiveJet Q s) (hD : D < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H) (hDegree : jetDegree Q s ≤ Δ)
    (roots : Finset (BoundedSolution Q D))
    (hRegular : ∀ solution ∈ roots,
      differentialSpecialization (separant Q s) solution.polynomial ≠ 0) :
    (Nat.card F - H) * roots.card ≤ Nat.card F * Δ * Nat.card F ^ d := by
  have h := BoundedSolution.card_mul_sub_le_of_isHighestActiveJet Q hs roots
    (natCast_choose_ne_zero_of_ringChar (Or.inr hD)) (tsub_le_self.trans hWeight) hRegular
  calc (Nat.card F - H) * roots.card = roots.card * (Nat.card F - H) := mul_comm _ _
    _ ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := h
    _ ≤ Nat.card F * Δ * Nat.card F ^ d := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDegree)

/-- When `q ≤ H`, every solution may have no regular witness and the count says nothing: the left
side is zero. -/
example [CommRing F] [IsDomain F] [Finite F] (roots : Finset F[X]) {H : ℕ}
    (hH : Nat.card F ≤ H) : roots.card * (Nat.card F - H) = 0 := by
  rw [Nat.sub_eq_zero_of_le hH, mul_zero]

/-- The equation `y' = 0` over `ZMod 2`, as the differential polynomial `Y₁`. -/
private abbrev constEquation : DifferentialPolynomial (ZMod 2) 1 :=
  MvPolynomial.X (some 1)

private theorem differentialSpecialization_constEquation (P : (ZMod 2)[X]) :
    differentialSpecialization constEquation P = derivative P := by
  simp [constEquation, differentialSpecialization, differentialSpecializationHom,
    hasseDeriv_one]

/-- The three solutions `1`, `X ^ 2` and `1 + X ^ 2` of `y' = 0` over `ZMod 2`. -/
private abbrev constRoots : Finset (ZMod 2)[X] :=
  {1, X ^ 2, 1 + X ^ 2}

private theorem card_constRoots : constRoots.card = 3 := by
  have h01 : (1 : (ZMod 2)[X]) ≠ X ^ 2 := fun h ↦ by
    simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 0) h
  have h02 : (1 : (ZMod 2)[X]) ≠ 1 + X ^ 2 := fun h ↦ by
    simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 2) h
  have h12 : (X ^ 2 : (ZMod 2)[X]) ≠ 1 + X ^ 2 := fun h ↦ by
    simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 0) h
  rw [card_insert_of_notMem (by simp [h01, h02]), card_insert_of_notMem (by simp [h12]),
    card_singleton]

/-- The binomial hypothesis of `card_mul_sub_le_of_isHighestActiveJet` cannot be dropped. For
`y' = 0` over `ZMod 2` with `s = 1`, `D = 2` and `H = 0`: `Y₁` is the highest active jet variable,
the three roots are solutions of degree at most `2` with separant `1`, the weighted-degree
hypothesis holds, the binomial coefficient `(1 + 1 choose 1)` vanishes, and the conclusion
fails. -/
example :
    IsHighestActiveJet constEquation 1 ∧
      (∀ P ∈ constRoots, differentialSpecialization constEquation P = 0) ∧
      (∀ P ∈ constRoots, P.degree ≤ 2) ∧
      differentialWeightedDegree 2 constEquation - (2 - (1 : Fin 2).val) ≤ 0 ∧
      (∀ P ∈ constRoots, differentialSpecialization (separant constEquation 1) P ≠ 0) ∧
      ((1 + (1 : Fin 2).val).choose (1 : Fin 2).val : ZMod 2) = 0 ∧
      ¬ constRoots.card * (Nat.card (ZMod 2) - 0) ≤
        Nat.card (ZMod 2) * (jetDegree constEquation 1 * Nat.card (ZMod 2) ^ 1) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, by decide, ?_⟩
  · refine ⟨by simp [DependsOnJet, jetDegree], fun j hj ↦ ?_⟩
    simp [DependsOnJet, jetDegree, MvPolynomial.degreeOf_X, hj.ne']
  · intro P hP
    simp only [mem_insert, mem_singleton] at hP
    rw [differentialSpecialization_constEquation]
    rcases hP with rfl | rfl | rfl
    · simp
    · rw [derivative_X_pow, show ((2 : ℕ) : ZMod 2) = 0 by decide, map_zero, zero_mul]
    · rw [derivative_add, derivative_one, derivative_X_pow,
        show ((2 : ℕ) : ZMod 2) = 0 by decide, map_zero, zero_mul, zero_add]
  · intro P hP
    simp only [mem_insert, mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    · exact degree_one_le.trans (by norm_num)
    · exact (degree_X_pow_le 2).trans (by norm_num)
    · exact (degree_add_le _ _).trans (max_le (degree_one_le.trans (by norm_num))
        ((degree_X_pow_le 2).trans (by norm_num)))
  · unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
    rw [MvPolynomial.support_X]
    simp [Finsupp.weight_apply]
  · intro P _
    simp [separant, constEquation, differentialSpecialization, differentialSpecializationHom]
  · have hdeg : jetDegree constEquation 1 = 1 := MvPolynomial.degreeOf_X_self _
    rw [card_constRoots, hdeg, Nat.card_zmod]
    decide

end

end PolynomialDifferential
