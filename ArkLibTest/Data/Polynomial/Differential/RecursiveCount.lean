/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.BaseChange
import ArkLib.Data.Polynomial.Differential.RecursiveCount
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for recursive counting

* `Y₀ + Y₁` has total jet degree `1` and jet degrees summing to `2`, so
  `jetTotalDegree_le_sum_jetDegree` can be strict.
* Over `ZMod 2`, the zero equation and `Y₀ ^ 2 = 0` each have the solution `0`, while every
  hypothesis of `card_mul_le_jetTotalDegree_mul` other than `Q ≠ 0`, respectively the cast
  hypothesis, holds with `left = 1` and `cost = 0`. The conclusion `1 * 1 ≤ _ * 0` fails.
* The source statement `boundedSolution_recursive_counting_of_jetDegree_le` at ArkLib revision
  a5aa2677fee4e3a79d6bb05136631cce4a08587d, with its regular-branch budget over bounded solutions
  and the characteristic guard `IsBelowCharacteristic D Q` written out, follows from
  `card_mul_le_jetTotalDegree_mul` and `jetTotalDegree_le_mul`.
* The source statement `boundedSolution_sub_mul_le_of_jetDegree_le` (from
  `RootFinding/FiniteField/ExtensionRootCount.lean`) follows from `card_mul_le_jetTotalDegree_mul`
  with the regular count `card_mul_sub_le_of_isHighestActiveJet` as the regular-part bound and the
  monotonicity lemmas along the singular chain.
-/

namespace PolynomialDifferential

noncomputable section

open Finset Polynomial

/-! ### Total and individual jet degrees -/

private def sumEquation : DifferentialPolynomial ℚ 1 :=
  MvPolynomial.X (some 0) + MvPolynomial.X (some 1)

private theorem mem_support_sumEquation (j : Fin 2) :
    Finsupp.single (some j) 1 ∈ sumEquation.support := by
  fin_cases j <;> simp [sumEquation, MvPolynomial.mem_support_iff, MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff]

/-- `Y₀ + Y₁` has total jet degree `1` while its jet degrees sum to `2`. -/
example : jetTotalDegree sumEquation = 1 ∧ ∑ j : Fin 2, jetDegree sumEquation j = 2 := by
  have hdeg (j : Fin 2) : jetDegree sumEquation j = 1 := by
    refine le_antisymm ?_ ?_
    · refine MvPolynomial.degreeOf_le_iff.mpr fun u hu ↦ ?_
      have hsub := MvPolynomial.support_add hu
      simp only [MvPolynomial.support_X, mem_union, mem_singleton] at hsub
      rcases hsub with rfl | rfl <;> simp [Finsupp.single_apply] <;> split_ifs <;> simp
    · have h := MvPolynomial.monomial_le_degreeOf (some j) (mem_support_sumEquation j)
      rw [Finsupp.single_eq_same] at h
      exact h
  refine ⟨le_antisymm ?_ ((hdeg 0).symm.le.trans (jetDegree_le_total _ 0)), by simp [hdeg]⟩
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  have hsub := MvPolynomial.support_add hu
  simp only [MvPolynomial.support_X, mem_union, mem_singleton] at hsub
  rcases hsub with rfl | rfl <;> simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

/-! ### The hypotheses of the recursive count are needed -/

private def squareEquation : DifferentialPolynomial (ZMod 2) 0 :=
  MvPolynomial.X (some 0) ^ 2

private theorem separant_zero : separant (0 : DifferentialPolynomial (ZMod 2) 0) 0 = 0 := by
  rw [separant, map_zero]

private theorem separant_squareEquation : separant squareEquation 0 = 0 := by
  rw [separant, squareEquation, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self, mul_one]
  change MvPolynomial.C ((2 : ℕ) : ZMod 2) * MvPolynomial.X (some 0) ^ 1 = 0
  rw [ZMod.natCast_self, MvPolynomial.C_0, zero_mul]

private theorem highestActiveJet_zero :
    highestActiveJet (0 : DifferentialPolynomial (ZMod 2) 0) = none :=
  (highestActiveJet_eq_none_iff _).mpr (by simp [DependsOnJet, jetDegree])

/-- Every equation reached from `Y₀ ^ 2` over `ZMod 2` by singular steps is `Y₀ ^ 2` or `0`. -/
private theorem reach_squareEquation {Q : DifferentialPolynomial (ZMod 2) 0}
    (hQ : Relation.ReflTransGen (SingularStep (F := ZMod 2) (d := 0)) Q squareEquation) :
    Q = squareEquation ∨ Q = 0 := by
  induction hQ using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | head hstep _ ih =>
      obtain ⟨s, hs, rfl⟩ := hstep
      rcases ih with h | h <;> subst h
      · rw [Fin.fin_one_eq_zero s, separant_squareEquation]
        exact Or.inr rfl
      · rw [highestActiveJet_zero] at hs
        exact absurd hs (Option.some_ne_none s).symm

private theorem zero_solves {Q : DifferentialPolynomial (ZMod 2) 0}
    (hQ : Q = squareEquation ∨ Q = 0) : differentialSpecialization Q 0 = 0 := by
  rcases hQ with rfl | rfl
  · rw [squareEquation, ← differentialSpecializationHom_apply, map_pow,
      differentialSpecializationHom_apply, differentialSpecialization_jet]
    simp
  · rw [← differentialSpecializationHom_apply, map_zero]

/-- The cast hypothesis is needed. Over `ZMod 2`, the equation `Y₀ ^ 2` is nonzero and every
separant along its singular chain is `0`, so every regular part is empty and the regular budget
holds with `cost = 0`; yet `0` is a solution. -/
example : ¬∀ roots : Finset (ZMod 2)[X],
    (∀ P ∈ roots, differentialSpecialization squareEquation P = 0) →
    (∀ (current : DifferentialPolynomial (ZMod 2) 0) (s : Fin 1),
      Relation.ReflTransGen (SingularStep (F := ZMod 2) (d := 0)) current squareEquation →
        highestActiveJet current = some s → ∀ regular ⊆ roots,
          (∀ P ∈ regular, differentialSpecialization current P = 0 ∧
            differentialSpecialization (separant current s) P ≠ 0) →
            1 * regular.card ≤ 0) →
    1 * roots.card ≤ jetTotalDegree squareEquation * 0 := by
  intro h
  have := h {0} (fun P hP ↦ by rw [mem_singleton.mp hP]; exact zero_solves (Or.inl rfl))
    fun current s hreach _ regular _ hregular ↦ by
      have hsep : separant current s = 0 := by
        rw [Fin.fin_one_eq_zero s]
        rcases reach_squareEquation hreach with rfl | rfl
        · exact separant_squareEquation
        · exact separant_zero
      rw [card_eq_zero.mpr (eq_empty_of_forall_notMem fun P hP ↦ (hregular P hP).2 (by
        rw [hsep, ← differentialSpecializationHom_apply, map_zero]))]
  simp at this

/-- `Q ≠ 0` is needed. The zero equation has no active jet, so the regular budget is vacuous,
and it satisfies the cast hypotheses; yet `0` is a solution. -/
example : ¬∀ roots : Finset (ZMod 2)[X],
    (∀ P ∈ roots, differentialSpecialization (0 : DifferentialPolynomial (ZMod 2) 0) P = 0) →
    (∀ (current : DifferentialPolynomial (ZMod 2) 0) (s : Fin 1),
      Relation.ReflTransGen (SingularStep (F := ZMod 2) (d := 0)) current 0 →
        highestActiveJet current = some s → ∀ regular ⊆ roots,
          (∀ P ∈ regular, differentialSpecialization current P = 0 ∧
            differentialSpecialization (separant current s) P ≠ 0) →
            1 * regular.card ≤ 0) →
    1 * roots.card ≤ jetTotalDegree (0 : DifferentialPolynomial (ZMod 2) 0) * 0 := by
  intro h
  have := h {0} (fun P _ ↦ by rw [← differentialSpecializationHom_apply, map_zero])
    fun current s hreach hs ↦ by
      have hcurrent : current = 0 := by
        clear hs
        induction hreach using Relation.ReflTransGen.head_induction_on with
        | refl => rfl
        | head hstep _ ih =>
            obtain ⟨s', hs', rfl⟩ := hstep
            rw [ih, highestActiveJet_zero] at hs'
            exact absurd hs' (Option.some_ne_none s').symm
      rw [hcurrent, highestActiveJet_zero] at hs
      exact absurd hs (Option.some_ne_none s).symm
  simp at this

/-! ### Source-shaped statements -/

/-- Source shape: `boundedSolution_recursive_counting_of_jetDegree_le`. The source's
`RegularBranchBudget Q D left cost` and `IsBelowCharacteristic D Q` are written out. The source
indexes regular parts by bounded solutions of the current equation; here they are converted to
finite sets of polynomials. -/
example {F : Type*} [CommRing F] [IsDomain F] {d D : ℕ} (Q : DifferentialPolynomial F d)
    (hQ : Q ≠ 0) (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (left cost Δ : ℕ) (roots : Finset (BoundedSolution Q D))
    (hDegree : ∀ s, jetDegree Q s ≤ Δ)
    (hRegular : ∀ (current : DifferentialPolynomial F d) (s : Fin (d + 1)),
      Relation.ReflTransGen (SingularStep (F := F) (d := d)) current Q →
        highestActiveJet current = some s →
          (D < ringChar F ∧ ∀ j, jetDegree current j < ringChar F) →
            ∀ regular : Finset (BoundedSolution current D),
              (∀ solution ∈ regular,
                differentialSpecialization (separant current s) solution.polynomial ≠ 0) →
                left * regular.card ≤ cost) :
    left * roots.card ≤ ((d + 1) * Δ) * cost := by
  classical
  have hpoly : Function.Injective (BoundedSolution.polynomial (Q := Q) (D := D)) :=
    fun P P' h ↦ Subtype.ext (Subtype.ext h)
  have hcount := card_mul_le_jetTotalDegree_mul hQ
    (fun j ↦ jetDegreeCastsNeZero_of_ringChar (Or.inr (hchar.2 j))) (roots.map ⟨_, hpoly⟩)
    (fun P hP ↦ by obtain ⟨P, -, rfl⟩ := mem_map.mp hP; exact P.equation)
    (left := left) (cost := cost) fun current s hreach hs regular hsub hregular ↦ by
      have hdeg (P : F[X]) (hP : P ∈ regular) : P ∈ degreeLT F (D + 1) := by
        obtain ⟨P, -, rfl⟩ := mem_map.mp (hsub hP)
        exact P.1.2
      let lift : regular ↪ BoundedSolution current D :=
        ⟨fun P ↦ ⟨⟨P.1, hdeg P.1 P.2⟩, (hregular P.1 P.2).1⟩, fun P P' h ↦
          Subtype.ext (congrArg (fun x : BoundedSolution current D ↦ x.polynomial) h)⟩
      have h := hRegular current s hreach hs
        ⟨hchar.1, fun j ↦ (jetDegree_le_of_reflTransGen_singularStep hreach j).trans_lt
          (hchar.2 j)⟩ (regular.attach.map lift) fun x hx ↦ by
            obtain ⟨P, -, rfl⟩ := mem_map.mp hx
            exact (hregular P.1 P.2).2
      rwa [card_map, card_attach] at h
  rw [card_map] at hcount
  exact hcount.trans (Nat.mul_le_mul_right _ (jetTotalDegree_le_mul Q hDegree))

/-- Source shape: `boundedSolution_sub_mul_le_of_jetDegree_le`, from
`RootFinding/FiniteField/ExtensionRootCount.lean`. The regular part at each equation `current`
on the singular chain is bounded by the regular count, whose hypotheses at `current` follow from
those at `Q` by monotonicity along the chain. The recursive composition then multiplies by
`jetTotalDegree Q ≤ (d + 1) * t`. -/
example {F : Type*} [Field F] [Finite F] {d D : ℕ} (Q : DifferentialPolynomial F d) (H t : ℕ)
    (hQ : Q ≠ 0) (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H)
    (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F * ((d + 1) * t ^ 2 * Nat.card F ^ d) := by
  classical
  have := Fintype.ofFinite (BoundedSolution Q D)
  have hpoly : Function.Injective (BoundedSolution.polynomial (Q := Q) (D := D)) :=
    fun P P' h ↦ Subtype.ext (Subtype.ext h)
  have hcount := card_mul_le_jetTotalDegree_mul hQ
    (fun j ↦ jetDegreeCastsNeZero_of_ringChar (Or.inr (hchar.2 j))) (univ.map ⟨_, hpoly⟩)
    (fun P hP ↦ by obtain ⟨P, -, rfl⟩ := mem_map.mp hP; exact P.equation)
    (left := Nat.card F - H) (cost := Nat.card F * (t * Nat.card F ^ d))
    fun current s hreach hs regular hsub hregular ↦ by
      have h := card_mul_sub_le_of_isHighestActiveJet current
        (isHighestActiveJet_of_highestActiveJet_eq_some hs) regular
        (fun P hP ↦ (hregular P hP).1)
        (fun P hP ↦ by obtain ⟨P, -, rfl⟩ := mem_map.mp (hsub hP); exact P.degree_le)
        (fun k hk hkD ↦ natCast_choose_ne_zero_of_ringChar (s := s.val) (Or.inr hchar.1) k hk hkD)
        (H := H) ((Nat.sub_le _ _).trans
          ((differentialWeightedDegree_le_of_reflTransGen_singularStep hreach).trans hWeight))
        fun P hP ↦ (hregular P hP).2
      rw [mul_comm]
      exact h.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        ((jetDegree_le_of_reflTransGen_singularStep hreach s).trans (hDegree s))))
  rw [card_map, card_univ, ← Nat.card_eq_fintype_card] at hcount
  calc
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
        jetTotalDegree Q * (Nat.card F * (t * Nat.card F ^ d)) := hcount
    _ ≤ (d + 1) * t * (Nat.card F * (t * Nat.card F ^ d)) :=
      Nat.mul_le_mul_right _ (jetTotalDegree_le_mul Q hDegree)
    _ = Nat.card F * ((d + 1) * t ^ 2 * Nat.card F ^ d) := by ring

end

end PolynomialDifferential
