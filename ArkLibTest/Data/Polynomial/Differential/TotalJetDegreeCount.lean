/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount
import ArkLib.Data.Polynomial.Differential.WitnessCount
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for the total-jet-degree count

* Over `ZMod 3`, `y' = 0` with `D = 2` gives `H = 0` and at most `3` solutions of degree at most
  `2`; the three constants attain the bound.
* Over `ZMod 2` with `D = 0`, the zero equation has the solutions `0` and `1` and total jet
  degree `0`, so `Q ≠ 0` is needed.
* Over `ZMod 2` with `D = 2`, `y' = 0` satisfies every hypothesis of
  `card_mul_sub_le_jetTotalDegree_mul` other than the binomial one, and `1`, `X ^ 2`,
  `1 + X ^ 2` violate the conclusion.
* Over a finite field with the characteristic guard `D < ringChar F` and
  `jetDegree Q j < ringChar F`, the counts follow from the general ones: with a bound `Δ` on the
  total jet degree, over an extension `FiniteField.Extension F (ringChar F) e`, with the budget
  from an interpolation degree, and with a bound `t` on every jet degree.
-/

namespace PolynomialDifferential

noncomputable section

open Finset Polynomial

/-! ### A sharp instance -/

/-- The differential polynomial `Y₁`, i.e. the equation `y' = 0`. -/
private abbrev constEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  MvPolynomial.X (some 1)

private theorem differentialSpecialization_constEquation {F : Type*} [CommRing F] (P : F[X]) :
    differentialSpecialization (constEquation F) P = derivative P := by
  simp [constEquation, differentialSpecialization, differentialSpecializationHom,
    hasseDeriv_one]

private theorem jetTotalDegree_constEquation_le {F : Type*} [CommRing F] [Nontrivial F] :
    jetTotalDegree (constEquation F) ≤ 1 := by
  refine (jetTotalDegree_le_iff _ 1).mpr fun u hu ↦ ?_
  rw [MvPolynomial.support_X, mem_singleton] at hu
  rw [hu]
  simp [totalJetDegree_eq_sum, Fin.sum_univ_two]

private theorem differentialWeightedDegree_constEquation {F : Type*} [CommRing F] [Nontrivial F] :
    differentialWeightedDegree 2 (constEquation F) = 1 := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_X]
  simp [Finsupp.weight_apply]

private theorem castsNeZero_constEquation {F : Type*} [CommRing F] [Nontrivial F]
    (j : Fin 2) : JetDegreeCastsNeZero (constEquation F) j := by
  intro k hk hkj
  have : jetDegree (constEquation F) j ≤ 1 :=
    (jetDegree_le_total _ j).trans jetTotalDegree_constEquation_le
  obtain rfl : k = 1 := by omega
  simp

/-- Over `ZMod 3`, `y' = 0` has at most `3` solutions of degree at most `2`: the weighted degree
is `1`, so `H = 1 - (2 - 1) = 0`, and the count reads `N * 3 ≤ 3 * (1 * 3)`. -/
example : Nat.card (BoundedSolution (constEquation (ZMod 3)) 2) ≤ 3 := by
  have h : Nat.card (BoundedSolution (constEquation (ZMod 3)) 2) * (Nat.card (ZMod 3) - 0) ≤
      Nat.card (ZMod 3) * (jetTotalDegree (constEquation (ZMod 3)) * Nat.card (ZMod 3) ^ 1) :=
    BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul (MvPolynomial.X_ne_zero _)
      castsNeZero_constEquation (H := 0)
      (fun k s ↦ natCast_choose_ne_zero_of_ringChar (F := ZMod 3) (D := 2) (s := s)
        (Or.inr (by rw [ZMod.ringChar_zmod_n]; decide)) k)
      (by rw [differentialWeightedDegree_constEquation])
  rw [Nat.card_zmod, Nat.sub_zero] at h
  have := jetTotalDegree_constEquation_le (F := ZMod 3)
  have : 3 * (jetTotalDegree (constEquation (ZMod 3)) * 3 ^ 1) ≤ 3 * 3 := by
    rw [pow_one]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The bound of the previous example is attained: the three constants solve `y' = 0`. -/
example : ((univ : Finset (ZMod 3)).image C).card = 3 ∧
    ∀ P ∈ (univ : Finset (ZMod 3)).image C,
      differentialSpecialization (constEquation (ZMod 3)) P = 0 ∧ P.degree ≤ 2 := by
  refine ⟨by rw [card_image_of_injective _ C_injective, card_univ, ZMod.card], fun P hP ↦ ?_⟩
  obtain ⟨c, -, rfl⟩ := mem_image.mp hP
  exact ⟨by rw [differentialSpecialization_constEquation, derivative_C],
    degree_C_le.trans (by norm_num)⟩

/-! ### The hypotheses are needed -/

/-- `Q ≠ 0` is needed: over `ZMod 2` with `D = 0` and `H = 0`, the zero equation has the solutions
`0` and `1`, and `2 * 2 > 2 * (0 * 1)`. -/
example : ¬(({0, 1} : Finset (ZMod 2)[X]).card * (Nat.card (ZMod 2) - 0) ≤
    Nat.card (ZMod 2) * (jetTotalDegree (0 : DifferentialPolynomial (ZMod 2) 0) *
      Nat.card (ZMod 2) ^ 0)) := by
  have h0 : jetTotalDegree (0 : DifferentialPolynomial (ZMod 2) 0) = 0 := by
    exact Nat.le_zero.mp ((jetTotalDegree_le_iff _ 0).mpr (by simp))
  rw [h0, card_insert_of_notMem (by simp), card_singleton]
  simp

/-- The binomial hypothesis is needed: over `ZMod 2` with `D = 2` and `H = 0`, `y' = 0` satisfies
`Q ≠ 0`, the cast hypotheses and the weighted-degree hypothesis, the three polynomials `1`,
`X ^ 2`, `1 + X ^ 2` are solutions of degree at most `2`, and `3 * 2 > 2 * (1 * 2)`. The binomial
coefficient `(1 + 1 choose 1)` vanishes in `ZMod 2`. -/
example : constEquation (ZMod 2) ≠ 0 ∧ (∀ j, JetDegreeCastsNeZero (constEquation (ZMod 2)) j) ∧
    (∀ P ∈ ({1, X ^ 2, 1 + X ^ 2} : Finset (ZMod 2)[X]),
      differentialSpecialization (constEquation (ZMod 2)) P = 0 ∧ P.degree ≤ 2) ∧
    differentialWeightedDegree 2 (constEquation (ZMod 2)) - (2 - 1) ≤ 0 ∧
    ((1 + 1).choose 1 : ZMod 2) = 0 ∧
    ¬(({1, X ^ 2, 1 + X ^ 2} : Finset (ZMod 2)[X]).card * (Nat.card (ZMod 2) - 0) ≤
      Nat.card (ZMod 2) * (jetTotalDegree (constEquation (ZMod 2)) * Nat.card (ZMod 2) ^ 1)) := by
  have htwo : ((2 : ℕ) : ZMod 2) = 0 := by decide
  refine ⟨MvPolynomial.X_ne_zero _, castsNeZero_constEquation, fun P hP ↦ ?_,
    by rw [differentialWeightedDegree_constEquation], by decide, fun h ↦ ?_⟩
  · simp only [mem_insert, mem_singleton] at hP
    rw [differentialSpecialization_constEquation]
    rcases hP with rfl | rfl | rfl
    · exact ⟨derivative_one, degree_one_le.trans (by norm_num)⟩
    · exact ⟨by rw [derivative_X_pow, htwo, map_zero, zero_mul],
        (degree_X_pow_le 2).trans (by norm_num)⟩
    · exact ⟨by rw [derivative_add, derivative_one, derivative_X_pow, htwo, map_zero, zero_mul,
        zero_add], (degree_add_le _ _).trans (max_le (degree_one_le.trans (by norm_num))
          ((degree_X_pow_le 2).trans (by norm_num)))⟩
  · have h01 : (1 : (ZMod 2)[X]) ≠ X ^ 2 := fun h ↦ by
      simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 0) h
    have h02 : (1 : (ZMod 2)[X]) ≠ 1 + X ^ 2 := fun h ↦ by
      simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 2) h
    have h12 : (X ^ 2 : (ZMod 2)[X]) ≠ 1 + X ^ 2 := fun h ↦ by
      simpa [coeff_X_pow, coeff_one] using congrArg (coeff · 0) h
    rw [card_insert_of_notMem (by simp [h01, h02]), card_insert_of_notMem (by simp [h12]),
      card_singleton, Nat.card_zmod] at h
    have := jetTotalDegree_constEquation_le (F := ZMod 2)
    have : 2 * (jetTotalDegree (constEquation (ZMod 2)) * 2 ^ 1) ≤ 4 := by
      rw [pow_one]; omega
    omega

/-! ### Forms with the characteristic guard -/

variable {F : Type*} {d D : ℕ}

/-- The characteristic guard gives the cast and binomial hypotheses. -/
private theorem hypotheses_of_ringChar [Field F] {Q : DifferentialPolynomial F d}
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F) :
    (∀ j, JetDegreeCastsNeZero Q j) ∧
      ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0 :=
  ⟨fun j ↦ jetDegreeCastsNeZero_of_ringChar (Or.inr (hchar.2 j)),
    fun _ _ ↦ natCast_choose_ne_zero_of_ringChar (Or.inr hchar.1) _⟩

/-- The count over a finite field with a bound `Δ` on the total jet degree. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (H Δ : ℕ) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H) (hDegree : jetTotalDegree Q ≤ Δ) :
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤ Δ * Nat.card F ^ (d + 1) := by
  have h := BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul hQ
    (hypotheses_of_ringChar hchar).1 (hypotheses_of_ringChar hchar).2 hWeight
  calc
    (Nat.card F - H) * Nat.card (BoundedSolution Q D) ≤
        Nat.card F * (jetTotalDegree Q * Nat.card F ^ d) := by rw [mul_comm]; exact h
    _ ≤ Nat.card F * (Δ * Nat.card F ^ d) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hDegree)
    _ = Δ * Nat.card F ^ (d + 1) := by ring

/-- The count when `2 * H ≤ q`, with a bound `Δ` on the total jet degree. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (H Δ : ℕ) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H) (hDegree : jetTotalDegree Q ≤ Δ)
    (hlarge : 2 * H ≤ Nat.card F) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ d :=
  (BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul hQ (hypotheses_of_ringChar hchar).1
    (hypotheses_of_ringChar hchar).2 hWeight hlarge).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDegree))

/-- The count with witnesses in `FiniteField.Extension F (ringChar F) e`. -/
theorem natCard_le_extension_two_totalJetDegree [Field F] [Finite F]
    (Q : DifferentialPolynomial F d) (e H Δ : ℕ) (he : 0 < e) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q - (D - d) ≤ H) (hDegree : jetTotalDegree Q ≤ Δ)
    (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ (e * d) :=
  (BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_extension hQ
    (hypotheses_of_ringChar hchar).1 (hypotheses_of_ringChar hchar).2 hWeight he hlarge).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDegree))

/-- The extension count with the budget from an interpolation degree. An interpolation step produces
`Q` with `differentialWeightedDegree D Q < L`; with `d ≤ D` this gives the budget
`H = L + d - (D + 1)`. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (e L Δ : ℕ) (he : 0 < e)
    (hdD : d ≤ D) (hQ : Q ≠ 0) (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q < L) (hDegree : jetTotalDegree Q ≤ Δ)
    (hlarge : 2 * (L + d - (D + 1)) ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * Δ * Nat.card F ^ (e * d) :=
  natCard_le_extension_two_totalJetDegree Q e _ Δ he hQ hchar (by omega) hDegree hlarge

/-- The extension count with a bound `t` on every jet degree. The count is the total-jet-degree
count over `FiniteField.Extension F (ringChar F) e`, and
`jetTotalDegree Q ≤ (d + 1) * t ≤ (d + 1) * t ^ 2`. -/
theorem extension_sub_mul_le [Field F] [Finite F] (Q : DifferentialPolynomial F d) (e H t : ℕ)
    (he : 0 < e) (hQ : Q ≠ 0) (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H) (hDegree : ∀ s, jetDegree Q s ≤ t) :
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
      Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d)) := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have : NeZero e := ⟨he.ne'⟩
  set E := FiniteField.Extension F (ringChar F) e
  have hcard : Nat.card E = Nat.card F ^ e := FiniteField.natCard_extension F (ringChar F) e
  set f := algebraMap F E
  have hf : Function.Injective f := f.injective
  obtain ⟨hcast, hbinom⟩ := hypotheses_of_ringChar hchar
  have hQE : MvPolynomial.map f Q ≠ 0 := fun h ↦
    hQ (MvPolynomial.map_injective f hf (by rw [h, map_zero]))
  have hcount := BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul hQE
    (fun j ↦ (jetDegreeCastsNeZero_map_iff hf Q j).mpr (hcast j)) (H := H)
    (fun k s hk hks ↦ by
      rw [← map_natCast f]
      exact (map_ne_zero_iff f hf).mpr (hbinom k s hk hks))
    (by rw [differentialWeightedDegree_map_eq f hf]; exact (Nat.sub_le _ _).trans hWeight)
  rw [jetTotalDegree_map_eq hf, hcard] at hcount
  have htotal : jetTotalDegree Q ≤ (d + 1) * t ^ 2 :=
    (jetTotalDegree_le_mul Q hDegree).trans (Nat.mul_le_mul_left _ (show t ≤ t ^ 2 by
      rw [sq]; exact Nat.le_mul_self t))
  calc
    (Nat.card F ^ e - H) * Nat.card (BoundedSolution Q D) ≤
        (Nat.card F ^ e - H) * Nat.card (BoundedSolution (MvPolynomial.map f Q) D) :=
      Nat.mul_le_mul_left _ (BoundedSolution.natCard_le_natCard_map hf Q D)
    _ ≤ Nat.card F ^ e * (jetTotalDegree Q * Nat.card F ^ (e * d)) := by
      rw [mul_comm, pow_mul]; exact hcount
    _ ≤ Nat.card F ^ e * ((d + 1) * t ^ 2 * Nat.card F ^ (e * d)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ htotal)

/-- The extension count with a bound `t` on every jet degree, when `2 * H ≤ q ^ e`. -/
theorem natCard_le_extension_pow [Field F] [Finite F] (Q : DifferentialPolynomial F d)
    (e H t : ℕ) (he : 0 < e) (hQ : Q ≠ 0)
    (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H) (hDegree : ∀ s, jetDegree Q s ≤ t)
    (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * (d + 1) * t ^ 2 * Nat.card F ^ (e * d) := by
  have h := natCard_le_extension_two_totalJetDegree Q e H _ he hQ hchar
    ((Nat.sub_le _ _).trans hWeight)
    ((jetTotalDegree_le_mul Q hDegree).trans (Nat.mul_le_mul_left (d + 1) (show t ≤ t ^ 2 by
      rw [sq]; exact Nat.le_mul_self t))) hlarge
  simpa [mul_assoc] using h

/-- The extension count with the jet degrees bounded by `ringChar F ≤ q`. -/
example [Field F] [Finite F] (Q : DifferentialPolynomial F d) (e H : ℕ) (he : 0 < e)
    (hQ : Q ≠ 0) (hchar : D < ringChar F ∧ ∀ j, jetDegree Q j < ringChar F)
    (hWeight : differentialWeightedDegree D Q ≤ H) (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * (d + 1) * Nat.card F ^ 2 * Nat.card F ^ (e * d) := by
  have := Fintype.ofFinite F
  have hCharCard : ringChar F ≤ Nat.card F := by
    obtain ⟨n, _, hcard⟩ := FiniteField.card F (ringChar F)
    apply Nat.le_of_dvd Nat.card_pos
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self _ n.ne_zero
  exact natCard_le_extension_pow Q e H _ he hQ hchar hWeight
    (fun s ↦ (hchar.2 s).le.trans hCharCard) hlarge

end

end PolynomialDifferential
