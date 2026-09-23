/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for loci in the rational Taylor chart

The main example is again `y' = 2x`, written as `Q = Y₁ - 2X`, at center `0`, with separant `1`
and the polynomial solution `X ^ 2`.

* The jet of `X ^ 2` is a zero of the high cuts for `k = 3` and of the initial equation, for any
  length and exponent; for `k = 2` and `K = 3` it is not a zero of the high cuts, so the degree
  hypothesis is needed.
* With `K = 2`, the chart equations involve only the initial jet. Agreement at the two points
  `0, 1` leaves at most one regular jet, while agreement at the single point `0` is satisfied by
  both `(0, 0)` and `(0, 1)`, so `k ≤ #ι` is needed.
* Over `ZMod 2`, `y' = 2x` becomes `y' = 0`, whose solutions `0` and `X ^ 2` have the same jet at
  `0`: the pivot hypothesis of `injOn_polynomialJet` is needed.
* Over `ZMod 2`, the polynomial `X (X - 1)` is a nonzero specialization that vanishes at every
  center, so `exists_forall_jetEvaluation_ne_zero` needs an infinite ring.

The file also derives the statement for the default exponent `τ = 2K` with `k` agreement points
given by an embedding `Fin k ↪ F`.
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-- The equation `y' = 2x`, as the differential polynomial `Y₁ - 2X`. -/
private abbrev linearEquation (F : Type*) [CommRing F] : DifferentialPolynomial F 1 :=
  X (some 1) - 2 * X none

/-- `X ^ 2` solves `y' = 2x` over every commutative ring. -/
private theorem differentialSpecialization_linearEquation (F : Type*) [CommRing F] :
    differentialSpecialization (linearEquation F) (Polynomial.X ^ 2) = 0 := by
  simp [linearEquation, differentialSpecialization, differentialSpecializationHom,
    Polynomial.hasseDeriv_one, one_add_one_eq_two, Polynomial.C_ofNat]

/-- The separant of `Y₁ - 2X` is `1`. -/
private theorem jetEvaluation_separant_linearEquation (F : Type*) [CommRing F] [Nontrivial F]
    (jet : Fin 2 → F) :
    jetEvaluation (separant (linearEquation F) (Fin.last 1)) 0 jet = 1 := by
  simp [separant, jetEvaluation, linearEquation, pderiv_X, Fin.last]

/-- The initial separant of `Y₁ - 2X` evaluates to `1` at every jet. -/
private theorem aeval_initialJetSeparant_linearEquation (F : Type*) [Field F]
    (jet : Fin 2 → F) :
    aeval jet (initialJetSeparant 0 (linearEquation F)) = 1 := by
  rw [aeval_initialJetSeparant, jetEvaluation_separant_linearEquation]

/-- The binomial pivots `(i choose 1)` for `1 < i` are nonzero in `ℚ`. -/
private theorem choose_one_ne_zero (i : ℕ) (hi : 1 < i) : (i.choose 1 : ℚ) ≠ 0 := by
  rw [Nat.choose_one_right]
  exact_mod_cast (by omega : i ≠ 0)

/-- `X ^ 2` has degree below `3`. -/
private theorem degree_X_sq_lt_three (F : Type*) [Field F] :
    (Polynomial.X ^ 2 : Polynomial F).degree < (3 : ℕ) := by
  rw [Polynomial.degree_X_pow]
  exact_mod_cast (by norm_num : 2 < 3)

/-- Over `ℚ`, the jet of `X ^ 2` is a regular zero of the initial equation and of the high cuts
for `k = 3`, for every length `K` and exponent `τ`. -/
example (K τ : ℕ) :
    polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ) ∈
        zeroLocus ℚ (Ideal.span {initialJetEquation 0 (linearEquation ℚ)} ⊔
          highTaylorCutsIdeal 0 (linearEquation ℚ) K 3 τ) ∧
      aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
        (initialJetSeparant 0 (linearEquation ℚ)) ≠ 0 :=
  polynomialJet_mem_zeroLocus_initialJetEquation_sup_highTaylorCutsIdeal 0 _ _
    (differentialSpecialization_linearEquation ℚ)
    (by rw [jetEvaluation_separant_linearEquation]; norm_num) τ (degree_X_sq_lt_three ℚ)
    (fun i hi _ ↦ choose_one_ne_zero i hi)

/-- The degree hypothesis of `polynomialJet_mem_zeroLocus_highTaylorCutsIdeal` is needed: the jet
of `X ^ 2` is not a zero of the high cuts for `k = 2` and `K = 3`, since the common numerator of
`c₂` evaluates to the Taylor coefficient `1`. -/
example : polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ) ∉
    zeroLocus ℚ (highTaylorCutsIdeal 0 (linearEquation ℚ) 3 2 1) := by
  rw [mem_zeroLocus_highTaylorCutsIdeal_iff]
  intro h
  have h2 := h 2 le_rfl (by norm_num)
  rw [aeval_commonTaylorNumerator 0 (linearEquation ℚ)
    (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ)) (by norm_num)
    (by rw [aeval_initialJetSeparant, jetEvaluation_separant_linearEquation]; norm_num),
    rationalTaylorCoefficient_eq_solution 0 (linearEquation ℚ) (Polynomial.X ^ 2)
      (differentialSpecialization_linearEquation ℚ)
      (by rw [jetEvaluation_separant_linearEquation]; norm_num) 2
      (fun i hi _ ↦ choose_one_ne_zero i hi), aeval_initialJetSeparant_linearEquation] at h2
  simp [Polynomial.coeff_X_pow] at h2

/-- With `K = 2` there are no high cuts for `k = 2`. -/
private theorem highTaylorCutsIdeal_two_two_le (τ : ℕ) (I : Ideal (MvPolynomial (Fin 2) ℚ)) :
    highTaylorCutsIdeal 0 (linearEquation ℚ) 2 2 τ ≤ I :=
  (highTaylorCutsIdeal_le_iff 0 _).mpr fun _ h2 hl ↦ absurd hl (by omega)

/-- With `K = 2` and any exponent, agreement at the two points `0` and `1` leaves at most one
regular jet for `y' = 2x`. -/
example (τ : ℕ) (received : Fin 2 → ℚ) :
    (regularAgreementCutLocus ⊥ 0 (linearEquation ℚ) 2 τ ![0, 1] received).Subsingleton :=
  regularAgreementCutLocus_subsingleton 0 _ (fun l ↦ by have := l.isLt; omega) (by norm_num)
    (highTaylorCutsIdeal_two_two_le τ ⊥)
    _ _ (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all) (by simp)

/-- Agreement at one point does not suffice for `k = 2`: with `K = 2` and `τ = 4`, the jets
`(0, 0)` and `(0, 1)` both lie in the regular agreement locus of `⊥` for the value `0` at `0`, so
the hypothesis `k ≤ #ι` of `regularAgreementCutLocus_subsingleton` is needed. -/
example : ¬ (regularAgreementCutLocus ⊥ 0 (linearEquation ℚ) 2 4 (fun _ : Unit ↦ 0)
    (fun _ ↦ 0)).Subsingleton := by
  have hmem : ∀ c : ℚ,
      ![0, c] ∈ regularAgreementCutLocus ⊥ 0 (linearEquation ℚ) 2 4 (fun _ : Unit ↦ 0)
        (fun _ ↦ 0) := by
    intro c
    refine ⟨by simp [zeroLocus_bot], by rw [aeval_initialJetSeparant_linearEquation]; simp,
      fun _ ↦ ?_⟩
    rw [taylorAgreementEquation_eq_zero_iff 0 _ (taylorExponentSufficient_two_mul 1 2) _
      (by rw [aeval_initialJetSeparant_linearEquation]; simp), eval_rationalTaylorPolynomial,
      Fin.sum_univ_two]
    have h0 : rationalTaylorCoefficient (0 : ℚ) (linearEquation ℚ) ![0, c] 0 = 0 := by
      simpa using rationalTaylorCoefficient_initial 0 (linearEquation ℚ) ![0, c] 0
    simp [h0]
  intro h
  have h01 := congrFun (h (hmem 0) (hmem 1)) 1
  simp at h01

/-- The pivot hypothesis of `injOn_polynomialJet` is needed: over `ZMod 2`, the equation
`y' = 2x` is `y' = 0`, and its solutions `0` and `X ^ 2`, of degree below `3` with separant `1`,
have the same jet at `0`. -/
example : polynomialJet (d := 1) 0 (0 : Polynomial (ZMod 2)) =
      polynomialJet 0 (Polynomial.X ^ 2) ∧
    differentialSpecialization (linearEquation (ZMod 2)) 0 = 0 ∧
    differentialSpecialization (linearEquation (ZMod 2)) (Polynomial.X ^ 2) = 0 ∧
    (0 : Polynomial (ZMod 2)) ≠ Polynomial.X ^ 2 := by
  refine ⟨?_, by simp [differentialSpecialization, differentialSpecializationHom,
      CharTwo.two_eq_zero],
    differentialSpecialization_linearEquation _, (pow_ne_zero 2 Polynomial.X_ne_zero).symm⟩
  funext i
  fin_cases i <;> simp [polynomialJet]

/-- Over `ℚ`, the jets at `0` of the solutions `X ^ 2` and `X ^ 2 + 1` of `y' = 2x` are
distinct. -/
example : (({Polynomial.X ^ 2, Polynomial.X ^ 2 + 1} : Finset (Polynomial ℚ)).image
    (polynomialJet (d := 1) 0)).card = 2 := by
  have hsol : differentialSpecialization (linearEquation ℚ) (Polynomial.X ^ 2 + 1) = 0 := by
    simp [linearEquation, differentialSpecialization, differentialSpecializationHom,
      Polynomial.hasseDeriv_one, one_add_one_eq_two, Polynomial.C_ofNat]
  have hne : (Polynomial.X ^ 2 : Polynomial ℚ) ≠ Polynomial.X ^ 2 + 1 := by
    intro h
    simpa using congrArg (Polynomial.eval 0) h
  rw [card_image_polynomialJet 0 (linearEquation ℚ) 3 (fun i hi _ ↦ choose_one_ne_zero i hi)]
  · exact Finset.card_pair hne
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact degree_X_sq_lt_three ℚ
    · rw [Finset.mem_singleton.mp hP]
      compute_degree!
  · intro P hP
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact differentialSpecialization_linearEquation ℚ
    · rw [Finset.mem_singleton.mp hP]
      exact hsol
  · intro P _
    rw [jetEvaluation_separant_linearEquation]
    norm_num

/-- `X (X - 1)`, as a differential polynomial of order `0` in the independent variable only. -/
private abbrev vanishingEverywhere : DifferentialPolynomial (ZMod 2) 0 :=
  X none * (X none - 1)

/-- The hypothesis `Infinite R` of `exists_forall_jetEvaluation_ne_zero` is needed: over
`ZMod 2`, the specialization of `X (X - 1)` along `0` is nonzero, but it vanishes at every
center. -/
example : differentialSpecialization vanishingEverywhere 0 ≠ 0 ∧
    ¬ ∃ center : ZMod 2, ∀ P ∈ ({0} : Finset (Polynomial (ZMod 2))),
      jetEvaluation vanishingEverywhere center (polynomialJet center P) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simp only [vanishingEverywhere, differentialSpecialization, differentialSpecializationHom,
      map_mul, map_sub, aeval_X, map_one]
    exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)
  · rintro ⟨center, h⟩
    apply h 0 (Finset.mem_singleton_self 0)
    simp only [vanishingEverywhere, jetEvaluation, map_mul, map_sub, eval_X, map_one]
    fin_cases center <;> decide

section DefaultExponent

variable {F : Type*} [Field F] {r : ℕ}

/-- With the default exponent `τ = 2K` and `r < K`, if `I` contains the high cuts for `k`, then
`k` agreement points given by an embedding `Fin k ↪ F`, chosen among the coordinates in `T`,
leave at most one regular zero of `I`. -/
example (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K) {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 1)) F))
    (hhigh : highTaylorCutsIdeal center Q K k (2 * K) ≤ I)
    (domain : Fin n ↪ F) (received : Fin n → F) (T : Finset (Fin n)) (hT : T.card = k)
    {jet jet' : Fin (r + 1) → F}
    (hjet : jet ∈ zeroLocus F I ∧ aeval jet (initialJetSeparant center Q) ≠ 0)
    (hjet' : jet' ∈ zeroLocus F I ∧ aeval jet' (initialJetSeparant center Q) ≠ 0)
    (hcuts : ∀ i ∈ T,
      aeval jet (taylorAgreementEquation center Q K (2 * K) (domain i) (received i)) = 0)
    (hcuts' : ∀ i ∈ T,
      aeval jet' (taylorAgreementEquation center Q K (2 * K) (domain i) (received i)) = 0) :
    jet = jet' :=
  eq_of_mem_zeroLocus_of_highTaylorCutsIdeal_le center Q (taylorExponentSufficient_two_mul r K)
    hK hhigh domain received T domain.injective.injOn hT.ge hjet.1 hjet'.1 hjet.2 hjet'.2 hcuts
    hcuts'

end DefaultExponent

end

end PolynomialDifferential
