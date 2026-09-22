/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.TaylorChart
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Acceptance tests for the rational Taylor chart

The main example is `y' = 2x`, written as `Q = Y₁ - 2X`, at center `0`, with the polynomial
solution `X ^ 2`. Its initial equation is `Y₁` and its separant is `1`. Over `ℚ` the
reconstruction of length `3` at the jet of `X ^ 2` is `X ^ 2`, the common numerator of `c₂`
evaluates to the Taylor coefficient `1`, and the agreement equations at the jet of `X ^ 2` hold
exactly at the points of its graph. Over `ZMod 2` the binomial pivot `(2 choose 1)` vanishes and
the reconstruction is not `X ^ 2`, so the pivot hypothesis is needed.

Boundary cases: the length `K = r` does not determine the initial jet, and for `(y')² = 0`, whose
separant `2 Y₁` vanishes at `Y₁ = 0`, the agreement equation vanishes at the zero jet although the
reconstruction does not take the prescribed value, so the separant hypothesis is needed.

The file also derives the statements for the default exponent `τ = 2K` from the general ones, and
checks that the chart equations of an equation of jet degree at most `1` are affine.
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

/-- The binomial pivots `(i choose 1)` for `1 < i` are nonzero in `ℚ`. -/
private theorem choose_one_ne_zero (i : ℕ) (hi : 1 < i) : (i.choose 1 : ℚ) ≠ 0 := by
  rw [Nat.choose_one_right]
  exact_mod_cast (by omega : i ≠ 0)

/-- `X ^ 2` has degree below `3`. -/
private theorem degree_X_sq_lt_three (F : Type*) [Field F] :
    (Polynomial.X ^ 2 : Polynomial F).degree < (3 : ℕ) := by
  rw [Polynomial.degree_X_pow]
  exact_mod_cast (by norm_num : 2 < 3)

/-- The initial equation of `y' = 2x` at center `0` is the coordinate `Y₁`. -/
example : initialJetEquation (0 : ℚ) (linearEquation ℚ) = X 1 := by
  simp [initialJetEquation, linearEquation]

/-- The initial separant of `y' = 2x` at center `0` is `1`, the derivative of `Y₁` in `Y₁`. -/
example : initialJetSeparant (0 : ℚ) (linearEquation ℚ) = 1 := by
  rw [← pderiv_last_initialJetEquation]
  simp [initialJetEquation, linearEquation, pderiv_X, Fin.last]

/-- Over `ℚ`, the common numerator of `c₂` for `y' = 2x` with any exponent `τ ≥ 1` evaluates to
the Taylor coefficient `1` of `X ^ 2` at the jet of `X ^ 2`. -/
example (τ : ℕ) (hτ : 1 ≤ τ) :
    aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
      (commonTaylorNumerator 0 (linearEquation ℚ) τ 2) = 1 := by
  rw [aeval_commonTaylorNumerator_polynomialJet 0 _ _
    (differentialSpecialization_linearEquation ℚ)
    (by rw [jetEvaluation_separant_linearEquation]; norm_num) (by omega)
    (fun i hi _ ↦ choose_one_ne_zero i hi), aeval_initialJetSeparant,
    jetEvaluation_separant_linearEquation]
  simp [Polynomial.coeff_X_pow]

/-- Over `ℚ`, the reconstruction of length `3` at the jet of the solution `X ^ 2` of `y' = 2x`
is `X ^ 2`. -/
example : rationalTaylorPolynomial 0 (linearEquation ℚ) 3
    (polynomialJet 0 (Polynomial.X ^ 2)) = Polynomial.X ^ 2 :=
  rationalTaylorPolynomial_polynomialJet 0 _ _ (differentialSpecialization_linearEquation ℚ)
    (by rw [jetEvaluation_separant_linearEquation]; norm_num) (degree_X_sq_lt_three ℚ)
    (fun i hi _ ↦ choose_one_ne_zero i hi)

/-- The pivot hypothesis of `rationalTaylorPolynomial_polynomialJet` is needed: over `ZMod 2`,
`X ^ 2` still solves `y' = 2x` with separant `1`, but `(2 choose 1) = 0` and the reconstruction
of length `3` has Taylor coefficient `0` at order `2`, so it is not `X ^ 2`. -/
example : rationalTaylorPolynomial 0 (linearEquation (ZMod 2)) 3
    (polynomialJet 0 (Polynomial.X ^ 2)) ≠ Polynomial.X ^ 2 := by
  intro h
  have h2 := congrArg (fun p ↦ (Polynomial.taylor 0 p).coeff 2) h
  simp only [coeff_taylor_rationalTaylorPolynomial, show (2 : ℕ) < 3 from by norm_num,
    ↓reduceIte] at h2
  have hchoose : ((Nat.choose 2 1 : ℕ) : ZMod 2) = 0 := by decide
  rw [rationalTaylorCoefficient, rationalTaylorNumerator,
    dite_eq_right_of_eq_false (eq_false (by norm_num)), hchoose] at h2
  simp [Polynomial.coeff_X_pow] at h2

/-- Over `ℚ`, the agreement equations of length `3` and exponent `6` hold at the jet of `X ^ 2`
exactly at points of its graph: the equation at `(3, 9)` vanishes and the one at `(3, 8)` does
not. -/
example :
    aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
        (taylorAgreementEquation 0 (linearEquation ℚ) 3 (2 * 3) 3 9) = 0 ∧
      aeval (polynomialJet 0 (Polynomial.X ^ 2 : Polynomial ℚ))
        (taylorAgreementEquation 0 (linearEquation ℚ) 3 (2 * 3) 3 8) ≠ 0 := by
  have h := aeval_taylorAgreementEquation_polynomialJet_eq_zero_iff 0 (linearEquation ℚ)
    (Polynomial.X ^ 2) (differentialSpecialization_linearEquation ℚ)
    (by rw [jetEvaluation_separant_linearEquation]; norm_num)
    (taylorExponentSufficient_two_mul 1 3) (degree_X_sq_lt_three ℚ)
    (fun i hi _ ↦ choose_one_ne_zero i hi)
  rw [h, Ne, h]
  norm_num

/-- The hypothesis `r < K` of `rationalTaylorMap_injective` is needed: for `r = 1` and `K = 1`
the map keeps only `c₀`, so the jets `(0, 0)` and `(0, 1)` have the same image. -/
example (Q : DifferentialPolynomial ℚ 1) : ¬ Function.Injective (rationalTaylorMap 0 Q 1) := by
  intro h
  have h01 : rationalTaylorMap 0 Q 1 ![0, 0] = rationalTaylorMap 0 Q 1 ![0, 1] := by
    funext l
    obtain rfl : l = 0 := Subsingleton.elim _ _
    simpa using (rationalTaylorCoefficient_initial 0 Q ![0, 0] 0).trans
      (rationalTaylorCoefficient_initial 0 Q ![0, 1] 0).symm
  have h1 := congrFun (h h01) 1
  simp at h1

/-- The equation `(y')² = 0`, whose separant `2 Y₁` vanishes where `Y₁ = 0`. -/
private abbrev squareEquation : DifferentialPolynomial ℚ 1 := X (some 1) ^ 2

/-- The separant of `(y')² = 0` vanishes at the zero jet. -/
private theorem jetEvaluation_separant_squareEquation :
    jetEvaluation (separant squareEquation (Fin.last 1)) 0 (![0, 0] : Fin 2 → ℚ) = 0 := by
  simp [separant, jetEvaluation, squareEquation, pderiv_X, Fin.last]

/-- The separant hypothesis of `taylorAgreementEquation_eq_zero_iff` is needed: for `(y')² = 0`
with `K = 2` and `τ = 1`, the agreement equation at `(0, 1)` vanishes at the zero jet, where the
separant is zero, although the reconstruction takes the value `0` at `0`. -/
example : TaylorExponentSufficient 1 2 1 ∧
    aeval (![0, 0] : Fin 2 → ℚ) (taylorAgreementEquation (0 : ℚ) squareEquation 2 1 0 1) = 0 ∧
    (rationalTaylorPolynomial (0 : ℚ) squareEquation 2 ![0, 0]).eval 0 ≠ 1 := by
  refine ⟨fun l ↦ by have := l.isLt; omega, ?_, ?_⟩
  · have hS : aeval (![0, 0] : Fin 2 → ℚ) (initialJetSeparant 0 squareEquation) = 0 := by
      rw [aeval_initialJetSeparant, jetEvaluation_separant_squareEquation]
    simp only [taylorAgreementEquation, commonTaylorNumerator, Fin.sum_univ_two, map_sub,
      map_add, map_mul, map_pow, hS]
    simp
  · have h0 : rationalTaylorCoefficient (0 : ℚ) squareEquation ![0, 0] 0 = 0 := by
      simpa using rationalTaylorCoefficient_initial 0 squareEquation ![0, 0] 0
    have h1 : rationalTaylorCoefficient (0 : ℚ) squareEquation ![0, 0] 1 = 0 := by
      simpa using rationalTaylorCoefficient_initial 0 squareEquation ![0, 0] 1
    simp [eval_rationalTaylorPolynomial, Fin.sum_univ_two, h0, h1]

section DefaultExponent

variable {F : Type*} [Field F] {r : ℕ}

/-- With the default exponent `τ = 2K`, every agreement equation has total degree at most
`1 + 2K (jetTotalDegree Q - 1)`. -/
example (center : F) (Q : DifferentialPolynomial F r) (K : ℕ) (x y : F) :
    (taylorAgreementEquation center Q K (2 * K) x y).totalDegree ≤
      1 + 2 * K * (jetTotalDegree Q - 1) :=
  totalDegree_taylorAgreementEquation_le center Q (taylorExponentSufficient_two_mul r K) x y

/-- With the default exponent `τ = 2K`, the common numerator of `c_l` for `l < K` evaluates to
`S ^ (2K) * c_l` on `S ≠ 0`. -/
example (center : F) (Q : DifferentialPolynomial F r) (K : ℕ) (jet : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (l : Fin K) :
    aeval jet (commonTaylorNumerator center Q (2 * K) l) =
      aeval jet (initialJetSeparant center Q) ^ (2 * K) *
        rationalTaylorCoefficient center Q jet l :=
  aeval_commonTaylorNumerator center Q jet (taylorExponentSufficient_two_mul r K l) hS

/-- With the default exponent `τ = 2K` and `r < K`, the high cuts for `k ≤ l < K` and agreement
at `k` distinct points given by an embedding `Fin k ↪ F` determine a jet with `S ≠ 0`. -/
example (center : F) (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K)
    (domain : Fin k ↪ F) (received : Fin k → F) (jet jet' : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hS' : aeval jet' (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val → aeval jet (commonTaylorNumerator center Q (2 * K) l) = 0)
    (hhigh' : ∀ l : Fin K, k ≤ l.val →
      aeval jet' (commonTaylorNumerator center Q (2 * K) l) = 0)
    (hcut : ∀ i,
      aeval jet (taylorAgreementEquation center Q K (2 * K) (domain i) (received i)) = 0)
    (hcut' : ∀ i,
      aeval jet' (taylorAgreementEquation center Q K (2 * K) (domain i) (received i)) = 0) :
    jet = jet' :=
  eq_of_highTaylorCuts_of_agreement center Q (taylorExponentSufficient_two_mul r K) hK domain
    received Finset.univ domain.injective.injOn (by simp) hS hS'
    (fun l hkl hlK ↦ hhigh ⟨l, hlK⟩ hkl) (fun l hkl hlK ↦ hhigh' ⟨l, hlK⟩ hkl)
    (fun i _ ↦ hcut i) (fun i _ ↦ hcut' i)

/-- If `jetTotalDegree Q ≤ 1`, every agreement equation is affine, for every exponent. -/
example (center : F) (Q : DifferentialPolynomial F r) (hQ : jetTotalDegree Q ≤ 1) {K τ : ℕ}
    (hτ : TaylorExponentSufficient r K τ) (x y : F) :
    (taylorAgreementEquation center Q K τ x y).totalDegree ≤ 1 := by
  have h := totalDegree_taylorAgreementEquation_le center Q hτ x y
  rwa [rationalTaylorCutDegreeBound, Nat.sub_eq_zero_of_le hQ, mul_zero, add_zero] at h

end DefaultExponent

end

end PolynomialDifferential
