/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Numerator


/-!
# A common-denominator rational Taylor chart

The first `K` Taylor coefficients admit any common denominator `S^τ` whose exponent
dominates their exact recurrence exponents. Literal numerators then have total degree at
most `1 + τ(v-1)`, where `S` is the initial separant and `v` is the total jet degree.
The default `τ = 2K` keeps the arbitrary-order and `K < 2` interface. For `K ≥ 2`, the
sharper `τ = 2K - 3` is sufficient at every order; finite first-order clients use it
uniformly for their order-zero and order-one stages. The chart retains the initial coordinates
and contains all regular solutions with invertible binomial pivots.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- A single common-denominator numerator for the `l`-th Taylor coefficient. -/
def commonTaylorNumerator (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (l : Fin K) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) F :=
  rationalTaylorNumerator center Q l.val *
    initialJetSeparant center Q ^ (τ - (2 * (l.val - r) - 1))

/-- Every numerator padded to a sufficient exponent has the corresponding exact chart
degree bound. -/
theorem totalDegree_commonTaylorNumerator_le_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)))
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (l : Fin K) :
    (commonTaylorNumerator center Q K l (τ := τ)).totalDegree ≤
      1 + τ * (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) := by
  have hd := totalDegree_rationalTaylorNumerator_le center Q hv l.val
  have hs := totalDegree_initialJetSeparant_le center Q
  have hp := (totalDegree_pow (initialJetSeparant center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := totalDegree_mul (rationalTaylorNumerator center Q l.val)
    (initialJetSeparant center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  change _ ≤ _ at hm
  unfold commonTaylorNumerator
  nlinarith

/-- Every common numerator has the uniform chart degree bound. -/
theorem totalDegree_commonTaylorNumerator_le (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)))
    (K : ℕ) (l : Fin K) :
    (commonTaylorNumerator center Q K l).totalDegree ≤
      1 + 2 * K * (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) := by
  exact totalDegree_commonTaylorNumerator_le_of_exponent center Q hv K (2 * K)
    (taylorExponentSufficient_two_mul r K) l

/-- Evaluating a numerator padded to a sufficient exponent recovers the rational
coefficient after clearing exactly that exponent of the separant. -/
theorem aeval_commonTaylorNumerator_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (l : Fin K) (hS : aeval jet (initialJetSeparant center Q) ≠ 0) :
    aeval jet (commonTaylorNumerator center Q K l (τ := τ)) =
      aeval jet (initialJetSeparant center Q) ^ τ *
        rationalTaylorCoefficient center Q jet l.val := by
  rw [commonTaylorNumerator, map_mul, map_pow, rationalTaylorCoefficient]
  have he : aeval jet (initialJetSeparant center Q) ^ τ =
      aeval jet (initialJetSeparant center Q) ^ (τ - (2 * (l.val - r) - 1)) *
        aeval jet (initialJetSeparant center Q) ^ (2 * (l.val - r) - 1) := by
    rw [← pow_add, Nat.sub_add_cancel (hτ l)]
  rw [he]
  field_simp

/-- Evaluating the common numerator recovers the rational coefficient after clearing
exactly the power `2K` of the separant. -/
theorem aeval_commonTaylorNumerator (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (K : ℕ) (l : Fin K)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) :
    aeval jet (commonTaylorNumerator center Q K l) =
      aeval jet (initialJetSeparant center Q) ^ (2 * K) *
        rationalTaylorCoefficient center Q jet l.val := by
  exact aeval_commonTaylorNumerator_of_exponent center Q jet K (2 * K)
    (taylorExponentSufficient_two_mul r K) l hS

/-- The actual rational map to the first `K` coefficient coordinates. -/
def rationalTaylorMap (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) : Fin K → F :=
  fun l ↦ rationalTaylorCoefficient center Q jet l.val

/-- Keeping the initial jet coordinates makes the Taylor chart injective. -/
theorem rationalTaylorMap_injective (center : F) (Q : DifferentialPolynomial F r)
    (K : ℕ) (hK : r < K) : Function.Injective (rationalTaylorMap center Q K) := by
  intro jet jet' heq
  funext j
  have hj : j.val < K := by omega
  have h := congrFun heq ⟨j.val, hj⟩
  change rationalTaylorCoefficient center Q jet j.val =
    rationalTaylorCoefficient center Q jet' j.val at h
  simpa only [rationalTaylorCoefficient_initial] using h

/-- Every regular solution lies in the concrete Taylor chart through all invertible pivots. -/
theorem rationalTaylorMap_eq_solution (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (K : ℕ) (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    rationalTaylorMap center Q K (polynomialJet center P) =
      fun l ↦ (Polynomial.taylor center P).coeff l.val := by
  funext l
  exact rationalTaylorCoefficient_eq_solution center Q P hsolution hseparant l.val
    (fun i hi hil ↦ hbin i hi (hil.trans_lt l.isLt))

/-- Common numerator equations hold for every actual regular solution. -/
theorem commonTaylorNumerator_solution_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) (l : Fin K) :
    aeval (polynomialJet center P) (commonTaylorNumerator center Q K l (τ := τ)) =
      aeval (polynomialJet center P) (initialJetSeparant center Q) ^ τ *
        (Polynomial.taylor center P).coeff l.val := by
  have hs : aeval (polynomialJet center P) (initialJetSeparant center Q) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  rw [aeval_commonTaylorNumerator_of_exponent center Q _ K τ hτ l hs]
  rw [rationalTaylorCoefficient_eq_solution center Q P hsolution hseparant l.val
    (fun i hi hil ↦ hbin i hi (hil.trans_lt l.isLt))]

/-- Common numerator equations hold for every actual regular solution. -/
theorem commonTaylorNumerator_solution (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (K : ℕ) (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) (l : Fin K) :
    aeval (polynomialJet center P) (commonTaylorNumerator center Q K l) =
      aeval (polynomialJet center P) (initialJetSeparant center Q) ^ (2 * K) *
        (Polynomial.taylor center P).coeff l.val := by
  exact commonTaylorNumerator_solution_of_exponent center Q P hsolution hseparant
    K (2 * K) (taylorExponentSufficient_two_mul r K) hbin l

/-- The initial differential equation specialized at the chosen center. -/
def initialJetEquation (center : F) (Q : DifferentialPolynomial F r) :
    MvPolynomial (Fin (r + 1)) F :=
  aeval (fun i ↦ i.elim (C center) X) Q

/-- Specializing the independent variable preserves the total jet degree bound. -/
theorem totalDegree_initialJetEquation_le (center : F) (Q : DifferentialPolynomial F r) :
    (initialJetEquation center Q).totalDegree ≤
      Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  cases i with
  | none => simp
  | some j => simp only [Option.elim_some, weightedTotalDegree_one, totalDegree_X, le_refl]

/-- The initial hypersurface equation evaluates to the actual differential equation on a jet. -/
theorem aeval_initialJetEquation (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) :
    aeval jet (initialJetEquation center Q) = jetEvaluation Q center jet := by
  have he : (aeval jet).comp (aeval (fun i : Option (Fin (r + 1)) ↦
      i.elim (C center) X)) = aeval (fun i ↦ match i with
        | none => center | some j => jet j) := by
    apply algHom_ext
    intro i
    cases i <;> simp
  exact DFunLike.congr_fun he Q

/-- The chart's denominator base is the derivative of its initial hypersurface equation. -/
theorem pderiv_initialJetEquation (center : F) (Q : DifferentialPolynomial F r)
    (j : Fin (r + 1)) :
    pderiv j (initialJetEquation center Q) = initialJetEquation center (separant Q j) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [initialJetEquation, separant]
  | add P Q hP hQ => simpa [initialJetEquation, separant] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [initialJetEquation, separant] at hP
    cases i with
    | none =>
      simp only [aeval_eq_bind₁] at hP
      simp [initialJetEquation, separant, hP]
    | some i =>
      simp only [initialJetEquation, separant, map_mul, aeval_X, Option.elim_some,
        pderiv_mul, pderiv_X, map_add]
      rw [hP]
      by_cases hi : i = j
      · subst i
        simp
      · simp [hi]

/-- Every actual solution starts on the explicit initial hypersurface. -/
theorem initialJetEquation_solution (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0) :
    aeval (polynomialJet center P) (initialJetEquation center Q) = 0 := by
  rw [aeval_initialJetEquation, ← eval_differentialSpecialization, hsolution]
  simp

open scoped BigOperators

/-- The literal polynomial equation for agreement at `x` with received symbol `y`,
after clearing the chart's common denominator. -/
def taylorAgreementEquation (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (x y : F) (τ : ℕ := 2 * K) : MvPolynomial (Fin (r + 1)) F :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumerator center Q K l (τ := τ)) -
      C y * initialJetSeparant center Q ^ τ

/-- Agreement equations padded to a sufficient exponent obey the corresponding chart bound. -/
theorem totalDegree_taylorAgreementEquation_le_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)))
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (x y : F) :
    (taylorAgreementEquation center Q K x y (τ := τ)).totalDegree ≤
      1 + τ * (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro l _
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using
        totalDegree_commonTaylorNumerator_le_of_exponent center Q hv K τ hτ l)
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _
      (totalDegree_initialJetSeparant_le center Q))).trans (Nat.le_add_left _ _)

/-- Every agreement equation has degree bounded by the same chart bound. -/
theorem totalDegree_taylorAgreementEquation_le (center : F) (Q : DifferentialPolynomial F r)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)))
    (K : ℕ) (x y : F) :
    (taylorAgreementEquation center Q K x y).totalDegree ≤
      1 + 2 * K * (Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) - 1) := by
  exact totalDegree_taylorAgreementEquation_le_of_exponent center Q hv K (2 * K)
    (taylorExponentSufficient_two_mul r K) x y

/-- A sufficiently padded agreement equation evaluates to the actual discrepancy times
the selected common denominator. -/
theorem taylorAgreementEquation_solution_of_exponent
    (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (hP : P.degree < K)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) (x y : F) :
    aeval (polynomialJet center P) (taylorAgreementEquation center Q K x y (τ := τ)) =
      aeval (polynomialJet center P) (initialJetSeparant center Q) ^ τ *
        (P.eval x - y) := by
  rw [taylorAgreementEquation, map_sub, map_sum]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, map_pow]
  simp_rw [commonTaylorNumerator_solution_of_exponent center Q P hsolution hseparant
    K τ hτ hbin]
  have hsum : (∑ l : Fin K, (Polynomial.taylor center P).coeff l.val *
      (x - center) ^ l.val) = P.eval x := by
    have hp : (∑ l : Fin K, Polynomial.monomial l.val
        ((Polynomial.taylor center P).coeff l.val)) = Polynomial.taylor center P := by
      rw [Polynomial.sum_fin (fun i c ↦ Polynomial.monomial i c) (by simp)
        (by simpa [Polynomial.degree_taylor] using hP), Polynomial.sum_monomial_eq]
    have he := congrArg (fun p : Polynomial F ↦ p.eval (x - center)) hp
    simpa [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.taylor_eval] using he
  have hreorder : (∑ l : Fin K, (x - center) ^ l.val *
      (aeval (polynomialJet center P) (initialJetSeparant center Q) ^ τ *
        (Polynomial.taylor center P).coeff l.val)) =
      aeval (polynomialJet center P) (initialJetSeparant center Q) ^ τ *
        (∑ l : Fin K, (Polynomial.taylor center P).coeff l.val * (x - center) ^ l.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hreorder, hsum]
  ring

/-- Agreement equations evaluate to the actual discrepancy, times the common denominator. -/
theorem taylorAgreementEquation_solution (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    (K : ℕ) (hP : P.degree < K)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) (x y : F) :
    aeval (polynomialJet center P) (taylorAgreementEquation center Q K x y) =
      aeval (polynomialJet center P) (initialJetSeparant center Q) ^ (2 * K) *
        (P.eval x - y) := by
  exact taylorAgreementEquation_solution_of_exponent center Q P hsolution hseparant
    K (2 * K) (taylorExponentSufficient_two_mul r K) hP hbin x y

end

end ReedSolomon.HiddenDerivative
