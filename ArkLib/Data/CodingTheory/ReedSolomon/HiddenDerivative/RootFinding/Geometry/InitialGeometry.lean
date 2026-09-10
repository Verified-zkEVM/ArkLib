/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.Agreement


/-!
# Initial hypersurface geometry of the rational Taylor chart

The regular part of the initial differential equation is covered by finitely many retained prime
components.  Every component has the expected Hilbert-polynomial dimension, and their total
Bezout potential is bounded by the total jet degree of the differential equation.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open MvPolynomial AffineHilbert
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {r : ℕ}

/-- Prime components of the initial differential hypersurface that meet the regular Taylor chart. -/
def initialJetPrimeFamily (center : F) (Q : DifferentialPolynomial F r) :
    Finset (Ideal (MvPolynomial (Fin (r + 1)) F)) :=
  (Ideal.span {initialJetEquation center Q}).retainedMinimalPrimes
    (initialJetSeparant center Q)

/-- A nonzero initial separant forces the initial hypersurface equation to be nonzero. -/
theorem initialJetEquation_ne_zero_of_separant_ne_zero
    (center : F) (Q : DifferentialPolynomial F r)
    (hsep : initialJetSeparant center Q ≠ 0) :
    initialJetEquation center Q ≠ 0 := by
  intro hzero
  have hderiv := congrArg (pderiv (Fin.last r)) hzero
  rw [pderiv_initialJetEquation, map_zero] at hderiv
  apply hsep
  change initialJetEquation center (separant Q (Fin.last r)) = 0
  exact hderiv

/-- Every retained initial component is prime and remains on the separant open. -/
theorem initialJetPrimeFamily_prime_open
    (center : F) (Q : DifferentialPolynomial F r) :
    ∀ P ∈ initialJetPrimeFamily center Q,
      P.IsPrime ∧ initialJetSeparant center Q ∉ P := by
  intro P hP
  have h := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hP
  exact ⟨h.1.isPrime, h.2⟩

/-- Every regular point of the initial hypersurface lies on a retained initial prime component. -/
theorem exists_mem_initialJetPrimeFamily_of_regular
    {E : Type*} [Field E] [Algebra F E]
    (center : F) (Q : DifferentialPolynomial F r) (jet : Fin (r + 1) → E)
    (hinit : aeval jet (initialJetEquation center Q) = 0)
    (hsep : aeval jet (initialJetSeparant center Q) ≠ 0) :
    ∃ P ∈ initialJetPrimeFamily center Q, jet ∈ zeroLocus E P := by
  have hzero : jet ∈ zeroLocus E (Ideal.span {initialJetEquation center Q}) := by
    rw [show jet ∈ zeroLocus E (Ideal.span {initialJetEquation center Q}) ↔
      aeval jet (initialJetEquation center Q) = 0 by
        change Ideal.span {initialJetEquation center Q} ≤ RingHom.ker (aeval jet).toRingHom ↔ _
        rw [Ideal.span_singleton_le_iff_mem]
        rfl]
    exact hinit
  exact exists_retainedMinimalPrime_of_mem_zeroLocus
    (Ideal.span {initialJetEquation center Q}) (initialJetSeparant center Q) jet hzero hsep

/-- Every retained initial component has Hilbert-polynomial degree `r`. -/
theorem initialJetPrimeFamily_hilbertPolynomial_natDegree
    (center : F) (Q : DifferentialPolynomial F r)
    (hinit : initialJetEquation center Q ≠ 0)
    {P : Ideal (MvPolynomial (Fin (r + 1)) F)}
    (hP : P ∈ initialJetPrimeFamily center Q) :
    (hilbertPolynomial P).natDegree = r := by
  have hminimal := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hP |>.1
  have hpure : (hilbertPolynomial P).natDegree + 1 =
      (hilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin (r + 1)) F))).natDegree :=
    principalCut_component_hilbertPolynomial_natDegree_add_one
      (F := F) (σ := Fin (r + 1)) (J := P)
      (P := (⊥ : Ideal (MvPolynomial (Fin (r + 1)) F))) Ideal.isPrime_bot
      (f := initialJetEquation center Q) (by simpa using hinit)
      (by simpa only [bot_sup_eq] using hminimal)
  rw [hilbertPolynomial_bot_natDegree, Nat.card_fin] at hpure
  omega

/-- If the initial equation has total degree at most `ν`, the retained initial components have
potential at most `ν B^r` for every nonnegative weight base `B`. -/
theorem sum_initialJetPrimeFamily_affineDegree_mul_pow_le
    (center : F) (Q : DifferentialPolynomial F r)
    (hinit : initialJetEquation center Q ≠ 0)
    {ν B : ℕ} (hν : (initialJetEquation center Q).totalDegree ≤ ν) :
    ∑ P ∈ initialJetPrimeFamily center Q,
        affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree ≤
      (ν : ℚ) * (B : ℚ) ^ r := by
  have hsum : ∑ P ∈ initialJetPrimeFamily center Q, affineDegree P ≤ (ν : ℚ) := by
    simpa only [initialJetPrimeFamily, bot_sup_eq, affineDegree_bot, mul_one] using
      sum_retained_affineDegree_le
        (P := (⊥ : Ideal (MvPolynomial (Fin (r + 1)) F))) Ideal.isPrime_bot
        (s := initialJetSeparant center Q) (f := initialJetEquation center Q)
        (by simpa using hinit) hν
  calc
    ∑ P ∈ initialJetPrimeFamily center Q,
        affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree =
        ∑ P ∈ initialJetPrimeFamily center Q, affineDegree P * (B : ℚ) ^ r := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [initialJetPrimeFamily_hilbertPolynomial_natDegree center Q hinit hP]
    _ = (∑ P ∈ initialJetPrimeFamily center Q, affineDegree P) * (B : ℚ) ^ r := by
      rw [Finset.sum_mul]
    _ ≤ (ν : ℚ) * (B : ℚ) ^ r :=
      mul_le_mul_of_nonneg_right hsum (by positivity)

/-- Total jet degree directly supplies the initial hypersurface potential bound. -/
theorem sum_initialJetPrimeFamily_affineDegree_mul_pow_le_totalJetDegree
    (center : F) (Q : DifferentialPolynomial F r)
    (hsep : initialJetSeparant center Q ≠ 0) (B : ℕ) :
    ∑ P ∈ initialJetPrimeFamily center Q,
        affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree ≤
      ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) : ℚ) *
        (B : ℚ) ^ r := by
  exact sum_initialJetPrimeFamily_affineDegree_mul_pow_le center Q
    (initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep)
    (totalDegree_initialJetEquation_le center Q)

end ReedSolomon.HiddenDerivative
