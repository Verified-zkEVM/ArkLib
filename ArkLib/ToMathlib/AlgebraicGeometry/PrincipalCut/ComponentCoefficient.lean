/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.RadicalDegree
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PrimeFamilyCoefficient
public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Dimension

/-!
# Component coefficient bounds for a principal cut

The actual minimal primes of a principal cut contribute, at the top possible
cut degree, at most the coefficient supplied by the principal-cut Hilbert
polynomial estimate. Components of smaller dimension contribute zero.
-/

@[expose] public section

noncomputable section

open MvPolynomial Polynomial Filter
open scoped Topology

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- The finite set of actual minimal primes over an affine ideal. -/
def minimalPrimesFinset (I : Ideal (MvPolynomial σ F)) :
    Finset (Ideal (MvPolynomial σ F)) :=
  (I.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ F)).toFinset

@[simp]
theorem mem_minimalPrimesFinset {I Q : Ideal (MvPolynomial σ F)} :
    Q ∈ minimalPrimesFinset I ↔ Q ∈ I.minimalPrimes := by
  simp [minimalPrimesFinset]

omit [Finite σ] in
private theorem minimalPrime_pairwise_incomparable
    (I : Ideal (MvPolynomial σ F))
    {Q R : I.minimalPrimes} (hQR : Q ≠ R) : ¬(Q : Ideal (MvPolynomial σ F)) ≤ R := by
  intro hle
  apply hQR
  apply Subtype.ext
  exact le_antisymm hle (R.property.2 Q.property.1 hle)

omit [Finite σ] in
private theorem iInf_minimalPrimes_eq_radical (I : Ideal (MvPolynomial σ F)) :
    (⨅ Q : I.minimalPrimes, (Q : Ideal (MvPolynomial σ F))) = I.radical := by
  rw [← Ideal.sInf_minimalPrimes, sInf_eq_iInf']

private theorem hilbertPolynomial_leadingCoeff_nonneg
    (I : Ideal (MvPolynomial σ F)) : 0 ≤ (hilbertPolynomial I).leadingCoeff := by
  rw [← Polynomial.coeff_natDegree]
  apply coeff_nonneg_of_natDegree_le_of_eventually_eval_nat_nonneg le_rfl
  filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
  rw [hN]
  positivity

/-- The actual minimal components of a principal cut satisfy the top possible
coefficient bound. No purity assumption is made: lower-dimensional components
have zero coefficient at this degree. -/
theorem principalCut_sum_minimalPrime_coeff_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {f : MvPolynomial σ F} (hfP : f ∉ P) {b : ℕ}
    (hfdeg : f.totalDegree ≤ b) :
    let J := P ⊔ Ideal.span {f}
    let d := (hilbertPolynomial P).natDegree
    ∑ Q ∈ minimalPrimesFinset J, (hilbertPolynomial Q).coeff (d - 1) ≤
      (b : ℚ) * d * (hilbertPolynomial P).leadingCoeff := by
  dsimp only
  let J := P ⊔ Ideal.span {f}
  let ι := J.minimalPrimes
  let _ : Fintype ι :=
    (J.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ F)).fintype
  let Q : ι → Ideal (MvPolynomial σ F) := fun q ↦ q
  have hQprime : ∀ q, (Q q).IsPrime := fun q ↦ q.property.isPrime
  have hQinc : ∀ ⦃q r⦄, q ≠ r → ¬Q q ≤ Q r := by
    exact fun _ _ hqr ↦ minimalPrime_pairwise_incomparable J hqr
  have hInf : (⨅ q, Q q) = J.radical := iInf_minimalPrimes_eq_radical J
  have hlcP : 0 ≤ (hilbertPolynomial P).leadingCoeff :=
    hilbertPolynomial_leadingCoeff_nonneg P
  obtain hJzero | ⟨hJdeg, hJcoeff⟩ :=
    principalCut_hilbertPolynomial_zero_or_degree_and_coeff hP hfP hfdeg
  · have hJtop : J = ⊤ := by
      by_contra hJne
      exact hilbertPolynomial_ne_zero hJne hJzero
    subst J
    have hrhs : 0 ≤ (b : ℚ) * (hilbertPolynomial P).natDegree *
        (hilbertPolynomial P).leadingCoeff :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hlcP
    have hsumzero : ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
        (hilbertPolynomial Q).coeff ((hilbertPolynomial P).natDegree - 1) = 0 := by
      rw [hJtop]
      have hempty : minimalPrimesFinset (⊤ : Ideal (MvPolynomial σ F)) = ∅ := by
        ext R
        simp only [mem_minimalPrimesFinset, Finset.notMem_empty, iff_false]
        intro hR
        have hRtop : R = ⊤ := top_unique hR.le
        exact hR.isPrime.ne_top hRtop
      rw [hempty]
      simp
    rw [hsumzero]
    exact hrhs
  · have hQdeg : ∀ q, (hilbertPolynomial (Q q)).natDegree ≤
        (hilbertPolynomial P).natDegree - 1 := by
      intro q
      exact (hilbertPolynomial_degree_and_leadingCoeff_antitone q.property.le
        q.property.isPrime.ne_top).1.trans hJdeg
    have hRadDeg : (hilbertPolynomial J.radical).natDegree ≤
        (hilbertPolynomial P).natDegree - 1 := by
      rw [hilbertPolynomial_radical_natDegree]
      exact hJdeg
    have hcomponents := sum_hilbertPolynomial_coeff_le_iInf Q hQprime hQinc
      ((hilbertPolynomial P).natDegree - 1) hQdeg (hInf ▸ hRadDeg)
    rw [hInf] at hcomponents
    have hradcut : (hilbertPolynomial J.radical).coeff
          ((hilbertPolynomial P).natDegree - 1) ≤
        (hilbertPolynomial J).coeff ((hilbertPolynomial P).natDegree - 1) := by
      apply coeff_le_of_natDegree_le_of_eventually_eval_nat_le hRadDeg hJdeg
      filter_upwards [hilbertPolynomial_eventually_eval J.radical,
        hilbertPolynomial_eventually_eval J] with N hradN hJN
      rw [hradN, hJN]
      exact_mod_cast hilbertFunction_antitone Ideal.le_radical N
    calc
      ∑ R ∈ minimalPrimesFinset J,
          (hilbertPolynomial R).coeff ((hilbertPolynomial P).natDegree - 1) =
          ∑ q : ι, (hilbertPolynomial (Q q)).coeff
            ((hilbertPolynomial P).natDegree - 1) := by
        exact Finset.sum_subtype (minimalPrimesFinset J)
          (fun _ ↦ mem_minimalPrimesFinset) _
      _ ≤ (hilbertPolynomial J.radical).coeff
          ((hilbertPolynomial P).natDegree - 1) := hcomponents
      _ ≤ (hilbertPolynomial J).coeff
          ((hilbertPolynomial P).natDegree - 1) := hradcut
      _ ≤ (b : ℚ) * (hilbertPolynomial P).natDegree *
          (hilbertPolynomial P).leadingCoeff := hJcoeff

/-- If every actual minimal component has the top possible cut degree, the
coefficient bound becomes the corresponding factorial-scaled leading
coefficient bound. This explicit purity hypothesis is not automatic here. -/
theorem principalCut_sum_minimalPrime_factorial_le
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {f : MvPolynomial σ F} (hfP : f ∉ P) {b : ℕ}
    (hfdeg : f.totalDegree ≤ b)
    (hchildren : ∀ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
      (hilbertPolynomial Q).natDegree = (hilbertPolynomial P).natDegree - 1) :
    ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
        (((hilbertPolynomial P).natDegree - 1).factorial : ℚ) *
          (hilbertPolynomial Q).leadingCoeff ≤
      (b : ℚ) * ((hilbertPolynomial P).natDegree.factorial : ℚ) *
        (hilbertPolynomial P).leadingCoeff := by
  have hlcP : 0 ≤ (hilbertPolynomial P).leadingCoeff :=
    hilbertPolynomial_leadingCoeff_nonneg P
  have hcoeff := principalCut_sum_minimalPrime_coeff_le hP hfP hfdeg
  have hleading : ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
      (hilbertPolynomial Q).leadingCoeff ≤
      (b : ℚ) * (hilbertPolynomial P).natDegree *
        (hilbertPolynomial P).leadingCoeff := by
    calc
      ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
          (hilbertPolynomial Q).leadingCoeff =
          ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
            (hilbertPolynomial Q).coeff ((hilbertPolynomial P).natDegree - 1) := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [← hchildren Q hQ, Polynomial.coeff_natDegree]
      _ ≤ (b : ℚ) * (hilbertPolynomial P).natDegree *
          (hilbertPolynomial P).leadingCoeff := hcoeff
  cases hd : (hilbertPolynomial P).natDegree with
  | zero =>
      have hleading0 : ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
          (hilbertPolynomial Q).leadingCoeff ≤ 0 := by
        simpa only [hd, Nat.cast_zero, mul_zero, zero_mul] using hleading
      simp only [Nat.zero_sub, Nat.factorial_zero, Nat.cast_one, one_mul]
      exact hleading0.trans
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) zero_le_one) hlcP)
  | succ e =>
      simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      calc
        ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
            (e.factorial : ℚ) * (hilbertPolynomial Q).leadingCoeff =
            (e.factorial : ℚ) *
              ∑ Q ∈ minimalPrimesFinset (P ⊔ Ideal.span {f}),
                (hilbertPolynomial Q).leadingCoeff := by
          simp only [Finset.mul_sum]
        _ ≤ (e.factorial : ℚ) *
            ((b : ℚ) * (e + 1) * (hilbertPolynomial P).leadingCoeff) :=
          mul_le_mul_of_nonneg_left (by simpa only [hd, Nat.cast_succ] using hleading)
            (by positivity)
        _ = (b : ℚ) * (((e : ℚ) + 1) * (e.factorial : ℚ)) *
            (hilbertPolynomial P).leadingCoeff := by ring

end AffineHilbert
