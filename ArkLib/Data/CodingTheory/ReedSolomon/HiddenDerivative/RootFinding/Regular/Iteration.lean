/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.JetPrefix
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.JetDivisibility


/-!
# Iterated uniqueness from a regular initial Hasse jet

This file iterates the regular one-coefficient lift from [Kop15, Theorem 4.4] to obtain the
below-characteristic fixed-initial-jet uniqueness consequence of [Kop15, Corollary 4.5].  The
argument has two layers.

First, agreement of two candidate polynomials through centered order `k + r` makes their Hasse
jets through order `r` congruent modulo `(X - center) ^ k`.  Substituting those jets into any
differential polynomial preserves that congruence.  Second, if two solutions already agree below
centered degree `k + r`, change the first solution's coefficient in that degree to match the
second.  The congruence lemma shows that this changed candidate raises the differential residual
from order `k` to order `k + 1`.  The verified one-step theorem says that the coefficient doing so
is unique; zero also works because the first candidate is itself a solution.  Hence the two
coefficients agree.  Strong induction forces every coefficient through the ambient degree bound.

The main theorem says **at most one** degree-`D` solution extends a fixed regular initial jet when
`D < ringChar F`.  It neither proves that an extension exists nor gives an enumeration algorithm.
In particular, uniqueness of every successive coefficient conditional on a solution must not be
confused with existence of a complete solution.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Theorem 4.4 and Corollary 4.5.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open Polynomial

variable {F : Type*} [Field F] {r d D k : ℕ}

/-! ### Substitution preserves centered jet congruences -/

/-- Evaluating a multivariate polynomial at pointwise-congruent tuples preserves divisibility by
the congruence modulus. -/
private theorem pow_dvd_eval₂Hom_sub_of_forall_pow_dvd_sub
    {R S σ : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : σ → S)
    (u : S) (m : ℕ) (h : ∀ v, u ^ m ∣ a v - b v) (Q : MvPolynomial σ R) :
    u ^ m ∣ MvPolynomial.eval₂Hom f a Q - MvPolynomial.eval₂Hom f b Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      simp only [map_add]
      ring
  | mul_X P n hP =>
      have hn := h n
      have hsum :
          u ^ m ∣
            (MvPolynomial.eval₂Hom f a P - MvPolynomial.eval₂Hom f b P) * a n +
              MvPolynomial.eval₂Hom f b P * (a n - b n) :=
        (dvd_mul_of_dvd_left hP _).add (dvd_mul_of_dvd_right hn _)
      convert hsum using 1
      simp only [map_mul, MvPolynomial.eval₂Hom_X']
      ring

/-- If two polynomials agree through centered order `m + r - 1`, their Hasse derivatives through
order `r` agree modulo centered order `m` after Taylor translation.  The additive exponent avoids
all truncated-subtraction ambiguity. -/
theorem X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd
    (P P' : F[X]) (center : F) (m r : ℕ)
    (h : X ^ (m + r) ∣ taylor center P - taylor center P') (j : Fin (r + 1)) :
    X ^ m ∣ taylor center (hasseDeriv j P) - taylor center (hasseDeriv j P') := by
  rw [← LinearMap.map_sub]
  change X ^ m ∣ taylor center (hasseDeriv j P - hasseDeriv j P')
  rw [← LinearMap.map_sub, ← hasseDeriv_taylor, X_pow_dvd_iff]
  intro i hi
  rw [hasseDeriv_coeff]
  have hcoeff := X_pow_dvd_iff.mp h (i + j.val) (by omega)
  rw [coeff_sub] at hcoeff
  rw [LinearMap.map_sub, coeff_sub, hcoeff, mul_zero]

/-- Agreement through centered order `m + r - 1` is preserved, with the expected loss of `r`
orders, by differential specialization of an order-`r` equation. -/
theorem X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd
    (Q : DifferentialPolynomial F r) (P P' : F[X]) (center : F) (m : ℕ)
    (h : X ^ (m + r) ∣ taylor center P - taylor center P') :
    X ^ m ∣ shiftedJetSubstitution center P Q - shiftedJetSubstitution center P' Q := by
  rw [shiftedJetSubstitution_eq_eval₂Hom, shiftedJetSubstitution_eq_eval₂Hom]
  apply pow_dvd_eval₂Hom_sub_of_forall_pow_dvd_sub Polynomial.C
      (shiftedJetValues center P) (shiftedJetValues center P') X m
  intro v
  rcases v with _ | j
  · simp [shiftedJetValues]
  · exact X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd P P' center m r h j

/-- Source-facing centered form: if two candidates agree through order `m + r - 1`, their
differential residuals agree modulo `(X - center) ^ m`. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd
    (Q : DifferentialPolynomial F r) (P P' : F[X]) (center : F) (m : ℕ)
    (h : (X - C center) ^ (m + r) ∣ P - P') :
    (X - C center) ^ m ∣
      differentialSpecialization Q P - differentialSpecialization Q P' := by
  rw [← X_pow_dvd_taylor_iff_X_sub_C_pow_dvd,
    LinearMap.map_sub, taylor_differentialSpecialization,
    taylor_differentialSpecialization]
  apply X_pow_dvd_shiftedJetSubstitution_sub_of_X_pow_add_dvd Q P P' center m
  rw [← LinearMap.map_sub, X_pow_dvd_taylor_iff_X_sub_C_pow_dvd]
  exact h

/-! ### One successive coefficient is forced -/

/-- At a regular solution, every next centered coefficient below the characteristic is forced.

The hypotheses say that `P` and `P'` are complete solutions and agree in centered degrees below
`k + r`.  The conclusion is agreement in degree `k + r`.  This is the exact induction step behind
fixed-initial-jet uniqueness; it does not assert that either solution exists. -/
theorem hasseCoeffAt_add_order_eq_of_regular_solutions_of_eq_below
    (hk : 0 < k) (Q : DifferentialPolynomial F r) (center : F) (P P' : F[X]) (D : ℕ)
    (hregular : IsRegularJet Q (Fin.last r) center (polynomialJet center P))
    (hdegree : k + r ≤ D) (hD : D < ringChar F)
    (hsolution : differentialSpecialization Q P = 0)
    (hsolution' : differentialSpecialization Q P' = 0)
    (hbelow : ∀ i < k + r, hasseCoeffAt center i P = hasseCoeffAt center i P') :
    hasseCoeffAt center (k + r) P = hasseCoeffAt center (k + r) P' := by
  let gamma := hasseCoeffAt center (k + r) P' - hasseCoeffAt center (k + r) P
  let lifted := regularLiftCandidate center gamma k r P
  have hliftedJet : hasseJet (k + r + 1) center lifted = hasseJet (k + r + 1) center P' := by
    funext i
    change hasseCoeffAt center i.val lifted = hasseCoeffAt center i.val P'
    by_cases hi : i.val < k + r
    · rw [show lifted = P + hassePerturbation center gamma (k + r) by rfl,
        hasseCoeffAt_add_hassePerturbation_of_lt P center gamma hi,
        hbelow i.val hi]
    · have hieq : i.val = k + r := by omega
      rw [hieq, show lifted = P + hassePerturbation center gamma (k + r) by rfl,
        hasseCoeffAt_add_hassePerturbation_self]
      simp only [gamma]
      ring
  have hagree : (X - C center) ^ (k + r + 1) ∣ lifted - P' :=
    (X_sub_C_pow_dvd_sub_iff_hasseJet_eq lifted P' center (k + r + 1)).2 hliftedJet
  have hcongr : (X - C center) ^ (k + 1) ∣
      differentialSpecialization Q lifted - differentialSpecialization Q P' := by
    have hexponent : k + 1 + r = k + r + 1 := by omega
    have :=
      X_sub_C_pow_dvd_differentialSpecialization_sub_of_X_sub_C_pow_add_dvd
        Q lifted P' center (k + 1) (by rw [hexponent]; exact hagree)
    exact this
  have hliftResidual :
      (X - C center) ^ (k + 1) ∣ differentialSpecialization Q lifted := by
    rw [hsolution', sub_zero] at hcongr
    exact hcongr
  have hbaseResidual :
      (X - C center) ^ k ∣ differentialSpecialization Q P := by
    rw [hsolution]
    exact dvd_zero _
  obtain ⟨gamma₀, hgamma₀, hunique⟩ :=
    existsUnique_regularLiftCoefficient_centered_of_isRegularJet_of_le_of_lt_ringChar
      hk Q center P D hregular hdegree hD hbaseResidual
  have hzero :
      (X - C center) ^ (k + 1) ∣
        differentialSpecialization Q (regularLiftCandidate center 0 k r P) := by
    have hcandidate : regularLiftCandidate center 0 k r P = P := by
      simp [regularLiftCandidate, hassePerturbation]
    rw [hcandidate, hsolution]
    exact dvd_zero _
  have hgamma_eq_zero : gamma = 0 := by
    calc
      gamma = gamma₀ := hunique gamma (by simpa [lifted] using hliftResidual)
      _ = 0 := (hunique 0 hzero).symm
  exact (sub_eq_zero.mp (by simpa only [gamma] using hgamma_eq_zero)).symm

/-! ### Iterated fixed-initial-jet uniqueness -/

/-- Below the characteristic, a fixed regular initial Hasse jet has at most one degree-`D`
solution of an order-`r` polynomial differential equation.

This is the uniqueness specialization of [Kop15, Corollary 4.5].  It is intentionally an
`at most one` theorem: no existence or algorithmic enumeration claim is included. -/
theorem eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq
    (Q : DifferentialPolynomial F r) (center : F) (P P' : F[X]) (D : ℕ)
    (hregular : IsRegularJet Q (Fin.last r) center (polynomialJet center P))
    (hdegree : P.degree ≤ D) (hdegree' : P'.degree ≤ D)
    (hD : D < ringChar F)
    (hsolution : differentialSpecialization Q P = 0)
    (hsolution' : differentialSpecialization Q P' = 0)
    (hjet : polynomialJet (d := r) center P = polynomialJet (d := r) center P') :
    P = P' := by
  apply taylor_injective center
  ext i
  rw [taylor_coeff, taylor_coeff]
  by_cases hiD : i ≤ D
  · induction i using Nat.strong_induction_on with
    | h i ih =>
        by_cases hir : i ≤ r
        · let j : Fin (r + 1) := ⟨i, Nat.lt_succ_iff.mpr hir⟩
          exact congrFun hjet j
        · let k := i - r
          have hk : 0 < k := by omega
          have hkr : k + r = i := by omega
          rw [← hkr]
          apply hasseCoeffAt_add_order_eq_of_regular_solutions_of_eq_below
              hk Q center P P' D hregular
          · simpa [hkr] using hiD
          · exact hD
          · exact hsolution
          · exact hsolution'
          · intro j hj
            exact ih j (by omega) (by omega)
  · have hDi : D < i := Nat.lt_of_not_ge hiD
    have hderivZero (S : F[X]) (hS : S.degree ≤ D) : hasseDeriv i S = 0 := by
      by_cases hSzero : S = 0
      · simp [hSzero]
      · apply hasseDeriv_eq_zero_of_lt_natDegree
        exact (natDegree_lt_iff_degree_lt hSzero).2
          (hS.trans_lt (by simpa using hDi))
    rw [hderivZero P hdegree, hderivZero P' hdegree']

/-- Root-solver form at an arbitrary highest active jet.  The ambient equation is restricted to
its active prefix before applying fixed-jet uniqueness. -/
theorem eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq_of_isHighestActiveJet
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : IsHighestActiveJet Q s)
    (center : F) (P P' : F[X]) (D : ℕ)
    (hregular : IsRegularJet Q s center (polynomialJet center P))
    (hdegree : P.degree ≤ D) (hdegree' : P'.degree ≤ D)
    (hD : D < ringChar F)
    (hsolution : differentialSpecialization Q P = 0)
    (hsolution' : differentialSpecialization Q P' = 0)
    (hjet : polynomialJet (d := s.val) center P = polynomialJet (d := s.val) center P') :
    P = P' := by
  obtain ⟨Q', hQ'⟩ := exists_prefixDifferentialPolynomial Q s hs
  rw [← hQ'] at hregular hsolution hsolution'
  apply eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq
      Q' center P P' D
  · exact (isRegularJet_rename_jetPrefixEmbedding_iff s Q' center P).mp hregular
  · exact hdegree
  · exact hdegree'
  · exact hD
  · simpa only [differentialSpecialization_rename_jetPrefixEmbedding] using hsolution
  · simpa only [differentialSpecialization_rename_jetPrefixEmbedding] using hsolution'
  · exact hjet

/-- Bounded-solution subtype form: over a fixed regular initial jet, the fiber of bounded
solutions contains at most one element. -/
theorem _root_.PolynomialDifferential.BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (hs : IsHighestActiveJet Q s)
    (center : F) (P P' : BoundedSolution Q D)
    (hregular : IsRegularJet Q s center (polynomialJet center P.polynomial))
    (hD : D < ringChar F)
    (hjet : polynomialJet (d := s.val) center P.polynomial =
      polynomialJet (d := s.val) center P'.polynomial) :
    P = P' := by
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_regular_solutions_of_degree_le_of_polynomialJet_eq_of_isHighestActiveJet
    Q s hs center P.polynomial P'.polynomial D hregular P.degree_le P'.degree_le hD
      P.equation P'.equation hjet

end

end ReedSolomon.HiddenDerivative
