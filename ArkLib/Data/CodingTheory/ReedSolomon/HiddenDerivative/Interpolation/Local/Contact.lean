/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Identity
/-!
# Local contact and root multiplicity

This file turns the low-contact coefficient constraints at an agreement point into a root of
multiplicity `m` of the canonical differential specialization.  A local monomial `T^i E^b Y^e`
has contact order `i + d * b`.  Under the actual-polynomial interpretation, `T` becomes `X` and
the hidden error is divisible by `X^d`, so every surviving monomial contributes the required
power of `X`.  Taylor translation then returns the centered factor `(X - C center)^m`.

The monomial divisibility argument is adapted, with permission, from Kai Zhe Zheng's
`rs-ld-mca` formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`, file
`RSListDecoding/Lemmas/Contact.lean`.  Its composition with ArkLib's canonical differential
specialization and local-constraint map is new.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 3 (local interpolation).
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]
variable {d m : ℕ}

/-- A local monomial acquires its contact-order power of `t` whenever `T` maps to `t` and
`E` maps to a multiple of `t^d`. -/
private theorem localContactOrder_pow_dvd_monomialSpecialization
    (g : LocalVariable d → S) (t : S)
    (hT : g (localT d) = t)
    (hE : t ^ d ∣ g (localE d))
    (e : LocalVariable d →₀ ℕ) :
    t ^ localContactOrder d e ∣
      e.prod fun v exponent ↦ g v ^ exponent := by
  have hprod :
      (∏ v ∈ e.support, t ^ (localContactWeight d v * e v)) ∣
        ∏ v ∈ e.support, g v ^ e v := by
    apply Finset.prod_dvd_prod_of_dvd
    intro v _hv
    rcases v with (_ | (_ | j))
    · have hT' : g none = t := by simpa [localT] using hT
      rw [hT']
      simp [localContactWeight]
    · simpa [localContactWeight, localE, localAux, pow_mul] using
        (pow_dvd_pow_of_dvd hE (e (some none)))
    · simp [localContactWeight]
  simpa [localContactOrder, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
    nsmul_eq_mul, mul_comm, Finset.prod_pow_eq_pow_sum] using hprod

/-- Vanishing of every coefficient below contact order `m` forces divisibility by `t^m` after
every specialization respecting the weights of `T` and `E`. -/
theorem pow_dvd_eval₂Hom_of_lowContact_coeff_zero
    (F : LocalPolynomial R d)
    (hcoeff : ∀ e, localContactOrder d e < m → MvPolynomial.coeff e F = 0)
    (f : R →+* S) (g : LocalVariable d → S) (t : S)
    (hT : g (localT d) = t)
    (hE : t ^ d ∣ g (localE d)) :
    t ^ m ∣ MvPolynomial.eval₂Hom f g F := by
  rw [F.as_sum, map_sum]
  apply Finset.dvd_sum
  intro e he
  rw [MvPolynomial.eval₂Hom_monomial]
  have hne : MvPolynomial.coeff e F ≠ 0 := MvPolynomial.mem_support_iff.mp he
  have hm : m ≤ localContactOrder d e := by
    by_contra h
    exact hne (hcoeff e (Nat.lt_of_not_ge h))
  refine (pow_dvd_pow t hm).trans ?_
  exact (localContactOrder_pow_dvd_monomialSpecialization g t hT hE e).mul_left
    (f (MvPolynomial.coeff e F))

/-- The polynomial projection form of the local constraints gives coefficientwise vanishing
below contact order `m`. -/
theorem coeff_unscaledLocalSubstitution_eq_zero_of_satisfiesLocalConstraints
    (Q : DifferentialPolynomial R d) (center received : R)
    (hQ : SatisfiesLocalConstraints m center received Q)
    (e : LocalVariable d →₀ ℕ) (he : localContactOrder d e < m) :
    MvPolynomial.coeff e (unscaledLocalSubstitution d center received Q) = 0 := by
  have hprojection :
      projectLowContact (R := R) (d := d) m
          (unscaledLocalSubstitution d center received Q) = 0 := by
    simpa [SatisfiesLocalConstraints, localConstraintAt] using hQ
  exact (projectLowContact_eq_zero_iff m
    (unscaledLocalSubstitution d center received Q)).mp hprojection e he

/-- Low contact implies `X^m` divisibility after substituting a hidden error divisible by `X^d`
and arbitrary moving visible jets. -/
theorem X_pow_dvd_localPolynomialEvaluation_of_lowContact
    (F : LocalPolynomial R d)
    (hcoeff : ∀ e, localContactOrder d e < m → MvPolynomial.coeff e F = 0)
    (center : R) (P error : R[X])
    (herror : Polynomial.X ^ d ∣ error) :
    Polynomial.X ^ m ∣ localPolynomialEvaluation center P error F := by
  change Polynomial.X ^ m ∣
    MvPolynomial.eval₂Hom Polynomial.C
      (fun v : LocalVariable d => match v with
        | none => Polynomial.X
        | some none => error
        | some (some j) =>
            Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P)) F
  exact pow_dvd_eval₂Hom_of_lowContact_coeff_zero
    F hcoeff Polynomial.C _ Polynomial.X rfl herror

/-- At an agreement point, the shifted differential specialization has an `X^m` factor.  This
is the local-coordinate form of the contact lemma. -/
theorem X_pow_dvd_shiftedJetSubstitution_of_contact
    (Q : DifferentialPolynomial R d) (P : R[X]) (center received : R)
    (hP : P.eval center = received)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    Polynomial.X ^ m ∣ shiftedJetSubstitution center P Q := by
  rw [← localPolynomialEvaluation_unscaled_backwardError Q center received P hP]
  apply X_pow_dvd_localPolynomialEvaluation_of_lowContact
  · exact coeff_unscaledLocalSubstitution_eq_zero_of_satisfiesLocalConstraints
      Q center received hQ
  · exact X_pow_dvd_hiddenTaylorError center P

/-- At an agreement point, Taylor translation of the canonical differential specialization is
divisible by `X^m`. -/
theorem X_pow_dvd_taylor_differentialSpecialization_of_contact
    (Q : DifferentialPolynomial R d) (P : R[X]) (center received : R)
    (hP : P.eval center = received)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    Polynomial.X ^ m ∣
      Polynomial.taylor center (differentialSpecialization Q P) := by
  rw [taylor_differentialSpecialization]
  exact X_pow_dvd_shiftedJetSubstitution_of_contact Q P center received hP hQ

/-- Local coefficient constraints at an actual agreement give multiplicity `m` for the
canonical differential specialization.  The result is characteristic-safe. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_of_contact
    (Q : DifferentialPolynomial R d) (P : R[X]) (center received : R)
    (hP : P.eval center = received)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    (Polynomial.X - Polynomial.C center) ^ m ∣ differentialSpecialization Q P := by
  rw [Polynomial.X_sub_C_pow_dvd_iff_hasseDeriv_eval_eq_zero,
    ← Polynomial.X_pow_dvd_taylor_iff]
  exact X_pow_dvd_taylor_differentialSpecialization_of_contact
    Q P center received hP hQ

/-- At `d = m = 0`, the low-contact projection is empty and every differential polynomial
satisfies the local constraints. -/
theorem order_zero_local_constraints_vacuous_canary
    {R : Type*} [CommRing R] (Q : DifferentialPolynomial R 0)
    (P : R[X]) (center received : R) (hP : P.eval center = received) :
    SatisfiesLocalConstraints 0 center received Q ∧
      (Polynomial.X - Polynomial.C center) ^ 0 ∣ differentialSpecialization Q P := by
  have hQ : SatisfiesLocalConstraints 0 center received Q := by
    rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply,
      projectLowContact_eq_zero_iff]
    intro e he
    omega
  exact ⟨hQ,
    X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P center received hP hQ⟩

end ReedSolomon.HiddenDerivative
