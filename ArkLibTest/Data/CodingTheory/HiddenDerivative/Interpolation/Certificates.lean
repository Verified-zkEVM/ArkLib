/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates

/-!
# Acceptance cases for hidden-derivative interpolation certificates

* A concrete certificate: on the two points `0, 1` of any nontrivial commutative ring, with the
  constant received word `r`, the order-zero polynomial `Y₀ - r` with `k = A = ambientDim = 2` and
  `m = 1`. Over `ℤ`, `specializes_to_zero` says that a polynomial of degree below `2` equal to `r`
  at `0` and `1` is the constant `r`.
* Over `ZMod 5` the same polynomial is a prime-field certificate, and `below_characteristic` gives
  the source's guard; `specializes_to_zero` is reached through the parent structure.
* A certificate with `A = 0` cannot exist: its weighted degree would be below `m * 0 = 0`.
* The source's `specializes_to_zero` over `ZMod q`, derived from the general statement.
-/

open MvPolynomial PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative ListDecoding

namespace CertificatesTest

/-- `Y₀ - r` satisfies the multiplicity-one constraints at `(center, r)`. -/
theorem satisfiesLocalConstraints_one_Y_zero_sub {R : Type*} [CommRing R] (center r : R) :
    SatisfiesLocalConstraints (d := 0) 1 center r (X (some 0) - C r) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply, projectLowContact,
    weightedTruncation_eq_zero_iff]
  have h : (unscaledLocalSubstitution 0 center r).toLinearMap (X (some 0) - C r) =
      X (localT 0) * (X (localE 0) + localJetSum 0) := by
    simp only [AlgHom.toLinearMap_apply, map_sub, unscaledLocalSubstitution_Y_zero, algHom_C,
      algebraMap_eq, mul_add, T_mul_localJetSum]
    ring
  rw [h]
  simpa using mul_mem_restrictWeightedOrder
    (X_mem_restrictWeightedOrder (R := R) (localContactWeight 0) (localT 0) le_rfl)
    (by simp : X (localE 0) + localJetSum 0 ∈
      restrictWeightedOrder (R := R) (localContactWeight 0) 0)

/-- `Y₀ - r` has weighted degree at most `1` at ambient degree `1`. -/
theorem differentialWeightedDegree_Y_zero_sub_le {R : Type*} [CommRing R] (r : R) :
    differentialWeightedDegree 1 (X (some 0) - C r : DifferentialPolynomial R 0) ≤ 1 := by
  rw [differentialWeightedDegree, ← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  refine Submodule.sub_mem _ (X_mem_restrictWeightedDegree _ _ _ ?_) ?_
  · simp [differentialWeight]
  · rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le, weightedTotalDegree_C]
    exact Nat.zero_le _

/-- `Y₀ - r` is nonzero: it evaluates to `1` at `Y₀ = r + 1`. -/
theorem Y_zero_sub_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (r : R) :
    (X (some 0) - C r : DifferentialPolynomial R 0) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ ↦ r + 1)) h
  simp at this

/-- The order-zero certificate on two evaluation points with a constant received word. -/
noncomputable def constantCertificate {R : Type*} [CommRing R] [Nontrivial R]
    (domain : Fin 2 ↪ R) (r : R) :
    InterpolationCertificate 2 2 0 1 domain (fun _ ↦ r) where
  ambientDim := 2
  messageDim_le := le_rfl
  ambientDim_le := by simp
  order_lt_degree := by decide
  interpolant := X (some 0) - C r
  nonzero := Y_zero_sub_ne_zero r
  weighted_degree_lt := (differentialWeightedDegree_Y_zero_sub_le r).trans_lt (by decide)
  local_constraints := fun i ↦ satisfiesLocalConstraints_one_Y_zero_sub (domain i) r

/-- The points `0, 1` of `ℤ`. -/
def intDomain : Fin 2 ↪ ℤ :=
  ⟨fun i ↦ ((i : ℕ) : ℤ), fun a b h ↦ Fin.ext (by simpa using h)⟩

/-- The points `0, 1` of `ZMod 5`. -/
def zmodDomain : Fin 2 ↪ ZMod 5 :=
  ⟨fun i ↦ ((i : ℕ) : ZMod 5), by intro a b h; revert a b h; decide⟩

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The jet degree of `Y₀ - r` is at most `1`. -/
theorem jetDegree_Y_zero_sub_le {R : Type*} [CommRing R] (r : R) (j : Fin 1) :
    jetDegree (X (some 0) - C r : DifferentialPolynomial R 0) j ≤ 1 := by
  rw [jetDegree]
  refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · exact (degreeOf_X_le _ _).trans le_rfl
  · simp

/-- The prime-field certificate over `ZMod 5`: `1 ≠ 0` in `ZMod 5`, and `m A = 2 ≤ 25`. -/
noncomputable def zmodCertificate (r : ZMod 5) :
    HiddenDerivativeInterpolationCertificate (k := 2) (A := 2) 0 1 zmodDomain (fun _ ↦ r) where
  toInterpolationCertificate := constantCertificate zmodDomain r
  castsNeZero := fun j k hk hkj ↦ by
    have : k = 1 := by
      have := jetDegree_Y_zero_sub_le r j
      simp only [constantCertificate] at hkj
      omega
    subst this
    decide
  contact_budget_le := by decide

end CertificatesTest

open CertificatesTest

/-- Over `ℤ`, a polynomial of degree below `2` equal to `r` at `0` and `1` is the constant `r`. -/
example (r : ℤ) (P : MessagePolynomial ℤ 2) (h0 : (P : Polynomial ℤ).eval 0 = r)
    (h1 : (P : Polynomial ℤ).eval 1 = r) : (P : Polynomial ℤ) = Polynomial.C r := by
  have hagree : 2 ≤ Code.agree (ReedSolomon.evalOnPoints intDomain P) (fun _ ↦ r) := by
    rw [Code.agree]
    have : ({i | (ReedSolomon.evalOnPoints intDomain P) i = r} : Finset (Fin 2)) = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases i
      · exact h0
      · exact h1
    simp [this]
  have h := (constantCertificate intDomain r).specializes_to_zero P hagree
  rw [← sub_eq_zero]
  simpa [constantCertificate, differentialSpecialization, differentialSpecializationHom] using h

/-- No certificate has `A = 0`: the weighted degree would be below `m * 0 = 0`. -/
example {ι R : Type*} [Fintype ι] [CommRing R] {k d m : ℕ} {domain : ι ↪ R} {received : ι → R}
    (c : InterpolationCertificate k 0 d m domain received) : False := by
  have := c.weighted_degree_lt
  simp at this

/-- Over `ZMod 5` the source's guard holds: `ambientDim - 1 = 1 < 5` and every jet degree is
below `5`. -/
example (r : ZMod 5) :
    (zmodCertificate r).ambientDim - 1 < 5 ∧
      ∀ j, jetDegree (zmodCertificate r).interpolant j < 5 :=
  (zmodCertificate r).below_characteristic

/-- `specializes_to_zero` on a prime-field certificate is reached through the parent structure. -/
example (r : ZMod 5) (P : MessagePolynomial (ZMod 5) 2)
    (hAgreement : 2 ≤ Code.agree (ReedSolomon.evalOnPoints zmodDomain P) (fun _ ↦ r)) :
    differentialSpecialization (zmodCertificate r).interpolant (P : Polynomial (ZMod 5)) = 0 :=
  (zmodCertificate r).specializes_to_zero P hAgreement

/-- Source shape of `HiddenDerivativeInterpolationCertificate.specializes_to_zero`. -/
example {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (P : MessagePolynomial (ZMod q) k)
    (hAgreement : A ≤ Code.agree (ReedSolomon.evalOnPoints domain P) received) :
    differentialSpecialization construction.interpolant (P : Polynomial (ZMod q)) = 0 :=
  construction.specializes_to_zero P hAgreement

/-- Source shape of the `IsBelowCharacteristic` field: `D < ringChar (ZMod q)` and every jet degree
is below `ringChar (ZMod q)`, with `D = ambientDim - 1`. -/
example {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    construction.ambientDim - 1 < ringChar (ZMod q) ∧
      ∀ j, jetDegree construction.interpolant j < ringChar (ZMod q) := by
  rw [ZMod.ringChar_zmod_n]
  exact construction.below_characteristic
