/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Univariate.EuclideanAlgorithm
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Executable inversion in a polynomial quotient

This file uses `CompPoly.CPolynomial.normXgcd` to compute an inverse behind a
coprimality guard, proves its modular multiplication contract, and interprets
the result in the proof-facing quotient `F[X] / (modulus)`.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Return the Bézout coefficient of `a` exactly when normalized extended gcd
certifies that `a` and `modulus` are coprime. -/
def inverseMod? (a modulus : CPolynomial F) : Option (CPolynomial F) :=
  let result := normXgcd a modulus
  if result.1 == 1 then some result.2.1 else none

theorem inverseMod?_eq_none_iff (a modulus : CPolynomial F) :
    inverseMod? a modulus = none ↔ (normXgcd a modulus).1 ≠ 1 := by
  simp [inverseMod?, beq_iff_eq]

theorem inverseMod?_eq_some_iff (a modulus inverse : CPolynomial F) :
    inverseMod? a modulus = some inverse ↔
      (normXgcd a modulus).1 = 1 ∧ inverse = (normXgcd a modulus).2.1 := by
  by_cases hgcd : (normXgcd a modulus).1 = 1
  · have hout : inverseMod? a modulus = some (normXgcd a modulus).2.1 := by
      simp [inverseMod?, hgcd]
    constructor
    · intro hin
      refine ⟨hgcd, ?_⟩
      exact Option.some.inj (hin.symm.trans hout)
    · rintro ⟨_, rfl⟩
      exact hout
  · simp [inverseMod?, beq_iff_eq, hgcd]

/-- A returned Bézout coefficient is a multiplicative inverse modulo a monic
polynomial. The right side is reduced as well, covering the unit modulus. -/
theorem inverseMod?_mul_modByMonic {a modulus inverse : CPolynomial F}
    (hmodulus : modulus.monic) (hinverse : inverseMod? a modulus = some inverse) :
    (a * inverse).modByMonic modulus = (1 : CPolynomial F).modByMonic modulus := by
  obtain ⟨hgcd, hinverse⟩ := (inverseMod?_eq_some_iff a modulus inverse).mp hinverse
  have hbezout := normXgcd_bezout a modulus 0
  simp only [Bezout] at hbezout
  apply toPoly_injective
  rw [modByMonic_toPoly_eq_modByMonic _ _ hmodulus,
    modByMonic_toPoly_eq_modByMonic _ _ hmodulus, toPoly_mul, toPoly_one]
  apply Polynomial.modByMonic_eq_of_dvd_sub ((monic_toPoly_iff modulus).mp hmodulus)
  refine ⟨-(normXgcd a modulus).2.2.toPoly, ?_⟩
  have hbezoutPoly := congrArg (CPolynomial.toPoly (R := F)) hbezout
  rw [hgcd, toPoly_one, toPoly_add, toPoly_mul, toPoly_mul] at hbezoutPoly
  rw [← hinverse] at hbezoutPoly
  calc
    a.toPoly * inverse.toPoly - 1 =
        -((normXgcd a modulus).2.2.toPoly * modulus.toPoly) := by
      rw [hbezoutPoly]
      ring
    _ = modulus.toPoly * -(normXgcd a modulus).2.2.toPoly := by ring

/-- The executable inverse guard succeeds exactly when the input is coprime to the modulus.
This discharges availability after a constructor has removed the denominator's common factors.
-/
theorem inverseMod_exists_iff_coprime (a h : CPolynomial F) :
    (∃ b, inverseMod? a h = some b) ↔ IsCoprime a.toPoly h.toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have heq : (normXgcd a h).1 = 1 ↔ IsCoprime a.toPoly h.toPoly := by
    rw [← toPoly_injective.eq_iff, normXgcd_fst_toPoly, toPoly_one, normalize_eq_one]
    constructor
    · intro hg
      rw [isUnit_iff_dvd_one] at hg
      obtain ⟨b, hb⟩ := hg
      refine ⟨EuclideanDomain.gcdA a.toPoly h.toPoly * b,
        EuclideanDomain.gcdB a.toPoly h.toPoly * b, ?_⟩
      rw [hb, EuclideanDomain.gcd_eq_gcd_ab]
      ring
    · intro hc
      rw [isUnit_iff_dvd_one]
      obtain ⟨u, v, huv⟩ := hc
      rw [← huv]
      exact dvd_add (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_left _ _) _)
        (dvd_mul_of_dvd_right (EuclideanDomain.gcd_dvd_right _ _) _)
  constructor
  · rintro ⟨b, hb⟩
    exact heq.mp ((inverseMod?_eq_some_iff a h b).mp hb).1
  · intro hc
    exact ⟨_, (inverseMod?_eq_some_iff a h _).mpr ⟨heq.mpr hc, rfl⟩⟩

/-- Specializing a returned inverse at any geometric root of the modulus gives the scalar
inverse equation. This remains valid when that root is absent from the coefficient field. -/
theorem eval₂_mul_inverseMod_eq_one {L : Type*} [Field L] (ι : F →+* L) (θ : L)
    {a modulus inverse : CPolynomial F}
    (hroot : modulus.toPoly.eval₂ ι θ = 0)
    (hinverse : inverseMod? a modulus = some inverse) :
    a.toPoly.eval₂ ι θ * inverse.toPoly.eval₂ ι θ = 1 := by
  obtain ⟨hgcd, hinverse⟩ := (inverseMod?_eq_some_iff a modulus inverse).mp hinverse
  have hb := normXgcd_bezout a modulus 0
  simp only [Bezout] at hb
  have heval := congrArg (fun p : CPolynomial F => p.toPoly.eval₂ ι θ) hb
  rw [hgcd, ← hinverse] at heval
  simpa [toPoly_one, toPoly_add, toPoly_mul, hroot, mul_comm] using heval.symm

end CompPoly.CPolynomial

namespace ArkLib.PolynomialQuotient

open CompPoly CompPoly.CPolynomial Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The principal ideal generated by a computable modulus. -/
noncomputable def modIdeal (modulus : CPolynomial F) : Ideal (Polynomial F) :=
  Ideal.span {modulus.toPoly}

/-- The proof-facing polynomial quotient by `modulus`. -/
abbrev ModAlgebra (modulus : CPolynomial F) : Type _ :=
  Polynomial F ⧸ modIdeal modulus

/-- Executable canonical reduction when `modulus` is monic. -/
def reduce (modulus p : CPolynomial F) : CPolynomial F :=
  p.modByMonic modulus

/-- Interpret a computable polynomial in the proof-facing quotient. -/
noncomputable def quotientHom (modulus : CPolynomial F) :
    CPolynomial F →+* ModAlgebra modulus :=
  (Ideal.Quotient.mk (modIdeal modulus)).comp
    (CPolynomial.ringEquiv : CPolynomial F ≃+* Polynomial F).toRingHom

@[simp] theorem quotientHom_apply (modulus p : CPolynomial F) :
    quotientHom modulus p = Ideal.Quotient.mk (modIdeal modulus) p.toPoly := by
  simp [quotientHom, CPolynomial.ringEquiv_apply]

/-- Executable monic reduction preserves the represented quotient element. -/
@[simp] theorem quotientHom_reduce {modulus : CPolynomial F} (hmodulus : modulus.monic)
    (p : CPolynomial F) : quotientHom modulus (reduce modulus p) = quotientHom modulus p := by
  rw [quotientHom_apply, quotientHom_apply, reduce,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hmodulus, Ideal.Quotient.eq]
  have h : p.toPoly %ₘ modulus.toPoly - p.toPoly =
      -(modulus.toPoly * (p.toPoly /ₘ modulus.toPoly)) := by
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    ring
  rw [h, modIdeal]
  exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

@[simp] theorem quotientHom_modulus (modulus : CPolynomial F) :
    quotientHom modulus modulus = 0 := by
  rw [quotientHom_apply, Ideal.Quotient.eq_zero_iff_mem, modIdeal]
  exact Ideal.mem_span_singleton_self _

/-- `inverseMod?` success is interpreted as a unit equation in the quotient. -/
theorem quotientHom_mul_inverseMod?_eq_one {a modulus inverse : CPolynomial F}
    (hmodulus : modulus.monic)
    (hinverse : inverseMod? a modulus = some inverse) :
    quotientHom modulus a * quotientHom modulus inverse = 1 := by
  rw [← map_mul]
  calc
    quotientHom modulus (a * inverse) = quotientHom modulus (reduce modulus (a * inverse)) :=
      (quotientHom_reduce hmodulus _).symm
    _ = quotientHom modulus (reduce modulus 1) := by
      exact congrArg (quotientHom modulus)
        (inverseMod?_mul_modByMonic hmodulus hinverse)
    _ = quotientHom modulus 1 := quotientHom_reduce hmodulus _
    _ = 1 := map_one _

/-- Reduction gives a coefficient polynomial of degree strictly below the modulus, including
the unit modulus where the reduced polynomial is zero. -/
theorem degree_reduce_lt {modulus : CPolynomial F} (hmodulus : modulus.monic)
    (p : CPolynomial F) : (reduce modulus p).toPoly.degree < modulus.toPoly.degree := by
  rw [reduce, modByMonic_toPoly_eq_modByMonic _ _ hmodulus]
  exact Polynomial.degree_modByMonic_lt _ ((monic_toPoly_iff _).mp hmodulus)

/-- Repeated reduction does not alter already canonical coefficient data. -/
@[simp] theorem reduce_idempotent {modulus : CPolynomial F} (hmodulus : modulus.monic)
    (p : CPolynomial F) : reduce modulus (reduce modulus p) = reduce modulus p := by
  apply toPoly_injective
  rw [reduce, modByMonic_toPoly_eq_modByMonic _ _ hmodulus]
  exact (Polynomial.modByMonic_eq_self_iff ((monic_toPoly_iff _).mp hmodulus)).mpr
    (degree_reduce_lt hmodulus p)

end ArkLib.PolynomialQuotient
