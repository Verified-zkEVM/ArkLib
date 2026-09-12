/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import CompPoly.Univariate.DivisionCorrectness
public import Mathlib.RingTheory.Ideal.Quotient.Defs
-- Coefficient refinement unfolds the stored array lookup at its defining modules.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Stored arithmetic in a monic polynomial quotient

Canonical representatives reuse CompPoly's monic division over a commutative ring.
The coefficient ring may be nonreduced. These operations have exact refinement to the
semantic quotient; no field structure or separability assumption is imposed.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Stored polynomials already reduced modulo the chosen monic equation. -/
abbrev Representative (h : CPolynomial R) := {p : CPolynomial R // p.modByMonic h = p}

/-- Monic reduction produces a polynomial of degree below the equation's degree. -/
theorem degree_remainder_lt (h p : CPolynomial R) (hh : h.monic) :
    (p.modByMonic h).toPoly.degree < h.toPoly.degree := by
  rw [modByMonic_toPoly_eq_modByMonic _ _ hh]
  exact Polynomial.degree_modByMonic_lt _ ((monic_toPoly_iff h).mp hh)

/-- CompPoly's stored monic remainder is idempotent. -/
theorem remainder_idempotent (h p : CPolynomial R) (hh : h.monic) :
    (p.modByMonic h).modByMonic h = p.modByMonic h := by
  apply toPoly_injective
  rw [modByMonic_toPoly_eq_modByMonic _ _ hh]
  exact (Polynomial.modByMonic_eq_self_iff ((monic_toPoly_iff h).mp hh)).mpr
    (degree_remainder_lt h p hh)

/-- Execute canonical monic reduction. -/
def reduce (h : CPolynomial R) (hh : h.monic) (p : CPolynomial R) : Representative h :=
  ⟨p.modByMonic h, remainder_idempotent h p hh⟩

/-- Execute addition and canonical reduction. -/
def add (h : CPolynomial R) (hh : h.monic) (p q : Representative h) : Representative h :=
  reduce h hh (p.val + q.val)

/-- Execute multiplication and canonical reduction. -/
def mul (h : CPolynomial R) (hh : h.monic) (p q : Representative h) : Representative h :=
  reduce h hh (p.val * q.val)

/-- Execute negation and canonical reduction. -/
def neg (h : CPolynomial R) (hh : h.monic) (p : Representative h) : Representative h :=
  reduce h hh (-p.val)

/-- The semantic quotient is used only to state refinement. -/
abbrev QuotientAlgebra (h : CPolynomial R) := Polynomial R ⧸ Ideal.span {h.toPoly}

/-- Interpret a stored polynomial in the semantic quotient. -/
noncomputable def quotientHom (h : CPolynomial R) : CPolynomial R →+* QuotientAlgebra h :=
  (Ideal.Quotient.mk (Ideal.span {h.toPoly})).comp
    (CPolynomial.ringEquiv : CPolynomial R ≃+* Polynomial R).toRingHom

@[simp] theorem quotientHom_apply (h p : CPolynomial R) :
    quotientHom h p = Ideal.Quotient.mk (Ideal.span {h.toPoly}) p.toPoly := by
  simp [quotientHom, CPolynomial.ringEquiv_apply]

/-- Reducing stored coefficients preserves the quotient element. -/
@[simp] theorem quotientHom_reduce (h p : CPolynomial R) (hh : h.monic) :
    quotientHom h (reduce h hh p).val = quotientHom h p := by
  rw [quotientHom_apply, quotientHom_apply]
  change Ideal.Quotient.mk _ (p.modByMonic h).toPoly = _
  rw [modByMonic_toPoly_eq_modByMonic _ _ hh, Ideal.Quotient.eq]
  have heq : p.toPoly %ₘ h.toPoly - p.toPoly = -(h.toPoly * (p.toPoly /ₘ h.toPoly)) := by
    rw [Polynomial.modByMonic_eq_sub_mul_div]
    ring
  rw [heq]
  exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- Stored addition refines addition in the monic quotient. -/
theorem quotientHom_add (h : CPolynomial R) (hh : h.monic) (p q : Representative h) :
    quotientHom h (add h hh p q).val = quotientHom h p.val + quotientHom h q.val := by
  rw [add, quotientHom_reduce, map_add]

/-- Stored multiplication refines multiplication in the monic quotient. -/
theorem quotientHom_mul (h : CPolynomial R) (hh : h.monic) (p q : Representative h) :
    quotientHom h (mul h hh p q).val = quotientHom h p.val * quotientHom h q.val := by
  rw [mul, quotientHom_reduce, map_mul]

/-- Stored negation refines negation in the monic quotient. -/
theorem quotientHom_neg (h : CPolynomial R) (hh : h.monic) (p : Representative h) :
    quotientHom h (neg h hh p).val = -quotientHom h p.val := by
  rw [neg, quotientHom_reduce, map_neg]

/-- Every returned canonical representative satisfies the strict degree bound. -/
theorem degree_representative_lt (h : CPolynomial R) (hh : h.monic) (p : Representative h) :
    p.val.toPoly.degree < h.toPoly.degree := by
  rw [← p.property]
  exact degree_remainder_lt h p.val hh

variable {S : Type*} [CommRing S] [BEq S] [LawfulBEq S]

/-- Apply a coefficient homomorphism directly to the stored array, then trim. -/
def mapCoefficients (f : R →+* S) (p : CPolynomial R) : CPolynomial S :=
  CPolynomial.ofArray (p.val.map f)

omit [Nontrivial R] in
/-- The executed array map is exactly semantic polynomial base change. -/
theorem toPoly_mapCoefficients (f : R →+* S) (p : CPolynomial R) :
    (mapCoefficients f p).toPoly = p.toPoly.map f := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly]
  change (CPolynomial.ofArray (p.val.map f)).coeff i = f (p.coeff i)
  rw [CPolynomial.coeff_ofArray]
  change (p.val.map f).getD i 0 = f (p.val.getD i 0)
  simp only [Array.getD, Array.size_map]
  split_ifs <;> simp

omit [Nontrivial R] in
/-- Monicity survives coefficient specialization, even into a nonreduced ring. -/
theorem monic_mapCoefficients (f : R →+* S) (h : CPolynomial R) (hh : h.monic) :
    (mapCoefficients f h).monic := by
  rw [monic_toPoly_iff, toPoly_mapCoefficients]
  exact ((monic_toPoly_iff h).mp hh).map f

/-- Monic reduction commutes with constant-fiber specialization or any coefficient homomorphism. -/
theorem mapCoefficients_remainder [Nontrivial S] (f : R →+* S)
    (h p : CPolynomial R) (hh : h.monic) :
    mapCoefficients f (p.modByMonic h) =
      (mapCoefficients f p).modByMonic (mapCoefficients f h) := by
  apply toPoly_injective
  rw [toPoly_mapCoefficients, modByMonic_toPoly_eq_modByMonic _ _ hh,
    Polynomial.map_modByMonic f ((monic_toPoly_iff h).mp hh),
    modByMonic_toPoly_eq_modByMonic _ _ (monic_mapCoefficients f h hh),
    toPoly_mapCoefficients, toPoly_mapCoefficients]

end ArkLib.ConfluentAlgebra
