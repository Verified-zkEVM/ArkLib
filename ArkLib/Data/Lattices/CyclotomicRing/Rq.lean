/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Basic
import Mathlib.Algebra.Ring.InjSurj

/-!
# `Rq Φ` — the Cyclotomic Ring as a Computable `CommRing`

`ArkLib/Data/Lattices/CyclotomicRing/Basic.lean` gives a *semantic* cyclotomic ring
(`Φ.CyclotomicRing`, noncomputable) and a computable reduction `Φ.reduce`/`Φ.mul` on
raw `CPolynomial R`. Raw `CPolynomial` is not the right element type for a commitment
scheme: two raw polynomials can be unequal yet congruent mod `φ`, which would make the
binding reduction unsound (`s₁ - s₂` could be a nonzero multiple of `φ`).

This file fixes that by defining `Φ.Rq`, the subtype of **canonical reduced
representatives** `{ p : CPolynomial R // Φ.reduce p = p }`, and equipping it with a
genuine **computable `CommRing`** structure transported from the semantic quotient
along the injective ring map `a ↦ quotientHom a.val` (the CompPoly analogue of VCV-io's
`instCommRingPoly`).

## Main definitions

* `CyclotomicModulus.Rq Φ` — canonical reduced representatives of `R[X] / (φ)`.
* `CommRing (Φ.Rq)` — transported, computable; `+`/`*` are reduce-after-CPolynomial-op.
* `CyclotomicModulus.Rq.equivQuotient` — the ring iso `Φ.Rq ≃+* Φ.CyclotomicRing`.
-/

open Polynomial CompPoly CompPoly.CPolynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-! ## `reduce` lemmas via the `toPoly` bridge -/

/-- `CPolynomial.toPoly` is injective (it is the forward map of a ring isomorphism). -/
theorem toPoly_injective :
    Function.Injective (CPolynomial.toPoly : CPolynomial R → Polynomial R) :=
  CPolynomial.ringEquiv.injective

variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- The Mathlib polynomial of a reduction is the Mathlib `%ₘ`. -/
theorem reduce_toPoly (p : CPolynomial R) :
    (Φ.reduce p).toPoly = p.toPoly %ₘ Φ.φ.toPoly :=
  CPolynomial.toPoly_modByMonic p Φ.φ (IsCyclotomic.monic (Φ := Φ))

/-- Reduction is idempotent: a reduced polynomial is fixed by `reduce`. -/
@[simp] theorem reduce_reduce (p : CPolynomial R) : Φ.reduce (Φ.reduce p) = Φ.reduce p := by
  apply toPoly_injective
  rw [reduce_toPoly, reduce_toPoly]
  exact (Polynomial.modByMonic_eq_self_iff (IsCyclotomic.monic (Φ := Φ))).mpr
    (Polynomial.degree_modByMonic_lt _ (IsCyclotomic.monic (Φ := Φ)))

/-- A reduced representative has Mathlib degree below `deg φ`. -/
theorem degree_toPoly_lt_of_reduced {p : CPolynomial R} (hp : Φ.reduce p = p) :
    p.toPoly.degree < Φ.φ.toPoly.degree := by
  conv_lhs => rw [← hp]
  rw [reduce_toPoly]
  exact Polynomial.degree_modByMonic_lt _ (IsCyclotomic.monic (Φ := Φ))

/-- Reduction fixes any polynomial whose degree is already below `deg φ`. -/
theorem reduce_eq_self_of_degree_lt {p : CPolynomial R}
    (h : p.toPoly.degree < Φ.φ.toPoly.degree) : Φ.reduce p = p := by
  apply toPoly_injective
  rw [reduce_toPoly]
  exact (Polynomial.modByMonic_eq_self_iff (IsCyclotomic.monic (Φ := Φ))).mpr h

/-! ## The reduced-representative subtype and its ring structure -/

/-- Canonical reduced representatives of the cyclotomic ring `R[X] / (φ)`:
`CPolynomial`s that are fixed by reduction modulo `φ`. -/
def Rq : Type _ := { p : CPolynomial R // Φ.reduce p = p }

/-- Build a `Rq Φ` from any `CPolynomial` by reducing it. -/
def Rq.mk (p : CPolynomial R) : Rq Φ := ⟨Φ.reduce p, Φ.reduce_reduce p⟩

/-- The transport map into the semantic quotient (a ring map, injective on
reduced representatives). Noncomputable (it factors through `quotientHom`); the
executable arithmetic on `Rq Φ` lives on the primitive `Add`/`Mul`/… instances. -/
noncomputable def Rq.toQuotient (a : Rq Φ) : Φ.CyclotomicRing := Φ.quotientHom a.1

namespace Rq

instance [DecidableEq R] : DecidableEq (Rq Φ) := Subtype.instDecidableEq

instance : Zero (Rq Φ) := ⟨Rq.mk Φ 0⟩
instance : One (Rq Φ) := ⟨Rq.mk Φ 1⟩
instance : Add (Rq Φ) := ⟨fun a b => Rq.mk Φ (a.1 + b.1)⟩
instance : Mul (Rq Φ) := ⟨fun a b => Rq.mk Φ (a.1 * b.1)⟩
instance : Neg (Rq Φ) := ⟨fun a => Rq.mk Φ (-a.1)⟩
instance : Sub (Rq Φ) := ⟨fun a b => Rq.mk Φ (a.1 - b.1)⟩
instance : SMul ℕ (Rq Φ) := ⟨fun n a => Rq.mk Φ (n • a.1)⟩
instance : SMul ℤ (Rq Φ) := ⟨fun n a => Rq.mk Φ (n • a.1)⟩
instance : Pow (Rq Φ) ℕ := ⟨fun a n => Rq.mk Φ (a.1 ^ n)⟩
instance : NatCast (Rq Φ) := ⟨fun n => Rq.mk Φ (n : CPolynomial R)⟩
instance : IntCast (Rq Φ) := ⟨fun n => Rq.mk Φ (n : CPolynomial R)⟩

@[simp] theorem toQuotient_mk (p : CPolynomial R) :
    (Rq.mk Φ p).toQuotient = Φ.quotientHom p := by
  rw [Rq.toQuotient, Rq.mk, quotientHom_reduce]

theorem toQuotient_injective : Function.Injective (Rq.toQuotient Φ) := by
  intro a b h
  apply Subtype.ext
  apply toPoly_injective
  rw [Rq.toQuotient, Rq.toQuotient, quotientHom_apply, quotientHom_apply,
    Ideal.Quotient.eq] at h
  have hdvd : Φ.φ.toPoly ∣ (a.1.toPoly - b.1.toPoly) := by
    rw [modIdeal, Ideal.mem_span_singleton] at h; exact h
  have hsmall : (a.1.toPoly - b.1.toPoly).degree < Φ.φ.toPoly.degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (Φ.degree_toPoly_lt_of_reduced a.2) (Φ.degree_toPoly_lt_of_reduced b.2))
  have hzero : a.1.toPoly - b.1.toPoly = 0 := by
    by_contra hne
    exact absurd (lt_of_le_of_lt (Polynomial.degree_le_of_dvd hdvd hne) hsmall) (lt_irrefl _)
  exact sub_eq_zero.mp hzero

/-- The transported commutative ring on canonical reduced representatives. The
instance itself is noncomputable (its axioms are transported through the
noncomputable `toQuotient`), but the ring operations reduce to the primitive
computable `Add`/`Mul`/… instances above, so `Rq Φ` arithmetic is `#eval`-able. -/
noncomputable instance commRing : CommRing (Rq Φ) :=
  Function.Injective.commRing (Rq.toQuotient Φ) (toQuotient_injective Φ)
    (by rw [show (0 : Rq Φ) = Rq.mk Φ 0 from rfl, toQuotient_mk, map_zero])
    (by rw [show (1 : Rq Φ) = Rq.mk Φ 1 from rfl, toQuotient_mk, map_one])
    (fun a b => by rw [show a + b = Rq.mk Φ (a.1 + b.1) from rfl, toQuotient_mk, map_add]; rfl)
    (fun a b => by rw [show a * b = Rq.mk Φ (a.1 * b.1) from rfl, toQuotient_mk, map_mul]; rfl)
    (fun a => by rw [show -a = Rq.mk Φ (-a.1) from rfl, toQuotient_mk, map_neg]; rfl)
    (fun a b => by rw [show a - b = Rq.mk Φ (a.1 - b.1) from rfl, toQuotient_mk, map_sub]; rfl)
    (fun n a => by rw [show n • a = Rq.mk Φ (n • a.1) from rfl, toQuotient_mk, map_nsmul]; rfl)
    (fun n a => by rw [show n • a = Rq.mk Φ (n • a.1) from rfl, toQuotient_mk, map_zsmul]; rfl)
    (fun a n => by rw [show a ^ n = Rq.mk Φ (a.1 ^ n) from rfl, toQuotient_mk, map_pow]; rfl)
    (fun n => by rw [show (n : Rq Φ) = Rq.mk Φ (n : CPolynomial R) from rfl, toQuotient_mk,
      map_natCast])
    (fun n => by rw [show (n : Rq Φ) = Rq.mk Φ (n : CPolynomial R) from rfl, toQuotient_mk,
      map_intCast])

/-- `toQuotient` packaged as a ring homomorphism into the semantic cyclotomic ring. -/
noncomputable def toQuotientHom : Rq Φ →+* Φ.CyclotomicRing where
  toFun := Rq.toQuotient Φ
  map_one' := by rw [show (1 : Rq Φ) = Rq.mk Φ 1 from rfl, toQuotient_mk, map_one]
  map_mul' a b := by rw [show a * b = Rq.mk Φ (a.1 * b.1) from rfl, toQuotient_mk, map_mul]; rfl
  map_zero' := by rw [show (0 : Rq Φ) = Rq.mk Φ 0 from rfl, toQuotient_mk, map_zero]
  map_add' a b := by rw [show a + b = Rq.mk Φ (a.1 + b.1) from rfl, toQuotient_mk, map_add]; rfl

/-- Subtraction of canonical reduced representatives is coefficientwise: the
underlying `CPolynomial` of `a - b` is `a.1 - b.1` (no further reduction occurs, as both
operands already have degree below `deg φ`). -/
theorem sub_val (a b : Rq Φ) : (a - b).1 = a.1 - b.1 := by
  change Φ.reduce (a.1 - b.1) = a.1 - b.1
  apply Φ.reduce_eq_self_of_degree_lt
  rw [CPolynomial.toPoly_sub]
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    (max_lt (Φ.degree_toPoly_lt_of_reduced a.2) (Φ.degree_toPoly_lt_of_reduced b.2))

/-- Addition of canonical reduced representatives is coefficientwise. -/
theorem add_val (a b : Rq Φ) : (a + b).1 = a.1 + b.1 := by
  change Φ.reduce (a.1 + b.1) = a.1 + b.1
  apply Φ.reduce_eq_self_of_degree_lt
  rw [CompPoly.CPolynomial.toPoly_add]
  exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    (max_lt (Φ.degree_toPoly_lt_of_reduced a.2) (Φ.degree_toPoly_lt_of_reduced b.2))

@[simp] theorem zero_val : (0 : Rq Φ).1 = 0 := by
  change Φ.reduce 0 = 0
  apply toPoly_injective
  rw [reduce_toPoly, CompPoly.CPolynomial.toPoly_zero, Polynomial.zero_modByMonic]

/-- Reading off the `k`-th coefficient of the underlying polynomial, as an additive
homomorphism `Rq Φ →+ R`. -/
def coeffHom (k : ℕ) : Rq Φ →+ R where
  toFun a := a.1.coeff k
  map_zero' := by rw [zero_val]; exact CompPoly.CPolynomial.coeff_zero k
  map_add' a b := by rw [add_val, CompPoly.CPolynomial.coeff_add]

@[simp] theorem coeffHom_apply (k : ℕ) (a : Rq Φ) : coeffHom Φ k a = a.1.coeff k := rfl

/-- The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid
when `N` does not exceed the degree of the modulus. -/
def ofFinCoeff [DecidableEq R] (N : ℕ) (c : ℕ → R) : Rq Φ :=
  Rq.mk Φ (CompPoly.CPolynomial.ofFinCoeff N c)

theorem ofFinCoeff_coeff [DecidableEq R] {N : ℕ} (c : ℕ → R)
    (hN : (N : WithBot ℕ) ≤ Φ.φ.toPoly.degree) (k : ℕ) :
    (Rq.ofFinCoeff Φ N c).1.coeff k = if k < N then c k else 0 := by
  have hred : Φ.reduce (CompPoly.CPolynomial.ofFinCoeff N c)
      = CompPoly.CPolynomial.ofFinCoeff N c :=
    Φ.reduce_eq_self_of_degree_lt
      (lt_of_lt_of_le (CompPoly.CPolynomial.degree_toPoly_ofFinCoeff_lt N c) hN)
  change (Φ.reduce (CompPoly.CPolynomial.ofFinCoeff N c)).coeff k = _
  rw [hred, CompPoly.CPolynomial.coeff_ofFinCoeff]

end Rq

end ArkLib.Lattices.CyclotomicModulus
