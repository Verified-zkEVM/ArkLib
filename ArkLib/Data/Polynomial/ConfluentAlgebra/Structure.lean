/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.MonicArithmetic
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Executable ring structure on monic quotient representatives

The ring operations reduce CompPoly polynomials and retain canonical stored representatives.
The semantic quotient is used only to prove the ring laws. A unit modulus is supported and
produces the zero ring; nontriviality is a separate consequence of positive modulus degree.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
variable (h : CPolynomial R) [Fact h.monic]

instance : BEq (Representative h) := ⟨fun p q => p.val == q.val⟩

instance : LawfulBEq (Representative h) where
  eq_of_beq he := Subtype.ext (eq_of_beq he)
  rfl := by intro p; exact beq_self_eq_true p.val

instance : DecidableEq (Representative h) := instDecidableEqOfLawfulBEq

/-- Interpret a canonical stored representative in the semantic quotient. -/
noncomputable def interpret (p : Representative h) : QuotientAlgebra h := quotientHom h p.val

/-- Canonical stored representatives are distinguished by their semantic quotient elements. -/
theorem interpret_injective : Function.Injective (interpret h) := by
  intro p q he
  apply Subtype.ext
  apply toPoly_injective
  change quotientHom h p.val = quotientHom h q.val at he
  rw [quotientHom_apply, quotientHom_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at he
  have hm := Polynomial.modByMonic_eq_of_dvd_sub
    ((monic_toPoly_iff h).mp Fact.out) he
  rw [← modByMonic_toPoly_eq_modByMonic _ _ Fact.out,
    ← modByMonic_toPoly_eq_modByMonic _ _ Fact.out, p.property, q.property] at hm
  exact hm

@[simp] theorem interpret_reduce (p : CPolynomial R) :
    interpret h (reduce h Fact.out p) = quotientHom h p := quotientHom_reduce h p Fact.out

/-- Every semantic quotient element has an executable canonical representative. -/
theorem interpret_surjective : Function.Surjective (interpret h) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨reduce h Fact.out (CPolynomial.ringEquiv.symm p), ?_⟩
  rw [interpret_reduce, quotientHom_apply]
  congr 1
  simpa only [CPolynomial.ringEquiv_apply] using CPolynomial.ringEquiv.apply_symm_apply p

instance : Zero (Representative h) := ⟨reduce h Fact.out 0⟩
instance : One (Representative h) := ⟨reduce h Fact.out 1⟩
instance : Add (Representative h) := ⟨add h Fact.out⟩
instance : Mul (Representative h) := ⟨mul h Fact.out⟩
instance : Neg (Representative h) := ⟨neg h Fact.out⟩
instance : Sub (Representative h) := ⟨fun p q => reduce h Fact.out (p.val - q.val)⟩
instance : NatCast (Representative h) := ⟨fun n => reduce h Fact.out n⟩
instance : IntCast (Representative h) := ⟨fun n => reduce h Fact.out n⟩
instance : SMul ℕ (Representative h) := ⟨fun n p => reduce h Fact.out (n • p.val)⟩
instance : SMul ℤ (Representative h) := ⟨fun n p => reduce h Fact.out (n • p.val)⟩
instance : Pow (Representative h) ℕ := ⟨fun p n => reduce h Fact.out (p.val ^ n)⟩

@[simp] theorem interpret_zero : interpret h 0 = 0 := by
  change interpret h (reduce h Fact.out 0) = 0
  rw [interpret_reduce, map_zero]

@[simp] theorem interpret_one : interpret h 1 = 1 := by
  change interpret h (reduce h Fact.out 1) = 1
  rw [interpret_reduce, map_one]

@[simp] theorem interpret_add (p q : Representative h) :
    interpret h (p + q) = interpret h p + interpret h q := quotientHom_add h Fact.out p q

@[simp] theorem interpret_mul (p q : Representative h) :
    interpret h (p * q) = interpret h p * interpret h q := quotientHom_mul h Fact.out p q

@[simp] theorem interpret_neg (p : Representative h) :
    interpret h (-p) = -interpret h p := quotientHom_neg h Fact.out p

@[simp] theorem interpret_sub (p q : Representative h) :
    interpret h (p - q) = interpret h p - interpret h q := by
  change interpret h (reduce h Fact.out (p.val - q.val)) = _
  rw [interpret_reduce, map_sub]
  rfl

@[simp] theorem interpret_nsmul (n : ℕ) (p : Representative h) :
    interpret h (n • p) = n • interpret h p := by
  change interpret h (reduce h Fact.out (n • p.val)) = _
  rw [interpret_reduce, map_nsmul]
  rfl

@[simp] theorem interpret_zsmul (n : ℤ) (p : Representative h) :
    interpret h (n • p) = n • interpret h p := by
  change interpret h (reduce h Fact.out (n • p.val)) = _
  rw [interpret_reduce, map_zsmul]
  rfl

@[simp] theorem interpret_pow (p : Representative h) (n : ℕ) :
    interpret h (p ^ n) = interpret h p ^ n := by
  change interpret h (reduce h Fact.out (p.val ^ n)) = _
  rw [interpret_reduce, map_pow]
  rfl

@[simp] theorem interpret_natCast (n : ℕ) : interpret h n = n := by
  change interpret h (reduce h Fact.out n) = n
  rw [interpret_reduce, map_natCast]

@[simp] theorem interpret_intCast (n : ℤ) : interpret h n = n := by
  change interpret h (reduce h Fact.out n) = n
  rw [interpret_reduce, map_intCast]

/-- Every canonical representative is obtained by reducing its stored polynomial. -/
theorem reduce_surjective : Function.Surjective (reduce h Fact.out) := by
  intro p
  refine ⟨p.val, Subtype.ext p.property⟩

instance : CommRing (Representative h) :=
  (reduce_surjective h).commRing (reduce h Fact.out) rfl rfl
    (fun p q => interpret_injective h (by simp only [interpret_reduce, interpret_add, map_add]))
    (fun p q => interpret_injective h (by simp only [interpret_reduce, interpret_mul, map_mul]))
    (fun p => interpret_injective h (by simp only [interpret_reduce, interpret_neg, map_neg]))
    (fun p q => interpret_injective h (by simp only [interpret_reduce, interpret_sub, map_sub]))
    (fun n p => interpret_injective h (by simp only [interpret_reduce, interpret_nsmul, map_nsmul]))
    (fun n p => interpret_injective h (by simp only [interpret_reduce, interpret_zsmul, map_zsmul]))
    (fun p n => interpret_injective h (by simp only [interpret_reduce, interpret_pow, map_pow]))
    (fun _ => rfl) (fun _ => rfl)

/-- The semantic interpretation is a ring equivalence; its inverse is proof-facing only. -/
noncomputable def quotientEquiv : Representative h ≃+* QuotientAlgebra h :=
  RingEquiv.ofBijective
    { toFun := interpret h
      map_one' := interpret_one h
      map_mul' := interpret_mul h
      map_zero' := interpret_zero h
      map_add' := interpret_add h : Representative h →+* QuotientAlgebra h }
    ⟨interpret_injective h, interpret_surjective h⟩

/-- Executable reduction is the quotient projection as a ring homomorphism. -/
def reductionHom : CPolynomial R →+* Representative h where
  toFun := reduce h Fact.out
  map_one' := rfl
  map_zero' := rfl
  map_add' p q := by
    apply interpret_injective h
    simp only [interpret_reduce, interpret_add, map_add]
  map_mul' p q := by
    apply interpret_injective h
    simp only [interpret_reduce, interpret_mul, map_mul]

/-- Reducing a canonical representative returns that same stored representative. -/
@[simp] theorem reductionHom_val (p : Representative h) : reductionHom h p.val = p := by
  apply Subtype.ext
  exact p.property

/-- Map coefficients computationally to reduced constant polynomials. -/
def constantHom : R →+* Representative h := (reductionHom h).comp CPolynomial.CHom

/-- The executable reduction homomorphism is surjective. -/
theorem reductionHom_surjective : Function.Surjective (reductionHom h) :=
  fun p => ⟨p.val, reductionHom_val h p⟩

/-- The equation itself vanishes under the executable quotient projection. -/
@[simp] theorem reductionHom_modulus : reductionHom h h = 0 := by
  apply interpret_injective h
  change interpret h (reduce h Fact.out h) = interpret h 0
  rw [interpret_reduce, interpret_zero, quotientHom_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- A unit equation produces the zero ring, rather than an artificial nontrivial instance. -/
theorem subsingleton_of_isUnit (hh : IsUnit h) : Subsingleton (Representative h) := by
  have hu := hh.map (reductionHom h)
  rw [reductionHom_modulus] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

/-- Positive equation degree preserves nontriviality of the coefficient ring. -/
theorem nontrivial_of_degree_pos (hh : 0 < h.toPoly.degree) : Nontrivial (Representative h) := by
  apply nontrivial_of_ne (0 : Representative h) 1
  intro he
  have hp := congrArg (fun p : Representative h => p.val.toPoly) he
  change (CPolynomial.modByMonic 0 h).toPoly = (CPolynomial.modByMonic 1 h).toPoly at hp
  rw [modByMonic_toPoly_eq_modByMonic _ _ Fact.out,
    modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_zero, toPoly_one,
    Polynomial.zero_modByMonic] at hp
  have hone : (1 : Polynomial R) %ₘ h.toPoly = 1 :=
    (Polynomial.modByMonic_eq_self_iff ((monic_toPoly_iff h).mp Fact.out)).mpr
      (by simpa only [Polynomial.degree_one] using hh)
  exact zero_ne_one (hp.trans hone)

instance [Fact (0 < h.toPoly.degree)] : Nontrivial (Representative h) :=
  nontrivial_of_degree_pos h Fact.out

variable {S : Type*} [CommRing S] [BEq S] [LawfulBEq S] [Nontrivial S]

/-- Executable coefficient base change is a ring homomorphism on stored polynomials. -/
def mapCoefficientsHom (f : R →+* S) : CPolynomial R →+* CPolynomial S where
  toFun := mapCoefficients f
  map_one' := by
    apply toPoly_injective
    rw [toPoly_mapCoefficients, toPoly_one, toPoly_one, Polynomial.map_one]
  map_zero' := by
    apply toPoly_injective
    rw [toPoly_mapCoefficients, toPoly_zero, toPoly_zero, Polynomial.map_zero]
  map_add' p q := by
    apply toPoly_injective
    rw [toPoly_mapCoefficients, toPoly_add, toPoly_add, Polynomial.map_add,
      toPoly_mapCoefficients, toPoly_mapCoefficients]
  map_mul' p q := by
    apply toPoly_injective
    rw [toPoly_mapCoefficients, toPoly_mul, toPoly_mul, Polynomial.map_mul,
      toPoly_mapCoefficients, toPoly_mapCoefficients]

instance (f : R →+* S) : Fact (mapCoefficients f h).monic :=
  ⟨monic_mapCoefficients f h (Fact.out : h.monic)⟩

/-- Base change preserves the stored canonical remainder invariant. -/
def mapRepresentative (f : R →+* S) (p : Representative h) :
    Representative (mapCoefficients f h) :=
  ⟨mapCoefficients f p.val, by rw [← mapCoefficients_remainder f h p.val Fact.out, p.property]⟩

/-- Executable coefficient specialization descends to the monic quotient rings. -/
def coefficientMapHom (f : R →+* S) :
    Representative h →+* Representative (mapCoefficients f h) where
  toFun := mapRepresentative h f
  map_one' := by
    apply Subtype.ext
    change mapCoefficients f (CPolynomial.modByMonic 1 h) =
      CPolynomial.modByMonic 1 (mapCoefficients f h)
    rw [mapCoefficients_remainder f h _ Fact.out]
    congr 1
    exact (mapCoefficientsHom f).map_one
  map_zero' := by
    apply Subtype.ext
    change mapCoefficients f (CPolynomial.modByMonic 0 h) =
      CPolynomial.modByMonic 0 (mapCoefficients f h)
    rw [mapCoefficients_remainder f h _ Fact.out]
    congr 1
    exact (mapCoefficientsHom f).map_zero
  map_add' p q := by
    apply Subtype.ext
    change mapCoefficients f ((p.val + q.val).modByMonic h) =
      (mapCoefficients f p.val + mapCoefficients f q.val).modByMonic (mapCoefficients f h)
    rw [mapCoefficients_remainder f h _ Fact.out]
    congr 1
    exact (mapCoefficientsHom f).map_add _ _
  map_mul' p q := by
    apply Subtype.ext
    change mapCoefficients f ((p.val * q.val).modByMonic h) =
      (mapCoefficients f p.val * mapCoefficients f q.val).modByMonic (mapCoefficients f h)
    rw [mapCoefficients_remainder f h _ Fact.out]
    congr 1
    exact (mapCoefficientsHom f).map_mul _ _

/-- Specializing a quotient element agrees with specializing and then reducing its input. -/
@[simp] theorem coefficientMapHom_reductionHom (f : R →+* S) (p : CPolynomial R) :
    coefficientMapHom h f (reductionHom h p) =
      reductionHom (mapCoefficients f h) (mapCoefficients f p) := by
  apply Subtype.ext
  exact mapCoefficients_remainder f h p Fact.out

end ArkLib.ConfluentAlgebra
