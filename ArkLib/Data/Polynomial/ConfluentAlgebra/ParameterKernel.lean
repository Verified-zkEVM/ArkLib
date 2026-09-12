/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.Structure
public import ArkLib.Data.MvPolynomial.BoxAlgebraNilpotence
public import ArkLib.Data.Polynomial.NilpotentInverse
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# The whole parameter kernel in a confluent monic quotient

Coefficient specialization of canonical representatives has exactly the extended coefficient
kernel. Consequently the whole parameter kernel, not just the individual parameters, has
exponent `r * (N - 1) + 1`. No field structure or squarefree constant fiber is required.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra

open CompPoly CompPoly.CPolynomial

variable {R S : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]
variable [CommRing S] [BEq S] [LawfulBEq S] [Nontrivial S]
variable (h : CPolynomial R) [Fact h.monic]

/-- The canonical zero representative stores the zero polynomial. -/
@[simp] theorem zero_val : (0 : Representative h).val = 0 := by
  apply toPoly_injective
  change (CPolynomial.modByMonic 0 h).toPoly = (0 : CPolynomial R).toPoly
  rw [modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_zero,
    Polynomial.zero_modByMonic]

/-- Specialization of a reduced constant agrees with mapping the coefficient first. -/
@[simp] theorem coefficientMapHom_constantHom (f : R →+* S) (a : R) :
    coefficientMapHom h f (constantHom h a) = constantHom (mapCoefficients f h) (f a) := by
  change coefficientMapHom h f (reductionHom h (CPolynomial.C a)) =
    reductionHom (mapCoefficients f h) (CPolynomial.C (f a))
  rw [coefficientMapHom_reductionHom]
  congr 1
  apply toPoly_injective
  rw [toPoly_mapCoefficients, C_toPoly, C_toPoly, Polynomial.map_C]

/-- A specialized zero representative has every coefficient in the coefficient-map kernel. -/
theorem coeff_mem_ker_of_coefficientMapHom_eq_zero (f : R →+* S) (p : Representative h)
    (hp : coefficientMapHom h f p = 0) (i : ℕ) : p.val.toPoly.coeff i ∈ RingHom.ker f := by
  have hv := congrArg (fun q : Representative (mapCoefficients f h) => q.val) hp
  change mapCoefficients f p.val = (0 : Representative (mapCoefficients f h)).val at hv
  rw [zero_val] at hv
  have hc := congrArg (fun q : CPolynomial S => q.toPoly.coeff i) hv
  rw [toPoly_mapCoefficients, toPoly_zero, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
  exact hc

/-- The kernel on a monic quotient is precisely the ideal extended from the coefficient kernel. -/
theorem ker_coefficientMapHom (f : R →+* S) :
    RingHom.ker (coefficientMapHom h f) = Ideal.map (constantHom h) (RingHom.ker f) := by
  apply le_antisymm
  · intro p hp
    let lift : Polynomial R →+* Representative h :=
      (reductionHom h).comp CPolynomial.ringEquiv.symm.toRingHom
    have hlift (q : CPolynomial R) : lift q.toPoly = reductionHom h q := by
      change reductionHom h (CPolynomial.ringEquiv.symm q.toPoly) = _
      congr 1
      rw [← CPolynomial.ringEquiv_apply, RingEquiv.symm_apply_apply]
    have hC : lift.comp Polynomial.C = constantHom h := by
      apply RingHom.ext
      intro a
      change lift (Polynomial.C a) = reductionHom h (CPolynomial.C a)
      rw [← C_toPoly, hlift]
    have hc : p.val.toPoly ∈ Ideal.map Polynomial.C (RingHom.ker f) :=
      Ideal.mem_map_C_iff.mpr (coeff_mem_ker_of_coefficientMapHom_eq_zero h f p hp)
    have hm := Ideal.mem_map_of_mem lift hc
    rw [Ideal.map_map, hC, hlift, reductionHom_val] at hm
    exact hm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change coefficientMapHom h f (constantHom h a) = 0
    rw [coefficientMapHom_constantHom, show f a = 0 from ha, map_zero]

/-- Nilpotence of an entire coefficient kernel transfers with the same exponent. -/
theorem coefficientMapHom_ker_pow (f : R →+* S) (k : ℕ)
    (hk : RingHom.ker f ^ k = ⊥) : RingHom.ker (coefficientMapHom h f) ^ k = ⊥ := by
  rw [ker_coefficientMapHom, ← Ideal.map_pow, hk, Ideal.map_bot]

section ParameterBox

variable {r N : ℕ} [Fact (0 < N)]
variable (g : CPolynomial (CPoly.BoxAlgebra.Carrier r N R)) [Fact g.monic]

/-- The whole constant-fiber specialization kernel in the confluent algebra is nilpotent. -/
theorem parameterSpecialization_ker_pow :
    RingHom.ker (coefficientMapHom g (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))) ^
      (r * (N - 1) + 1) = ⊥ := by
  apply coefficientMapHom_ker_pow
  exact CPoly.BoxAlgebra.constantSpecialization_ker_pow Fact.out

/-- Any quotient residual with zero constant fiber satisfies the uniform parameter bound. -/
theorem pow_eq_zero_of_parameterSpecialization_eq_zero (p : Representative g)
    (hp : coefficientMapHom g (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) p = 0) :
    p ^ (r * (N - 1) + 1) = 0 :=
  Ideal.pow_eq_zero_of_mem (parameterSpecialization_ker_pow g) le_rfl hp

/-- A product that specializes to one has a uniformly nilpotent multiplicative residual. -/
theorem residual_pow_eq_zero_of_specialized_mul_eq_one (a b : Representative g)
    (hab : coefficientMapHom g (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      (a * b) = 1) : (1 - a * b) ^ (r * (N - 1) + 1) = 0 := by
  apply pow_eq_zero_of_parameterSpecialization_eq_zero g
  rw [map_sub, map_one, hab, sub_self]

/-- Finite geometric correction lifts a supplied constant-fiber inverse to a two-sided inverse. -/
theorem corrected_inverse_of_specialized_mul_eq_one (a b : Representative g)
    (hab : coefficientMapHom g (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      (a * b) = 1) :
    a * Polynomial.NilpotentInverse.correct (r * (N - 1) + 1) a b = 1 ∧
      Polynomial.NilpotentInverse.correct (r * (N - 1) + 1) a b * a = 1 := by
  have he := residual_pow_eq_zero_of_specialized_mul_eq_one g a b hab
  exact ⟨Polynomial.NilpotentInverse.right_inverse _ a b he,
    Polynomial.NilpotentInverse.left_inverse _ a b he⟩

end ParameterBox

end ArkLib.ConfluentAlgebra
