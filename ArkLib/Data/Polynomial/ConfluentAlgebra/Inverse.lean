/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ConfluentAlgebra.ParameterKernel
public import ArkLib.Data.Polynomial.ModularInverse
public import ArkLib.Data.Polynomial.NewtonInverse

/-!
# Computed inversion in the confluent monic algebra

Compute a Bézout inverse in the constant fiber, lift its stored coefficients to constant
parameter polynomials, and execute Newton inverse doubling through the whole parameter kernel.
The fiber may have repeated roots; only coprimality of the input with its equation is required.
-/

@[expose] public section

namespace ArkLib.ConfluentAlgebra

open CompPoly CompPoly.CPolynomial

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable {r N : ℕ} [Fact (0 < N)]

/-- Map coefficients to executable sparse constant parameter polynomials. -/
def parameterConstantHom : E →+* CPoly.BoxAlgebra.Carrier r N E where
  toFun a := CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C a)
  map_one' := by
    change CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C 1) = CPoly.BoxAlgebra.reduce 1
    apply congrArg CPoly.BoxAlgebra.reduce
    apply CPoly.eq_iff_fromCMvPolynomial.mpr
    simp [CPoly.CMvPolynomial.fromCMvPolynomial_C, CPoly.map_one]
  map_zero' := by
    change CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C 0) = CPoly.BoxAlgebra.reduce 0
    apply congrArg CPoly.BoxAlgebra.reduce
    apply CPoly.eq_iff_fromCMvPolynomial.mpr
    simp [CPoly.CMvPolynomial.fromCMvPolynomial_C, CPoly.map_zero]
  map_add' a b := by
    change CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C (a + b)) =
      CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C a) +
        CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C b)
    rw [← CPoly.BoxAlgebra.reduce_add]
    apply congrArg CPoly.BoxAlgebra.reduce
    apply CPoly.eq_iff_fromCMvPolynomial.mpr
    simp [CPoly.CMvPolynomial.fromCMvPolynomial_C, CPoly.map_add]
  map_mul' a b := by
    change CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C (a * b)) =
      CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C a) *
        CPoly.BoxAlgebra.reduce (CPoly.CMvPolynomial.C b)
    rw [← CPoly.BoxAlgebra.reduce_mul]
    apply congrArg CPoly.BoxAlgebra.reduce
    apply CPoly.eq_iff_fromCMvPolynomial.mpr
    simp [CPoly.CMvPolynomial.fromCMvPolynomial_C, CPoly.map_mul]

/-- Constant parameter embedding is a section of zero-parameter specialization. -/
@[simp] theorem constantSpecialization_parameterConstantHom (a : E) :
    CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)
      (parameterConstantHom (r := r) (N := N) a) = a := by
  change MvPolynomial.coeff 0 (CPoly.fromCMvPolynomial
    (CPoly.BoxTruncation.truncate N (CPoly.CMvPolynomial.C a : CPoly.CMvPolynomial r E))) = a
  rw [CPoly.BoxTruncation.coeff_semantics]
  simp [Fact.out, CPoly.CMvPolynomial.fromCMvPolynomial_C]

/-- Lifting and then specializing a stored coefficient array is exactly the identity. -/
theorem mapCoefficients_constant_roundtrip (p : CPolynomial E) :
    mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      (mapCoefficients (parameterConstantHom (r := r) (N := N)) p) = p := by
  apply toPoly_injective
  rw [toPoly_mapCoefficients, toPoly_mapCoefficients, Polynomial.map_map]
  have hc : (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)).comp
      (parameterConstantHom (r := r) (N := N) (E := E)) = RingHom.id E := by
    ext a
    exact constantSpecialization_parameterConstantHom a
  rw [hc, Polynomial.map_id]

variable (h : CPolynomial (CPoly.BoxAlgebra.Carrier r N E)) [Fact h.monic]

/-- Lift a computed constant-fiber polynomial and reduce it in the original monic equation. -/
def liftFiberPolynomial (p : CPolynomial E) : Representative h :=
  reductionHom h (mapCoefficients parameterConstantHom p)

/-- The lifted polynomial represents its original value in the constant fiber. -/
theorem specialize_liftFiberPolynomial (p : CPolynomial E) :
    coefficientMapHom h (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      (liftFiberPolynomial h p) =
    reductionHom
      (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) h) p := by
  rw [liftFiberPolynomial, coefficientMapHom_reductionHom, mapCoefficients_constant_roundtrip]

/-- Compute the constant-fiber Bézout inverse, then lift it by actual Newton doubling. -/
def inverse? (a : Representative h) : Option (Representative h) :=
  (CPolynomial.inverseMod?
    (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) a.val)
    (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) h)).map
      (fun b => Polynomial.NewtonInverse.correct (r * (N - 1) + 1) a (liftFiberPolynomial h b))

/-- A computed fiber Bézout coefficient lifts to an approximation with exact fiber product. -/
theorem specialized_mul_liftFiberPolynomial (a : Representative h) (b : CPolynomial E)
    (hb : CPolynomial.inverseMod?
      (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) a.val)
      (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) h) = some b) :
    coefficientMapHom h (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N))
      (a * liftFiberPolynomial h b) = 1 := by
  let f := CPoly.BoxAlgebra.constantSpecialization (r := r) (R := E) (Fact.out : 0 < N)
  let h₀ := mapCoefficients f h
  have he : (mapCoefficients f a.val * b).modByMonic h₀ = (1 : CPolynomial E).modByMonic h₀ :=
    CPolynomial.inverseMod?_mul_modByMonic (monic_mapCoefficients f h Fact.out) hb
  have hred : reductionHom h₀ (mapCoefficients f a.val * b) = 1 := Subtype.ext he
  rw [map_mul, specialize_liftFiberPolynomial]
  change coefficientMapHom h f a * reductionHom h₀ b = 1
  have ha : coefficientMapHom h f a = reductionHom h₀ (mapCoefficients f a.val) := by
    simpa only [reductionHom_val] using (coefficientMapHom_reductionHom h f a.val)
  rw [ha, ← map_mul]
  exact hred

/-- Every successful output is a two-sided inverse in the original nonreduced quotient. -/
theorem inverse?_sound (a b : Representative h) (hb : inverse? h a = some b) :
    a * b = 1 ∧ b * a = 1 := by
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.mp hb
  have he := residual_pow_eq_zero_of_specialized_mul_eq_one h a (liftFiberPolynomial h b₀)
    (specialized_mul_liftFiberPolynomial h a b₀ hb₀)
  exact ⟨Polynomial.NewtonInverse.right_inverse _ a _ he,
    Polynomial.NewtonInverse.left_inverse _ a _ he⟩

/-- Success is equivalent to constant-fiber coprimality with the equation. -/
theorem inverse?_exists_iff_coprime (a : Representative h) :
    (∃ b, inverse? h a = some b) ↔
      IsCoprime
        (mapCoefficients (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) a.val).toPoly
        (mapCoefficients
          (CPoly.BoxAlgebra.constantSpecialization (Fact.out : 0 < N)) h).toPoly := by
  rw [← CPolynomial.inverseMod_exists_iff_coprime]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨b₀, hb₀, _⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨b₀, hb₀⟩
  · rintro ⟨b₀, hb₀⟩
    exact ⟨_, Option.map_eq_some_iff.mpr ⟨b₀, hb₀, rfl⟩⟩

/-- An actual quotient inverse forces the computed constant-fiber gcd guard to succeed. -/
theorem inverse?_exists_of_mul_eq_one (a b : Representative h) (hab : a * b = 1) :
    ∃ c, inverse? h a = some c := by
  apply (inverse?_exists_iff_coprime h a).mpr
  let f := CPoly.BoxAlgebra.constantSpecialization (r := r) (R := E) (Fact.out : 0 < N)
  let h₀ := mapCoefficients f h
  let a₀ := mapCoefficients f a.val
  let b₀ := mapCoefficients f b.val
  have hs : coefficientMapHom h f a * coefficientMapHom h f b = 1 := by
    rw [← map_mul, hab, map_one]
  have hi := congrArg (interpret h₀) hs
  rw [interpret_mul, interpret_one] at hi
  change quotientHom h₀ a₀ * quotientHom h₀ b₀ = 1 at hi
  have hq : quotientHom h₀ (a₀ * b₀) = quotientHom h₀ 1 := by
    rw [map_mul, map_one]
    exact hi
  rw [quotientHom_apply, quotientHom_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton, toPoly_mul, toPoly_one] at hq
  obtain ⟨q, hq⟩ := hq
  refine ⟨b₀.toPoly, -q, ?_⟩
  change b₀.toPoly * a₀.toPoly + -q * h₀.toPoly = 1
  calc
    b₀.toPoly * a₀.toPoly + -q * h₀.toPoly = a₀.toPoly * b₀.toPoly - h₀.toPoly * q := by ring
    _ = 1 := by
      rw [show a₀.toPoly * b₀.toPoly = h₀.toPoly * q + 1 from (sub_eq_iff_eq_add).mp hq]
      ring

/-- Success is equivalent to existence of an inverse in the original confluent algebra. -/
theorem inverse?_exists_iff_exists_inverse (a : Representative h) :
    (∃ b, inverse? h a = some b) ↔ ∃ b, a * b = 1 := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (inverse?_sound h a b hb).1⟩
  · rintro ⟨b, hab⟩
    exact inverse?_exists_of_mul_eq_one h a b hab

/-- A rejected input has no multiplicative inverse; failure is not a missing-backend result. -/
theorem inverse?_eq_none_iff (a : Representative h) :
    inverse? h a = none ↔ ¬ ∃ b, a * b = 1 := by
  rw [← inverse?_exists_iff_exists_inverse]
  cases inverse? h a <;> simp

end ArkLib.ConfluentAlgebra
