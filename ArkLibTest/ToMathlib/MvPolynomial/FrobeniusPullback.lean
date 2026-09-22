/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for the inverse Frobenius coefficient twist

The examples cover:

* the identity `(X 0 + X 1) ^ 2 = X 0 ^ 2 + X 1 ^ 2` in characteristic two, computed by
  `inverseFrobeniusTwist_pow`;
* the three-variable split `G̃(T, W, U) ^ s = F(T ^ s, W ^ s, U)` for `F(X, Z, Y) = G(X, Z, Y ^ s)`,
  in polynomial and coordinate form, derived from the complementary-exponent statements;
* root transport for the nonconstant polynomial `X 0 + X 1 - X 2` at `(t, w, t + w)`;
* a characteristic-two coefficient computation separating the twist from the identity and from
  forward Frobenius, with its partial derivative;
* injectivity of the coefficient map is needed in `degreeOf_map_of_injective`;
* injectivity and surjectivity of `x ↦ x ^ p ^ e` on a perfect field, from Mathlib.
-/

open MvPolynomial

section ThreeVariables

variable {K : Type*} [Field K] (p e : ℕ) [ExpChar K p] [PerfectField K]

/-- Exponent `s` on the last variable `Y = X 2` and `1` on the base variables `X 0`, `X 1`. -/
private abbrev lastExponent (s : ℕ) (i : Fin 3) : ℕ := if i = 2 then s else 1

/-- Exponent `s` on the base variables `X 0`, `X 1` and `1` on the last variable. -/
private abbrev baseExponent (s : ℕ) (i : Fin 3) : ℕ := if i = 2 then 1 else s

private theorem baseExponent_mul_lastExponent (s : ℕ) (i : Fin 3) :
    baseExponent s i * lastExponent s i = s := by
  fin_cases i <;> simp

/-- The three-variable split: if `F(X, Z, Y) = G(X, Z, Y ^ s)` with `s = p ^ e`, then
`G̃ ^ s = F(X ^ s, Z ^ s, Y)`. -/
example (F G : MvPolynomial (Fin 3) K)
    (hF : F = variablePowerSubstitution (lastExponent (p ^ e)) G) :
    inverseFrobeniusTwist p e G ^ p ^ e =
      variablePowerSubstitution (baseExponent (p ^ e)) F :=
  inverseFrobeniusTwist_pow_eq_variablePowerSubstitution p e
    (baseExponent_mul_lastExponent _) hF

/-- The coordinate form: if `F(X, Z, Y) = G(X, Z, Y ^ s)` and `F(T ^ s, W ^ s, U) = 0`, then the
twist of `G` vanishes at `(T, W, U)`. -/
example (F G : MvPolynomial (Fin 3) K)
    (hF : F = variablePowerSubstitution (lastExponent (p ^ e)) G) (t w u : K)
    (hroot : eval ![t ^ p ^ e, w ^ p ^ e, u] F = 0) :
    eval ![t, w, u] (inverseFrobeniusTwist p e G) = 0 := by
  apply eval_inverseFrobeniusTwist_eq_zero_of_variablePowerSubstitution p e
    (baseExponent_mul_lastExponent _) hF
  have hpoint : (fun i ↦ ![t, w, u] i ^ baseExponent (p ^ e) i) = ![t ^ p ^ e, w ^ p ^ e, u] := by
    funext i
    fin_cases i <;> simp
  rw [hpoint]
  exact hroot

/-- The twist of `X 0 + X 1 - X 2` vanishes at `(t, w, t + w)`, since `x ↦ x ^ p ^ e` is
additive. -/
example (t w : K) :
    eval ![t, w, t + w]
      (inverseFrobeniusTwist p e (X 0 + X 1 - X 2 : MvPolynomial (Fin 3) K)) = 0 := by
  apply eval_inverseFrobeniusTwist_eq_zero
  simp [add_pow_expChar_pow]

/-- `x ↦ x ^ p ^ e` is injective on a perfect field. -/
example : Function.Injective (fun x : K ↦ x ^ p ^ e) :=
  (iterateFrobeniusEquiv K p e).injective

/-- Every element of a perfect field has a unique `p ^ e`-th root. -/
example (z : K) : ∃! w : K, w ^ p ^ e = z :=
  (iterateFrobeniusEquiv K p e).bijective.existsUnique z

end ThreeVariables

section CharacteristicTwo

variable {L : Type*} [Field L] [CharP L 2] [PerfectField L]

/-- In characteristic two, `inverseFrobeniusTwist_pow` computes
`(X 0 + X 1) ^ 2 = X 0 ^ 2 + X 1 ^ 2`. -/
example : (X 0 + X 1 : MvPolynomial (Fin 2) L) ^ 2 = X 0 ^ 2 + X 1 ^ 2 := by
  have h := inverseFrobeniusTwist_pow 2 1 (X 0 + X 1 : MvPolynomial (Fin 2) L)
  simpa only [inverseFrobeniusTwist, map_add, map_X, pow_one, expand_X] using h

omit [PerfectField L] in
/-- If `a ^ 3 + a + 1 = 0` in characteristic two, then `(a ^ 2 + a) ^ 2 = a`. -/
private theorem sq_sq_add_self_of_cubic {a : L} (ha : a ^ 3 + a + 1 = 0) :
    (a ^ 2 + a) ^ 2 = a := by
  have hcubic : a ^ 3 = a + 1 := by
    apply sub_eq_zero.mp
    rw [CharTwo.sub_eq_add]
    simpa only [add_assoc] using ha
  have hfour : a ^ 4 = a ^ 2 + a := by
    calc
      a ^ 4 = a * a ^ 3 := by ring
      _ = a * (a + 1) := by rw [hcubic]
      _ = a ^ 2 + a := by ring
  calc
    (a ^ 2 + a) ^ 2 = (a ^ 2) ^ 2 + a ^ 2 := by rw [CharTwo.add_sq]
    _ = a ^ 4 + a ^ 2 := by rw [← pow_mul]
    _ = (a ^ 2 + a) + a ^ 2 := by rw [hfour]
    _ = (a ^ 2 + a ^ 2) + a := by ac_rfl
    _ = a := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- In characteristic two, for a root `a` of `a ^ 3 + a + 1`, the twist sends the coefficient
`a` to `a ^ 2 + a`, which differs from `a` (identity) and from `a ^ 2` (forward Frobenius). -/
example (a : L) (ha : a ^ 3 + a + 1 = 0) :
    inverseFrobeniusTwist 2 1 (C a * X 0 + X 1 : MvPolynomial (Fin 2) L) =
        C (a ^ 2 + a) * X 0 + X 1 ∧ a ^ 2 + a ≠ a ∧ a ^ 2 + a ≠ a ^ 2 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hcoeff : (frobeniusEquiv L 2).symm a = a ^ 2 + a := by
    apply (frobeniusEquiv L 2).injective
    rw [RingEquiv.apply_symm_apply, coe_frobeniusEquiv, frobenius_def,
      sq_sq_add_self_of_cubic ha]
  refine ⟨by simp [inverseFrobeniusTwist, hcoeff], fun h ↦ ?_, fun h ↦ ha0 ?_⟩
  · have : a ^ 2 = 0 := by simpa using h
    exact ha0 (pow_eq_zero_iff two_ne_zero |>.mp this)
  · simpa using h

/-- The partial derivative in `X 0` of the twisted polynomial is the nonzero constant
`a ^ 2 + a`. -/
example (a : L) (ha : a ^ 3 + a + 1 = 0) :
    pderiv 0 (inverseFrobeniusTwist 2 1 (C a * X 0 + X 1 : MvPolynomial (Fin 2) L)) ≠ 0 := by
  rw [pderiv_inverseFrobeniusTwist_ne_zero_iff]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  simpa using ha0

end CharacteristicTwo

/-- Injectivity is needed in `degreeOf_map_of_injective`: reducing `2 * X 0` from `ℤ` to
`ZMod 2` lowers its degree in `X 0` from `1` to `0`. -/
example :
    degreeOf 0 (map (Int.castRingHom (ZMod 2)) (C 2 * X 0 : MvPolynomial (Fin 1) ℤ)) = 0 ∧
      degreeOf 0 (C 2 * X 0 : MvPolynomial (Fin 1) ℤ) = 1 := by
  constructor
  · have : map (Int.castRingHom (ZMod 2)) (C 2 * X 0 : MvPolynomial (Fin 1) ℤ) = 0 := by
      rw [map_mul, map_C, map_X, show Int.castRingHom (ZMod 2) 2 = 0 from rfl, C_0, zero_mul]
    rw [this, degreeOf_zero]
  · rw [degreeOf_C_mul _ _ (mem_nonZeroDivisors_of_ne_zero two_ne_zero), degreeOf_X_self]
