/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Variables

/-!
# Structured hidden-derivative substitutions

This file separates the two algebraic changes of variables in the hidden-derivative argument.

First,

```text
X   = alpha + T,
Y₀  = y + T U,
Y_j = Y_j                         (1 ≤ j ≤ d).
```

Then

```text
U = E + sum_{j=1}^d (-1)^(j+1) T^(j-1) Y_j.
```

Their composition is the unscaled local substitution, in which `E` denotes the candidate-derived
backward Taylor error and occurs as `T E`.  The normalized substitution additionally sends
`E` to `T^d E`, so its free error occurs as `T^(d+1) E`.

The definitions rework the sound algebraic material from ArkLib commit `d3370654`, while exposing
the intermediate `U` map needed by the later local-rank factorization.  The global variables are
the donor-compatible `JetVariable` type; the old proof-hole-bearing merge stack is not imported.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Equations (14) and (25).
-/

noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d : ℕ}

/-- The visible-jet part of the auxiliary variable:
`sum_r (-1)^r T^r Y_(r+1)`. -/
def localJetSum (d : ℕ) : LocalPolynomial R d :=
  ∑ j : Fin d,
    C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j)

/-- The signed correction appearing directly in `Y₀`:
`sum_r (-1)^r T^(r+1) Y_(r+1)`. -/
def localCorrection (d : ℕ) : LocalPolynomial R d :=
  ∑ j : Fin d,
    C ((-1 : R) ^ j.val) * X (localT d) ^ (j.val + 1) * X (localY j)

/-- Multiplication by `T` converts the auxiliary-variable jet sum into the direct correction. -/
theorem T_mul_localJetSum (d : ℕ) :
    X (localT d) * localJetSum (R := R) d = localCorrection d := by
  rw [localJetSum, localCorrection, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- First local change of variables, introducing the auxiliary variable `U`. -/
def translateToU (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ fun
    | none => C center + X (localT d)
    | some j => Fin.cases
        (C received + X (localT d) * X (localU d))
        (fun highOrder => X (localY highOrder)) j

/-- Second local change of variables, rewriting `U` as a visible-jet sum plus the error `E`. -/
def rewriteUToE (d : ℕ) : LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ fun
    | none => X (localT d)
    | some none => X (localE d) + localJetSum d
    | some (some j) => X (localY j)

/-- Generator images for the complete unscaled local substitution. -/
def unscaledLocalImage (d : ℕ) (center received : R) :
    JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases
      (C received + localCorrection d + X (localT d) * X (localE d))
      (fun highOrder => X (localY highOrder)) j

/-- Complete unscaled local substitution.  Its error must later be specialized to a polynomial
divisible by `X^d`. -/
def unscaledLocalSubstitution (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (unscaledLocalImage d center received)

@[simp]
theorem unscaledLocalSubstitution_X (d : ℕ) (center received : R) :
    unscaledLocalSubstitution d center received (X none) =
      C center + X (localT d) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

@[simp]
theorem unscaledLocalSubstitution_Y_zero (d : ℕ) (center received : R) :
    unscaledLocalSubstitution d center received (X (some 0)) =
      C received + localCorrection d + X (localT d) * X (localE d) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

@[simp]
theorem unscaledLocalSubstitution_Y_succ (d : ℕ) (center received : R)
    (j : Fin d) :
    unscaledLocalSubstitution d center received (X (some j.succ)) = X (localY j) := by
  simp [unscaledLocalSubstitution, unscaledLocalImage]

/-- The direct unscaled substitution is exactly the composition of the two primitive changes of
variables. -/
theorem unscaledLocalSubstitution_eq_rewrite_comp_translate (d : ℕ)
    (center received : R) :
    unscaledLocalSubstitution d center received =
      (rewriteUToE d).comp (translateToU d center received) := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp [translateToU, rewriteUToE, localT]
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [unscaledLocalSubstitution_Y_zero, AlgHom.coe_comp,
        Function.comp_apply, translateToU, bind₁_X_right, Fin.cases_zero, map_add, map_mul,
        rewriteUToE, bind₁_C_right, localT, localU, localE, localAux]
      rw [mul_add]
      have hcorrection :
          X (none : LocalVariable d) * localJetSum (R := R) d =
            localCorrection (R := R) d := by
        simpa [localT] using T_mul_localJetSum (R := R) d
      rw [hcorrection]
      ring
    · simp [translateToU, rewriteUToE, localY]

/-- Rescale the error generator by `E ↦ T^d E`, fixing every other local generator. -/
def normalizeError (d : ℕ) : LocalPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ fun
    | none => X (localT d)
    | some none => X (localT d) ^ d * X (localE d)
    | some (some j) => X (localY j)

@[simp]
theorem normalizeError_T (d : ℕ) :
    normalizeError (R := R) d (X (localT d)) = X (localT d) := by
  simp [normalizeError, localT]

@[simp]
theorem normalizeError_E (d : ℕ) :
    normalizeError (R := R) d (X (localE d)) =
      X (localT d) ^ d * X (localE d) := by
  simp [normalizeError, localT, localE, localAux]

@[simp]
theorem normalizeError_Y (d : ℕ) (j : Fin d) :
    normalizeError (R := R) d (X (localY j)) = X (localY j) := by
  simp [normalizeError, localY]

@[simp]
theorem normalizeError_localCorrection (d : ℕ) :
    normalizeError (R := R) d (localCorrection d) = localCorrection d := by
  simp [localCorrection]

/-- Generator images for the normalized local substitution with a free error variable. -/
def normalizedLocalImage (d : ℕ) (center received : R) :
    JetVariable d → LocalPolynomial R d
  | none => C center + X (localT d)
  | some j => Fin.cases
      (C received + localCorrection d + X (localT d) ^ (d + 1) * X (localE d))
      (fun highOrder => X (localY highOrder)) j

/-- Normalized local substitution, where the free error occurs as `T^(d+1) E`. -/
def normalizedLocalSubstitution (d : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₐ[R] LocalPolynomial R d :=
  bind₁ (normalizedLocalImage d center received)

@[simp]
theorem normalizedLocalSubstitution_X (d : ℕ) (center received : R) :
    normalizedLocalSubstitution d center received (X none) =
      C center + X (localT d) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

@[simp]
theorem normalizedLocalSubstitution_Y_zero (d : ℕ) (center received : R) :
    normalizedLocalSubstitution d center received (X (some 0)) =
      C received + localCorrection d +
        X (localT d) ^ (d + 1) * X (localE d) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

@[simp]
theorem normalizedLocalSubstitution_Y_succ (d : ℕ) (center received : R)
    (j : Fin d) :
    normalizedLocalSubstitution d center received (X (some j.succ)) = X (localY j) := by
  simp [normalizedLocalSubstitution, normalizedLocalImage]

/-- Normalizing the error in the unscaled substitution gives the normalized substitution. -/
theorem normalizedLocalSubstitution_eq_normalize_comp_unscaled (d : ℕ)
    (center received : R) :
    normalizedLocalSubstitution d center received =
      (normalizeError d).comp (unscaledLocalSubstitution d center received) := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [normalizedLocalSubstitution_Y_zero, AlgHom.coe_comp, Function.comp_apply,
        unscaledLocalSubstitution_Y_zero, map_add, map_mul, algHom_C, algebraMap_eq,
        normalizeError_localCorrection, normalizeError_T, normalizeError_E, add_right_inj]
      rw [pow_succ]
      ring
    · simp

/-! ### Weighted substitution bounds -/

/-- The direct correction has contact weight at most `d`. -/
theorem localCorrection_mem_contactWeight (d : ℕ) :
    localCorrection (R := R) d ∈
      restrictWeightedDegree (R := R) (localContactWeight d) d := by
  apply Submodule.sum_mem
  intro j _
  apply restrictWeightedDegree_mono (d := j.val + 1)
  · omega
  have hpow := pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) (localContactWeight d) 1 (localT d) (by rfl))
    (j.val + 1)
  have hcoefficient := mul_mem_restrictWeightedDegree
    (C_mem_restrictWeightedDegree (R := R) (localContactWeight d) 0
      ((-1 : R) ^ j.val)) hpow
  simpa using mul_mem_restrictWeightedDegree hcoefficient
    (X_mem_restrictWeightedDegree (R := R) (localContactWeight d) 0 (localY j) (by rfl))

/-- The direct correction has `T`-degree at most `d`. -/
theorem localCorrection_mem_TWeight (d : ℕ) :
    localCorrection (R := R) d ∈
      restrictWeightedDegree (R := R) (localTWeight d) d := by
  apply Submodule.sum_mem
  intro j _
  apply restrictWeightedDegree_mono (d := j.val + 1)
  · omega
  have hpow := pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) (localTWeight d) 1 (localT d) (by rfl))
    (j.val + 1)
  have hcoefficient := mul_mem_restrictWeightedDegree
    (C_mem_restrictWeightedDegree (R := R) (localTWeight d) 0
      ((-1 : R) ^ j.val)) hpow
  simpa using mul_mem_restrictWeightedDegree hcoefficient
    (X_mem_restrictWeightedDegree (R := R) (localTWeight d) 0 (localY j) (by rfl))

/-- Every unscaled generator image meets its natural contact-weight cap. -/
theorem unscaledLocalImage_mem (d : ℕ) (center received : R) (v : JetVariable d) :
    unscaledLocalImage d center received v ∈
      restrictWeightedDegree (R := R) (localContactWeight d)
        (localSubstitutionSourceWeight d v) := by
  rcases v with _ | j
  · exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
      (X_mem_restrictWeightedDegree _ _ _ (by rfl))
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [unscaledLocalImage, localSubstitutionSourceWeight]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact C_mem_restrictWeightedDegree _ _ _
        · exact restrictWeightedDegree_mono _ (Nat.le_succ _)
            (localCorrection_mem_contactWeight d)
      · simpa [Nat.add_comm] using mul_mem_restrictWeightedDegree
          (X_mem_restrictWeightedDegree (R := R) (localContactWeight d) 1 (localT d)
            (by rfl))
          (X_mem_restrictWeightedDegree (R := R) (localContactWeight d) d (localE d)
            (by rfl))
    · exact X_mem_restrictWeightedDegree _ _ _ (by rfl)

/-- Every normalized generator image meets its natural `T`-degree cap. -/
theorem normalizedLocalImage_mem (d : ℕ) (center received : R) (v : JetVariable d) :
    normalizedLocalImage d center received v ∈
      restrictWeightedDegree (R := R) (localTWeight d)
        (localSubstitutionSourceWeight d v) := by
  rcases v with _ | j
  · exact Submodule.add_mem _ (C_mem_restrictWeightedDegree _ _ _)
      (X_mem_restrictWeightedDegree _ _ _ (by rfl))
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [normalizedLocalImage, localSubstitutionSourceWeight]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact C_mem_restrictWeightedDegree _ _ _
        · exact restrictWeightedDegree_mono _ (Nat.le_succ _)
            (localCorrection_mem_TWeight d)
      · simpa using mul_mem_restrictWeightedDegree
          (pow_mem_restrictWeightedDegree
            (X_mem_restrictWeightedDegree (R := R) (localTWeight d) 1 (localT d) (by rfl))
            (d + 1))
          (X_mem_restrictWeightedDegree (R := R) (localTWeight d) 0 (localE d) (by rfl))
    · exact X_mem_restrictWeightedDegree _ _ _ (by rfl)

/-- The unscaled substitution preserves bounds measured with its natural source and contact
weights. -/
theorem unscaledLocalSubstitution_mem {degreeCap : ℕ}
    {center received : R} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightedDegree (R := R)
      (localSubstitutionSourceWeight d) degreeCap) :
    unscaledLocalSubstitution d center received Q ∈
      restrictWeightedDegree (R := R) (localContactWeight d) degreeCap :=
  bind₁_mem_restrictWeightedDegree
    (unscaledLocalImage_mem d center received) hQ

/-- The normalized substitution preserves bounds measured with its natural source and `T`
weights. -/
theorem normalizedLocalSubstitution_mem {degreeCap : ℕ}
    {center received : R} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightedDegree (R := R)
      (localSubstitutionSourceWeight d) degreeCap) :
    normalizedLocalSubstitution d center received Q ∈
      restrictWeightedDegree (R := R) (localTWeight d) degreeCap :=
  bind₁_mem_restrictWeightedDegree
    (normalizedLocalImage_mem d center received) hQ

/-- If `d < D`, every natural local-substitution cap is bounded by the differential weight
formula `(1,D,D-1,...,D-d)`.  The strict inequality is load-bearing at `Y₀`: it is exactly
what gives `d+1 ≤ D`. -/
theorem localSubstitutionSourceWeight_le_differentialFormula {D : ℕ} (h : d < D)
    (v : JetVariable d) :
    localSubstitutionSourceWeight d v ≤
      match v with
      | none => 1
      | some j => D - j.val := by
  rcases v with _ | j
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [localSubstitutionSourceWeight_Y_zero, Fin.val_zero, Nat.sub_zero]
      omega
    · simp

/-- Under the explicit condition `d < D`, every unscaled generator image meets its ambient
differential-weight cap. -/
theorem unscaledLocalImage_mem_differentialFormula {D : ℕ} (h : d < D)
    (center received : R) (v : JetVariable d) :
    unscaledLocalImage d center received v ∈
      restrictWeightedDegree (R := R) (localContactWeight d)
        (match v with | none => 1 | some j => D - j.val) :=
  restrictWeightedDegree_mono _
    (localSubstitutionSourceWeight_le_differentialFormula h v)
    (unscaledLocalImage_mem d center received v)

/-- Under the explicit condition `d < D`, every normalized generator image meets its ambient
differential-weight cap. -/
theorem normalizedLocalImage_mem_differentialFormula {D : ℕ} (h : d < D)
    (center received : R) (v : JetVariable d) :
    normalizedLocalImage d center received v ∈
      restrictWeightedDegree (R := R) (localTWeight d)
        (match v with | none => 1 | some j => D - j.val) :=
  restrictWeightedDegree_mono _
    (localSubstitutionSourceWeight_le_differentialFormula h v)
    (normalizedLocalImage_mem d center received v)

/-- The unscaled substitution sends an ambient differential-weight bound to the same contact-
weight bound, provided the derivative order is strictly below the ambient degree. -/
theorem unscaledLocalSubstitution_mem_differentialFormula {D degreeCap : ℕ}
    (h : d < D) {center received : R} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightedDegree (R := R)
      (fun v ↦ match v with | none => 1 | some j => D - j.val) degreeCap) :
    unscaledLocalSubstitution d center received Q ∈
      restrictWeightedDegree (R := R) (localContactWeight d) degreeCap :=
  bind₁_mem_restrictWeightedDegree
    (unscaledLocalImage_mem_differentialFormula h center received) hQ

/-- The normalized substitution sends an ambient differential-weight bound to the same
`T`-degree bound, provided the derivative order is strictly below the ambient degree. -/
theorem normalizedLocalSubstitution_mem_differentialFormula {D degreeCap : ℕ}
    (h : d < D) {center received : R} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightedDegree (R := R)
      (fun v ↦ match v with | none => 1 | some j => D - j.val) degreeCap) :
    normalizedLocalSubstitution d center received Q ∈
      restrictWeightedDegree (R := R) (localTWeight d) degreeCap :=
  bind₁_mem_restrictWeightedDegree
    (normalizedLocalImage_mem_differentialFormula h center received) hQ

/-! ### Boundary canaries -/

/-- At the rejected boundary `D=d`, the top jet's differential weight truncates to zero while
the `Y₀` image needs the larger cap `d+1`. -/
theorem differentialFormula_truncation_boundary_canary :
    2 - (Fin.last 2).val = 0 ∧
      ¬localSubstitutionSourceWeight 2 (some 0) ≤ 2 - (0 : Fin 3).val := by
  decide

/-- At order two, this checks both alternating signs and the distinct error factors `T` and
`T³`. -/
theorem substitution_order_two_canary :
    let source : DifferentialPolynomial ℤ 2 :=
      X (some 0) * X (some (Fin.succ (1 : Fin 2)))
    let t : LocalPolynomial ℤ 2 := X (localT 2)
    let e : LocalPolynomial ℤ 2 := X (localE 2)
    let y₁ : LocalPolynomial ℤ 2 := X (localY (0 : Fin 2))
    let y₂ : LocalPolynomial ℤ 2 := X (localY (1 : Fin 2))
    unscaledLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t * e) * y₂ ∧
      normalizedLocalSubstitution 2 2 3 source =
        (C 3 + t * y₁ - t ^ 2 * y₂ + t ^ 3 * e) * y₂ := by
  dsimp only
  constructor
  · rw [map_mul, unscaledLocalSubstitution_Y_zero,
      unscaledLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring
  · rw [map_mul, normalizedLocalSubstitution_Y_zero,
      normalizedLocalSubstitution_Y_succ]
    simp [localCorrection, Fin.sum_univ_two]
    ring

end ReedSolomon.HiddenDerivative
