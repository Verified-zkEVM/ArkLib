/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.LinearCapture
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart
/-!
# Algebraic differentials of the regular Taylor chart

This file defines the characteristic-free formal differential of a multivariate polynomial and
the quotient differential used by the rational Taylor chart. Initial Taylor coordinates are the
input jet coordinates, so their quotient differentials are literal coordinate projections. The
initial hypersurface differential is nonzero at every point where the separant is nonzero.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SquareSystems

open MvPolynomial
open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- The formal differential of a multivariate polynomial at a point. -/
noncomputable def mvPolynomialDifferential (point : ι → F) (p : MvPolynomial ι F) :
    (ι → F) →ₗ[F] F where
  toFun direction :=
    ∑ i, direction i * aeval point (pderiv i p)
  map_add' direction direction' := by
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' scalar direction := by
    simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
@[simp]
theorem mvPolynomialDifferential_X (point : ι → F) (i : ι) :
    mvPolynomialDifferential point (X i) = LinearMap.proj i := by
  classical
  apply LinearMap.ext
  intro direction
  change (∑ j, direction j * aeval point (pderiv j (X i))) = direction i
  simp [pderiv_X, Pi.single_apply]

/-- Evaluating the differential on a coordinate direction extracts the corresponding partial
derivative. -/
theorem mvPolynomialDifferential_single_one (point : ι → F) (p : MvPolynomial ι F) (i : ι) :
    mvPolynomialDifferential point p (Pi.single i 1) = aeval point (pderiv i p) := by
  classical
  change (∑ j, (Pi.single i (1 : F) : ι → F) j * aeval point (pderiv j p)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

omit [DecidableEq ι] in
/-- Product rule for the formal multivariate differential. -/
theorem mvPolynomialDifferential_mul (point : ι → F) (p q : MvPolynomial ι F) :
    mvPolynomialDifferential point (p * q) =
      aeval point q • mvPolynomialDifferential point p +
        aeval point p • mvPolynomialDifferential point q := by
  classical
  apply LinearMap.ext
  intro direction
  change (∑ i, direction i * aeval point (pderiv i (p * q))) =
    aeval point q * (∑ i, direction i * aeval point (pderiv i p)) +
      aeval point p * (∑ i, direction i * aeval point (pderiv i q))
  simp_rw [pderiv_mul, map_add, map_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
@[simp]
theorem mvPolynomialDifferential_C (point : ι → F) (a : F) :
    mvPolynomialDifferential point (C a) = 0 := by
  classical
  apply LinearMap.ext
  intro direction
  simp [mvPolynomialDifferential]

omit [DecidableEq ι] in
@[simp]
theorem mvPolynomialDifferential_zero (point : ι → F) :
    mvPolynomialDifferential point 0 = 0 := by
  classical
  apply LinearMap.ext
  intro direction
  simp [mvPolynomialDifferential]

omit [DecidableEq ι] in
@[simp]
theorem mvPolynomialDifferential_add (point : ι → F) (p q : MvPolynomial ι F) :
    mvPolynomialDifferential point (p + q) =
      mvPolynomialDifferential point p + mvPolynomialDifferential point q := by
  classical
  apply LinearMap.ext
  intro direction
  simp [mvPolynomialDifferential, Finset.sum_add_distrib, mul_add]

omit [DecidableEq ι] in
@[simp]
theorem mvPolynomialDifferential_sub (point : ι → F) (p q : MvPolynomial ι F) :
    mvPolynomialDifferential point (p - q) =
      mvPolynomialDifferential point p - mvPolynomialDifferential point q := by
  classical
  apply LinearMap.ext
  intro direction
  simp [mvPolynomialDifferential, Finset.sum_sub_distrib, mul_sub]

/-- Formal quotient rule, defined wherever the denominator value is nonzero. -/
noncomputable def quotientDifferential (point : ι → F)
    (numerator denominator : MvPolynomial ι F) :
    (ι → F) →ₗ[F] F :=
  (aeval point denominator) ⁻¹ • mvPolynomialDifferential point numerator -
    (aeval point numerator * ((aeval point denominator) ^ 2) ⁻¹) •
      mvPolynomialDifferential point denominator

omit [DecidableEq ι] in
@[simp]
theorem quotientDifferential_add (point : ι → F) (p q denominator : MvPolynomial ι F) :
    quotientDifferential point (p + q) denominator =
      quotientDifferential point p denominator + quotientDifferential point q denominator := by
  apply LinearMap.ext
  intro direction
  simp only [quotientDifferential, map_add, mvPolynomialDifferential_add,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
@[simp]
theorem quotientDifferential_sub (point : ι → F) (p q denominator : MvPolynomial ι F) :
    quotientDifferential point (p - q) denominator =
      quotientDifferential point p denominator - quotientDifferential point q denominator := by
  apply LinearMap.ext
  intro direction
  simp only [quotientDifferential, map_sub, mvPolynomialDifferential_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem quotientDifferential_C_mul (point : ι → F) (a : F)
    (p denominator : MvPolynomial ι F) :
    quotientDifferential point (C a * p) denominator =
      a • quotientDifferential point p denominator := by
  apply LinearMap.ext
  intro direction
  rw [quotientDifferential, quotientDifferential, mvPolynomialDifferential_mul]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    mvPolynomialDifferential_C, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, mul_zero, LinearMap.sub_apply, smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem quotientDifferential_self (point : ι → F) (denominator : MvPolynomial ι F)
    (hdenominator : aeval point denominator ≠ 0) :
    quotientDifferential point denominator denominator = 0 := by
  apply LinearMap.ext
  intro direction
  simp only [quotientDifferential, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.zero_apply, smul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
@[simp]
theorem quotientDifferential_zero (point : ι → F) (denominator : MvPolynomial ι F) :
    quotientDifferential point 0 denominator = 0 := by
  apply LinearMap.ext
  intro direction
  simp [quotientDifferential]

omit [DecidableEq ι] in
theorem quotientDifferential_finsetSum {J : Type*} (point : ι → F)
    (denominator : MvPolynomial ι F) (s : Finset J) (p : J → MvPolynomial ι F) :
    quotientDifferential point (∑ j ∈ s, p j) denominator =
      ∑ j ∈ s, quotientDifferential point (p j) denominator := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [hj, ih]

omit [DecidableEq ι] in
/-- The quotient differential of `X_i * denominator` by a nonzero denominator is projection to
coordinate `i`. -/
theorem quotientDifferential_X_mul (point : ι → F) (i : ι)
    (denominator : MvPolynomial ι F) (hdenominator : aeval point denominator ≠ 0) :
    quotientDifferential point (X i * denominator) denominator = LinearMap.proj i := by
  rw [quotientDifferential, mvPolynomialDifferential_mul, mvPolynomialDifferential_X]
  apply LinearMap.ext
  intro direction
  simp only [map_mul, aeval_X, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
/-- At a zero of the numerator, clearing a nonzero denominator scales the quotient differential
by the denominator value. -/
theorem mvPolynomialDifferential_eq_smul_quotientDifferential (point : ι → F)
    (numerator denominator : MvPolynomial ι F)
    (hdenominator : aeval point denominator ≠ 0) (hnumerator : aeval point numerator = 0) :
    mvPolynomialDifferential point numerator =
      aeval point denominator • quotientDifferential point numerator denominator := by
  apply LinearMap.ext
  intro direction
  simp only [quotientDifferential, LinearMap.smul_apply, hnumerator, zero_mul, zero_smul,
    sub_zero, smul_eq_mul]
  field_simp

variable {r : ℕ}

/-- Differential of the initial Taylor hypersurface at a jet. -/
noncomputable def initialJetDifferential (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) : (Fin (r + 1) → F) →ₗ[F] F :=
  mvPolynomialDifferential jet (initialJetEquation center Q)

/-- A nonzero separant value makes the initial hypersurface differential nonzero. -/
theorem initialJetDifferential_ne_zero (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0) :
    initialJetDifferential center Q jet ≠ 0 := by
  intro hzero
  have hvalue := LinearMap.congr_fun hzero (Pi.single (Fin.last r) 1)
  have hderivative :
      (initialJetDifferential center Q jet) (Pi.single (Fin.last r) 1) =
        aeval jet (initialJetSeparant center Q) := by
    rw [initialJetDifferential,
      mvPolynomialDifferential_single_one (i := Fin.last r),
      pderiv_initialJetEquation]
    rfl
  rw [hderivative] at hvalue
  simp only [LinearMap.zero_apply] at hvalue
  exact hseparant hvalue

/-- Differential of the common-denominator rational Taylor coefficient map. Every coordinate is
the quotient differential of its literal common numerator by the common separant power. -/
noncomputable def rationalTaylorMapDifferential (center : F) (Q : DifferentialPolynomial F r)
    (K τ : ℕ) (jet : Fin (r + 1) → F) :
    (Fin (r + 1) → F) →ₗ[F] (Fin K → F) :=
  LinearMap.pi fun l ↦
    quotientDifferential jet (commonTaylorNumerator center Q K l (τ := τ))
      (initialJetSeparant center Q ^ τ)

/-- A cleared agreement row has the same quotient differential as evaluation of the rational
Taylor coefficient differential. -/
theorem quotientDifferential_taylorAgreementEquation (center : F)
    (Q : DifferentialPolynomial F r) (K τ : ℕ) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    quotientDifferential jet (taylorAgreementEquation center Q K x y (τ := τ))
        (initialJetSeparant center Q ^ τ) =
      ∑ l : Fin K, (x - center) ^ l.val •
        quotientDifferential jet (commonTaylorNumerator center Q K l (τ := τ))
          (initialJetSeparant center Q ^ τ) := by
  rw [taylorAgreementEquation, quotientDifferential_sub,
    quotientDifferential_finsetSum]
  simp_rw [quotientDifferential_C_mul]
  rw [quotientDifferential_self]
  · simp
  · simp only [map_pow]
    exact pow_ne_zero _ hseparant

/-- The differential of every initial Taylor coefficient is its input-coordinate projection. -/
theorem rationalTaylorMapDifferential_initial (center : F) (Q : DifferentialPolynomial F r)
    (K τ : ℕ) (hK : r < K) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0)
    (direction : Fin (r + 1) → F) (j : Fin (r + 1)) :
    rationalTaylorMapDifferential center Q K τ jet direction ⟨j, by omega⟩ = direction j := by
  let l : Fin K := ⟨j, by omega⟩
  let denominator : MvPolynomial (Fin (r + 1)) F := initialJetSeparant center Q ^ τ
  have hdenominator : aeval jet denominator ≠ 0 := by
    simp only [denominator, map_pow]
    exact pow_ne_zero _ hseparant
  have hjle : j.val ≤ r := Nat.lt_succ_iff.mp j.isLt
  have hsub : l.val - r = 0 := by
    apply Nat.sub_eq_zero_of_le
    simpa only [l] using hjle
  have hnumerator : commonTaylorNumerator center Q K l (τ := τ) =
      X j * denominator := by
    rw [commonTaylorNumerator, rationalTaylorNumerator]
    rw [dif_pos (show l.val < r + 1 by simpa only [l] using j.isLt)]
    simp only [hsub, mul_zero, Nat.zero_sub, Nat.sub_zero, denominator, l]
  change quotientDifferential jet (commonTaylorNumerator center Q K l (τ := τ))
      denominator direction = direction j
  rw [hnumerator, quotientDifferential_X_mul jet j denominator hdenominator]
  rfl

/-- Retaining the initial jet coordinates makes the rational Taylor coefficient differential
injective, independently of the later recursively constructed coordinates. -/
theorem rationalTaylorMapDifferential_injective (center : F) (Q : DifferentialPolynomial F r)
    (K τ : ℕ) (hK : r < K) (jet : Fin (r + 1) → F)
    (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0) :
    Function.Injective (rationalTaylorMapDifferential center Q K τ jet) := by
  intro direction direction' hdirection
  funext j
  have hj := congrFun hdirection (⟨j, by omega⟩ : Fin K)
  rw [rationalTaylorMapDifferential_initial center Q K τ hK jet hseparant,
    rationalTaylorMapDifferential_initial center Q K τ hK jet hseparant] at hj
  exact hj

/-- At a regular chart point, some `r` evaluation-or-tail quotient differentials combine with the
initial equation differential into an injective square map. -/
theorem exists_regularChart_squareRows (center : F) (Q : DifferentialPolynomial F r)
    (K k τ : ℕ) (hK : r < K) (hk : k ≤ K) (points : Fin k ↪ F)
    (jet : Fin (r + 1) → F) (hseparant : aeval jet (initialJetSeparant center Q) ≠ 0) :
    ∃ selected : Fin r ↪ (Fin k ⊕ Fin (K - k)),
      Function.Injective
        (normalSelectedMap (initialJetDifferential center Q jet)
          ((evaluationTailPoolMap K k hk center points).comp
            (rationalTaylorMapDifferential center Q K τ jet)) selected) := by
  apply exists_evaluationTail_squareRows hk center points
    (initialJetDifferential center Q jet)
    (rationalTaylorMapDifferential center Q K τ jet)
  · rw [Module.finrank_pi]
    simp
  · exact initialJetDifferential_ne_zero center Q jet hseparant
  · intro x y hxy
    exact Subtype.ext
      (rationalTaylorMapDifferential_injective center Q K τ hK jet hseparant hxy)

end ReedSolomon.HiddenDerivative.SquareSystems
