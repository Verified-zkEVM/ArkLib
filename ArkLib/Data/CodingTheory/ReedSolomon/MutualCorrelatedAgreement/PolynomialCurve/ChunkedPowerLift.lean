/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Degree
/-!
# Chunked coefficient lifts for polynomial curves

A coefficient monomial `Z^e` of degree at most `M*D` is represented using the degree-`D`
moment coordinates as `X_D^(e / D) * X_(e % D)`.  Thus its lifted degree is at most `M+1`,
while evaluation through the moment map is still exactly `Z^e`.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative

variable {F : Type*} [Field F]

/-- Chunk a coefficient polynomial of degree at most `M*D` into degree-`D` moment
coordinates.  The coordinate `0` maps to one, so the same formula also covers zero remainder. -/
def chunkedCoefficientPowerLift {σ : Type*} (D M : ℕ) (hD : 0 < D) (p : F[X])
    (_hp : p.natDegree ≤ M * D) : MvPolynomial (PowerLiftIndex D σ) F :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    MvPolynomial.C (p.coeff j) *
      MvPolynomial.X (Sum.inl ⟨D, Nat.lt_succ_self D⟩) ^ (j / D) *
      MvPolynomial.X (Sum.inl ⟨j % D, (Nat.mod_lt j hD).trans_le (Nat.le_succ D)⟩)

/-- Chunking is exact under the moment substitution. -/
theorem powerMomentMap_chunkedCoefficientPowerLift {σ : Type*} (D M : ℕ) (hD : 0 < D)
    (p : F[X]) (hp : p.natDegree ≤ M * D) :
    powerMomentMap D (chunkedCoefficientPowerLift (σ := σ) D M hD p hp) =
      Polynomial.aeval (MvPolynomial.X none : MvPolynomial (Option σ) F) p := by
  classical
  rw [chunkedCoefficientPowerLift, map_sum]
  simp only [map_mul, map_pow, powerMomentMap, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Sum.elim_inl]
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← pow_mul, mul_assoc, ← pow_add]
  have he : D * (j / D) + j % D = j := by
    simpa only [Nat.add_comm] using (Nat.mod_add_div j D)
  rw [he]
  simp only [MvPolynomial.algebraMap_eq]

/-- Chunk every challenge coefficient of a joint challenge/jet polynomial. -/
def chunkedPolynomialPowerLift {σ : Type*} (D M : ℕ) (hD : 0 < D)
    (P : MvPolynomial σ F[X]) (hP : ChallengeHeightLE P (M * D)) :
    MvPolynomial (PowerLiftIndex D σ) F :=
  ∑ m ∈ P.support,
    chunkedCoefficientPowerLift D M hD (MvPolynomial.coeff m P) (hP m) *
      ∏ i ∈ m.support, MvPolynomial.X (Sum.inr i) ^ m i

/-- Chunked coefficient linearization recovers the ordinary challenge flattening exactly. -/
theorem powerMomentMap_chunkedPolynomialPowerLift {σ : Type*} (D M : ℕ) (hD : 0 < D)
    (P : MvPolynomial σ F[X]) (hP : ChallengeHeightLE P (M * D)) :
    powerMomentMap D (chunkedPolynomialPowerLift D M hD P hP) = flattenChallenge P := by
  classical
  rw [chunkedPolynomialPowerLift, map_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, monomial_eq, map_mul, Finsupp.prod, map_prod, map_pow,
    flattenChallenge_C, flattenChallenge_X]
  apply Finset.sum_congr rfl
  intro m hm
  change powerMomentMap D
      (chunkedCoefficientPowerLift D M hD (MvPolynomial.coeff m P) (hP m)) * _ = _
  rw [powerMomentMap_chunkedCoefficientPowerLift]
  simp [powerMomentMap]

/-- A coefficient of challenge degree at most `M*D` has chunked lift degree at most `M+1`. -/
theorem chunkedCoefficientPowerLift_totalDegree_le {σ : Type*} (D M : ℕ) (hD : 0 < D)
    (p : F[X]) (hp : p.natDegree ≤ M * D) :
    (chunkedCoefficientPowerLift (σ := σ) D M hD p hp).totalDegree ≤ M + 1 := by
  classical
  rw [chunkedCoefficientPowerLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  apply (Nat.add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow,
    MvPolynomial.totalDegree_X, zero_add, add_le_add_iff_right]
  have hjdeg : j ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hjMD : j ≤ M * D := hjdeg.trans hp
  have hq : j / D ≤ M := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hjMD)
  omega

/-- A joint polynomial of jet degree at most `B` and challenge height at most `M*D` has
chunked lifted total degree at most `B + M + 1`. -/
theorem chunkedPolynomialPowerLift_totalDegree_le {σ : Type*} (D M B : ℕ) (hD : 0 < D)
    (P : MvPolynomial σ F[X]) (hP : ChallengeHeightLE P (M * D))
    (hdeg : P.totalDegree ≤ B) :
    (chunkedPolynomialPowerLift D M hD P hP).totalDegree ≤ B + M + 1 := by
  classical
  rw [chunkedPolynomialPowerLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hc := chunkedCoefficientPowerLift_totalDegree_le (σ := σ) D M hD
    (MvPolynomial.coeff m P) (hP m)
  have hj : (∏ i ∈ m.support,
      (MvPolynomial.X (Sum.inr i) : MvPolynomial (PowerLiftIndex D σ) F) ^ m i).totalDegree ≤
      m.sum fun _ e ↦ e := by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    simp [Finsupp.sum, MvPolynomial.totalDegree_X_pow]
  exact (Nat.add_le_add hc (hj.trans (MvPolynomial.le_totalDegree hm))).trans (by omega)

end ReedSolomon
