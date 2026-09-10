/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.Lifting
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ConcreteEquation
public import CompPoly.Multivariate.MvPolyEquiv.Eval
public import CompPoly.Univariate.ToPoly.Impl
-- The executable bridge reduces CompPoly coefficient and semantic-conversion definitions.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv
/-!
# Executable regular coefficient lifting

This file gives a computable version of one regular coefficient-lifting step. A candidate is
stored in coordinates centered at the lifting point, as a `CompPoly.CPolynomial`. The differential
equation is a `CPoly.CMvPolynomial` whose variables are ordered as `X, Y₀, ..., Y_r`. The step
enumerates only the finite base field and retains exactly the coefficients whose next differential
residual coefficient vanishes.

The semantic bridge maps the concrete representations to the shifted-jet presentation used by
`RegularLifting`. No polynomial equality or divisibility test occurs in the executable kernel.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential
open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Concrete representations -/

/-- Interpret a centered coefficient polynomial as an ordinary polynomial in the original
coordinate. -/
noncomputable def unshift (center : F) (P : CompPoly.CPolynomial F) : F[X] :=
  Polynomial.taylor (-center) P.toPoly

/-- The constant-polynomial embedding into computable univariate polynomials. -/
def cPolynomialCHom : F →+* CompPoly.CPolynomial F where
  toFun := CompPoly.CPolynomial.C
  map_one' := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_one]
  map_mul' a b := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_mul]
  map_zero' := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_zero]
  map_add' a b := by
    apply CompPoly.CPolynomial.ringEquiv.injective
    simp only [CompPoly.CPolynomial.ringEquiv_apply, CompPoly.CPolynomial.C_toPoly,
      map_add]

/-- Semantic ring homomorphism from computable to Mathlib polynomials. -/
noncomputable def cPolynomialToPolyHom : CompPoly.CPolynomial F →+* F[X] :=
  CompPoly.CPolynomial.ringEquiv.toRingHom

@[simp]
theorem cPolynomialToPolyHom_apply (P : CompPoly.CPolynomial F) :
    cPolynomialToPolyHom P = P.toPoly :=
  CompPoly.CPolynomial.ringEquiv_apply P

/-- Hasse derivative on a centered coefficient array. Keeping the source array length makes the
coefficient formula direct; `ofArray` removes the trailing zero coefficients. -/
def centeredHasseDeriv (j : ℕ) (P : CompPoly.CPolynomial F) :
    CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.ofArray <|
    Array.ofFn (n := P.val.size) fun i =>
      ((i.val + j).choose j : F) * P.coeff (i.val + j)

/-! ### Primitive arithmetic accounting for centered Hasse derivatives

The counted routine below expands each natural-number scalar as repeated addition of `1`,
then performs one field multiplication per source coefficient. Constants, coefficient access,
array allocation, natural-number arithmetic (including `choose`), and normalization are not field
operations. The visited-entry counter records the finite coefficient loop separately. These are
field-operation counts, not machine-time bounds. In particular this does not yet account for
`CMvPolynomial.eval₂`, polynomial arithmetic, equality filters, or the whole decoder.

This instrumentation has no independent operational-semantics adequacy bridge. Its result
refinement and counters are intermediate evidence, not a runtime certificate for the original
Hasse implementation or for a decoder. A closed execution semantics must account for the same
program before a runtime theorem can consume these results.
-/

/-- Evaluate a natural scalar by repeated field addition, counting the additions as they run. -/
def effectiveNatCast (F : Type*) [Field F] : ℕ → F × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      let previous := effectiveNatCast F n
      (previous.1 + 1, previous.2 + 1)

@[simp]
theorem effectiveNatCast_value {F : Type*} [Field F] (n : ℕ) :
    (effectiveNatCast F n).1 = (n : F) := by
  induction n with
  | zero => simp [effectiveNatCast]
  | succ n ih => simp [effectiveNatCast, ih, Nat.cast_add, Nat.cast_one]

@[simp]
theorem effectiveNatCast_additions {F : Type*} [Field F] (n : ℕ) :
    (effectiveNatCast F n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [effectiveNatCast, ih]

/-- Concrete Hasse execution output with separate arithmetic and coefficient-loop counts. -/
structure EffectiveHasseRun (F : Type*) [Zero F] where
  /-- The normalized derivative coefficient array. -/
  result : CompPoly.CPolynomial F
  /-- Number of additions executed in natural-scalar expansion. -/
  additions : ℕ
  /-- Number of coefficient multiplications executed. -/
  multiplications : ℕ
  /-- Number of source coefficient positions visited. -/
  visited : ℕ

/-- Instrumented implementation of the centered Hasse derivative. Every counted multiplication
is executed in the entry loop; every counted addition comes from `effectiveNatCast`. -/
def effectiveHasseRun (j : ℕ) (P : CompPoly.CPolynomial F) : EffectiveHasseRun F :=
  let entries := Array.ofFn (n := P.val.size) fun i =>
    let scalar := effectiveNatCast F ((i.val + j).choose j)
    (scalar.1 * P.coeff (i.val + j), scalar.2)
  ⟨CompPoly.CPolynomial.ofArray (entries.map Prod.fst),
    (entries.map Prod.snd).foldl (· + ·) 0, entries.size, entries.size⟩

/-- The counted arithmetic implementation computes the existing executable Hasse derivative. -/
@[simp]
theorem effectiveHasseRun_result (j : ℕ) (P : CompPoly.CPolynomial F) :
    (effectiveHasseRun j P).result = centeredHasseDeriv j P := by
  simp [effectiveHasseRun, centeredHasseDeriv, Array.map_ofFn, Function.comp_def]

/-- One field multiplication is executed at every source coefficient position, including zeros. -/
@[simp]
theorem effectiveHasseRun_multiplications (j : ℕ) (P : CompPoly.CPolynomial F) :
    (effectiveHasseRun j P).multiplications = P.val.size := by
  simp [effectiveHasseRun]

/-- The coefficient loop visits the full source array, even when normalization shortens
its output. -/
@[simp]
theorem effectiveHasseRun_visited (j : ℕ) (P : CompPoly.CPolynomial F) :
    (effectiveHasseRun j P).visited = P.val.size := by
  simp [effectiveHasseRun]

/-- Concrete shifted values for `X, Y₀, ..., Y_r`. -/
def centeredJetValues {r : ℕ} (center : F) (P : CompPoly.CPolynomial F) :
    Fin (r + 2) → CompPoly.CPolynomial F :=
  Fin.cases (CompPoly.CPolynomial.C center + CompPoly.CPolynomial.X)
    (fun j => centeredHasseDeriv j.val P)

/-- Add the next centered candidate coefficient. -/
def effectiveRegularCandidate (k r : ℕ) (P : CompPoly.CPolynomial F) (gamma : F) :
    CompPoly.CPolynomial F :=
  P + CompPoly.CPolynomial.monomial (k + r) gamma

/-- Compute the full shifted differential residual of a centered candidate. -/
def effectiveResidual {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) : CompPoly.CPolynomial F :=
  Q.eval₂ cPolynomialCHom (centeredJetValues center P)

/-- Compute the first unresolved residual coefficient after adding `gamma`. -/
def effectiveResidualCoeff {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) (gamma : F) : F :=
  (effectiveResidual Q center (effectiveRegularCandidate k r P gamma)).coeff k

/-- Enumerate the base-field coefficients that make the next residual coefficient vanish. -/
def effectiveRegularCoefficients [Fintype F] {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) : Finset F :=
  Finset.univ.filter fun gamma => effectiveResidualCoeff Q center P k gamma = 0

/-! ### Representation equations -/

theorem coeff_centeredHasseDeriv (j : ℕ) (P : CompPoly.CPolynomial F) (i : ℕ) :
    (centeredHasseDeriv j P).coeff i =
      ((i + j).choose j : F) * P.coeff (i + j) := by
  rw [centeredHasseDeriv, CompPoly.CPolynomial.coeff_ofArray]
  by_cases hi : i < P.val.size
  · simp [Array.getD, hi]
  · have hij : P.val.size ≤ i + j := (Nat.le_of_not_gt hi).trans (Nat.le_add_right i j)
    simp [Array.getD, hi, CompPoly.CPolynomial.coeff,
      CompPoly.CPolynomial.Raw.coeff, hij]

@[simp]
theorem centeredHasseDeriv_toPoly (j : ℕ) (P : CompPoly.CPolynomial F) :
    (centeredHasseDeriv j P).toPoly = Polynomial.hasseDeriv j P.toPoly := by
  ext i
  rw [← CompPoly.CPolynomial.coeff_toPoly, coeff_centeredHasseDeriv,
    Polynomial.hasseDeriv_coeff, CompPoly.CPolynomial.coeff_toPoly]

@[simp]
theorem effectiveRegularCandidate_toPoly (k r : ℕ) (P : CompPoly.CPolynomial F) (gamma : F) :
    (effectiveRegularCandidate k r P gamma).toPoly =
      P.toPoly + Polynomial.monomial (k + r) gamma := by
  rw [effectiveRegularCandidate, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.monomial_toPoly]

theorem coeff_effectiveRegularCandidate (k r : ℕ) (P : CompPoly.CPolynomial F)
    (gamma : F) (i : ℕ) :
    (effectiveRegularCandidate k r P gamma).coeff i =
      P.coeff i + if i = k + r then gamma else 0 := by
  rw [effectiveRegularCandidate, CompPoly.CPolynomial.coeff_add,
    CompPoly.CPolynomial.coeff_monomial]

theorem unshift_effectiveRegularCandidate (center gamma : F) (k r : ℕ)
    (P : CompPoly.CPolynomial F) :
    unshift center (effectiveRegularCandidate k r P gamma) =
      regularLiftCandidate center gamma k r (unshift center P) := by
  rw [unshift, unshift, effectiveRegularCandidate_toPoly]
  simp only [map_add, Polynomial.taylor_monomial, regularLiftCandidate, hassePerturbation]
  congr 2
  rw [Polynomial.C_neg, sub_eq_add_neg]

theorem centeredJetValues_toPoly {r : ℕ} (center : F) (P : CompPoly.CPolynomial F)
    (v : Fin (r + 2)) :
    (centeredJetValues center P v).toPoly =
      match finToJetVariable r v with
      | none => Polynomial.C center + Polynomial.X
      | some j => Polynomial.taylor center (Polynomial.hasseDeriv j.val (unshift center P)) := by
  cases v using Fin.cases with
  | zero =>
      change (CompPoly.CPolynomial.C center + CompPoly.CPolynomial.X).toPoly =
        Polynomial.C center + Polynomial.X
      rw [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.C_toPoly,
        CompPoly.CPolynomial.X_toPoly]
  | succ j =>
      change (centeredHasseDeriv j.val P).toPoly =
        Polynomial.taylor center (Polynomial.hasseDeriv j.val (unshift center P))
      rw [centeredHasseDeriv_toPoly, unshift, Polynomial.hasseDeriv_taylor,
        Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]

/-- The computable residual denotes the existing shifted differential specialization. -/
theorem effectiveResidual_toPoly {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (P : CompPoly.CPolynomial F) :
    (effectiveResidual Q center P).toPoly =
      shiftedJetSubstitution center (unshift center P) (semanticEquation Q) := by
  rw [← cPolynomialToPolyHom_apply]
  rw [effectiveResidual, CPoly.eval₂_equiv]
  change cPolynomialToPolyHom
    (MvPolynomial.eval₂Hom cPolynomialCHom (centeredJetValues center P)
      (CPoly.fromCMvPolynomial Q)) = _
  calc
    _ = MvPolynomial.eval₂Hom
          (cPolynomialToPolyHom.comp cPolynomialCHom)
          (fun v => cPolynomialToPolyHom (centeredJetValues center P v))
          (CPoly.fromCMvPolynomial Q) :=
      MvPolynomial.map_eval₂Hom
        (R := F) (S₁ := CompPoly.CPolynomial F) (S₂ := F[X]) (σ := Fin (r + 2))
        cPolynomialCHom (centeredJetValues center P) cPolynomialToPolyHom
        (CPoly.fromCMvPolynomial Q)
    _ = shiftedJetSubstitution center (unshift center P) (semanticEquation Q) := by
      rw [semanticEquation, shiftedJetSubstitution, MvPolynomial.aeval_def,
        MvPolynomial.eval₂_rename]
      change MvPolynomial.eval₂Hom
          (cPolynomialToPolyHom.comp cPolynomialCHom)
          (fun v => cPolynomialToPolyHom (centeredJetValues center P v))
          (CPoly.fromCMvPolynomial Q) =
        MvPolynomial.eval₂Hom (algebraMap F F[X])
          ((fun v : JetVariable r => match v with
            | none => Polynomial.C center + Polynomial.X
            | some j => Polynomial.taylor center
                (Polynomial.hasseDeriv j.val (unshift center P))) ∘ finToJetVariable r)
          (CPoly.fromCMvPolynomial Q)
      apply MvPolynomial.eval₂Hom_congr
      · ext x n
        change (CompPoly.CPolynomial.C x).toPoly.coeff n = (Polynomial.C x).coeff n
        rw [CompPoly.CPolynomial.C_toPoly]
      · funext v
        exact centeredJetValues_toPoly center P v
      · rfl

@[simp]
theorem mem_effectiveRegularCoefficients [Fintype F] {r : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (k : ℕ) (gamma : F) :
    gamma ∈ effectiveRegularCoefficients Q center P k ↔
      effectiveResidualCoeff Q center P k gamma = 0 := by
  simp only [effectiveRegularCoefficients, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Under the established prefix invariant, the executable coefficient filter accepts exactly
those lifts that extend residual divisibility by one order. No regularity or characteristic
hypothesis is needed for this equivalence; those hypotheses ensure unique continuation. -/
theorem mem_effectiveRegularCoefficients_iff_dvd [Fintype F] {r k : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (gamma : F) (hk : 0 < k)
    (hresidual : X ^ k ∣ shiftedJetSubstitution center (unshift center P)
      (semanticEquation Q)) :
    gamma ∈ effectiveRegularCoefficients Q center P k ↔
      X ^ (k + 1) ∣ shiftedJetSubstitution center
        (unshift center (effectiveRegularCandidate k r P gamma)) (semanticEquation Q) := by
  rw [mem_effectiveRegularCoefficients]
  have hp := X_pow_dvd_shiftedJetSubstitution_regularLiftCandidate hk
    (semanticEquation Q) center gamma (unshift center P) hresidual
  rw [unshift_effectiveRegularCandidate]
  rw [X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd _ k hp]
  unfold effectiveResidualCoeff
  rw [CompPoly.CPolynomial.coeff_toPoly, effectiveResidual_toPoly,
    unshift_effectiveRegularCandidate]

/-- The same executable acceptance criterion in the manuscript's original centered coordinate. -/
theorem mem_effectiveRegularCoefficients_iff_centered_dvd [Fintype F] {r k : ℕ}
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F)
    (P : CompPoly.CPolynomial F) (gamma : F) (hk : 0 < k)
    (hresidual : (X - C center) ^ k ∣
      differentialSpecialization (semanticEquation Q) (unshift center P)) :
    gamma ∈ effectiveRegularCoefficients Q center P k ↔
      (X - C center) ^ (k + 1) ∣ differentialSpecialization (semanticEquation Q)
        (unshift center (effectiveRegularCandidate k r P gamma)) := by
  have hshifted : X ^ k ∣ shiftedJetSubstitution center (unshift center P)
      (semanticEquation Q) := by
    rw [← taylor_differentialSpecialization, X_pow_dvd_taylor_iff_X_sub_C_pow_dvd]
    exact hresidual
  rw [mem_effectiveRegularCoefficients_iff_dvd Q center P gamma hk hshifted,
    ← taylor_differentialSpecialization, X_pow_dvd_taylor_iff_X_sub_C_pow_dvd]

end ReedSolomon.HiddenDerivative
