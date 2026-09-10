/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ComponentAgreement
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Specialization
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.HighCutGeometry
/-!
# Admissible polynomial graphs in the symbolic Taylor chart

An admissible tuple carries literal polynomial identities along its whole retained-challenge
graph.  The reconstruction identities ensure that every regular specialization is the actual
power-batched message polynomial, not merely a jet with the same initial coordinates.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- Restriction to the polynomial initial-jet graph of a base-field tuple. -/
def chartTuplePullback (iota : F →+* E) (center : E)
    (P : Fin (ℓ + 1) → F[X]) :
    MvPolynomial (Option (Fin (r + 1))) E →ₐ[E] E[X] :=
  polynomialGraphPullback
    (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota))

/-- The specialized initial jet on a tuple graph. -/
def chartTupleJet (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) : Fin (r + 1) → E :=
  fun j ↦ (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota) j).eval z

/-- One Taylor coefficient of the power-batched tuple, retained as a polynomial in the
batching challenge. -/
def powerBatchedTaylorCoefficient (iota : F →+* E) (center : E)
    (P : Fin (ℓ + 1) → F[X]) (l : ℕ) : E[X] :=
  powerBatchedCoordinate (fun t ↦ (Polynomial.taylor center ((P t).map iota)).coeff l)

theorem powerBatchedTaylorCoefficient_eval (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) (l : ℕ) :
    (powerBatchedTaylorCoefficient iota center P l).eval z =
      (Polynomial.taylor center
        (powerBatchedPolynomial (fun t ↦ (P t).map iota) z)).coeff l := by
  rw [powerBatchedTaylorCoefficient, powerBatchedCoordinate_eval]
  simp only [powerBatchedPolynomial, map_sum, map_smul, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]

/-- Admissibility at an explicit common Taylor exponent. All high equations and reconstruction
identities use the same numerator padding. -/
structure IsAdmissibleChartTupleAtExponent [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) (P : Fin (ℓ + 1) → F[X]) : Prop where
  degree : ∀ t, (P t).degree < k
  common : L ≤ (commonCurveAgreementSet domain w P).card
  initial : chartTuplePullback iota center P (symbolicSourceInitialEquation center Q) = 0
  high : ∀ l : Fin K, k ≤ l.val →
    chartTuplePullback iota center P
      ((optionEquivRight E _).symm
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) = 0
  regular : chartTuplePullback iota center P (symbolicSourceSeparant center Q) ≠ 0
  reconstruction : ∀ l : Fin K,
    chartTuplePullback iota center P
        ((optionEquivRight E _).symm
          (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))) =
      (chartTuplePullback iota center P (symbolicSourceSeparant center Q)) ^ τ *
        powerBatchedTaylorCoefficient iota center P l.val

/-- Graph restriction followed by retained-challenge evaluation is evaluation at the
specialized tuple jet. -/
theorem eval_chartTuplePullback (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) (p : MvPolynomial (Option (Fin (r + 1))) E) :
    (chartTuplePullback iota center P p).eval z =
      aeval (fun j ↦ j.elim z (chartTupleJet iota center z P)) p := by
  rw [chartTuplePullback, eval_polynomialGraphPullback]
  rfl

/-- A flattened symbolic polynomial specializes its retained coefficients before it is
evaluated at the tuple jet. -/
theorem eval_chartTuplePullback_symbolic (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) (p : MvPolynomial (Fin (r + 1)) E[X]) :
    (chartTuplePullback iota center P ((optionEquivRight E _).symm p)).eval z =
      aeval (chartTupleJet iota center z P)
        (MvPolynomial.map (Polynomial.evalRingHom z) p) := by
  rw [eval_chartTuplePullback, MvPolynomial.aeval_optionEquivRight_symm]
  rfl

/-- Every regular specialization of an explicitly padded admissible graph reconstructs the
actual power-batched polynomial. -/
theorem IsAdmissibleChartTupleAtExponent.specialize [DecidableEq F]
    {domain : Fin n ↪ F} {w : Fin (ℓ + 1) → Fin n → F}
    {iota : F →+* E} {center : E} {Q : DifferentialPolynomial E[X] r}
    {K k L τ : ℕ} {P : Fin (ℓ + 1) → F[X]}
    (hP : IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K) (z : E)
    (hz : (chartTuplePullback iota center P (symbolicSourceSeparant center Q)).eval z ≠ 0) :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    let jet := chartTupleJet iota center z P
    aeval jet (initialJetEquation center Qz) = 0 ∧
      aeval jet (initialJetSeparant center Qz) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval jet (commonTaylorNumerator center Qz K l (τ := τ)) = 0) ∧
      rationalTaylorPolynomial center Qz K jet =
        powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jet : Fin (r + 1) → E := chartTupleJet iota center z P
  have hsep : aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [symbolicSourceSeparant, eval_chartTuplePullback_symbolic] at hz
    rw [map_initialJetSeparantOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hz
    exact hz
  have hinit : aeval jet (initialJetEquation center Qz) = 0 := by
    have h := congrArg (fun p : E[X] ↦ p.eval z) hP.initial
    rw [symbolicSourceInitialEquation, eval_chartTuplePullback_symbolic] at h
    rw [map_initialJetEquationOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C,
      Polynomial.eval_zero] at h
    exact h
  have hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (commonTaylorNumerator center Qz K l (τ := τ)) = 0 := by
    intro l hl
    have h := congrArg (fun p : E[X] ↦ p.eval z) (hP.high l hl)
    rw [eval_chartTuplePullback_symbolic] at h
    simpa only [eval_commonTaylorNumeratorOver, Polynomial.eval_zero] using h
  refine ⟨hinit, hsep, hhigh, ?_⟩
  apply Polynomial.taylor_injective center
  ext l
  by_cases hl : l < K
  · have h := congrArg (fun p : E[X] ↦ p.eval z) (hP.reconstruction ⟨l, hl⟩)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      powerBatchedTaylorCoefficient_eval] at h
    rw [eval_chartTuplePullback_symbolic,
      eval_commonTaylorNumeratorOver (τ := τ),
      symbolicSourceSeparant, eval_chartTuplePullback_symbolic, map_initialJetSeparantOver,
      show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at h
    rw [aeval_commonTaylorNumerator_of_exponent _ _ _ K τ hτ _ hsep] at h
    have he := (mul_left_cancel₀ (pow_ne_zero _ hsep)) h
    simpa only [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix,
      if_pos hl] using he
  · have hleft := degree_rationalTaylorPolynomial_lt_of_high_cuts_and_exponent
      center Qz K k τ hτ jet hsep hhigh
    have hright := powerBatchedPolynomial_degree_lt
      (fun t ↦ (P t).map iota) z k (fun t ↦ Polynomial.degree_map_le.trans_lt (hP.degree t))
    have hkl : (k : WithBot ℕ) ≤ l := by exact_mod_cast (show k ≤ l by omega)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hleft.trans_le hkl),
      Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hright.trans_le hkl)]

/-- A recognized positive-dimensional prime component produces an intrinsically admissible
tuple, including all reconstruction identities on the full polynomial graph. -/
theorem exists_admissibleChartTuple_of_symbolic_prime_agreements_of_exponent
    [IsAlgClosed E] [DecidableEq F] {K k L : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ I)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l (τ := τ) ∈ I)
    (hcuts : ∀ i ∈ indices,
      symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
        (fun t ↦ iota (w t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X],
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P ∧
      ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) (x none) := by
  obtain ⟨P, hdegree, hcommon, hgraph, hpoly, hvanish, hregular⟩ :=
    exists_polynomialGraph_of_symbolic_prime_agreements_of_exponent domain w indices
      hcard hkL iota center Q hK τ hτ I hI hs hd hhigh hcuts
  refine ⟨P, ⟨hdegree, hcommon, hvanish _ hinit,
    (fun l hl ↦ hvanish _ (hhigh l hl)), hregular, ?_⟩, hgraph⟩
  intro l
  have hinfinite : (principalOpenZeroLocus I
      (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hI hs hfinite
    omega
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none)
      (principalOpenZeroLocus I (symbolicSourceSeparant center Q)) := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  apply Polynomial.eq_of_infinite_eval_eq
  apply (hinfinite.image hinj).mono
  rintro z ⟨x, hx, rfl⟩
  change (chartTuplePullback iota center P
      (symbolicSourceNumerator center Q K l (τ := τ))).eval (x none) =
    ((chartTuplePullback iota center P (symbolicSourceSeparant center Q)) ^ τ *
      powerBatchedTaylorCoefficient iota center P l.val).eval (x none)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [eval_chartTuplePullback, eval_chartTuplePullback,
    powerBatchedTaylorCoefficient_eval]
  change aeval (polynomialGraphPoint
      (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) (x none))
        (symbolicSourceNumerator center Q K l (τ := τ)) =
    aeval (polynomialGraphPoint
      (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) (x none))
        (symbolicSourceSeparant center Q) ^ τ *
      (Polynomial.taylor center
        (powerBatchedPolynomial (fun t ↦ (P t).map iota) (x none))).coeff l.val
  rw [← hgraph x hx]
  let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
  have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
    ext a <;> simp [φ]
  have hS : aeval (fun j ↦ x (some j))
      (MvPolynomial.map φ.toRingHom (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 := by
    simpa only [symbolicSourceSeparant, MvPolynomial.aeval_optionEquivRight_symm,
      hφ] using hx.2
  have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
    (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hS l
  simp only [hφ, φ, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id, Polynomial.eval_C] at hcoeff
  rw [hpoly x hx] at hcoeff
  simpa only [symbolicSourceNumerator, symbolicSourceSeparant,
    MvPolynomial.aeval_optionEquivRight_symm] using hcoeff


end ReedSolomon
