/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentAgreement
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedPointRecognition
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen

/-!
# Admissible graphs of power-batched polynomial tuples

A polynomial tuple determines a graph in the retained-challenge and initial-jet coordinates.
Admissibility records the initial equation, regularity, high Taylor cuts, and reconstruction
identities along the entire graph. A positive-dimensional prime component with the corresponding
agreement cuts yields such an admissible tuple.

## Main statements

* `IsAdmissibleChartTupleAtExponent`: graph identities and degree and agreement bounds for a
  power-batched tuple.
* `IsAdmissibleChartTupleAtExponent.specialize`: every regular specialization satisfies the
  Taylor-chart equations and reconstructs the power-batched polynomial.
* `exists_admissibleChartTuple_of_primeTaylorComponent_agreements`: a regular positive-dimensional
  prime component yields an admissible tuple with its agreement bound.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- Restriction to the polynomial initial-jet graph of a base-field tuple. -/
def chartTuplePullback (iota : F →+* E) (center : E)
    (P : Fin (ℓ + 1) → F[X]) :
    MvPolynomial (Option (Fin (r + 1))) E →ₐ[E] E[X] :=
  MvPolynomial.aeval (powerBatchedJetGraphMap (r := r) center
    (fun t ↦ (P t).map iota))

/-- The specialized initial jet on a tuple graph. -/
def chartTupleJet (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) : Fin (r + 1) → E :=
  fun j ↦ (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota) j).eval z

/-- One Taylor coefficient of the power-batched tuple, retained as a polynomial in the
batching challenge. -/
def powerBatchedTaylorCoefficient (iota : F →+* E) (center : E)
    (P : Fin (ℓ + 1) → F[X]) (l : ℕ) : E[X] :=
  powerBatchedCoordinate (fun t ↦ (Polynomial.taylor center ((P t).map iota)).coeff l)

/-- Evaluation of a power-batched Taylor coefficient is the corresponding coefficient of the
Taylor expansion of the specialized tuple polynomial. -/
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
  initial : chartTuplePullback iota center P (jointInitialJetEquation center Q) = 0
  high : ∀ l : Fin K, k ≤ l.val →
    chartTuplePullback iota center P (jointCommonTaylorNumerator center Q τ l) = 0
  regular : chartTuplePullback iota center P (jointInitialJetSeparant center Q) ≠ 0
  reconstruction : ∀ l : Fin K,
    chartTuplePullback iota center P (jointCommonTaylorNumerator center Q τ l) =
      (chartTuplePullback iota center P (jointInitialJetSeparant center Q)) ^ τ *
        powerBatchedTaylorCoefficient iota center P l.val

/-- Evaluating graph restriction at `z` is evaluation at the specialized tuple jet. -/
theorem eval_chartTuplePullback (iota : F →+* E) (center z : E)
    (P : Fin (ℓ + 1) → F[X]) (p : MvPolynomial (Option (Fin (r + 1))) E) :
    (chartTuplePullback iota center P p).eval z =
      aeval (fun j ↦ j.elim z (chartTupleJet iota center z P)) p := by
  rw [chartTuplePullback, MvPolynomial.polynomial_eval_aeval]
  have hpoint : (fun i ↦ (powerBatchedJetGraphMap (r := r) center
      (fun t ↦ (P t).map iota) i).eval z) =
      (fun j ↦ j.elim z (chartTupleJet iota center z P)) := by
    funext j
    cases j <;> simp [chartTupleJet, powerBatchedJetGraphMap]
  rw [hpoint]
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
    (hz : (chartTuplePullback iota center P (jointInitialJetSeparant center Q)).eval z ≠ 0) :
    let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
    let jet := chartTupleJet iota center z P
    aeval jet (initialJetEquation center Qz) = 0 ∧
      aeval jet (initialJetSeparant center Qz) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        aeval jet (commonTaylorNumerator center Qz τ l.val) = 0) ∧
      rationalTaylorPolynomial center Qz K jet =
        powerBatchedPolynomial (fun t ↦ (P t).map iota) z := by
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jet : Fin (r + 1) → E := chartTupleJet iota center z P
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ]
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hsep : aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [jointInitialJetSeparant, eval_chartTuplePullback_symbolic,
      ← hφ, map_initialJetSeparant] at hz
    simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hcenter] using hz
  have hinit : aeval jet (initialJetEquation center Qz) = 0 := by
    have h := congrArg (fun p : E[X] ↦ p.eval z) hP.initial
    rw [jointInitialJetEquation, eval_chartTuplePullback_symbolic,
      ← hφ, map_initialJetEquation] at h
    simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hcenter, Polynomial.eval_zero] using h
  have hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (commonTaylorNumerator center Qz τ l.val) = 0 := by
    intro l hl
    have h := congrArg (fun p : E[X] ↦ p.eval z) (hP.high l hl)
    rw [jointCommonTaylorNumerator, eval_chartTuplePullback_symbolic,
      ← hφ, map_commonTaylorNumeratorOver_eq] at h
    simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, hcenter, Polynomial.eval_zero] using h
  refine ⟨hinit, hsep, hhigh, ?_⟩
  apply Polynomial.taylor_injective center
  ext l
  by_cases hl : l < K
  · have h := congrArg (fun p : E[X] ↦ p.eval z) (hP.reconstruction ⟨l, hl⟩)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      powerBatchedTaylorCoefficient_eval] at h
    rw [jointCommonTaylorNumerator, eval_chartTuplePullback_symbolic] at h
    rw [jointInitialJetSeparant, eval_chartTuplePullback_symbolic] at h
    rw [← hφ, map_commonTaylorNumeratorOver_eq, map_initialJetSeparant] at h
    have h' := h
    have h : aeval jet (commonTaylorNumerator center Qz τ l) =
        aeval jet (initialJetSeparant center Qz) ^ τ *
          (Polynomial.taylor center
            (powerBatchedPolynomial (fun t ↦ (P t).map iota) z)).coeff l := by
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using h'
    have hsepφ : aeval jet
        (map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
      rw [map_initialJetSeparant]
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using hsep
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      φ (Polynomial.C center) Q K τ hτ jet hsepφ ⟨l, hl⟩
    rw [map_commonTaylorNumeratorOver_eq, map_initialJetSeparant] at hcoeff
    have hcoeff' := hcoeff
    have hcoeff : aeval jet (commonTaylorNumerator center Qz τ l) =
        aeval jet (initialJetSeparant center Qz) ^ τ *
          (Polynomial.taylor center
            (rationalTaylorPolynomial center Qz K jet)).coeff l := by
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using hcoeff'
    rw [hcoeff] at h
    have he := (mul_left_cancel₀ (pow_ne_zero _ hsep)) h
    simpa [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix, hl] using he
  · have hsepφ : aeval jet
        (map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
      rw [map_initialJetSeparant]
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using hsep
    have hhighφ : ∀ l : Fin K, k ≤ l.val →
        aeval jet (map φ.toRingHom
          (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) = 0 := by
      intro l hl
      rw [map_commonTaylorNumeratorOver_eq]
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using hhigh l hl
    have hleft := degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent
      φ (Polynomial.C center) Q K k τ hτ jet hsepφ hhighφ
    have hleft' : (rationalTaylorPolynomial center Qz K jet).degree < k := by
      simpa only [jet, Qz, ← hφ, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, hcenter] using hleft
    have hright := powerBatchedPolynomial_degree_lt
      (fun t ↦ (P t).map iota) z k
      (fun t ↦ Polynomial.degree_map_le.trans_lt (hP.degree t))
    have hkl : (k : WithBot ℕ) ≤ l := by
      exact_mod_cast (show k ≤ l by omega)
    rw [Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hleft'.trans_le hkl),
      Polynomial.coeff_eq_zero_of_degree_lt (by
        simpa only [Polynomial.degree_taylor] using hright.trans_le hkl)]

open Classical in
/-- A positive-dimensional regular prime Taylor component with agreement cuts determines an
admissible tuple and is covered by its polynomial graph. -/
theorem exists_admissibleChartTuple_of_primeTaylorComponent_agreements
    [IsAlgClosed E] {K k L : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) (hI : I.IsPrime)
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hinit : jointInitialJetEquation center Q ∈ I)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ indices,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (iota (domain i)))
        (powerBatchedCoordinate (fun t ↦ iota (w t i))) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X],
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P ∧
      ∀ x ∈ {x | x ∈ zeroLocus E I ∧
          aeval x (jointInitialJetSeparant center Q) ≠ 0},
        x = fun j ↦ (powerBatchedJetGraphMap (r := r) center
          (fun t ↦ (P t).map iota) j).eval (x none) := by
  obtain ⟨P, hdegree, hcommon, hgraph, hpoly, hvanish, hregular⟩ :=
    exists_polynomialGraph_of_primeTaylorComponent_agreements domain w indices hcard hkL
      iota center Q hK τ hτ I hs hd hhigh hcuts
  refine ⟨P, ⟨hdegree, hcommon, ?_, ?_, ?_, ?_⟩, hgraph⟩
  · exact hvanish _ hinit
  · intro l hl
    exact hvanish _ (hhigh l hl)
  · exact hregular
  · intro l
    have hinfinite : {x : Option (Fin (r + 1)) → E |
        x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0}.Infinite := by
      intro hfinite
      have hreg : IsLeftRegular (Ideal.Quotient.mk I (jointInitialJetSeparant center Q)) :=
        IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
          (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
      have hzero :=
        (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hreg).mp hfinite
      omega
    have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none)
        {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0} := by
      intro x hx y hy hxy
      change x none = y none at hxy
      rw [hgraph x hx, hgraph y hy, hxy]
    apply Polynomial.eq_of_infinite_eval_eq
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    change (chartTuplePullback iota center P (jointCommonTaylorNumerator center Q τ l)).eval
        (x none) =
      ((chartTuplePullback iota center P (jointInitialJetSeparant center Q)) ^ τ *
        powerBatchedTaylorCoefficient iota center P l.val).eval (x none)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow]
    rw [eval_chartTuplePullback, eval_chartTuplePullback,
      powerBatchedTaylorCoefficient_eval]
    have hpoint : x = fun j ↦ j.elim (x none) (chartTupleJet iota center (x none) P) := by
      funext j
      have hj := congrFun (hgraph x hx) j
      cases j with
      | none => simp
      | some j => simpa [powerBatchedJetGraphMap, chartTupleJet] using hj
    rw [← hpoint]
    change aeval x (jointCommonTaylorNumerator center Q τ l) =
      aeval x (jointInitialJetSeparant center Q) ^ τ *
      (Polynomial.taylor center
        (powerBatchedPolynomial (fun t ↦ (P t).map iota) (x none))).coeff l.val
    let φ : E[X] →ₐ[E] E := Polynomial.aeval (x none)
    have hφ : φ.toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp [φ]
    have hcenter : φ (Polynomial.C center) = center := by simp [φ]
    have hS : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
      simpa only [jointInitialJetSeparant, aeval_optionEquivRight_symm] using hx.2
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
      (Polynomial.C center) Q K τ hτ (fun j ↦ x (some j)) hS l
    have hcoeff' : aeval (fun j ↦ x (some j))
        (MvPolynomial.map φ.toRingHom
          (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)) =
        aeval (fun j ↦ x (some j))
          (MvPolynomial.map φ.toRingHom (initialJetSeparant (Polynomial.C center) Q)) ^ τ *
          (Polynomial.taylor center
            (rationalTaylorPolynomial center (MvPolynomial.map φ.toRingHom Q) K
              (fun j ↦ x (some j)))).coeff l.val := by
      simpa only [hcenter, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using hcoeff
    have hpoly' := hpoly x hx
    rw [← hφ] at hpoly'
    rw [hpoly'] at hcoeff'
    simpa only [jointCommonTaylorNumerator, jointInitialJetSeparant,
      aeval_optionEquivRight_symm, φ] using hcoeff'

end ReedSolomon
