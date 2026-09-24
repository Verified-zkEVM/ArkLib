/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
/-!
# Agreement cuts on polynomial-graph components

A positive-dimensional regular component containing power-batched agreement cuts forces the
corresponding message polynomials to agree at those coordinates. A fixed interpolation sample
therefore determines a tuple with at least as many common agreements as the component cuts.

## Main statements

* `commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime`: a regular prime component's
  agreement cut implies agreement of every constituent polynomial.
* `exists_polynomialGraph_of_primeTaylorComponent_agreements`: agreement cuts determine a
  polynomial graph with the corresponding common-agreement lower bound.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- A regular prime component's power-batched agreement cut forces agreement of each
constituent polynomial at that coordinate. -/
theorem commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (ιₑ : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [I.IsPrime]
    (hsep : jointInitialJetSeparant center Q ∉ I)
    (hdim : 0 < (affineHilbertPolynomial I).natDegree)
    (P : Fin (ℓ + 1) → F[X])
    (hgraph : ∀ x, x ∈ {x | x ∈ zeroLocus E I ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0} →
      x = fun j ↦ (powerBatchedJetGraphMap (r := r) center
        (fun t ↦ (P t).map ιₑ) j).eval (x none))
    (hpoly : ∀ x, x ∈ {x | x ∈ zeroLocus E I ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0} →
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
        K (fun j ↦ x (some j)) = powerBatchedPolynomial
          (fun t ↦ (P t).map ιₑ) (x none))
    (i : Fin n)
    (hcut : jointTaylorAgreementEquation center Q K τ (Polynomial.C (ιₑ (domain i)))
      (powerBatchedCoordinate (fun t ↦ ιₑ (w t i))) ∈ I) :
    ∀ t, (P t).eval (domain i) = w t i := by
  let regularSet := {x : Option (Fin (r + 1)) → E | x ∈ zeroLocus E I ∧
    aeval x (jointInitialJetSeparant center Q) ≠ 0}
  have hregular : IsLeftRegular (Ideal.Quotient.mk I (jointInitialJetSeparant center Q)) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hsep)
  have hinfinite : regularSet.Infinite := by
    intro hfinite
    have hzero := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp hfinite
    omega
  have hinj : Set.InjOn (fun x : Option (Fin (r + 1)) → E ↦ x none) regularSet := by
    intro x hx y hy hxy
    change x none = y none at hxy
    rw [hgraph x hx, hgraph y hy, hxy]
  let domainE := domain.trans ⟨ιₑ, ιₑ.injective⟩
  let wordE := fun t j ↦ ιₑ (w t j)
  let tupleE := fun t ↦ (P t).map ιₑ
  let mismatch := curveDiscrepancy domainE wordE tupleE i
  have hzero : mismatch = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (hinfinite.image hinj).mono
    rintro z ⟨x, hx, rfl⟩
    have hφ : (Polynomial.aeval (x none)).toRingHom = Polynomial.evalRingHom (x none) := by
      ext a <;> simp
    let Qz := MvPolynomial.map (Polynomial.evalRingHom (x none)) Q
    let y := powerBatchedCoordinate (fun t ↦ ιₑ (w t i))
    have hsep' : aeval (fun j ↦ x (some j)) (initialJetSeparant center Qz) ≠ 0 := by
      have h := hx.2
      rw [aeval_jointInitialJetSeparant] at h
      simpa only [Qz, hφ] using h
    have hcut' : aeval (fun j ↦ x (some j))
        (taylorAgreementEquation center Qz K τ (ιₑ (domain i)) (y.eval (x none))) = 0 := by
      have h := hx.1 _ hcut
      rw [aeval_jointTaylorAgreementEquation] at h
      simpa only [Qz, y, hφ, Polynomial.eval_C] using h
    have heval := (taylorAgreementEquation_eq_zero_iff center
      Qz hτ
      (fun j ↦ x (some j)) hsep' (ιₑ (domain i))
      (y.eval (x none))).mp hcut'
    have heval' := heval
    simp only [Qz] at heval'
    change mismatch.eval (x none) = 0
    rw [curveDiscrepancy_eval]
    rw [sub_eq_zero]
    simp only [domainE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rw [← hpoly x hx, heval']
    rw [powerBatchedCoordinate_eval]
    rfl
  have hcommon := (curveDiscrepancy_eq_zero_iff domainE wordE tupleE i).mp hzero
  intro t
  apply ιₑ.injective
  simpa only [domainE, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk,
    wordE, tupleE, Polynomial.eval_map, Polynomial.eval₂_at_apply] using hcommon t

noncomputable local instance componentAgreementDecidableEq : DecidableEq F :=
  Classical.decEq _

open Classical in
/-- A positive-dimensional prime Taylor component containing `L` agreement cuts determines a
degree-bounded polynomial tuple with at least `L` common agreements. -/
theorem exists_polynomialGraph_of_primeTaylorComponent_agreements [IsAlgClosed E]
    {L : ℕ} (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (indices : Finset (Fin n)) (hcard : indices.card = L) (hkL : k ≤ L)
    (ιₑ : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [I.IsPrime]
    (hsep : jointInitialJetSeparant center Q ∉ I)
    (hdim : 0 < (affineHilbertPolynomial I).natDegree)
    (hhigh : ∀ l : Fin K, k ≤ l.val → jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ indices,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (ιₑ (domain i)))
        (powerBatchedCoordinate (fun t ↦ ιₑ (w t i))) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      L ≤ (commonCurveAgreementSet domain w P).card ∧
      (∀ x, x ∈ {x | x ∈ zeroLocus E I ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0} →
        x = fun j ↦ (powerBatchedJetGraphMap (r := r) center
          (fun t ↦ (P t).map ιₑ) j).eval (x none)) ∧
      (∀ x, x ∈ {x | x ∈ zeroLocus E I ∧
        aeval x (jointInitialJetSeparant center Q) ≠ 0} →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) = powerBatchedPolynomial
            (fun t ↦ (P t).map ιₑ) (x none)) ∧
      (∀ p ∈ I, aeval (powerBatchedJetGraphMap (r := r) center
        (fun t ↦ (P t).map ιₑ)) p = 0) ∧
      aeval (powerBatchedJetGraphMap (r := r) center (fun t ↦ (P t).map ιₑ))
        (jointInitialJetSeparant center Q) ≠ 0 := by
  classical
  obtain ⟨sample, hsub, hsample⟩ := Finset.exists_subset_card_eq (hcard ▸ hkL)
  obtain ⟨P, hP, _hsampleP, hgraph, hpoly, hvanish, hsepGraph⟩ :=
    exists_polynomialGraph_of_primeTaylorComponent domain w sample hsample ιₑ center Q
      hK τ hτ I hsep hdim hhigh (fun i hi ↦ hcuts i (hsub hi))
  refine ⟨P, hP, ?_, hgraph, hpoly, hvanish, hsepGraph⟩
  rw [← hcard]
  apply Finset.card_le_card
  intro i hi
  simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact commonCurveAgreement_of_jointTaylorAgreementEquation_mem_prime domain w ιₑ center Q K τ
    hτ I hsep hdim P hgraph hpoly i (hcuts i hi)

end ReedSolomon
